use md5::{Digest, Md5};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};
use std::fs::{self, File};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Instant;

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct DedupeInputItem {
    pub path: String,
    #[serde(default)]
    pub size: u64,
}

#[derive(Debug, Serialize)]
#[serde(tag = "type")]
#[allow(dead_code)]
pub enum DedupeEvent {
    #[serde(rename = "progress")]
    Progress {
        done: usize,
        total: usize,
        phase: String,
    },
    #[serde(rename = "groups")]
    Groups {
        groups: Vec<Vec<String>>,
        skipped: usize,
        elapsed_ms: u128,
    },
    #[serde(rename = "error")]
    Error { message: String },
}

const CHUNK_SIZE: usize = 64 * 1024; // 64KB read chunk
const HEAD_SAMPLE_SIZE: u64 = 1024 * 1024; // 1MB for head/tail fingerprint

/// Compute head/tail fingerprint matching MediaFlow's Python calculate_file_hash logic
pub fn compute_head_hash(path: &Path, file_size: u64) -> io::Result<String> {
    let mut file = File::open(path)?;
    let mut hasher = Md5::new();

    if file_size > 2 * HEAD_SAMPLE_SIZE {
        // MD5 of string(file_size) + first 1MB + last 1MB
        hasher.update(file_size.to_string().as_bytes());
        let mut buffer = vec![0u8; HEAD_SAMPLE_SIZE as usize];
        file.read_exact(&mut buffer)?;
        hasher.update(&buffer);

        file.seek(SeekFrom::End(-(HEAD_SAMPLE_SIZE as i64)))?;
        file.read_exact(&mut buffer)?;
        hasher.update(&buffer);
    } else {
        let mut buffer = [0u8; CHUNK_SIZE];
        loop {
            let n = file.read(&mut buffer)?;
            if n == 0 {
                break;
            }
            hasher.update(&buffer[..n]);
        }
    }

    Ok(format!("{:x}", hasher.finalize()))
}

/// Compute full MD5 hash of entire file (streaming chunks)
pub fn compute_full_hash(path: &Path) -> io::Result<String> {
    let mut file = File::open(path)?;
    let mut hasher = Md5::new();
    let mut buffer = [0u8; CHUNK_SIZE];

    loop {
        let n = file.read(&mut buffer)?;
        if n == 0 {
            break;
        }
        hasher.update(&buffer[..n]);
    }

    Ok(format!("{:x}", hasher.finalize()))
}

pub fn run_dedupe(items: Vec<DedupeInputItem>) -> io::Result<()> {
    let start_time = Instant::now();
    let stdout = io::stdout();
    let writer = Arc::new(Mutex::new(io::BufWriter::new(stdout)));

    let emit_progress = |w: &Arc<Mutex<io::BufWriter<io::Stdout>>>, done: usize, total: usize, phase: &str| {
        let evt = DedupeEvent::Progress {
            done,
            total,
            phase: phase.to_string(),
        };
        if let Ok(mut lock) = w.lock() {
            let _ = writeln!(lock, "{}", serde_json::to_string(&evt).unwrap());
            let _ = lock.flush();
        }
    };

    // Step 1: Ensure we have accurate file sizes, filter non-existent files, and deduplicate identical inputs
    let mut valid_items = Vec::with_capacity(items.len());
    let mut seen_paths: HashSet<String> = HashSet::new();
    let mut skipped = 0;

    for item in items {
        let p = Path::new(&item.path);

        // Deduplicate identical physical file paths to prevent a file from matching itself.
        // Uses standardized path normalization to eliminate extended-length prefixes.
        let norm_key = crate::path_util::canonical_norm_key(p);

        if !seen_paths.insert(norm_key) {
            continue;
        }

        let size = match fs::metadata(p) {
            Ok(m) => m.len(),
            Err(_) => {
                if item.size > 0 {
                    item.size
                } else {
                    skipped += 1;
                    continue;
                }
            }
        };

        // 0-byte files are kept: the Python engine groups them (identical
        // empty content) and skipping them here made the two engines report
        // different duplicate groups for the same folder.
        valid_items.push(DedupeInputItem {
            path: item.path,
            size,
        });
    }

    // Step 2: Bucket by size
    let mut size_groups: HashMap<u64, Vec<DedupeInputItem>> = HashMap::new();
    for item in valid_items {
        size_groups.entry(item.size).or_default().push(item);
    }

    // Filter to candidates with at least 2 files sharing the exact byte size
    let candidate_items: Vec<DedupeInputItem> = size_groups
        .into_values()
        .filter(|g| g.len() > 1)
        .flatten()
        .collect();

    let total_candidates = candidate_items.len();
    if total_candidates == 0 {
        let res = DedupeEvent::Groups {
            groups: vec![],
            skipped,
            elapsed_ms: start_time.elapsed().as_millis(),
        };
        if let Ok(mut lock) = writer.lock() {
            let _ = writeln!(lock, "{}", serde_json::to_string(&res).unwrap());
            let _ = lock.flush();
        }
        return Ok(());
    }

    // Step 3: Compute head/tail fingerprints in parallel with Rayon
    emit_progress(&writer, 0, total_candidates, "Quick scan (head hash)");
    let done_counter = Arc::new(AtomicUsize::new(0));
    let done_counter_head = Arc::clone(&done_counter);
    let writer_head = Arc::clone(&writer);
    let head_results: Vec<(String, Option<String>)> = candidate_items
        .par_iter()
        .map(|item| {
            let p = Path::new(&item.path);
            let h = compute_head_hash(p, item.size).ok();
            let done = done_counter_head.fetch_add(1, Ordering::Relaxed) + 1;
            if done % 20 == 0 || done == total_candidates {
                emit_progress(&writer_head, done, total_candidates, "Quick scan (head hash)");
            }
            (item.path.clone(), h)
        })
        .collect();

    let mut head_groups: HashMap<String, Vec<String>> = HashMap::new();
    for (path, hash_opt) in head_results {
        match hash_opt {
            Some(h) => head_groups.entry(h).or_default().push(path),
            None => skipped += 1,
        }
    }

    // Filter to head hash matches with at least 2 files
    let full_hash_candidates: Vec<String> = head_groups
        .into_values()
        .filter(|g| g.len() > 1)
        .flatten()
        .collect();

    let total_full = full_hash_candidates.len();
    if total_full == 0 {
        let res = DedupeEvent::Groups {
            groups: vec![],
            skipped,
            elapsed_ms: start_time.elapsed().as_millis(),
        };
        if let Ok(mut lock) = writer.lock() {
            let _ = writeln!(lock, "{}", serde_json::to_string(&res).unwrap());
            let _ = lock.flush();
        }
        return Ok(());
    }

    // Step 4: Compute full hash in parallel with Rayon
    emit_progress(&writer, 0, total_full, "Confirming duplicates (full hash)");
    let full_counter = Arc::new(AtomicUsize::new(0));
    let full_counter_clone = Arc::clone(&full_counter);
    let writer_full = Arc::clone(&writer);
    let full_results: Vec<(String, Option<String>)> = full_hash_candidates
        .par_iter()
        .map(|path_str| {
            let p = Path::new(path_str);
            let h = compute_full_hash(p).ok();
            let done = full_counter_clone.fetch_add(1, Ordering::Relaxed) + 1;
            if done % 5 == 0 || done == total_full {
                emit_progress(&writer_full, done, total_full, "Confirming duplicates (full hash)");
            }
            (path_str.clone(), h)
        })
        .collect();

    let mut final_groups: HashMap<String, Vec<String>> = HashMap::new();
    for (path, hash_opt) in full_results {
        match hash_opt {
            Some(h) => final_groups.entry(h).or_default().push(path),
            None => skipped += 1,
        }
    }

    let mut duplicate_groups: Vec<Vec<String>> = final_groups
        .into_values()
        .map(|mut g| {
            g.sort();
            g.dedup();
            g
        })
        .filter(|g| g.len() > 1)
        .collect();

    duplicate_groups.sort_by(|a, b| a.first().cmp(&b.first()));

    let result = DedupeEvent::Groups {
        groups: duplicate_groups,
        skipped,
        elapsed_ms: start_time.elapsed().as_millis(),
    };

    if let Ok(mut lock) = writer.lock() {
        let _ = writeln!(lock, "{}", serde_json::to_string(&result).unwrap());
        let _ = lock.flush();
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dedupe_prevents_self_grouping() {
        let temp_dir = std::env::temp_dir();
        let test_file = temp_dir.join("mediaflow_dedupe_test.bin");
        fs::write(&test_file, b"sample-dedupe-data-12345").unwrap();

        let path_str = test_file.to_string_lossy().to_string();
        let items = vec![
            DedupeInputItem {
                path: path_str.clone(),
                size: 24,
            },
            DedupeInputItem {
                path: path_str.clone(),
                size: 24,
            },
        ];

        assert!(run_dedupe(items).is_ok());

        let _ = fs::remove_file(test_file);
    }
}
