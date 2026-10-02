use std::collections::HashMap;
use std::fs::{self, File};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::Instant;
use md5::{Digest, Md5};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

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
        let n1 = file.read(&mut buffer)?;
        hasher.update(&buffer[..n1]);

        file.seek(SeekFrom::End(-(HEAD_SAMPLE_SIZE as i64)))?;
        let n2 = file.read(&mut buffer)?;
        hasher.update(&buffer[..n2]);
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
    let mut writer = io::BufWriter::new(stdout.lock());

    // Step 1: Ensure we have accurate file sizes and filter non-existent files
    let mut valid_items = Vec::with_capacity(items.len());
    let mut skipped = 0;

    for item in items {
        let p = Path::new(&item.path);
        let size = if item.size > 0 {
            item.size
        } else {
            match fs::metadata(p) {
                Ok(m) => m.len(),
                Err(_) => {
                    skipped += 1;
                    continue;
                }
            }
        };

        if size == 0 {
            // Skip 0-byte files or treat separately if desired
            skipped += 1;
            continue;
        }

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
        let _ = writeln!(writer, "{}", serde_json::to_string(&res).unwrap());
        let _ = writer.flush();
        return Ok(());
    }

    // Step 3: Compute head/tail fingerprints in parallel with Rayon
    let done_counter = Arc::new(AtomicUsize::new(0));
    let head_results: Vec<(String, Option<String>)> = candidate_items
        .par_iter()
        .map(|item| {
            let p = Path::new(&item.path);
            let h = compute_head_hash(p, item.size).ok();
            done_counter.fetch_add(1, Ordering::Relaxed);
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
        let _ = writeln!(writer, "{}", serde_json::to_string(&res).unwrap());
        let _ = writer.flush();
        return Ok(());
    }

    // Step 4: Compute full hash in parallel with Rayon
    let full_counter = Arc::new(AtomicUsize::new(0));
    let full_results: Vec<(String, Option<String>)> = full_hash_candidates
        .par_iter()
        .map(|path_str| {
            let p = Path::new(path_str);
            let h = compute_full_hash(p).ok();
            full_counter.fetch_add(1, Ordering::Relaxed);
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

    let duplicate_groups: Vec<Vec<String>> = final_groups
        .into_values()
        .filter(|g| g.len() > 1)
        .collect();

    let result = DedupeEvent::Groups {
        groups: duplicate_groups,
        skipped,
        elapsed_ms: start_time.elapsed().as_millis(),
    };

    let _ = writeln!(writer, "{}", serde_json::to_string(&result).unwrap());
    let _ = writer.flush();

    Ok(())
}
