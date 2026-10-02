use std::collections::HashSet;
use std::fs;
use std::io::{self, Write};
use std::path::PathBuf;
use std::time::Instant;
use serde::{Deserialize, Serialize};
use walkdir::WalkDir;

pub const VIDEO_EXTENSIONS: &[&str] = &[
    "mp4", "mkv", "avi", "mov", "wmv", "flv", "webm", "m4v", "mpg", "mpeg",
    "m2v", "ts", "m2ts", "mts", "vob", "3gp", "3g2", "ogv", "f4v", "f4p"
];

pub const AUDIO_EXTENSIONS: &[&str] = &[
    "mp3", "wav", "aac", "flac", "ogg", "m4a", "wma", "opus", "aiff", "aif",
    "alac", "mid", "midi", "mka", "ape"
];

pub const IMAGE_EXTENSIONS: &[&str] = &[
    "jpg", "jpeg", "png", "gif", "bmp", "webp", "tiff", "tif", "ico", "svg",
    "heic", "heif", "avif", "raw", "cr2", "nef", "arw"
];

pub const PDF_EXTENSIONS: &[&str] = &["pdf"];

#[derive(Debug, Serialize, Deserialize)]
pub struct ScannedFile {
    pub path: String,
    pub filename: String,
    pub ext: String,
    pub size: u64,
    pub mtime: f64,
    pub ctime: f64,
    pub media_type: String,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum ScanEvent {
    #[serde(rename = "file")]
    File(ScannedFile),
    #[serde(rename = "progress")]
    Progress { found: usize },
    #[serde(rename = "complete")]
    Complete { total: usize, elapsed_ms: u128 },
    #[serde(rename = "error")]
    Error { message: String },
}

pub fn matches_exclusion(filename_lower: &str, patterns: &[String]) -> bool {
    for pat in patterns {
        let p = pat.trim().to_lowercase();
        if p.is_empty() {
            continue;
        }
        if p.starts_with('*') && p.ends_with('*') && p.len() > 2 {
            let inner = &p[1..p.len() - 1];
            if filename_lower.contains(inner) {
                return true;
            }
        } else if p.starts_with('*') {
            let suffix = &p[1..];
            if filename_lower.ends_with(suffix) {
                return true;
            }
        } else if p.ends_with('*') {
            let prefix = &p[..p.len() - 1];
            if filename_lower.starts_with(prefix) {
                return true;
            }
        } else if filename_lower.contains(&p) {
            return true;
        }
    }
    false
}

pub fn detect_media_type(ext_clean: &str) -> Option<&'static str> {
    if VIDEO_EXTENSIONS.contains(&ext_clean) {
        Some("video")
    } else if AUDIO_EXTENSIONS.contains(&ext_clean) {
        Some("audio")
    } else if IMAGE_EXTENSIONS.contains(&ext_clean) {
        Some("image")
    } else if PDF_EXTENSIONS.contains(&ext_clean) {
        Some("pdf")
    } else {
        None
    }
}

pub fn run_scan(
    directories: &[PathBuf],
    target_media_type: &str,
    exclude_patterns: &[String],
    include_no_ext: bool,
) -> io::Result<()> {
    let start_time = Instant::now();
    let stdout = io::stdout();
    let mut writer = io::BufWriter::with_capacity(64 * 1024, stdout.lock());

    let mut seen_norm_paths = HashSet::new();
    let mut total_found = 0;

    let target_type = target_media_type.to_lowercase();

    for dir in directories {
        if !dir.is_dir() {
            continue;
        }

        for entry in WalkDir::new(dir)
            .follow_links(false)
            .into_iter()
            .filter_entry(|e| {
                let name = e.file_name().to_string_lossy();
                // Skip dotfiles and dotdirs (.git, .vscode, .DS_Store, etc.)
                !name.starts_with('.')
            })
            .filter_map(|e| e.ok())
        {
            if !entry.file_type().is_file() {
                continue;
            }

            let file_name = entry.file_name().to_string_lossy();
            let file_name_lower = file_name.to_lowercase();

            if matches_exclusion(&file_name_lower, exclude_patterns) {
                continue;
            }

            let path = entry.path();
            let ext_with_dot = path
                .extension()
                .map(|s| format!(".{}", s.to_string_lossy().to_lowercase()))
                .unwrap_or_default();

            let ext_clean = ext_with_dot.trim_start_matches('.');

            let detected = detect_media_type(ext_clean);

            let accepted_type = match target_type.as_str() {
                "video" => if detected == Some("video") { Some("video") } else { None },
                "audio" => if detected == Some("audio") { Some("audio") } else { None },
                "image" => if detected == Some("image") { Some("image") } else { None },
                "pdf" => if detected == Some("pdf") { Some("pdf") } else { None },
                _ => detected.or_else(|| if include_no_ext && ext_clean.is_empty() { Some("unknown") } else { None }),
            };

            let media_type_str = match accepted_type {
                Some(t) => t,
                None => continue,
            };

            let norm_path = match path.canonicalize() {
                Ok(p) => p.to_string_lossy().trim_start_matches(r"\\?\").to_string(),
                Err(_) => path.to_string_lossy().to_string(),
            };

            let norm_key = norm_path.to_lowercase();
            if !seen_norm_paths.insert(norm_key) {
                continue;
            }

            let metadata = match fs::metadata(path) {
                Ok(m) => m,
                Err(_) => continue,
            };

            let size = metadata.len();
            let mtime = metadata
                .modified()
                .ok()
                .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
                .map(|d| d.as_secs_f64())
                .unwrap_or(0.0);

            let ctime = metadata
                .created()
                .ok()
                .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
                .map(|d| d.as_secs_f64())
                .unwrap_or(mtime);

            let item = ScannedFile {
                path: norm_path,
                filename: file_name.to_string(),
                ext: ext_with_dot,
                size,
                mtime,
                ctime,
                media_type: media_type_str.to_string(),
            };

            let event = ScanEvent::File(item);
            if let Ok(json) = serde_json::to_string(&event) {
                let _ = writeln!(writer, "{}", json);
            }

            total_found += 1;
            if total_found % 500 == 0 {
                let prog = ScanEvent::Progress { found: total_found };
                if let Ok(json) = serde_json::to_string(&prog) {
                    let _ = writeln!(writer, "{}", json);
                }
                let _ = writer.flush();
            }
        }
    }

    let complete = ScanEvent::Complete {
        total: total_found,
        elapsed_ms: start_time.elapsed().as_millis(),
    };
    if let Ok(json) = serde_json::to_string(&complete) {
        let _ = writeln!(writer, "{}", json);
    }
    let _ = writer.flush();

    Ok(())
}
