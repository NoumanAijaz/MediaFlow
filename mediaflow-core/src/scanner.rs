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

pub fn sniff_media_type(path: &std::path::Path) -> Option<&'static str> {
    use std::io::Read;
    let mut file = fs::File::open(path).ok()?;
    let mut buffer = [0u8; 32];
    let n = file.read(&mut buffer).ok()?;
    if n < 4 {
        return None;
    }

    // Check PNG: 89 50 4E 47
    if buffer.starts_with(&[0x89, b'P', b'N', b'G']) {
        return Some("image");
    }
    // Check JPEG: FF D8 FF
    if buffer.starts_with(&[0xFF, 0xD8, 0xFF]) {
        return Some("image");
    }
    // Check GIF: GIF87a or GIF89a
    if buffer.starts_with(b"GIF8") {
        return Some("image");
    }
    // Check BMP: BM
    if buffer.starts_with(b"BM") {
        return Some("image");
    }
    // Check PDF: %PDF
    if buffer.starts_with(b"%PDF") {
        return Some("pdf");
    }
    // Check WebP: RIFF....WEBP
    if buffer.starts_with(b"RIFF") && n >= 12 && &buffer[8..12] == b"WEBP" {
        return Some("image");
    }
    // Check AVI: RIFF....AVI
    if buffer.starts_with(b"RIFF") && n >= 12 && &buffer[8..11] == b"AVI" {
        return Some("video");
    }
    // Check WAV: RIFF....WAVE
    if buffer.starts_with(b"RIFF") && n >= 12 && &buffer[8..12] == b"WAVE" {
        return Some("audio");
    }
    // Check MP4 / MOV / M4V / M4A: ftyp at offset 4
    if n >= 8 && &buffer[4..8] == b"ftyp" {
        if n >= 12 && (&buffer[8..12] == b"M4A " || &buffer[8..12] == b"m4a ") {
            return Some("audio");
        }
        return Some("video");
    }
    // Check Matroska / WebM: 1A 45 DF A3
    if buffer.starts_with(&[0x1A, 0x45, 0xDF, 0xA3]) {
        return Some("video");
    }
    // Check FLAC: fLaC
    if buffer.starts_with(b"fLaC") {
        return Some("audio");
    }
    // Check OGG: OggS
    if buffer.starts_with(b"OggS") {
        return Some("audio");
    }
    // Check MP3: ID3 or sync bytes FF FB / FF F3 / FF F2
    if buffer.starts_with(b"ID3") || (buffer[0] == 0xFF && (buffer[1] & 0xE0) == 0xE0) {
        return Some("audio");
    }

    None
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

            let is_no_ext = ext_clean.is_empty();
            let mut detected = detect_media_type(ext_clean);
            if detected.is_none() && is_no_ext {
                detected = sniff_media_type(path);
            }

            let accepted_type: Option<&str> = match target_type.as_str() {
                "video" => {
                    if detected == Some("video") || (include_no_ext && is_no_ext) {
                        Some(detected.unwrap_or("video"))
                    } else {
                        None
                    }
                }
                "audio" => {
                    if detected == Some("audio") || (include_no_ext && is_no_ext) {
                        Some(detected.unwrap_or("audio"))
                    } else {
                        None
                    }
                }
                "image" => {
                    if detected == Some("image") || (include_no_ext && is_no_ext) {
                        Some(detected.unwrap_or("image"))
                    } else {
                        None
                    }
                }
                "pdf" => {
                    if detected == Some("pdf") || (include_no_ext && is_no_ext) {
                        Some(detected.unwrap_or("pdf"))
                    } else {
                        None
                    }
                }
                _ => {
                    if let Some(d) = detected {
                        Some(d)
                    } else if include_no_ext && is_no_ext {
                        Some("unknown")
                    } else {
                        None
                    }
                }
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
