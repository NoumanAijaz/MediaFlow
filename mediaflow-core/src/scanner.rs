use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fs;
use std::io::{self, Write};
use std::path::PathBuf;
use std::time::Instant;
use walkdir::WalkDir;

pub const VIDEO_EXTENSIONS: &[&str] = &[
    "mp4", "mkv", "avi", "mov", "wmv", "flv", "webm", "m4v", "mpg", "mpeg", "m2v", "ts", "m2ts",
    "mts", "vob", "3gp", "3g2", "ogv", "f4v", "f4p", "divx", "rm", "rmvb", "asf", "amv", "svi",
];

pub const AUDIO_EXTENSIONS: &[&str] = &[
    "mp3", "wav", "aac", "flac", "ogg", "m4a", "wma", "opus", "aiff", "aif", "alac", "mid", "midi",
    "mka", "ape", "amr", "m4b",
];

pub const IMAGE_EXTENSIONS: &[&str] = &[
    "jpg", "jpeg", "png", "gif", "bmp", "webp", "tiff", "tif", "jfif", "ico", "svg", "heic", "heif",
    "avif", "raw", "cr2", "nef", "arw",
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
        } else if let Some(suffix) = p.strip_prefix('*') {
            if filename_lower.ends_with(suffix) {
                return true;
            }
        } else if let Some(prefix) = p.strip_suffix('*') {
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

    // Check PNG: 89 50 4E 47 0D 0A 1A 0A
    if buffer.starts_with(&[0x89, b'P', b'N', b'G', 0x0D, 0x0A, 0x1A, 0x0A]) {
        return Some("image");
    }
    // Check JPEG: FF D8 FF
    if buffer.starts_with(&[0xFF, 0xD8, 0xFF]) {
        return Some("image");
    }
    // Check GIF: GIF87a or GIF89a
    if buffer.starts_with(b"GIF87a") || buffer.starts_with(b"GIF89a") {
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
    if buffer.starts_with(b"RIFF") && n >= 12 && &buffer[8..12] == b"AVI " {
        return Some("video");
    }
    // Check WAV: RIFF....WAVE
    if buffer.starts_with(b"RIFF") && n >= 12 && &buffer[8..12] == b"WAVE" {
        return Some("audio");
    }
    // Check MP4 / MOV / M4V / M4A / M4B / HEIC / AVIF: ftyp at offset 4
    if n >= 8 && &buffer[4..8] == b"ftyp" {
        let brand: &[u8] = if n >= 12 { &buffer[8..12] } else { &[] };
        if [&b"M4A "[..], &b"m4a "[..], &b"M4B "[..], &b"m4b "[..]].contains(&brand) {
            return Some("audio");
        }
        if [
            &b"heic"[..],
            &b"heix"[..],
            &b"heim"[..],
            &b"heis"[..],
            &b"hevc"[..],
            &b"hevx"[..],
            &b"avif"[..],
            &b"avis"[..],
        ]
        .contains(&brand)
        {
            return Some("image");
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

/// Seconds since the Unix epoch.
///
/// Timestamps before 1970 are negative; `duration_since(UNIX_EPOCH)` fails for
/// them, which reported them as 0.0 (1970-01-01) instead of the real time.
fn epoch_seconds(t: std::time::SystemTime) -> f64 {
    match t.duration_since(std::time::UNIX_EPOCH) {
        Ok(d) => d.as_secs_f64(),
        Err(e) => -e.duration().as_secs_f64(),
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
                if e.depth() == 0 {
                    return true;
                }
                let name = e.file_name().to_string_lossy();
                // Skip dotfiles and dotdirs (.git, .vscode, .DS_Store, etc.)
                !name.starts_with('.')
            })
            .filter_map(|e| e.ok())
        {
            // fs::metadata() follows symlinks: a symlink pointing at a media
            // file IS a file, but walkdir's entry.file_type() describes the
            // link itself, so every symlinked file was dropped from the scan
            // (the Python fallback scanner keeps them).
            let metadata = match fs::metadata(entry.path()) {
                Ok(m) => m,
                Err(_) => continue,
            };
            if !metadata.is_file() {
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
                    if detected == Some("video") && (!is_no_ext || include_no_ext) {
                        Some("video")
                    } else {
                        None
                    }
                }
                "audio" => {
                    if detected == Some("audio") && (!is_no_ext || include_no_ext) {
                        Some("audio")
                    } else {
                        None
                    }
                }
                "image" => {
                    if detected == Some("image") && (!is_no_ext || include_no_ext) {
                        Some("image")
                    } else {
                        None
                    }
                }
                "pdf" => {
                    if detected == Some("pdf") && (!is_no_ext || include_no_ext) {
                        Some("pdf")
                    } else {
                        None
                    }
                }
                _ => {
                    if let Some(d) = detected {
                        if !is_no_ext || include_no_ext {
                            Some(d)
                        } else {
                            None
                        }
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

            // Duplicate key: the canonical path resolves symlinks, so a file
            // reachable through two different links is only reported once.
            let canonical_path = match path.canonicalize() {
                Ok(p) => {
                    let s = p.to_string_lossy();
                    if let Some(unc_suffix) = s.strip_prefix(r"\\?\UNC\") {
                        format!(r"\\{}", unc_suffix)
                    } else if let Some(local_suffix) = s.strip_prefix(r"\\?\") {
                        local_suffix.to_string()
                    } else {
                        s.to_string()
                    }
                }
                Err(_) => path.to_string_lossy().to_string(),
            };

            // Case-fold only where the filesystem is case-insensitive: on
            // POSIX "Song.mp3" and "song.mp3" are two different files and
            // folding them silently dropped one of them from the scan.
            let norm_key = if cfg!(windows) {
                canonical_path.to_lowercase()
            } else {
                canonical_path.clone()
            };
            if !seen_norm_paths.insert(norm_key) {
                continue;
            }

            let size = metadata.len();
            let mtime = metadata
                .modified()
                .map(epoch_seconds)
                .unwrap_or(0.0);

            let ctime = metadata
                .created()
                .map(epoch_seconds)
                .unwrap_or(mtime);

            let item = ScannedFile {
                // The path AS WALKED, not the canonical one: for a symlinked
                // file the canonical path points at the link's target, so the
                // row would show a path outside the scanned folder and a
                // rename or delete would act on that target instead of the
                // entry the user sees (breaking the link / moving the
                // original file). The Python scanner reports the walked path.
                path: path.to_string_lossy().to_string(),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_matches_exclusion() {
        let patterns = vec![
            "*.tmp".to_string(),
            "*_backup*".to_string(),
            "prefix_*".to_string(),
            "sample".to_string(),
            "".to_string(),
            "   ".to_string(),
        ];

        assert!(matches_exclusion("video.tmp", &patterns));
        assert!(matches_exclusion("my_backup_file.mp4", &patterns));
        assert!(matches_exclusion("prefix_test.mov", &patterns));
        assert!(matches_exclusion("mysamplefile.mkv", &patterns));
        assert!(!matches_exclusion("other_file.mp4", &patterns));
    }

    #[test]
    fn test_epoch_seconds_keeps_pre_epoch_timestamps_negative() {
        // 1969-12-31 23:59:59 UTC -> one second before the epoch
        let before = std::time::UNIX_EPOCH - std::time::Duration::from_secs(1);
        assert_eq!(epoch_seconds(before), -1.0);
        assert_eq!(epoch_seconds(std::time::UNIX_EPOCH), 0.0);
        assert_eq!(
            epoch_seconds(std::time::UNIX_EPOCH + std::time::Duration::from_secs(90)),
            90.0
        );
    }

    #[test]
    fn test_sniff_ftyp_brands() {
        fn write_brand(name: &str, brand: &[u8; 4]) -> PathBuf {
            let path = std::env::temp_dir()
                .join(format!("mf_sniff_{}_{}", std::process::id(), name));
            let mut data = b"\x00\x00\x00\x18ftyp".to_vec();
            data.extend_from_slice(brand);
            data.extend_from_slice(b"\x00\x00\x00\x00");
            data.extend_from_slice(brand);
            data.extend_from_slice(b"isom");
            fs::write(&path, data).unwrap();
            path
        }

        let cases: [(&str, &[u8; 4], &str); 4] = [
            ("heic", b"heic", "image"),
            ("avif", b"avif", "image"),
            ("m4b", b"M4B ", "audio"),
            ("mp4", b"mp42", "video"),
        ];
        for (name, brand, expected) in cases {
            let path = write_brand(name, brand);
            assert_eq!(sniff_media_type(&path), Some(expected));
            let _ = fs::remove_file(path);
        }
    }
}
