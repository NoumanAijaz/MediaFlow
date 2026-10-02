use std::path::Path;
use lofty::file::{AudioFile, TaggedFileExt};
use lofty::probe::Probe;
use lofty::tag::Accessor;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct MediaMetadataResult {
    pub path: String,
    pub width: u32,
    pub height: u32,
    pub duration_seconds: f64,
    pub duration_formatted: String,
    pub artist: Option<String>,
    pub title: Option<String>,
    pub album: Option<String>,
    pub year: Option<u32>,
    pub is_valid: bool,
    pub error_message: Option<String>,
}

pub fn format_duration(seconds: f64) -> String {
    if seconds <= 0.0 {
        return "—".to_string();
    }
    let total = seconds.round() as u64;
    let h = total / 3600;
    let m = (total % 3600) / 60;
    let s = total % 60;
    if h > 0 {
        format!("{}h {:02}m {:02}s", h, m, s)
    } else {
        format!("{}m {:02}s", m, s)
    }
}

pub fn extract_audio_metadata(path: &Path) -> Result<MediaMetadataResult, String> {
    let tagged_file = Probe::open(path)
        .map_err(|e| format!("Failed to open audio: {}", e))?
        .read()
        .map_err(|e| format!("Failed to parse audio tags: {}", e))?;

    let properties = tagged_file.properties();
    let duration = properties.duration();
    let duration_seconds = duration.as_secs_f64();

    let tag = tagged_file.primary_tag().or_else(|| tagged_file.first_tag());

    let (artist, title, album, year) = match tag {
        Some(t) => (
            t.artist().map(|s| s.to_string()),
            t.title().map(|s| s.to_string()),
            t.album().map(|s| s.to_string()),
            t.year(),
        ),
        None => (None, None, None, None),
    };

    Ok(MediaMetadataResult {
        path: path.to_string_lossy().to_string(),
        width: 0,
        height: 0,
        duration_seconds,
        duration_formatted: format_duration(duration_seconds),
        artist,
        title,
        album,
        year,
        is_valid: true,
        error_message: None,
    })
}

pub fn extract_image_metadata(path: &Path) -> Result<MediaMetadataResult, String> {
    let reader = image::ImageReader::open(path)
        .map_err(|e| format!("Failed to open image: {}", e))?
        .with_guessed_format()
        .map_err(|e| format!("Unsupported format: {}", e))?;

    let (width, height) = reader
        .into_dimensions()
        .map_err(|e| format!("Failed to read dimensions: {}", e))?;

    Ok(MediaMetadataResult {
        path: path.to_string_lossy().to_string(),
        width,
        height,
        duration_seconds: 0.0,
        duration_formatted: "—".to_string(),
        artist: None,
        title: None,
        album: None,
        year: None,
        is_valid: true,
        error_message: None,
    })
}

pub fn extract_metadata(path_str: &str, media_type: &str) -> MediaMetadataResult {
    let path = Path::new(path_str);
    match media_type {
        "audio" => match extract_audio_metadata(path) {
            Ok(res) => res,
            Err(e) => MediaMetadataResult {
                path: path_str.to_string(),
                width: 0,
                height: 0,
                duration_seconds: 0.0,
                duration_formatted: "—".to_string(),
                artist: None,
                title: None,
                album: None,
                year: None,
                is_valid: false,
                error_message: Some(e),
            },
        },
        "image" => match extract_image_metadata(path) {
            Ok(res) => res,
            Err(e) => MediaMetadataResult {
                path: path_str.to_string(),
                width: 0,
                height: 0,
                duration_seconds: 0.0,
                duration_formatted: "—".to_string(),
                artist: None,
                title: None,
                album: None,
                year: None,
                is_valid: false,
                error_message: Some(e),
            },
        },
        _ => MediaMetadataResult {
            path: path_str.to_string(),
            width: 0,
            height: 0,
            duration_seconds: 0.0,
            duration_formatted: "—".to_string(),
            artist: None,
            title: None,
            album: None,
            year: None,
            is_valid: true,
            error_message: None,
        },
    }
}
