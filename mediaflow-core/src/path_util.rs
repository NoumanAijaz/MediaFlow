use std::path::Path;

/// Strips Windows extended-length prefix (\\?\ and \\?\UNC\) from a path string, case-insensitively.
pub fn strip_extended_prefix(path_str: &str) -> String {
    if path_str.len() >= 8
        && (path_str[..8].eq_ignore_ascii_case(r"\\?\UNC\")
            || path_str[..8].eq_ignore_ascii_case("//?/UNC/"))
    {
        format!(r"\\{}", &path_str[8..])
    } else if path_str.len() >= 4
        && (path_str[..4].eq_ignore_ascii_case(r"\\?\")
            || path_str[..4].eq_ignore_ascii_case("//?/"))
    {
        path_str[4..].to_string()
    } else {
        path_str.to_string()
    }
}

/// Returns a clean string representation of a path, stripping extended-length prefixes.
pub fn clean_path_string(path: &Path) -> String {
    strip_extended_prefix(&path.to_string_lossy())
}

/// Resolves symlinks via canonicalize and returns a clean path string without extended prefixes.
/// Falls back to the clean path itself if canonicalize fails.
pub fn canonical_path_clean(path: &Path) -> String {
    match path.canonicalize() {
        Ok(p) => clean_path_string(&p),
        Err(_) => clean_path_string(path),
    }
}

/// Generates a standardized deduplication/lookup key:
/// Canonical path without extended prefix, lowercased on Windows for case-insensitive matching.
pub fn canonical_norm_key(path: &Path) -> String {
    let clean = canonical_path_clean(path);
    if cfg!(windows) {
        clean.replace('/', "\\").to_lowercase()
    } else {
        clean
    }
}

/// Normalizes a path string key without canonicalizing (for walked paths).
pub fn normalize_walked_key(path_str: &str) -> String {
    let clean = strip_extended_prefix(path_str);
    if cfg!(windows) {
        clean.replace('/', "\\").to_lowercase()
    } else {
        clean
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_strip_extended_prefix() {
        assert_eq!(strip_extended_prefix(r"\\?\C:\foo\bar.txt"), r"C:\foo\bar.txt");
        assert_eq!(strip_extended_prefix(r"\\?\UNC\server\share\file.mp4"), r"\\server\share\file.mp4");
        assert_eq!(strip_extended_prefix(r"\\?\unc\server\share\file.mp4"), r"\\server\share\file.mp4");
        assert_eq!(strip_extended_prefix("//?/UNC/server/share/file.mp4"), r"\\server/share/file.mp4");
        assert_eq!(strip_extended_prefix(r"C:\normal\path.txt"), r"C:\normal\path.txt");
        assert_eq!(strip_extended_prefix("/unix/style/path"), "/unix/style/path");
    }

    #[test]
    fn test_canonical_norm_key_consistency() {
        let temp = std::env::temp_dir();
        let key = canonical_norm_key(&temp);
        assert!(!key.starts_with(r"\\?\"));
        if cfg!(windows) {
            assert_eq!(key, key.to_lowercase());
            assert!(!key.contains('/'));
        }
    }
}
