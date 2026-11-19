use serde::{Deserialize, Serialize};
use std::fs;
use std::path::Path;

#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct RenameTask {
    pub source: String,
    pub target: String,
}

#[derive(Debug, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct RenamePlanItem {
    pub source: String,
    pub target: String,
    pub will_overwrite: bool,
    pub error: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct RenameResult {
    pub successful: Vec<(String, String)>,
    pub failed: Vec<(String, String, String)>, // (source, target, error)
}

/// Reasons a target name can never be created on Windows.
///
/// A dry run that reports such a target as "successful" promises a rename
/// that is guaranteed to fail at execution time.
fn invalid_target_reason(target: &Path) -> Option<String> {
    let name = match target.file_name() {
        Some(n) => n.to_string_lossy().to_string(),
        None => return Some("Target has no file name".to_string()),
    };
    if name.is_empty() {
        return Some("Target has an empty file name".to_string());
    }
    if let Some(c) = name.chars().find(|c| "<>:\"|?*".contains(*c) || (*c as u32) < 32) {
        return Some(format!(
            "Target file name contains the illegal character '{}'",
            c
        ));
    }
    if name.ends_with(' ') || name.ends_with('.') {
        return Some("Target file name cannot end with a space or period".to_string());
    }
    let stem = name.split('.').next().unwrap_or("").to_uppercase();
    const RESERVED: [&str; 25] = [
        "CON", "PRN", "AUX", "NUL", "COM1", "COM2", "COM3", "COM4", "COM5", "COM6", "COM7",
        "COM8", "COM9", "LPT1", "LPT2", "LPT3", "LPT4", "LPT5", "LPT6", "LPT7", "LPT8", "LPT9",
        "CLOCK$", "CONIN$", "CONOUT$",
    ];
    if RESERVED.contains(&stem.as_str()) {
        return Some(format!(
            "Target file name '{}' is a reserved device name",
            stem
        ));
    }
    None
}

pub fn execute_rename_plan(tasks: Vec<RenameTask>, dry_run: bool) -> RenameResult {
    let mut successful = Vec::new();
    let mut failed = Vec::new();

    for task in tasks {
        let src_path = Path::new(&task.source);
        let tgt_path = Path::new(&task.target);

        if !src_path.exists() {
            failed.push((
                task.source,
                task.target,
                "Source file does not exist".to_string(),
            ));
            continue;
        }

        if let Some(reason) = invalid_target_reason(tgt_path) {
            failed.push((task.source, task.target, reason));
            continue;
        }

        if dry_run {
            successful.push((task.source, task.target));
            continue;
        }

        // Ensure parent directory of target exists
        if let Some(parent) = tgt_path.parent() {
            if !parent.as_os_str().is_empty() && !parent.exists() {
                if let Err(e) = fs::create_dir_all(parent) {
                    failed.push((
                        task.source,
                        task.target,
                        format!("Cannot create parent directory: {}", e),
                    ));
                    continue;
                }
            }
        }

        let is_case_only_rename = cfg!(windows) && {
            let src_parent = src_path.parent();
            let tgt_parent = tgt_path.parent();
            let same_parent = match (src_parent, tgt_parent) {
                (Some(sp), Some(tp)) => {
                    let sp_eff = if sp.as_os_str().is_empty() { Path::new(".") } else { sp };
                    let tp_eff = if tp.as_os_str().is_empty() { Path::new(".") } else { tp };
                    crate::path_util::canonical_norm_key(sp_eff) == crate::path_util::canonical_norm_key(tp_eff)
                }
                (None, None) => true,
                _ => false,
            };
            let src_name = src_path.file_name().map(|s| s.to_string_lossy().to_lowercase());
            let tgt_name = tgt_path.file_name().map(|s| s.to_string_lossy().to_lowercase());
            same_parent && src_name == tgt_name && src_path.file_name() != tgt_path.file_name()
        };

        if is_case_only_rename {
            let nanos = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(12345);
            let tmp_path_str = format!("{}.__mf_tmp_{}__", task.target, nanos);
            let tmp_p = Path::new(&tmp_path_str);
            let rename_res = fs::rename(src_path, tmp_p).and_then(|_| fs::rename(tmp_p, tgt_path));
            match rename_res {
                Ok(_) => {
                    successful.push((task.source, task.target));
                }
                Err(e) => {
                    if tmp_p.exists() {
                        let _ = fs::rename(tmp_p, src_path);
                    }
                    failed.push((task.source, task.target, e.to_string()));
                }
            }
        } else {
            match fs::rename(src_path, tgt_path) {
                Ok(_) => {
                    successful.push((task.source, task.target));
                }
                Err(e) => {
                    failed.push((task.source, task.target, e.to_string()));
                }
            }
        }
    }

    RenameResult { successful, failed }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    #[test]
    fn test_execute_rename_plan_dry_run() {
        let task = RenameTask {
            source: "non_existent_file_123.mp4".to_string(),
            target: "new_file_123.mp4".to_string(),
        };
        let res = execute_rename_plan(vec![task], true);
        assert_eq!(res.successful.len(), 0);
        assert_eq!(res.failed.len(), 1);
    }

    #[test]
    fn test_execute_rename_plan_dry_run_reports_invalid_target() {
        let tmp_dir = std::env::temp_dir().join(format!(
            "mf_test_dryrun_{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let _ = fs::create_dir_all(&tmp_dir);
        let src_file = tmp_dir.join("source.mp4");
        fs::write(&src_file, b"sample content").unwrap();

        // '<' is not allowed in a Windows file name: the dry run must report
        // the failure instead of promising a successful rename.
        let task = RenameTask {
            source: src_file.to_string_lossy().to_string(),
            target: tmp_dir.join("a<b.mp4").to_string_lossy().to_string(),
        };

        let res = execute_rename_plan(vec![task], true);
        assert_eq!(res.successful.len(), 0);
        assert_eq!(res.failed.len(), 1);
        assert!(res.failed[0].2.contains("illegal character"));

        let _ = fs::remove_file(src_file);
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_execute_rename_plan_case_only() {
        let tmp_dir = std::env::temp_dir().join(format!(
            "mf_test_rename_{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let _ = fs::create_dir_all(&tmp_dir);
        let src_file = tmp_dir.join("sample_clip.mp4");
        let tgt_file = tmp_dir.join("SAMPLE_CLIP.MP4");

        let mut f = fs::File::create(&src_file).unwrap();
        f.write_all(b"sample content").unwrap();
        drop(f);

        let task = RenameTask {
            source: src_file.to_string_lossy().to_string(),
            target: tgt_file.to_string_lossy().to_string(),
        };

        let res = execute_rename_plan(vec![task], false);
        assert_eq!(res.successful.len(), 1);
        assert_eq!(res.failed.len(), 0);
        assert!(tgt_file.exists());

        let _ = fs::remove_file(&tgt_file);
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_execute_rename_plan_case_only_mixed_slashes() {
        let tmp_dir = std::env::temp_dir().join(format!(
            "mf_test_rename_slashes_{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let _ = fs::create_dir_all(&tmp_dir);
        let src_file = tmp_dir.join("mixed_clip.mp4");
        fs::write(&src_file, b"sample content").unwrap();

        // One path with backslashes, one with forward slashes
        let src_str = src_file.to_string_lossy().replace('/', "\\");
        let tgt_str = tmp_dir.join("MIXED_CLIP.MP4").to_string_lossy().replace('\\', "/");

        let task = RenameTask {
            source: src_str,
            target: tgt_str,
        };

        let res = execute_rename_plan(vec![task], false);
        assert_eq!(res.successful.len(), 1);
        assert_eq!(res.failed.len(), 0);

        let final_file = tmp_dir.join("MIXED_CLIP.MP4");
        assert!(final_file.exists());
        let _ = fs::remove_file(&final_file);
        let _ = fs::remove_dir_all(&tmp_dir);
    }

    #[test]
    fn test_invalid_target_trailing_space_or_dot() {
        assert!(invalid_target_reason(Path::new("test.mp4 ")).is_some());
        assert!(invalid_target_reason(Path::new("test.mp4.")).is_some());
        assert!(invalid_target_reason(Path::new("CLOCK$")).is_some());
    }
}
