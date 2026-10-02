use std::fs;
use std::path::Path;
use serde::{Deserialize, Serialize};

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

pub fn execute_rename_plan(tasks: Vec<RenameTask>, dry_run: bool) -> RenameResult {
    let mut successful = Vec::new();
    let mut failed = Vec::new();

    for task in tasks {
        let src_path = Path::new(&task.source);
        let tgt_path = Path::new(&task.target);

        if !src_path.exists() {
            failed.push((task.source, task.target, "Source file does not exist".to_string()));
            continue;
        }

        if dry_run {
            successful.push((task.source, task.target));
            continue;
        }

        // Ensure parent directory of target exists
        if let Some(parent) = tgt_path.parent() {
            if !parent.exists() {
                if let Err(e) = fs::create_dir_all(parent) {
                    failed.push((task.source, task.target, format!("Cannot create parent directory: {}", e)));
                    continue;
                }
            }
        }

        match fs::rename(src_path, tgt_path) {
            Ok(_) => {
                successful.push((task.source, task.target));
            }
            Err(e) => {
                failed.push((task.source, task.target, e.to_string()));
            }
        }
    }

    RenameResult {
        successful,
        failed,
    }
}
