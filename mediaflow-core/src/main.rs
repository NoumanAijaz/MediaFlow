mod dedupe;
mod metadata;
mod renamer;
mod scanner;

use std::io::{self, Read};
use std::path::PathBuf;
use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(name = "mediaflow-core")]
#[command(about = "High-performance multi-threaded core engine for MediaFlow", long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Fast multi-threaded directory scan streaming NDJSON
    Scan {
        /// Directories to scan
        #[arg(short, long, num_args = 1..)]
        dirs: Vec<PathBuf>,

        /// Target media type: video, audio, image, pdf, all
        #[arg(short, long, default_value = "all")]
        media_type: String,

        /// Glob / substring patterns to exclude
        #[arg(short, long, num_args = 0..)]
        exclude: Vec<String>,

        /// Include files with no extension
        #[arg(long, default_value_t = true)]
        include_no_ext: bool,
    },

    /// Multi-threaded duplicate detection (size bucketing + SIMD head/full hashing)
    Dedupe {
        /// Path to JSON file containing array of {path, size}, or omit to read from stdin
        #[arg(short, long)]
        input: Option<PathBuf>,
    },

    /// Extract audio / image metadata directly without spawning heavy processes
    Metadata {
        /// Path to the media file
        #[arg(short, long)]
        path: String,

        /// Media type (audio, image, video)
        #[arg(short, long, default_value = "audio")]
        media_type: String,
    },

    /// Batch execute rename plan with rollback checks
    Rename {
        /// Path to JSON file containing array of {source, target}, or omit to read from stdin
        #[arg(short, long)]
        input: Option<PathBuf>,

        /// Dry run simulation only
        #[arg(long, default_value_t = false)]
        dry_run: bool,
    },
}

fn main() -> io::Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Scan {
            dirs,
            media_type,
            exclude,
            include_no_ext,
        } => {
            scanner::run_scan(&dirs, &media_type, &exclude, include_no_ext)?;
        }
        Commands::Dedupe { input } => {
            let json_str = match input {
                Some(path) => std::fs::read_to_string(path)?,
                None => {
                    let mut buffer = String::new();
                    io::stdin().read_to_string(&mut buffer)?;
                    buffer
                }
            };

            let items: Vec<dedupe::DedupeInputItem> = match serde_json::from_str(&json_str) {
                Ok(it) => it,
                Err(e) => {
                    eprintln!("Failed to parse dedupe input JSON: {}", e);
                    std::process::exit(1);
                }
            };

            dedupe::run_dedupe(items)?;
        }
        Commands::Metadata { path, media_type } => {
            let res = metadata::extract_metadata(&path, &media_type);
            println!("{}", serde_json::to_string(&res).unwrap());
        }
        Commands::Rename { input, dry_run } => {
            let json_str = match input {
                Some(path) => std::fs::read_to_string(path)?,
                None => {
                    let mut buffer = String::new();
                    io::stdin().read_to_string(&mut buffer)?;
                    buffer
                }
            };

            let tasks: Vec<renamer::RenameTask> = match serde_json::from_str(&json_str) {
                Ok(t) => t,
                Err(e) => {
                    eprintln!("Failed to parse rename plan JSON: {}", e);
                    std::process::exit(1);
                }
            };

            let res = renamer::execute_rename_plan(tasks, dry_run);
            println!("{}", serde_json::to_string(&res).unwrap());
        }
    }

    Ok(())
}
