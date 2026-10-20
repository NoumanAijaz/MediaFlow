"""
Rust Core Bridge for MediaFlow.
Interfaces with the compiled high-performance 'mediaflow-core' Rust binary.
Provides massive speedups for directory scanning and duplicate detection.
Gracefully falls back to pure Python if the Rust binary is not present.
"""

import json
import logging
import os
import shutil
import subprocess
import sys
import time
from typing import Callable, Dict, List, Optional, Tuple, Any

logger = logging.getLogger("mediaflow.rust_bridge")

_CACHED_BINARY_PATH: Optional[str] = None
_CHECKED_BINARY: bool = False


def get_rust_core_binary() -> Optional[str]:
    """Find the path to the mediaflow-core executable."""
    global _CACHED_BINARY_PATH, _CHECKED_BINARY
    if _CHECKED_BINARY:
        return _CACHED_BINARY_PATH

    exe_name = "mediaflow-core.exe" if sys.platform == "win32" else "mediaflow-core"
    candidates = []

    # 1. PyInstaller bundled location
    if hasattr(sys, "_MEIPASS"):
        candidates.append(os.path.join(sys._MEIPASS, exe_name))

    # 2. Same directory as current executable or script
    app_dir = os.path.dirname(os.path.abspath(__file__))
    candidates.append(os.path.join(app_dir, exe_name))

    # 3. Rust project target/release directory
    candidates.append(os.path.join(app_dir, "mediaflow-core", "target", "release", exe_name))

    # 4. Rust project target/debug directory (development)
    candidates.append(os.path.join(app_dir, "mediaflow-core", "target", "debug", exe_name))

    # 5. System PATH
    path_hit = shutil.which("mediaflow-core")
    if path_hit:
        candidates.append(path_hit)

    for path in candidates:
        if path and os.path.isfile(path) and os.access(path, os.X_OK):
            logger.info("Found mediaflow-core Rust binary: %s", path)
            _CACHED_BINARY_PATH = path
            _CHECKED_BINARY = True
            return path

    _CHECKED_BINARY = True
    _CACHED_BINARY_PATH = None
    logger.info("Rust binary mediaflow-core not found; using native Python fallback.")
    return None


def is_rust_core_available() -> bool:
    """Return True if mediaflow-core Rust binary is available."""
    return get_rust_core_binary() is not None


class RustScanProcess:
    """Manages an active Rust scan subprocess with cancellation support."""

    def __init__(self, proc: subprocess.Popen):
        self.proc = proc
        self._cancelled = False

    def cancel(self):
        self._cancelled = True
        try:
            self.proc.terminate()
            self.proc.kill()
        except Exception:
            pass


def scan_directories_rust(
    directories: List[str],
    media_type: str = "all",
    exclude_patterns: Optional[List[str]] = None,
    include_no_ext: bool = True,
    on_file_found: Optional[Callable[[Dict[str, Any]], None]] = None,
    on_progress: Optional[Callable[[int], None]] = None,
    on_status: Optional[Callable[[str], None]] = None,
    is_interrupted: Optional[Callable[[], bool]] = None,
) -> Tuple[int, float]:
    """
    Stream directory scan results using mediaflow-core.
    Returns (total_files_found, elapsed_ms).
    """
    binary = get_rust_core_binary()
    if not binary:
        raise RuntimeError("mediaflow-core binary is not available")

    valid_dirs = [os.path.abspath(d) for d in directories if os.path.isdir(d)]
    if not valid_dirs:
        return 0, 0.0

    args = [binary, "scan", "--media-type", media_type]
    if include_no_ext:
        args.append("--include-no-ext")

    if exclude_patterns:
        # "--exclude=<value>" form: a pattern that starts with "-" is parsed as
        # a flag by clap and aborts the whole scan (exit code 2), which
        # silently disabled the Rust engine for that scan.
        for pattern in exclude_patterns:
            args.append(f"--exclude={pattern}")

    # Same reason: a directory whose name starts with "-" must not be read
    # as a flag.
    for directory in valid_dirs:
        args.append(f"--dirs={directory}")

    creationflags = 0
    if sys.platform == "win32":
        creationflags = subprocess.CREATE_NO_WINDOW

    proc = subprocess.Popen(
        args,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        errors="replace",
        bufsize=1,
        creationflags=creationflags,
    )

    total_found = 0
    elapsed_ms = 0.0

    try:
        for line in proc.stdout:
            if is_interrupted and is_interrupted():
                proc.terminate()
                proc.kill()
                break

            line = line.strip()
            if not line:
                continue

            try:
                event = json.loads(line)
            except Exception:
                continue

            event_type = event.get("type")
            if event_type == "file":
                total_found += 1
                if on_file_found:
                    on_file_found(event)
            elif event_type == "progress":
                if on_progress:
                    on_progress(event.get("found", 0))
            elif event_type == "complete":
                total_found = event.get("total", total_found)
                elapsed_ms = float(event.get("elapsed_ms", 0.0))
            elif event_type == "error":
                logger.warning("Rust scan error: %s", event.get("message"))

        proc.wait(timeout=5)
        if (not is_interrupted or not is_interrupted()) and proc.returncode != 0:
            stderr_out = ""
            if proc.stderr:
                try:
                    stderr_out = proc.stderr.read()
                except Exception:
                    pass
            raise RuntimeError(f"mediaflow-core scan exited with code {proc.returncode}: {stderr_out.strip()}")
    except Exception as e:
        logger.error("Error during Rust directory scan: %s", e)
        try:
            proc.kill()
        except Exception:
            pass
        raise

    return total_found, elapsed_ms


def find_duplicates_rust(
    items: List[Dict[str, Any]],
    on_progress: Optional[Callable[[int, int, str], None]] = None,
    is_cancelled: Optional[Callable[[], bool]] = None,
) -> Tuple[List[List[str]], int]:
    """
    Find exact duplicates in parallel using mediaflow-core.
    Returns (duplicate_groups, skipped_count).
    """
    binary = get_rust_core_binary()
    if not binary:
        raise RuntimeError("mediaflow-core binary is not available")

    # Serialize items payload
    payload = json.dumps([{"path": it["path"], "size": int(it.get("size", 0) or 0)} for it in items])

    creationflags = 0
    if sys.platform == "win32":
        creationflags = subprocess.CREATE_NO_WINDOW

    proc = subprocess.Popen(
        [binary, "dedupe"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        errors="replace",
        bufsize=1,
        creationflags=creationflags,
    )

    try:
        proc.stdin.write(payload)
        proc.stdin.close()
    except Exception as e:
        try:
            proc.kill()
        except Exception:
            pass
        raise RuntimeError(f"Failed to send input payload to mediaflow-core dedupe: {e}")

    groups = []
    skipped = 0
    start_time = time.time()
    try:
        for line in proc.stdout:
            if is_cancelled and is_cancelled():
                try:
                    proc.terminate()
                    proc.kill()
                except Exception:
                    pass
                return [], 0
            if time.time() - start_time > 600:
                try:
                    proc.kill()
                except Exception:
                    pass
                raise RuntimeError("Rust dedupe timed out after 600 seconds")

            line = line.strip()
            if not line:
                continue
            try:
                event = json.loads(line)
            except Exception:
                continue

            event_type = event.get("type")
            if event_type == "progress":
                if on_progress:
                    on_progress(event.get("done", 0), event.get("total", 0), event.get("phase", "Analyzing duplicates…"))
            elif event_type == "groups":
                groups = event.get("groups", [])
                skipped = event.get("skipped", 0)
            elif event_type == "error":
                logger.warning("Rust dedupe error: %s", event.get("message"))

        proc.wait(timeout=5)
        if proc.returncode != 0 and (not is_cancelled or not is_cancelled()):
            stderr_out = ""
            if proc.stderr:
                try:
                    stderr_out = proc.stderr.read()
                except Exception:
                    pass
            raise RuntimeError(f"mediaflow-core dedupe exited with code {proc.returncode}: {stderr_out}")
    except Exception as e:
        try:
            proc.kill()
        except Exception:
            pass
        raise

    return groups, skipped


def execute_rename_rust(
    tasks: List[Dict[str, str]],
    dry_run: bool = False,
) -> Tuple[List[Tuple[str, str]], List[Tuple[str, str, str]]]:
    """
    Batch execute file renames using mediaflow-core.
    Returns (successful_pairs, failed_triples).
    successful_pairs: [(source, target), ...]
    failed_triples: [(source, target, error_message), ...]
    """
    binary = get_rust_core_binary()
    if not binary:
        raise RuntimeError("mediaflow-core binary is not available")

    payload = json.dumps(tasks)
    cmd = [binary, "rename"]
    if dry_run:
        cmd.append("--dry-run")

    creationflags = 0
    if sys.platform == "win32":
        creationflags = subprocess.CREATE_NO_WINDOW

    proc = subprocess.Popen(
        cmd,
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        errors="replace",
        creationflags=creationflags,
    )

    try:
        stdout_data, stderr_data = proc.communicate(input=payload, timeout=120)
    except subprocess.TimeoutExpired:
        try:
            proc.kill()
        except Exception:
            pass
        raise RuntimeError("Rust batch rename timed out")

    if proc.returncode != 0:
        raise RuntimeError(f"mediaflow-core rename exited with code {proc.returncode}: {stderr_data}")

    try:
        data = json.loads(stdout_data.strip())
        successful = [tuple(x) for x in data.get("successful", [])]
        failed = [tuple(x) for x in data.get("failed", [])]
        return successful, failed
    except Exception as e:
        raise RuntimeError(f"Failed to parse rename results from mediaflow-core: {e}")



def extract_metadata_rust(filepath: str, media_type: str = "audio") -> Optional[Dict[str, Any]]:
    """Extract audio or image metadata using mediaflow-core."""
    binary = get_rust_core_binary()
    if not binary:
        return None

    creationflags = 0
    if sys.platform == "win32":
        creationflags = subprocess.CREATE_NO_WINDOW

    try:
        res = subprocess.run(
            [binary, "metadata", "--path", filepath, "--media-type", media_type],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=10,
            creationflags=creationflags,
        )
        if res.returncode == 0 and res.stdout.strip():
            return json.loads(res.stdout.strip())
    except Exception as e:
        logger.debug("Rust metadata extraction failed for %s: %s", filepath, e)

    return None
