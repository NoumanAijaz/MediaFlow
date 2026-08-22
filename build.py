"""
MediaFlow Build Script
Run this to compile mediaflow.py into a standalone .exe
Usage: python build.py   (or: venv\\Scripts\\python.exe build.py)

NOTE: The build MUST run inside the project venv — PyInstaller can only bundle
packages that are importable by the interpreter running the analysis. Building
with a bare system Python silently produces an exe missing cv2/PyQt6 extras.
"""

import subprocess
import sys
import os

# Modules mediaflow.py imports at top level — all must be present at build time
REQUIRED_MODULES = ["cv2", "numpy", "PyQt6", "PyQt6.QtMultimedia"]
OPTIONAL_MODULES = ["mutagen"]  # lazy-imported fallbacks in the app


def find_build_python(script_dir):
    """Return the interpreter that should run PyInstaller."""
    # 1. If we're already inside the venv, use it
    if sys.executable and os.path.normcase(os.path.join(script_dir, "venv")) in os.path.normcase(sys.executable):
        return [sys.executable]
    # 2. Otherwise prefer the project venv explicitly
    venv_python = os.path.join(script_dir, "venv", "Scripts", "python.exe")
    if os.path.exists(venv_python):
        print(f"[INFO] Using project venv interpreter: {venv_python}")
        return [venv_python]
    # 3. Fall back to whatever python invoked us
    return [sys.executable]


def preflight_check(cmd_prefix):
    """Fail fast with a clear error if a hard dependency can't be imported."""
    code = (
        "import importlib, sys\n"
        f"required = {REQUIRED_MODULES!r}\n"
        "missing = []\n"
        "for m in required:\n"
        "    try: importlib.import_module(m)\n"
        "    except ImportError: missing.append(m)\n"
        "if missing:\n"
        "    print('MISSING:' + ','.join(missing)); sys.exit(1)\n"
        "print('deps OK')\n"
    )
    result = subprocess.run(cmd_prefix + ["-c", code], capture_output=True, text=True)
    output = (result.stdout or "").strip()
    print(f"[PREFLIGHT] {output or result.stderr.strip()}")
    if result.returncode != 0:
        print("\n" + "=" * 50)
        print("  [ABORTED] Required packages missing in the build environment.")
        print("  Install them into the venv and retry:")
        print("      venv\\Scripts\\python.exe -m pip install -r requirements.txt")
        print("=" * 50)
        sys.exit(1)


def ensure_output_unlocked(script_dir):
    """Abort early if dist\\MediaFlow.exe is locked by a running instance.

    PyInstaller only fails on this at the very END of a ~90s build
    (PermissionError removing the old exe), which is confusing. Detect it up
    front — the usual culprit is a still-running MediaFlow.exe (e.g. an error
    dialog left open from a previous broken build).
    """
    exe_path = os.path.join(script_dir, "dist", "MediaFlow.exe")
    if not os.path.exists(exe_path):
        return
    try:
        os.remove(exe_path)
    except PermissionError:
        running = subprocess.run(["tasklist", "/FI", "IMAGENAME eq MediaFlow.exe"],
                                 capture_output=True, text=True).stdout or ""
        pids = [line.split()[1] for line in running.splitlines()
                if line.strip().startswith("MediaFlow.exe")]
        print("\n" + "=" * 50)
        print("  [ABORTED] dist\\MediaFlow.exe is locked and cannot be replaced.")
        if pids:
            print(f"  Running MediaFlow.exe processes found: {', '.join(pids)}")
            print("  Close the app / its error dialogs, or run:")
            print("      taskkill /F /IM MediaFlow.exe")
        else:
            print("  No visible process found — antivirus may be scanning it.")
            print("  Wait a few seconds and try again.")
        print("=" * 50)
        sys.exit(1)


def main():
    script_dir = os.path.dirname(os.path.abspath(__file__))
    cmd_prefix = find_build_python(script_dir)

    # Verify the interpreter that will do the bundling can see every hard dep.
    # This prevents the classic failure mode where the exe builds 'successfully'
    # but dies on launch with ModuleNotFoundError: No module named 'cv2'.
    preflight_check(cmd_prefix)

    # Fail fast if the previous exe is locked instead of failing at the end
    ensure_output_unlocked(script_dir)

    cmd = cmd_prefix + [
        "-m", "PyInstaller",
        "--onefile",
        "--windowed",
        "--name", "MediaFlow",
        "--add-data", "logo.png;.",
        "--icon", "logo.ico",
        "--exclude-module", "PyQt6.QtWebEngineWidgets",
        "--exclude-module", "PyQt6.QtWebEngineCore",
        "--exclude-module", "PyQt6.QtWebEngine",
        os.path.join(script_dir, "mediaflow.py"),
    ]

    print("=" * 50)
    print("  MediaFlow — Building .exe")
    print("=" * 50)
    print(f"\nCommand: {' '.join(cmd)}\n")

    result = subprocess.run(cmd, cwd=script_dir)

    if result.returncode == 0:
        exe_path = os.path.join(script_dir, "dist", "MediaFlow.exe")
        print("\n" + "=" * 50)
        print("  [SUCCESS] Build successful!")
        print(f"  Output: {exe_path}")
        print("=" * 50)
    else:
        print("\n  [FAILED] Build failed.")
        sys.exit(1)


if __name__ == "__main__":
    main()
