"""
MediaFlow Build Script
Run this to compile mediaflow.py into a standalone .exe
Usage: python build.py
"""

import subprocess
import sys
import os

def main():
    script_dir = os.path.dirname(os.path.abspath(__file__))
    try:
        import PyInstaller
        pyinstaller_cmd = [sys.executable, "-m", "PyInstaller"]
    except ImportError:
        pyinstaller_cmd = ["pyinstaller"]

    cmd = pyinstaller_cmd + [
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
