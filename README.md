# MediaFlow

**MediaFlow** is a premium, high-performance desktop media manager and batch renamer built with Python and **PyQt6**. Designed for creators, archivists, and power users, MediaFlow effortlessly handles massive libraries of **Videos**, **Images**, **Audio**, and **PDF documents** with real-time metadata previews, background multi-threading, native playback, and automated renaming rules.

---

## ✨ Features

### 🏷️ Dynamic Batch Renaming Engine
- **Pattern & Token System**: Build dynamic naming schemes using rich metadata tokens: `{name}`, `{ext}`, `{res}`, `{width}`, `{height}`, `{duration}`, `{fps}`, `{bitrate}`, `{date}`, `{created}`, `{modified}`, `{counter}`, and more.
- **Instant Preview**: Live side-by-side comparison of current and generated filenames before committing.
- **Find & Replace & Regex**: Advanced string transformation and pattern matching.
- **Safety First**: Full Undo/Redo history stack, collision detection, and automated audit logging (`rename_audit.csv`).

### ⚡ High-Performance Architecture
- **Multithreaded Scanning**: Directory parsing and metadata extraction run entirely on background threads (`QThread`), keeping the UI responsive even with thousands of files.
- **Persistent Scan Cache**: Fast incremental indexing and instant tab switching via an optimized disk cache.
- **Table & Grid Views**: Toggle between high-density metadata tables and visual thumbnail grid layouts.

### 🎬 Built-in Players & Discovery Tools
- **Native Video, Audio & Image Players**: Quick in-app media playback using Qt's `QMediaPlayer` with timeline seeking, volume control, and aspect-ratio scaling.
- **🔍 File Comparison**: Side-by-side comparison of media files and stream parameters.
- **✂️ Quick Trim**: Lossless video trimming and clipping dialog directly from the dashboard.

### 📂 File Management & Workflow Integration
- **Open Containing Folder**: Deep Windows Explorer integration (`/select`) with fallbacks to reveal files without blocking the UI thread.
- **Open With Configurator**: Launch files using external players (VLC, MPC-HC, etc.) or system defaults.
- **Folder Profiles & Auto-Watch**: Save directory presets and set up smart rules.
- **Floating Overlay Drawers**: Smooth floating overlay panels for Inspector / Preview, Library Statistics, and Settings without squashing the main table columns.

---

## 📥 Installation

### Prerequisites
- **Python 3.10+** (Python 3.11 recommended)
- **FFmpeg / FFprobe** (recommended for deep metadata inspection and video stream probing)

### Setup Instructions

1. **Clone the repository:**
   ```bash
   git clone https://github.com/NoumanAijaz/MediaFlow.git
   cd MediaFlow
   ```

2. **Create and activate a virtual environment:**
   ```bash
   python -m venv venv
   # On Windows:
   venv\Scripts\activate
   # On macOS/Linux:
   source venv/bin/activate
   ```

3. **Install dependencies:**
   ```bash
   pip install -r requirements.txt
   ```

4. **Launch MediaFlow:**
   ```bash
   python mediaflow.py
   ```

---

## 🛠️ Building Standalone Executable (.exe)

MediaFlow includes a pre-configured build system utilizing PyInstaller to bundle the entire application into a single standalone `.exe` with all dependencies and icons:

```bash
# Run the automated build script inside the venv:
venv\Scripts\python.exe build.py
```

The compiled executable will be generated at: `dist/MediaFlow.exe`.

---

## ⌨️ Keyboard Shortcuts

| Shortcut | Action |
| :--- | :--- |
| **`Ctrl + R`** | Sync / Reload Library Files |
| **`Ctrl + O`** | Add Folder to Library |
| **`Ctrl + Alt + P`** | Folder Profiles & Auto-Watch |
| **`Ctrl + Z` / `Ctrl + Y`** | Undo / Redo Rename Operation |
| **`F`** / **Double Click** | Toggle Fullscreen (in Video Players) |
| **`Space`** | Play / Pause Playback |
| **`R`** | Launch 🎲 Random Discovery Player (in Player or Selection) |
| **`[` / `]`** | Seek -5s / +5s |
| **`Ctrl + Left` / `Ctrl + Right`** | Seek -10s / +10s |
| **`M`** | Mute / Unmute Audio |

---

## ⚠️ Media Decoding & Codec Support

MediaFlow uses PyQt6's `QMediaPlayer` backed by Windows Media Foundation (WMF). If a video codec is not installed in Windows (e.g. HEVC/H.265, AV1, VP9), the video stream may display black while audio plays.

- **Solution 1**: Install the official HEVC/AV1 Video Extensions from the Microsoft Store or a standard codec pack (such as K-Lite Codec Pack).
- **Solution 2**: In MediaFlow settings under **Default Applications**, select VLC or MPC-HC as your default external video player.

---

## 🔍 Deep Metadata & FFprobe Requirement

For advanced stream parameters (bitrates, codec profiles, audio tracks, subtitle streams), **FFprobe** must be present on your system.

1. **Install via Windows Package Manager:**
   ```powershell
   winget install Gnu.FFmpeg
   ```
2. Or download from [ffmpeg.org](https://ffmpeg.org/download.html) and add its `bin` folder to your system `PATH`.
3. Alternatively, specify the custom path to `ffprobe.exe` in MediaFlow's settings dialog.

---

## 📄 License

This project is licensed under the terms of the GNU Affero General Public License v3.0 ([AGPL-3.0](LICENSE)).
