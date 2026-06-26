# MediaFlow

**MediaFlow** is a desktop utility designed to organize and rename your video, image, and audio libraries using dynamic, custom-defined naming templates. It provides real-time previews, instant directory scanning with an optimized metadata cache, a native player, and advanced multithreaded operations.

## Features
- **Dynamic Naming Templates:** Organize and rename files with ease.
- **Real-time Previews:** Instantly preview video, audio, and image files.
- **Optimized Scanning:** Fast directory scanning with an advanced metadata cache.
- **Native Player:** Play your media files directly within the application.
- **Multithreaded:** Advanced multithreading for smooth, responsive operations.

## Installation

### Requirements
- Python 3.9+
- [FFprobe](https://ffmpeg.org/download.html) (Optional but recommended for deep metadata extraction)

### Setup Instructions

1. Clone the repository:
   ```bash
   git clone https://github.com/yourusername/MediaFlow.git
   cd MediaFlow
   ```

2. Create and activate a virtual environment:
   ```bash
   python -m venv venv
   # On Windows:
   venv\Scripts\activate
   # On macOS/Linux:
   source venv/bin/activate
   ```

3. Install the dependencies:
   ```bash
   pip install -r requirements.txt
   ```

4. Run the application:
   ```bash
   python mediaflow.py
   ```

## Media Decoding & Codec Support Warning

MediaFlow uses the native PyQt6 QMediaPlayer which relies on the OS's system media backend (Windows Media Foundation / WMF) to decode files.

If a video is compressed with a codec that is not natively supported or licensed on your Windows machine by default (such as HEVC/H.265, VP9, or AV1), the Windows media pipeline can decode the audio track but cannot decode the video stream, resulting in a black screen with audio playing.

### How to resolve this:

1. **Install Codecs**: Install a free codec pack (like the K-Lite Codec Pack) or the official HEVC Video Extensions from the Microsoft Store. This will register the video decoder on your system, allowing QMediaPlayer to play them natively.
2. **Change Default Player in Settings**: In MediaFlow settings under "Default Applications", click Browse next to Video Player to use a powerful player like VLC or MPC-HC as your default player instead of the native system player. These players package their own codecs and can decode all formats out-of-the-box.

## Deep Metadata & FFprobe Requirement

To view advanced, deep metadata details for files (such as codecs, audio tracks, bitrates, format specifications, and subtitle streams) using the **Detailed Info** right-click option, **FFprobe** (part of the FFmpeg suite) must be installed on your system.

Without FFprobe installed, MediaFlow can only read basic file attributes (size, modification date, name) and won't be able to display advanced codec-level parameters or metadata fields.

### How to install and configure FFprobe:

1. **Download FFmpeg/FFprobe**:
   - **Windows Terminal (Recommended)**: Run `winget install Gnu.FFmpeg` in Windows Terminal (PowerShell or Command Prompt) to install it automatically.
   - **Manual Download**: Visit the official website [ffmpeg.org](https://ffmpeg.org/download.html), download a Windows build (such as from gyan.dev or BtbN), and extract the package.
2. **Add to System PATH**:
   - Extract the downloaded ZIP file to a folder (e.g., `C:\ffmpeg`).
   - Add the `bin` folder (e.g., `C:\ffmpeg\bin`) to your Windows **System Environment Variables (PATH)**. This allows MediaFlow to automatically detect and run `ffprobe` from any command line.
3. **Configure Custom Path in Settings**:
   - If you prefer not to add it to system PATH, open MediaFlow settings, scroll down to the **Deep Metadata (FFprobe)** section, click **Browse**, and manually select the path to your `ffprobe.exe` binary.
