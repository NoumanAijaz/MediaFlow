"""
MediaFlow — Multimedia Manager & Renamer
A specialized desktop application that parses video/image/audio metadata,
allows user inputs, and renames files based on a strict custom convention.
Includes Dark/Light theme support with OS preference detection.
"""
import sys
import os
import re
import shutil
import hashlib
import subprocess
import json
import ctypes
import random
import time
import shlex
import math
import logging
import threading
from datetime import datetime
import numpy as np
import cv2

# ─── Module-level setup ────────────────────────────────────────────────────────
logger = logging.getLogger(__name__)
if not logger.handlers:
    logging.basicConfig(level=logging.INFO, format="[MediaFlow] %(levelname)s: %(message)s")

# Module-level cache for vector icons to avoid rebuilding on every theme toggle
_ICON_CACHE = {}

# Single source of truth for naming field mappings
FIELD_MAP = {"Name": "name", "Duration": "duration", "Resolution": "resolution", "Rating": "rating", "Tags": "tags",
             "Date Taken": "date_taken", "Year-Month": "ym"}  # date fields: EXIF for photos, mtime fallback
DEFAULT_NAMING_FIELDS = ["name", "duration", "resolution", "rating", "tags"]
DEFAULT_NAMING_FIELDS_ORDERED = ["Name", "Duration", "Resolution", "Rating", "Tags", "Date Taken", "Year-Month"]

# Lock to serialize OpenCV calls (FFmpeg backend is not guaranteed thread-safe)
_CV_LOCK = threading.Lock()

# Cross-platform base font resolved at startup
if sys.platform == "win32":
    BASE_FONT_FAMILY = "Segoe UI"
elif sys.platform == "darwin":
    BASE_FONT_FAMILY = "SF Pro Text"
else:
    BASE_FONT_FAMILY = "Ubuntu"

from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout, QGridLayout,
    QPushButton, QLabel, QFileDialog, QTableWidget, QTableWidgetItem,
    QHeaderView, QComboBox, QLineEdit, QMessageBox, QProgressBar, QProgressDialog,
    QFrame, QAbstractItemView, QMenu, QCheckBox, QDialog, QDialogButtonBox, QRadioButton,
    QFormLayout, QGroupBox, QStackedWidget, QListWidget, QListWidgetItem,
    QStyledItemDelegate, QSlider, QScrollArea, QStyle, QSpinBox, QDoubleSpinBox,
    QSplitter, QSizePolicy, QInputDialog, QTableWidgetSelectionRange, QDateEdit
)
from PyQt6.QtCore import (
    Qt, QThread, pyqtSignal, pyqtSlot, QPropertyAnimation, QEasingCurve,
    QTimer, QSize, QRect, QUrl, QPoint, QPointF, QRectF, QEvent, QObject, QThreadPool, QRunnable,
    QEventLoop, QDate, QDateTime
)
from PyQt6.QtNetwork import QLocalServer, QLocalSocket
from PyQt6.QtGui import (
    QFont, QColor, QIcon, QPalette, QPainter,
    QAction, QPixmap, QKeySequence, QImage, QBrush, QGuiApplication,
    QPen, QPainterPath, QCursor, QImageReader, QPolygon, QLinearGradient
)
from PyQt6.QtMultimedia import QMediaPlayer, QAudioOutput
from PyQt6.QtMultimediaWidgets import QVideoWidget

class NamingTemplateListWidget(QListWidget):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.parent_win = parent

    def dropEvent(self, event):
        super().dropEvent(event)
        if self.parent_win:
            self.parent_win._on_naming_template_changed()

# ─── Constants ──────────────────────────────────────────────────────────────────

IMAGE_EXTENSIONS = {
    '.jpg', '.jpeg', '.png', '.bmp', '.webp', '.gif', '.tiff'
}
VIDEO_EXTENSIONS = {
    '.mp4', '.mkv', '.avi', '.mov', '.wmv', '.flv', '.webm',
    '.m4v', '.mpg', '.mpeg', '.3gp', '.3g2', '.ts', '.mts',
    '.m2ts', '.vob', '.ogv', '.divx', '.f4v', '.rm', '.rmvb',
    '.asf', '.amv', '.svi'
}
AUDIO_EXTENSIONS = {
    '.mp3', '.wav', '.flac', '.aac', '.ogg', '.m4a', '.wma',
    '.ape', '.alac', '.opus', '.amr', '.m4b'
}
PDF_EXTENSIONS = {
    '.pdf'
}

def get_extensions_for_type(media_type: str) -> set[str]:
    if media_type == 'video': return VIDEO_EXTENSIONS
    elif media_type == 'audio': return AUDIO_EXTENSIONS
    elif media_type == 'image': return IMAGE_EXTENSIONS
    elif media_type == 'pdf': return PDF_EXTENSIONS
    else: return VIDEO_EXTENSIONS | AUDIO_EXTENSIONS | IMAGE_EXTENSIONS | PDF_EXTENSIONS

def _resolve_config_dir() -> str:
    """Resolve where MediaFlow stores its config.

    Portable mode: if a 'MediaFlow.portable' flag file sits next to the
    executable (or the .py script), all config lives in 'MediaFlowData/'
    beside it instead of %APPDATA% — USB / no-install friendly.
    Otherwise: %APPDATA%/MediaFlow on Windows, ~/.config/MediaFlow on
    Linux/macOS (avoids polluting CWD when APPDATA is unset).
    """
    base = os.path.dirname(sys.executable) if getattr(sys, 'frozen', False) else os.path.dirname(os.path.abspath(__file__))
    if os.path.exists(os.path.join(base, "MediaFlow.portable")):
        return os.path.join(base, "MediaFlowData")
    appdata = os.environ.get('APPDATA')
    if appdata:
        return os.path.join(appdata, 'MediaFlow')
    # Linux/macOS fallback — XDG or HOME
    xdg = os.environ.get('XDG_CONFIG_HOME')
    if xdg:
        return os.path.join(xdg, 'MediaFlow')
    return os.path.join(os.path.expanduser('~'), '.config', 'MediaFlow')

CONFIG_DIR = _resolve_config_dir()
CONFIG_FILE = os.path.join(CONFIG_DIR, 'config.json')

def get_resource_path(relative_path):
    """Get absolute path to resource, works for dev and for PyInstaller"""
    try:
        base_path = sys._MEIPASS
    except AttributeError:
        base_path = os.path.dirname(os.path.abspath(__file__))
    return os.path.join(base_path, relative_path)

CACHE_LOCK = threading.Lock()

def update_metadata_cache(entries_to_add: dict, paths_to_delete: list = None):
    """Atomically update the metadata cache using os.replace() safely across threads."""
    with CACHE_LOCK:
        cache_path = os.path.join(CONFIG_DIR, 'scan_cache.json')
        try:
            os.makedirs(CONFIG_DIR, exist_ok=True)
            for _ in range(5):
                try:
                    current_cache = {}
                    if os.path.exists(cache_path):
                        with open(cache_path, 'r', encoding='utf-8') as f:
                            current_cache = json.load(f)
                    if entries_to_add:
                        current_cache.update(entries_to_add)
                    if paths_to_delete:
                        for p in paths_to_delete:
                            current_cache.pop(p, None)
                    temp_path = cache_path + '.tmp'
                    # Write + fsync for durability, then atomic replace
                    with open(temp_path, 'w', encoding='utf-8') as f:
                        json.dump(current_cache, f, ensure_ascii=False, indent=2)
                        f.flush()
                        os.fsync(f.fileno())
                    os.replace(temp_path, cache_path)  # atomic on both Windows and POSIX
                    break
                except Exception as e:
                    logger.warning("Cache write attempt failed: %s", e)
                    time.sleep(0.05)
        except Exception as e:
            logger.warning("update_metadata_cache failed: %s", e)

def get_resolution_tag(width: int, height: int) -> str:
    if width <= 0 or height <= 0: return "K"
    lesser = min(width, height)
    if lesser >= 2160: return "4K"
    elif lesser >= 1440: return "2K"
    elif lesser >= 1080: return "1K"
    else: return "K"

def format_duration_compact(total_seconds: float) -> str:
    total_seconds = int(round(total_seconds))
    hours = total_seconds // 3600
    minutes = (total_seconds % 3600) // 60
    seconds = total_seconds % 60
    if hours > 0: return f"{hours}{minutes:02d}{seconds:02d}"
    else: return f"{minutes}{seconds:02d}"

def format_duration(total_seconds: float) -> str:
    total_seconds = int(round(total_seconds))
    hours = total_seconds // 3600
    minutes = (total_seconds % 3600) // 60
    seconds = total_seconds % 60
    if hours > 0:
        return f"{hours}h {minutes:02d}m {seconds:02d}s"
    elif minutes > 0:
        return f"{minutes}m {seconds:02d}s"
    else:
        return f"{seconds}s"

def format_timestamp(ts: float) -> str:
    """Human date for table cells ('—' when unknown)."""
    try:
        if ts and ts > 0:
            return datetime.fromtimestamp(ts).strftime("%Y-%m-%d %H:%M")
    except (OverflowError, OSError, ValueError, TypeError):
        pass
    return "—"

def format_size(size_bytes: int) -> str:
    if size_bytes <= 0: return "0 B"
    for unit in ['B', 'KB', 'MB', 'GB', 'TB']:
        if abs(size_bytes) < 1024.0:
            return f"{size_bytes:.1f} {unit}"
        size_bytes /= 1024.0
    return f"{size_bytes:.1f} PB"

def parse_naming_format(filename: str) -> tuple[str | None, str | None]:
    # NOTE: removed redundant '|k' alternative (IGNORECASE already handles it)
    match = re.match(r"^(.+?)\s+(\d+)\s+(4K|2K|1K)(?:\s+(\d+|—))?(?:\.[^.]+)?$", filename, re.IGNORECASE)
    if match:
        artist = match.group(1).strip()
        rating = match.group(4)
        return artist, (None if rating == "—" else rating)
    
    match_img = re.match(r"^(.+?)\s+(4K|2K|1K)(?:\s+(\d+|—))?(?:\.[^.]+)?$", filename, re.IGNORECASE)
    if match_img:
        artist = match_img.group(1).strip()
        rating = match_img.group(3)
        return artist, (None if rating == "—" else rating)
        
    match_aud = re.match(r"^(.+?)\s+(\d+)\s+(\d+|—)(?:\.[^.]+)?$", filename, re.IGNORECASE)
    if match_aud:
        artist = match_aud.group(1).strip()
        rating = match_aud.group(3)
        return artist, (None if rating == "—" else rating)
        
    return None, None

def calculate_file_hash(filepath: str, head_only: bool = False) -> str | None:
    """Compute MD5. If head_only, fingerprint using size + first/last 1MB (fast for large media)."""
    try:
        if not os.path.exists(filepath): return None
        hasher = hashlib.md5()
        file_size = os.path.getsize(filepath)
        with open(filepath, 'rb') as f:
            if head_only and file_size > 2 * 1024 * 1024:
                # Hash: size + first 1MB + last 1MB
                hasher.update(str(file_size).encode())
                hasher.update(f.read(1024 * 1024))
                f.seek(-1024 * 1024, os.SEEK_END)
                hasher.update(f.read(1024 * 1024))
            else:
                for chunk in iter(lambda: f.read(65536), b''):
                    hasher.update(chunk)
        return hasher.hexdigest()
    except Exception: return None

def calculate_perceptual_hash(filepath: str, media_type: str) -> str | None:
    try:
        if not os.path.exists(filepath): return None
        img = None
        if media_type == 'image':
            with _CV_LOCK:
                img = cv2.imdecode(np.fromfile(filepath, dtype=np.uint8), cv2.IMREAD_GRAYSCALE)
        elif media_type == 'video':
            cap = None
            try:
                with _CV_LOCK:
                    cap = cv2.VideoCapture(filepath)
                    if cap.isOpened():
                        total_frames = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))
                        mid_frame = total_frames // 2 if total_frames > 0 else 0
                        cap.set(cv2.CAP_PROP_POS_FRAMES, mid_frame)
                        ret, frame = cap.read()
                        if ret: img = cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY)
            finally:
                if cap is not None:
                    cap.release()
        if img is None: return None
        with _CV_LOCK:
            resized = cv2.resize(img, (9, 8), interpolation=cv2.INTER_AREA)
        diff = resized[:, 1:] > resized[:, :-1]
        hash_val = 0
        for bit in diff.flatten(): hash_val = (hash_val << 1) | int(bit)
        return f"{hash_val:016x}"
    except Exception as e:
        logger.warning("perceptual hash failed for %s: %s", filepath, e)
        return None

def hamming_distance(h1: str, h2: str) -> int:
    try:
        val1 = int(h1, 16)
        val2 = int(h2, 16)
        return bin(val1 ^ val2).count('1')
    except Exception: return 999

def matches_query(info: 'MediaInfo', query_str: str, preview_name: str = "") -> bool:
    if not query_str: return True
    try: terms = shlex.split(query_str.strip())
    except Exception: terms = query_str.strip().split()
    
    parsed_artist, parsed_rating = parse_naming_format(info.filename)
    artist = (parsed_artist or "").lower().strip()
    rating = (parsed_rating or "").lower().strip()
    filename = info.filename.lower()
    
    for term in terms:
        term_clean = term.strip('"\'')
        if ':' in term_clean:
            try: key, val = term_clean.split(':', 1)
            except ValueError: continue
            key = key.lower().strip()
            val = val.lower().strip().strip('"\'')
            
            if key == 'rating':
                if ',' in val:
                    if rating not in [x.strip() for x in val.split(',')]: return False
                elif val.startswith('>=') and val[2:].isdigit():
                    if not rating.isdigit() or int(rating) < int(val[2:]): return False
                elif val.startswith('>') and val[1:].isdigit():
                    if not rating.isdigit() or int(rating) <= int(val[1:]): return False
                elif val.startswith('<=') and val[2:].isdigit():
                    if not rating.isdigit() or int(rating) > int(val[2:]): return False
                elif val.startswith('<') and val[1:].isdigit():
                    if not rating.isdigit() or int(rating) >= int(val[1:]): return False
                else:
                    if rating != val: return False
            elif key in ['tag', 'tags']:
                tags = [t.lower().strip() for t in getattr(info, 'tags', [])]
                if ',' in val:
                    query_tags = [x.strip() for x in val.split(',')]
                    if not any(qt in tags for qt in query_tags): return False
                else:
                    if val not in tags: return False
            elif key in ['name', 'artist']:
                if val not in artist: return False
            elif key in ['res', 'resolution']:
                if val not in info.resolution_tag.lower(): return False
            elif key == 'type':
                if val != info.media_type.lower(): return False
            elif key in ['ext', 'extension']:
                ext_val = val if val.startswith('.') else f".{val}"
                if info.extension != ext_val: return False
            else:
                val_sub = f"{key}:{val}"
                tags = [t.lower().strip() for t in getattr(info, 'tags', [])]
                if not (val_sub in filename or val_sub in artist or val_sub in rating or (preview_name and val_sub in preview_name.lower()) or any(val_sub in t for t in tags)): return False
        else:
            val = term_clean.lower()
            tags = [t.lower().strip() for t in getattr(info, 'tags', [])]
            if not (val in filename or val in artist or val in rating or (preview_name and val in preview_name.lower()) or any(val in t for t in tags)): return False
    return True

def sanitize_folder_name(name: str) -> str:
    """Remove illegal characters for folder names across OS."""
    if not name: return "Unknown"
    # Remove Windows illegal characters: \ / : * ? " < > |
    clean = re.sub(r'[\\/*?:"<>|]', "", name)
    clean = clean.strip()
    if sys.platform == "win32":
        clean = clean.rstrip(".")
    return clean or "Unknown"

def _strip_path_traversal(value: str) -> str:
    """Remove path separators and '..' components from a substituted path segment."""
    if not value:
        return value
    # Strip OS-specific separators AND forward slash (cross-platform safety)
    value = value.replace(os.sep, '').replace('/', '').replace('\\', '')
    # Remove any '..' segments left over
    value = re.sub(r'\.\.', '', value)
    return value


def parse_destination_template(template: str, info: 'MediaInfo', tags: list[str] = None) -> str:
    """
    Replaces {variables} in a path template with actual MediaInfo data.
    Also sanitizes substituted values to prevent path traversal.
    """
    parsed_artist, parsed_rating = parse_naming_format(info.filename)

    # Fallback to tags if artist isn't in the filename
    artist = parsed_artist or (tags[0] if tags else "Unknown Artist")
    rating = parsed_rating or "Unrated"

    # Map variables to data; apply extra traversal-stripping to user-controlled fields
    replacements = {
        '{type}': _strip_path_traversal(info.media_type),
        '{ext}': _strip_path_traversal(info.extension.replace('.', '')),
        '{name}': _strip_path_traversal(sanitize_folder_name(artist)),
        '{rating}': _strip_path_traversal(sanitize_folder_name(rating)),
        '{resolution}': _strip_path_traversal(info.resolution_tag or "Unknown"),
        '{tag}': _strip_path_traversal(sanitize_folder_name(tags[0]) if tags else "Untagged"),
        '{tags}': _strip_path_traversal(sanitize_folder_name(", ".join(tags)) if tags else "Untagged")
    }

    result = template
    for key, val in replacements.items():
        result = result.replace(key, val)

    return result

def get_ffprobe_command(custom_path=None) -> str | None:
    if custom_path and os.path.exists(custom_path): return custom_path
    sh_path = shutil.which("ffprobe")
    return sh_path

def get_ffmpeg_command(custom_path=None) -> str | None:
    if custom_path and os.path.exists(custom_path): return custom_path
    sh_path = shutil.which("ffmpeg")
    if sh_path: return sh_path
    ffprobe_cmd = get_ffprobe_command()
    if ffprobe_cmd:
        ffmpeg_sibling = os.path.join(os.path.dirname(ffprobe_cmd), "ffmpeg.exe" if sys.platform == "win32" else "ffmpeg")
        if os.path.exists(ffmpeg_sibling):
            return ffmpeg_sibling
    return None

def get_file_deep_metadata(filepath: str, ffprobe_path: str = None) -> dict | None:
    ffprobe_cmd = get_ffprobe_command(ffprobe_path)
    if not ffprobe_cmd: return None
    try:
        cmd = [ffprobe_cmd, "-v", "error", "-show_format", "-show_streams", "-of", "json", os.path.abspath(filepath)]
        startupinfo = None
        if sys.platform == "win32":
            startupinfo = subprocess.STARTUPINFO()
            startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
        result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, encoding='utf-8', startupinfo=startupinfo, timeout=10)
        if result.returncode == 0 and result.stdout:
            return parse_ffprobe_json(json.loads(result.stdout))
    except Exception: pass
    return None

def parse_ffprobe_json(data: dict) -> dict:
    parsed = {'format': '', 'size_bytes': 0, 'duration_seconds': 0.0, 'bitrate_kbps': 0, 'video': None, 'audio': None, 'hdr_type': 'SDR'}
    fmt = data.get('format', {})
    parsed['format'] = fmt.get('format_long_name', fmt.get('format_name', 'Unknown'))
    try: parsed['size_bytes'] = int(fmt.get('size', 0))
    except ValueError: pass
    try: parsed['duration_seconds'] = float(fmt.get('duration', 0.0))
    except ValueError: pass
    try: parsed['bitrate_kbps'] = int(fmt.get('bit_rate', 0)) // 1000
    except ValueError: pass
    for stream in data.get('streams', []):
        codec_type = stream.get('codec_type')
        if codec_type == 'video' and not parsed['video']:
            v_info = {'codec': stream.get('codec_name', '').upper(), 'profile': stream.get('profile', ''), 'width': int(stream.get('width', 0)), 'height': int(stream.get('height', 0)), 'fps': 0.0, 'bitrate_kbps': 0, 'pix_fmt': stream.get('pix_fmt', '')}
            fps_str = stream.get('r_frame_rate', '')
            if '/' in fps_str:
                try:
                    num, den = map(float, fps_str.split('/'))
                    if den > 0: v_info['fps'] = round(num / den, 2)
                except ValueError: pass
            try: v_info['bitrate_kbps'] = int(stream.get('bit_rate', 0)) // 1000
            except ValueError: pass
            parsed['video'] = v_info
            for sd in stream.get('side_data_list', []):
                sd_type = sd.get('side_data_type', '')
                if 'dovi' in sd_type.lower() or 'dolby vision' in sd_type.lower() or sd.get('dovi_profile') is not None:
                    parsed['hdr_type'] = 'Dolby Vision'; break
            if parsed['hdr_type'] == 'SDR':
                color_transfer = stream.get('color_transfer', '')
                if color_transfer == 'smpte2084':
                    codec_tag = stream.get('codec_tag_string', '')
                    parsed['hdr_type'] = 'Dolby Vision' if codec_tag in ['dvh1', 'dvhe'] else 'HDR10'
                elif color_transfer == 'arib-std-b67': parsed['hdr_type'] = 'HLG'
        elif codec_type == 'audio' and not parsed['audio']:
            a_info = {'codec': stream.get('codec_name', '').upper(), 'sample_rate_hz': int(stream.get('sample_rate', 0)), 'channels': int(stream.get('channels', 0)), 'channel_layout': stream.get('channel_layout', ''), 'bitrate_kbps': 0}
            try: a_info['bitrate_kbps'] = int(stream.get('bit_rate', 0)) // 1000
            except ValueError: pass
            ch = a_info['channels']
            if ch == 1: a_info['channel_layout'] = 'Mono'
            elif ch == 2: a_info['channel_layout'] = 'Stereo'
            elif ch == 6: a_info['channel_layout'] = '5.1 Surround'
            elif ch == 8: a_info['channel_layout'] = '7.1 Surround'
            elif a_info['channel_layout']: a_info['channel_layout'] = f"{a_info['channel_layout']} ({ch} ch)"
            else: a_info['channel_layout'] = f"{ch} channels"
            parsed['audio'] = a_info
    return parsed

def generate_thumbnail(filepath: str, media_type: str = 'video', width: int = 120, height: int = 68) -> QImage | None:
    """Build a thumbnail as a QImage.

    Returns QImage (not QPixmap) because this runs on QThreadPool worker
    threads — QPixmap may only be touched on the GUI thread. Callers on the
    main thread convert via QPixmap.fromImage().
    """
    try:
        if media_type == 'audio':
            img = QImage(width, height, QImage.Format.Format_ARGB32_Premultiplied)
            img.fill(QColor("#1e1b4b"))
            with QPainter(img) as painter:
                painter.setRenderHint(QPainter.RenderHint.Antialiasing)
                painter.setFont(QFont(BASE_FONT_FAMILY, 24))
                painter.setPen(QColor("#a78bfa"))
                painter.drawText(QRect(0, 0, width, height), Qt.AlignmentFlag.AlignCenter, "🎵")
            return img
        if media_type == 'pdf':
            img = QImage(width, height, QImage.Format.Format_ARGB32_Premultiplied)
            img.fill(QColor("#1e1b4b"))
            with QPainter(img) as painter:
                painter.setRenderHint(QPainter.RenderHint.Antialiasing)
                painter.setFont(QFont(BASE_FONT_FAMILY, 24))
                painter.setPen(QColor("#f87171"))
                painter.drawText(QRect(0, 0, width, height), Qt.AlignmentFlag.AlignCenter, "📄")
            return img
        if media_type == 'video':
            cap = None
            try:
                with _CV_LOCK:
                    cap = cv2.VideoCapture(filepath)
                    if not cap.isOpened(): return None
                    total_frames = cap.get(cv2.CAP_PROP_FRAME_COUNT)
                    if total_frames <= 0: return None
                    target_frame = int(total_frames * 0.1)
                    cap.set(cv2.CAP_PROP_POS_FRAMES, target_frame)
                    ret, frame = cap.read()
                    if not ret or frame is None:
                        cap.set(cv2.CAP_PROP_POS_FRAMES, 0)
                        ret, frame = cap.read()
            finally:
                if cap is not None:
                    cap.release()
        else:
            with _CV_LOCK:
                frame = cv2.imdecode(np.fromfile(filepath, dtype=np.uint8), cv2.IMREAD_COLOR)
            ret = frame is not None
        if not ret or frame is None: return None
        with _CV_LOCK:
            frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
        h, w = frame.shape[:2]
        if h == 0 or w == 0: return None
        aspect = w / h
        if width / height > aspect: new_h = height; new_w = int(height * aspect)
        else: new_w = width; new_h = int(width / aspect)
        if new_w <= 0 or new_h <= 0: return None
        with _CV_LOCK:
            frame = cv2.resize(frame, (new_w, new_h), interpolation=cv2.INTER_AREA).copy()
        bytes_per_line = new_w * 3
        qimg = QImage(frame.data, new_w, new_h, bytes_per_line, QImage.Format.Format_RGB888).copy()
        canvas = QImage(width, height, QImage.Format.Format_ARGB32_Premultiplied)
        canvas.fill(QColor("#1e1b4b"))
        with QPainter(canvas) as painter:
            painter.drawImage((width - new_w) // 2, (height - new_h) // 2, qimg)
        return canvas
    except Exception as e:
        logger.warning("generate_thumbnail failed for %s: %s", filepath, e)
        return None

# ─── EXIF / Sidecar helpers ─────────────────────────────────────────────────────

_SIDECAR_EXTS = {'.srt', '.ass', '.ssa', '.sub', '.vtt', '.nfo'}

def find_sidecars(filepath: str) -> list[str]:
    """Sibling subtitle/NFO files sharing this file's stem (plus optional
    language tags like movie.en.srt) — they follow the video on rename/move."""
    base = os.path.splitext(filepath)[0]
    parent = os.path.dirname(filepath)
    stem = os.path.basename(base)
    low = stem.lower()
    found = []
    try:
        entries = os.listdir(parent)
    except OSError:
        return found
    for name in entries:
        full = os.path.join(parent, name)
        if full == filepath or not os.path.isfile(full):
            continue
        nlow = name.lower()
        ext = os.path.splitext(nlow)[1]
        if ext not in _SIDECAR_EXTS or not nlow.startswith(low) or len(nlow) <= len(low):
            continue
        mid = nlow[len(low):-len(ext)]
        # Accept exact stem, or a short language marker (.en / -de / _pt-br …)
        if mid == "" or re.fullmatch(r"[\.\-_ ]{1,3}[a-z]{2,3}(?:[-_][a-z]{2,4})?", mid):
            found.append(full)
    return found

def _exif_datetime_original(filepath: str) -> datetime | None:
    """Read DateTimeOriginal/CreateDate from JPEG (APP1 Exif) or TIFF files."""
    try:
        with open(filepath, 'rb') as f:
            head = f.read(2)
            tiff_data = None
            if head == b"\xff\xd8":  # JPEG — scan segments for APP1/Exif
                while True:
                    b = f.read(2)
                    if len(b) < 2: return None
                    marker = b[1]
                    # Standalone markers (SOI/TEM/RSTn) have no length/payload — must not consume bytes
                    if marker in (0xD8, 0x01) or 0xD0 <= marker <= 0xD7:
                        continue
                    sz_bytes = f.read(2)
                    if len(sz_bytes) < 2: return None
                    size = int.from_bytes(sz_bytes, "big")
                    if size < 2: return None
                    payload = f.read(size - 2)
                    if len(payload) < size - 2: return None
                    if marker == 0xDA: return None  # start of scan — no Exif found
                    if marker == 0xE1 and payload.startswith(b"Exif\x00\x00"):
                        tiff_data = payload[6:]
                        break
            elif head in (b"II", b"MM"):
                f.seek(0)
                tiff_data = f.read()
            if not tiff_data or len(tiff_data) < 16:
                return None

            endian = "little" if tiff_data[:2] == b"II" else "big"
            ifd0 = int.from_bytes(tiff_data[4:8], endian)

            def rd(off, n): return tiff_data[off:off + n]

            def walk_ifd(ifd_off, want):
                vals = {}
                if ifd_off + 2 > len(tiff_data):
                    return vals
                cnt = int.from_bytes(rd(ifd_off, 2), endian)
                if ifd_off + 2 + cnt * 12 > len(tiff_data):
                    return vals
                for i in range(cnt):
                    e = ifd_off + 2 + i * 12
                    if e + 12 > len(tiff_data):
                        break
                    tag = int.from_bytes(rd(e, 2), endian)
                    typ = int.from_bytes(rd(e + 2, 2), endian)
                    num = int.from_bytes(rd(e + 4, 4), endian)
                    if tag in want and typ == 2:
                        if num <= 4:
                            vo = e + 8
                        else:
                            vo = int.from_bytes(rd(e + 8, 4), endian)
                            if vo + num > len(tiff_data):
                                continue
                        vals[tag] = rd(vo, max(0, num - 1)).decode("ascii", "replace")
                    elif tag == 0x8769:
                        if typ != 4:  # must be LONG
                            continue
                        sub = int.from_bytes(rd(e + 8, 4), endian)
                        if sub < len(tiff_data):
                            vals.update(walk_ifd(sub, want))
                return vals

            got = walk_ifd(ifd0, {0x9003, 0x9004, 0x0132})
            raw = got.get(0x9003) or got.get(0x9004) or got.get(0x0132)
            if raw:
                return datetime.strptime(raw.strip()[:19], "%Y:%m:%d %H:%M:%S")
    except Exception:
        return None
    return None

def get_media_datetime(info) -> datetime | None:
    """Best capture-time guess: EXIF for images, else file modified time."""
    if getattr(info, 'media_type', '') == 'image':
        dt = _exif_datetime_original(info.filepath)
        if dt is not None:
            return dt
    ts = float(getattr(info, 'mtime', 0) or 0)
    try:
        return datetime.fromtimestamp(ts) if ts > 0 else None
    except (OverflowError, OSError, ValueError):
        return None

def send_to_recycle_bin(path: str) -> bool:
    if sys.platform == "win32":
        try:
            import ctypes
            from ctypes import windll, c_int, c_wchar_p, byref, create_unicode_buffer, cast, Structure, POINTER
            from ctypes.wintypes import HWND, UINT, BOOL, LPCWSTR

            class SHFILEOPSTRUCTW(Structure):
                _fields_ = [
                    ("hwnd", HWND),
                    ("wFunc", UINT),
                    ("pFrom", LPCWSTR),
                    ("pTo", LPCWSTR),
                    ("fFlags", ctypes.c_ushort),
                    ("fAnyOperationsAborted", BOOL),
                    ("hNameMappings", ctypes.c_void_p),
                    ("lpszProgressTitle", LPCWSTR),
                ]

            path = os.path.abspath(path)
            # SHFileOperationW requires DOUBLE-null-terminated string
            p_from_buf = create_unicode_buffer(path + "\0\0")
            fileop = SHFILEOPSTRUCTW()
            fileop.hwnd = None
            fileop.wFunc = 3  # FO_DELETE
            fileop.pFrom = cast(p_from_buf, LPCWSTR)
            fileop.pTo = None
            fileop.fFlags = 0x0040 | 0x0010 | 0x0004  # ALLOWUNDO | NOCONFIRMATION | SILENT
            fileop.fAnyOperationsAborted = 0
            fileop.hNameMappings = None
            fileop.lpszProgressTitle = None
            return windll.shell32.SHFileOperationW(byref(fileop)) == 0
        except Exception as e:
            logger.warning("send_to_recycle_bin failed for %s: %s", path, e)
            return False
    else:
        try:
            from send2trash import send2trash
            send2trash(path); return True
        except ImportError:
            logger.warning("send2trash not installed; cannot trash %s", path)
            return False
        except Exception as e:
            logger.warning("send2trash failed for %s: %s", path, e)
            return False

def get_vector_icon(name: str, is_dark: bool) -> QIcon:
    # Cache icons to avoid rebuilding 6 sizes x ~20 icons on every theme toggle
    cache_key = (name, is_dark)
    if cache_key in _ICON_CACHE:
        return _ICON_CACHE[cache_key]
    icon = _build_vector_icon(name, is_dark)
    _ICON_CACHE[cache_key] = icon
    return icon


def _build_vector_icon(name: str, is_dark: bool) -> QIcon:
    if name in ['delete', 'clear', 'mute', 'stop', 'close', 'btnSettingsRemove']:
        color_hex = '#f87171' if is_dark else '#dc2626'
    elif name in ['process', 'play', 'pause', 'valid']:
        color_hex = '#34d399' if is_dark else '#059669'
    elif name in ['video', 'image', 'audio', 'star', 'save', 'plus', 'pdf', 'relocate']:
        color_hex = '#a78bfa' if is_dark else '#6366f1'
    else:
        color_hex = '#c4b5fd' if is_dark else '#4338ca'

    icon = QIcon()
    color = QColor(color_hex)
    for size_val in [16, 20, 24, 32, 48, 64]:
        pixmap = QPixmap(size_val, size_val)
        pixmap.fill(Qt.GlobalColor.transparent)
        painter = QPainter(pixmap)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        
        s = size_val / 24.0
        painter.scale(s, s)
        
        pen = QPen(color, 2.0, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin)
        painter.setPen(pen)
        painter.setBrush(Qt.BrushStyle.NoBrush)
        
        if name == 'sync':
            rect = QRectF(4, 4, 16, 16)
            painter.drawArc(rect, 30 * 16, 120 * 16)
            painter.drawLine(QPointF(18.5, 9.5), QPointF(18.5, 5))
            painter.drawLine(QPointF(18.5, 5), QPointF(14, 5))
            painter.drawArc(rect, 210 * 16, 120 * 16)
            painter.drawLine(QPointF(5.5, 14.5), QPointF(5.5, 19))
            painter.drawLine(QPointF(5.5, 19), QPointF(10, 19))
        elif name == 'stop':
            fill_color = QColor(color)
            fill_color.setAlpha(60)
            painter.setBrush(QBrush(fill_color))
            painter.drawRoundedRect(QRectF(6, 6, 12, 12), 3, 3)
        elif name == 'clear' or name == 'close':
            painter.drawLine(QPointF(7, 7), QPointF(17, 17))
            painter.drawLine(QPointF(17, 7), QPointF(7, 17))
        elif name == 'grid':
            fill_color = QColor(color)
            fill_color.setAlpha(45)
            painter.setBrush(QBrush(fill_color))
            painter.drawRoundedRect(QRectF(4, 4, 7, 7), 1.5, 1.5)
            painter.drawRoundedRect(QRectF(13, 4, 7, 7), 1.5, 1.5)
            painter.drawRoundedRect(QRectF(4, 13, 7, 7), 1.5, 1.5)
            painter.drawRoundedRect(QRectF(13, 13, 7, 7), 1.5, 1.5)
        elif name == 'list':
            fill_color = QColor(color)
            painter.setBrush(QBrush(fill_color))
            painter.drawEllipse(QPointF(5, 6), 1.5, 1.5)
            painter.drawEllipse(QPointF(5, 12), 1.5, 1.5)
            painter.drawEllipse(QPointF(5, 18), 1.5, 1.5)
            painter.setBrush(Qt.BrushStyle.NoBrush)
            painter.drawLine(QPointF(9, 6), QPointF(20, 6))
            painter.drawLine(QPointF(9, 12), QPointF(20, 12))
            painter.drawLine(QPointF(9, 18), QPointF(20, 18))
        elif name == 'preview':
            path = QPainterPath()
            path.moveTo(3, 12)
            path.quadTo(QPointF(12, 4), QPointF(21, 12))
            path.quadTo(QPointF(12, 20), QPointF(3, 12))
            painter.drawPath(path)
            painter.drawEllipse(QPointF(12, 12), 3, 3)
            fill_color = QColor(color)
            painter.setBrush(QBrush(fill_color))
            painter.drawEllipse(QPointF(12, 12), 1.5, 1.5)
        elif name == 'undo':
            path = QPainterPath()
            path.moveTo(18, 17)
            path.quadTo(QPointF(18, 9), QPointF(12, 9))
            path.lineTo(6, 9)
            painter.drawPath(path)
            painter.drawLine(QPointF(9, 5.5), QPointF(5, 9.5))
            painter.drawLine(QPointF(5, 9.5), QPointF(9, 13.5))
        elif name == 'redo':
            path = QPainterPath()
            path.moveTo(6, 17)
            path.quadTo(QPointF(6, 9), QPointF(12, 9))
            path.lineTo(18, 9)
            painter.drawPath(path)
            painter.drawLine(QPointF(15, 5.5), QPointF(19, 9.5))
            painter.drawLine(QPointF(19, 9.5), QPointF(15, 13.5))
        elif name == 'search':
            painter.drawEllipse(QRectF(4, 4, 9, 9))
            painter.drawLine(QPointF(11.5, 11.5), QPointF(18, 18))
        elif name == 'edit':
            path = QPainterPath()
            path.moveTo(12, 5)
            path.lineTo(19, 12)
            path.lineTo(8, 23)
            path.lineTo(3, 23)
            path.lineTo(3, 18)
            path.closeSubpath()
            painter.drawPath(path)
            painter.drawLine(QPointF(15, 8), QPointF(11, 12))
        elif name == 'delete':
            painter.drawLine(QPointF(3, 6), QPointF(21, 6))
            painter.drawRoundedRect(QRectF(9, 3, 6, 3), 1, 1)
            path = QPainterPath()
            path.moveTo(5, 6)
            path.lineTo(6, 20)
            path.quadTo(QPointF(6, 21), QPointF(7, 21))
            path.lineTo(17, 21)
            path.quadTo(QPointF(18, 21), QPointF(18, 20))
            path.lineTo(19, 6)
            
            fill_color = QColor(color)
            fill_color.setAlpha(45)
            painter.setBrush(QBrush(fill_color))
            painter.drawPath(path)
            
            painter.setBrush(Qt.BrushStyle.NoBrush)
            painter.drawLine(QPointF(9, 9), QPointF(9, 18))
            painter.drawLine(QPointF(12, 9), QPointF(12, 18))
            painter.drawLine(QPointF(15, 9), QPointF(15, 18))
        elif name == 'process':
            fill_color = QColor(color)
            fill_color.setAlpha(90)
            painter.setBrush(QBrush(fill_color))
            
            p1 = QPainterPath()
            p1.moveTo(5, 6)
            p1.lineTo(11, 12)
            p1.lineTo(5, 18)
            p1.lineTo(7.5, 18)
            p1.lineTo(13.5, 12)
            p1.lineTo(7.5, 6)
            p1.closeSubpath()
            painter.drawPath(p1)
            
            p2 = QPainterPath()
            p2.moveTo(11, 6)
            p2.lineTo(17, 12)
            p2.lineTo(11, 18)
            p2.lineTo(13.5, 18)
            p2.lineTo(19.5, 12)
            p2.lineTo(13.5, 6)
            p2.closeSubpath()
            painter.drawPath(p2)
        elif name == 'folder':
            path = QPainterPath()
            path.moveTo(3, 6)
            path.lineTo(9, 6)
            path.lineTo(11, 9)
            path.lineTo(20, 9)
            path.quadTo(QPointF(21, 9), QPointF(21, 10))
            path.lineTo(21, 18)
            path.quadTo(QPointF(21, 19), QPointF(20, 19))
            path.lineTo(4, 19)
            path.quadTo(QPointF(3, 19), QPointF(3, 18))
            path.closeSubpath()
            
            fill_color = QColor(color)
            fill_color.setAlpha(60)
            painter.setBrush(QBrush(fill_color))
            painter.drawPath(path)
        elif name == 'pdf':
            path = QPainterPath()
            path.moveTo(5, 3)
            path.lineTo(14, 3)
            path.lineTo(19, 8)
            path.lineTo(19, 21)
            path.lineTo(5, 21)
            path.closeSubpath()
            
            fill_color = QColor(color)
            fill_color.setAlpha(60)
            painter.setBrush(QBrush(fill_color))
            painter.drawPath(path)
            
            painter.setBrush(Qt.BrushStyle.NoBrush)
            painter.drawLine(QPointF(14, 3), QPointF(14, 8))
            painter.drawLine(QPointF(14, 8), QPointF(19, 8))
            painter.drawLine(QPointF(8, 12), QPointF(16, 12))
            painter.drawLine(QPointF(8, 15), QPointF(16, 15))
            painter.drawLine(QPointF(8, 18), QPointF(13, 18))
        elif name == 'relocate':
            rect = QRectF(4, 8, 16, 11)
            painter.drawRect(rect)
            painter.drawLine(QPointF(4, 12), QPointF(20, 12))
            painter.drawLine(QPointF(12, 12), QPointF(12, 19))
            painter.drawLine(QPointF(12, 8), QPointF(12, 3))
            painter.drawLine(QPointF(12, 3), QPointF(9, 6))
            painter.drawLine(QPointF(12, 3), QPointF(15, 6))
        elif name == 'settings':
            painter.drawEllipse(QRectF(9, 9, 6, 6))
            path = QPainterPath()
            path.addEllipse(QRectF(6, 6, 12, 12))
            painter.drawPath(path)
            for i in range(8):
                angle = i * 45
                import math
                rad = math.radians(angle)
                c = math.cos(rad)
                s_val = math.sin(rad)
                painter.drawLine(QPointF(12 + 6*c, 12 + 6*s_val), QPointF(12 + 8.5*c, 12 + 8.5*s_val))
        elif name == 'mute':
            path = QPainterPath()
            path.moveTo(3, 9)
            path.lineTo(7, 9)
            path.lineTo(12, 4)
            path.lineTo(12, 20)
            path.lineTo(7, 15)
            path.lineTo(3, 15)
            path.closeSubpath()
            
            fill_color = QColor(color)
            fill_color.setAlpha(60)
            painter.setBrush(QBrush(fill_color))
            painter.drawPath(path)
            
            painter.setBrush(Qt.BrushStyle.NoBrush)
            painter.drawLine(QPointF(15, 10), QPointF(19, 14))
            painter.drawLine(QPointF(19, 10), QPointF(15, 14))
        elif name == 'unmute':
            path = QPainterPath()
            path.moveTo(3, 9)
            path.lineTo(7, 9)
            path.lineTo(12, 4)
            path.lineTo(12, 20)
            path.lineTo(7, 15)
            path.lineTo(3, 15)
            path.closeSubpath()
            
            fill_color = QColor(color)
            fill_color.setAlpha(60)
            painter.setBrush(QBrush(fill_color))
            painter.drawPath(path)
            
            painter.setBrush(Qt.BrushStyle.NoBrush)
            painter.drawArc(QRectF(10, 8, 6, 8), -60 * 16, 120 * 16)
            painter.drawArc(QRectF(8, 5, 10, 14), -60 * 16, 120 * 16)
        elif name == 'plus':
            painter.drawLine(QPointF(12, 5), QPointF(12, 19))
            painter.drawLine(QPointF(5, 12), QPointF(19, 12))
        elif name == 'star':
            path = QPainterPath()
            import math
            pts = []
            for i in range(5):
                a_outer = math.radians(i * 72 - 90)
                pts.append(QPointF(12 + 8 * math.cos(a_outer), 12 + 8 * math.sin(a_outer)))
                a_inner = math.radians(i * 72 - 90 + 36)
                pts.append(QPointF(12 + 3.2 * math.cos(a_inner), 12 + 3.2 * math.sin(a_inner)))
            path.moveTo(pts[0])
            for pt in pts[1:]:
                path.lineTo(pt)
            path.closeSubpath()
            
            fill_color = QColor(color)
            fill_color.setAlpha(80)
            painter.setBrush(QBrush(fill_color))
            painter.drawPath(path)
        elif name == 'video':
            painter.drawRoundedRect(QRectF(3, 6, 11, 12), 2, 2)
            path = QPainterPath()
            path.moveTo(14, 10)
            path.lineTo(20, 6)
            path.lineTo(20, 18)
            path.lineTo(14, 14)
            path.closeSubpath()
            
            fill_color = QColor(color)
            fill_color.setAlpha(60)
            painter.setBrush(QBrush(fill_color))
            painter.drawPath(path)
            painter.drawRoundedRect(QRectF(3, 6, 11, 12), 2, 2)
        elif name == 'image':
            painter.drawRoundedRect(QRectF(3, 4, 18, 16), 2, 2)
            painter.drawEllipse(QPointF(15.5, 8.5), 1.5, 1.5)
            
            path = QPainterPath()
            path.moveTo(3, 19)
            path.lineTo(9, 11)
            path.lineTo(13, 15)
            path.lineTo(17, 12)
            path.lineTo(21, 17)
            path.lineTo(21, 19)
            path.closeSubpath()
            
            fill_color = QColor(color)
            fill_color.setAlpha(60)
            painter.setBrush(QBrush(fill_color))
            painter.drawPath(path)
        elif name == 'audio':
            painter.setBrush(QBrush(color))
            painter.drawEllipse(QRectF(4, 13, 5, 4))
            painter.drawEllipse(QRectF(13, 11, 5, 4))
            painter.setBrush(Qt.BrushStyle.NoBrush)
            painter.drawLine(QPointF(8, 15), QPointF(8, 5))
            painter.drawLine(QPointF(17, 13), QPointF(17, 3))
            
            path = QPainterPath()
            path.moveTo(8, 5)
            path.lineTo(17, 3)
            path.lineTo(17, 6)
            path.lineTo(8, 8)
            path.closeSubpath()
            
            fill_color = QColor(color)
            painter.setBrush(QBrush(fill_color))
            painter.drawPath(path)
        elif name == 'save':
            path = QPainterPath()
            path.moveTo(4, 4)
            path.lineTo(16, 4)
            path.lineTo(20, 8)
            path.lineTo(20, 20)
            path.lineTo(4, 20)
            path.closeSubpath()
            
            fill_color = QColor(color)
            fill_color.setAlpha(60)
            painter.setBrush(QBrush(fill_color))
            painter.drawPath(path)
            
            painter.setBrush(Qt.BrushStyle.NoBrush)
            painter.drawRect(QRectF(7, 12, 10, 8))
            painter.drawRect(QRectF(8, 4, 6, 5))
        elif name == 'play':
            painter.setBrush(QBrush(color))
            path = QPainterPath()
            path.moveTo(8, 5)
            path.lineTo(18, 12)
            path.lineTo(8, 19)
            path.closeSubpath()
            painter.drawPath(path)
        elif name == 'pause':
            painter.setBrush(QBrush(color))
            painter.drawRoundedRect(QRectF(7, 5, 3.5, 14), 1, 1)
            painter.drawRoundedRect(QRectF(13.5, 5, 3.5, 14), 1, 1)

        painter.end()
        icon.addPixmap(pixmap)
    return icon

class NoTextDelegate(QStyledItemDelegate):
    def paint(self, painter, option, index):
        painter.save()
        # Use the same fallback logic as elsewhere — defaults to dark
        is_dark = True
        top_win = self.window() if hasattr(self, 'window') else None
        if top_win and hasattr(top_win, 'current_theme'):
            is_dark = (top_win.current_theme == 'dark')
        
        # Draw background selection/hover only
        if option.state & QStyle.StateFlag.State_Selected:
            bg_color = QColor(99, 102, 241, 64) if is_dark else QColor(99, 102, 241, 45)
            painter.fillRect(option.rect, bg_color)
        elif option.state & QStyle.StateFlag.State_MouseOver:
            bg_color = QColor(255, 255, 255, 12) if is_dark else QColor(0, 0, 0, 10)
            painter.fillRect(option.rect, bg_color)
            
        widget = None
        if hasattr(self.parent(), 'table'):
            widget = self.parent().table.cellWidget(index.row(), index.column())
            
        if widget is None:
            painter.restore()
            super().paint(painter, option, index)
        else:
            painter.restore()

class StatusBadgeDelegate(QStyledItemDelegate):
    def initStyleOption(self, option, index):
        super().initStyleOption(option, index)

    def paint(self, painter, option, index):
        opt = option.__class__(option)
        self.initStyleOption(opt, index)
        
        painter.save()
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        
        is_dark = getattr(self.parent(), 'window', lambda: None)()
        is_dark = getattr(is_dark, 'current_theme', 'dark') == 'dark' if is_dark else True
        
        if opt.state & QStyle.StateFlag.State_Selected:
            bg_color = QColor(99, 102, 241, 46) if is_dark else QColor(99, 102, 241, 30)
            painter.fillRect(opt.rect, bg_color)
        elif opt.state & QStyle.StateFlag.State_MouseOver:
            bg_color = QColor(255, 255, 255, 12) if is_dark else QColor(0, 0, 0, 10)
            painter.fillRect(opt.rect, bg_color)
            
        text = opt.text
        if not text or text == "—":
            super().paint(painter, option, index)
            painter.restore()
            return
            
        badge_bg = QColor(255, 255, 255, 15)
        badge_fg = QColor("#9ca3af") if is_dark else QColor("#4b5563")
        
        if "Valid" in text:
            badge_bg = QColor(16, 185, 129, 30) if is_dark else QColor(16, 185, 129, 25)
            badge_fg = QColor("#34d399") if is_dark else QColor("#059669")
        elif "Unsupported" in text or "Error" in text:
            badge_bg = QColor(239, 68, 68, 30) if is_dark else QColor(239, 68, 68, 25)
            badge_fg = QColor("#f87171") if is_dark else QColor("#dc2626")
        elif "Renamed" in text:
            badge_bg = QColor(99, 102, 241, 30) if is_dark else QColor(99, 102, 241, 25)
            badge_fg = QColor("#c4b5fd") if is_dark else QColor("#4338ca")
        elif "Dup" in text:
            badge_bg = QColor(245, 158, 11, 30) if is_dark else QColor(245, 158, 11, 25)
            badge_fg = QColor("#facc15") if is_dark else QColor("#d97706")
            
        badge_height = 24
        y_offset = (opt.rect.height() - badge_height) // 2
        badge_rect = QRect(opt.rect.x() + 6, opt.rect.y() + y_offset, opt.rect.width() - 12, badge_height)
        
        painter.setBrush(badge_bg)
        painter.setPen(Qt.PenStyle.NoPen)
        painter.drawRoundedRect(QRectF(badge_rect), 6, 6)
        
        painter.setFont(QFont(BASE_FONT_FAMILY, 9, QFont.Weight.Bold))
        painter.setPen(badge_fg)
        painter.drawText(badge_rect, Qt.AlignmentFlag.AlignCenter, text)
        painter.restore()

class NumericTableWidgetItem(QTableWidgetItem):
    def __init__(self, text, sort_key=None):
        super().__init__(text)
        self.sort_key = sort_key
    def __lt__(self, other):
        if not isinstance(other, QTableWidgetItem): return super().__lt__(other)
        self_key = getattr(self, 'sort_key', None)
        other_key = getattr(other, 'sort_key', None)
        if self_key is not None and other_key is not None:
            try: return self_key < other_key
            except TypeError: pass
        def split_alphanumeric(t): return [int(c) if c.isdigit() else c.lower() for c in re.split(r'(\d+)', t)]
        return split_alphanumeric(self.text()) < split_alphanumeric(other.text())

# ─── Theme Manager ──────────────────────────────────────────────────────────────

DARK_STYLESHEET = """
QMainWindow { background: qlineargradient(x1:0, y1:0, x2:1, y2:1, stop:0 #0f0c29, stop:0.5 #302b63, stop:1 #24243e); }
QWidget { color: #e0e0e0; font-family: 'Segoe UI', 'Inter', sans-serif; }
#sidebar { background: #09071c; border-right: 1px solid rgba(167, 139, 250, 0.15); min-width: 220px; max-width: 220px; }
#titleLabel { font-size: 20px; font-weight: 800; color: #ffffff; letter-spacing: 2px; margin-top: 10px; }
#subtitleLabel { font-size: 10px; font-weight: 600; color: #a78bfa; letter-spacing: 1.5px; text-transform: uppercase; margin-top: 2px; }
#smartSidebarTitle { font-size: 11px; font-weight: 700; color: #7c7c9a; letter-spacing: 1.5px; text-transform: uppercase; margin-left: 12px; }
#navButton { background: transparent; color: #9ca3af; text-align: left; padding: 12px 24px; font-size: 13px; font-weight: 600; letter-spacing: 0.5px; border-radius: 8px; margin: 4px 16px; border: 1px solid transparent; }
#navButton:hover { background: rgba(139, 92, 246, 0.08); color: #c4b5fd; border: 1px solid rgba(139, 92, 246, 0.15); }
#navButton[active="true"] { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #6366f1, stop:1 #8b5cf6); color: #ffffff; border: 1px solid rgba(124, 58, 237, 0.3); font-weight: 700; }
#controlPanel { background: rgba(30, 27, 75, 0.65); border: 1px solid rgba(167, 139, 250, 0.2); border-radius: 16px; padding: 16px 20px; }
#filterPanel { background: rgba(30, 27, 75, 0.50); border: 1px solid rgba(167, 139, 250, 0.15); border-radius: 12px; padding: 10px 16px; margin-bottom: 8px; }
#advancedFilterPanel { background: rgba(30, 27, 75, 0.50); border: 1px solid rgba(167, 139, 250, 0.15); border-radius: 12px; padding: 10px 16px; margin-bottom: 8px; }
#statsPanel { background: rgba(30, 27, 75, 0.60); border: 1px solid rgba(167, 139, 250, 0.2); border-left: 4px solid #8b5cf6; border-radius: 8px; padding: 0px; }
#statValue { font-size: 18px; font-weight: 800; color: #ffffff; }
#statLabel { font-size: 9px; color: #a78bfa; text-transform: uppercase; letter-spacing: 1px; font-weight: bold; }
QPushButton { border: none; border-radius: 8px; padding: 10px 24px; font-size: 13px; font-weight: 600; letter-spacing: 0.5px; }
#btnSelectFolder { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #6366f1, stop:1 #8b5cf6); color: white; min-width: 180px; }
/* Compact padding for control-panel action buttons — the generic 24px h-padding made six-button rows overflow at minimum window width */
#btnLoadFiles, #btnStopLoading, #btnClearAll, #btnWatch, #btnViewMode, #btnTogglePreview, #btnToggleStats, #btnBatchEdit, #btnBatchTag, #btnFindDuplicates, #btnDelete, #btnProcessAll, #btnUndo, #btnRedo { padding-left: 14px; padding-right: 14px; }

#btnSelectFolder:hover { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #4f46e5, stop:1 #7c3aed); }
#btnSelectFolder:pressed { background: #4338ca; }
#btnSelectFolder:disabled { background: rgba(255, 255, 255, 0.05); color: rgba(255, 255, 255, 0.2); }
#btnProcessAll { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #10b981, stop:1 #06d6a0); color: white; min-width: 130px; font-size: 14px; padding: 12px 22px; }
#btnProcessAll:hover { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #059669, stop:1 #10b981); }
#btnProcessAll:pressed { background: #047857; }
#btnProcessAll:disabled { background: rgba(255, 255, 255, 0.05); color: rgba(255, 255, 255, 0.2); }
#btnClearAll { background: rgba(239, 68, 68, 0.15); color: #f87171; border: 1px solid rgba(239, 68, 68, 0.3); min-width: 100px; }
#btnClearAll:hover { background: rgba(239, 68, 68, 0.25); color: #ffffff; border: 1px solid #ef4444; }
#btnClearAll:pressed { background: #b91c1c; }
#btnClearAll:disabled { background: rgba(255, 255, 255, 0.05); color: rgba(255, 255, 255, 0.2); }
#btnWatch { background: rgba(255, 255, 255, 0.05); color: #c4b5fd; border: 1px solid rgba(167, 139, 250, 0.2); }
#btnWatch:checked { background: rgba(16, 185, 129, 0.2); color: #34d399; border: 1px solid rgba(16, 185, 129, 0.4); }
#btnLoadFiles { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #3b82f6, stop:1 #60a5fa); color: white; min-width: 120px; }
#btnLoadFiles:hover { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #2563eb, stop:1 #3b82f6); }
#btnLoadFiles:pressed { background: #1d4ed8; }
#btnLoadFiles:disabled { background: rgba(255, 255, 255, 0.05); color: rgba(255, 255, 255, 0.2); }
#btnStopLoading { background: rgba(239, 68, 68, 0.25); color: #f87171; border: 1px solid rgba(239, 68, 68, 0.4); min-width: 120px; }
#btnStopLoading:hover { background: rgba(239, 68, 68, 0.35); color: #ffffff; }
#btnStopLoading:pressed { background: rgba(185, 28, 28, 0.5); }
#btnStopLoading:disabled { background: rgba(255, 255, 255, 0.05); color: rgba(255, 255, 255, 0.2); }
#btnBatchEdit { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #f59e0b, stop:1 #fbbf24); color: #1f2937; min-width: 115px; }
#btnBatchEdit:hover { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #d97706, stop:1 #f59e0b); color: #ffffff; }
#btnBatchEdit:pressed { background: #b45309; }
#btnBatchEdit:disabled { background: rgba(255, 255, 255, 0.05); color: rgba(255, 255, 255, 0.2); }
#btnFindDuplicates { background: rgba(14, 165, 233, 0.15); color: #38bdf8; border: 1px solid rgba(14, 165, 233, 0.3); min-width: 105px; }
#btnFindDuplicates:hover { background: rgba(14, 165, 233, 0.25); color: #ffffff; border: 1px solid #0ea5e9; }
#btnFindDuplicates:pressed { background: #0369a1; }
#btnFindDuplicates:disabled { background: transparent; color: rgba(255, 255, 255, 0.15); border: 1px solid rgba(255, 255, 255, 0.05); }
#btnViewMode, #btnTogglePreview, #btnToggleStats { background: rgba(167, 139, 250, 0.15); color: #c4b5fd; border: 1px solid rgba(167, 139, 250, 0.3); min-width: 100px; padding: 6px 12px; font-size: 11px; border-radius: 6px; }
#btnViewMode:hover, #btnTogglePreview:hover, #btnToggleStats:hover { background: rgba(167, 139, 250, 0.25); color: #ffffff; }
#btnViewMode:pressed, #btnTogglePreview:pressed, #btnToggleStats:pressed { background: rgba(139, 92, 246, 0.4); }
#btnViewMode:checked, #btnTogglePreview:checked, #btnToggleStats:checked { background: rgba(99, 102, 241, 0.4); color: #ffffff; border: 1px solid rgba(99, 102, 241, 0.6); }
#btnViewMode:disabled, #btnTogglePreview:disabled, #btnToggleStats:disabled { background: transparent; color: rgba(255, 255, 255, 0.05); }
#previewPanel { background: rgba(15, 12, 41, 0.7); border: 1px solid rgba(167, 139, 250, 0.2); border-radius: 12px; }
#btnUndo, #btnRedo { background: rgba(139, 92, 246, 0.2); color: #a78bfa; border: 1px solid rgba(139, 92, 246, 0.4); min-width: 100px; }
#btnUndo:hover, #btnRedo:hover { background: rgba(139, 92, 246, 0.3); color: #ffffff; border: 1px solid #8b5cf6; }
#btnUndo:pressed, #btnRedo:pressed { background: #6d28d9; }
#btnUndo:disabled, #btnRedo:disabled { background: transparent; color: rgba(255, 255, 255, 0.15); border: 1px solid rgba(255, 255, 255, 0.05); }
#btnDelete { background: rgba(239, 68, 68, 0.15); color: #f87171; border: 1px solid rgba(239, 68, 68, 0.3); min-width: 105px; }
#btnDelete:hover { background: rgba(239, 68, 68, 0.25); color: #ffffff; border: 1px solid #ef4444; }
#btnDelete:pressed { background: #b91c1c; }
#btnDelete:disabled { background: transparent; color: rgba(255, 255, 255, 0.15); border: 1px solid rgba(255, 255, 255, 0.05); }
QTableWidget { background: rgba(15, 12, 41, 0.7); border: 1px solid rgba(167, 139, 250, 0.15); border-radius: 14px; gridline-color: rgba(167, 139, 250, 0.08); selection-background-color: rgba(99, 102, 241, 0.25); font-size: 12px; outline: none; }
QTableWidget::item { padding: 6px 10px; border-bottom: 1px solid rgba(167, 139, 250, 0.06); }
QTableWidget::item:selected { background: rgba(99, 102, 241, 0.18); }
QHeaderView::section { background: #151233; color: #a78bfa; font-weight: 700; font-size: 10px; text-transform: uppercase; letter-spacing: 1.5px; padding: 12px 14px; border: none; border-bottom: 2px solid rgba(167, 139, 250, 0.3); border-right: 1px solid rgba(167, 139, 250, 0.08); }
QScrollBar:vertical { background: transparent; width: 8px; margin: 4px 2px; }
QScrollBar::handle:vertical { background: rgba(167, 139, 250, 0.35); border-radius: 4px; min-height: 30px; }
QScrollBar::handle:vertical:hover { background: rgba(167, 139, 250, 0.55); }
QScrollBar:horizontal { background: transparent; height: 8px; margin: 2px 4px; }
QScrollBar::handle:horizontal { background: rgba(167, 139, 250, 0.35); border-radius: 4px; min-width: 30px; }
QScrollBar::handle:horizontal:hover { background: rgba(167, 139, 250, 0.55); }
QLineEdit { background: rgba(45, 40, 90, 0.8); border: 1px solid rgba(167, 139, 250, 0.25); border-radius: 6px; padding: 4px 8px; color: #e0e0e0; font-size: 12px; }
QLineEdit:focus { border: 1px solid #8b5cf6; background: rgba(55, 48, 110, 0.9); }
QComboBox { background: rgba(45, 40, 90, 0.8); border: 1px solid rgba(167, 139, 250, 0.25); border-radius: 6px; padding: 4px 8px; color: #e0e0e0; font-size: 12px; min-width: 55px; }
#searchComboBox { background: rgba(45, 40, 90, 0.8); border: 1px solid rgba(167, 139, 250, 0.25); border-radius: 6px; }
#searchComboBox QLineEdit { background: transparent; border: none; padding: 4px 8px; color: #e0e0e0; font-size: 12px; }
QComboBox QAbstractItemView { background: #1e1b4b; border: 1px solid rgba(167, 139, 250, 0.3); border-radius: 6px; selection-background-color: rgba(99, 102, 241, 0.4); color: #e0e0e0; }
QProgressBar { background: rgba(30, 27, 75, 0.6); border: 1px solid rgba(167, 139, 250, 0.15); border-radius: 8px; text-align: center; color: #a78bfa; font-size: 11px; font-weight: 600; height: 18px; }
QProgressBar::chunk { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #6366f1, stop:1 #a78bfa); border-radius: 7px; }
#statusBar { background: rgba(15, 12, 41, 0.5); border-top: 1px solid rgba(167, 139, 250, 0.1); padding: 6px 16px; font-size: 11px; color: #7c7c9a; }
#statusLabelReady { color: #34d399; } #statusLabelWarning { color: #fbbf24; } #statusLabelError { color: #f87171; }
#folderPathLabel { color: #9ca3af; font-size: 12px; padding: 0 8px; }
QToolTip { background: #1e1b4b; color: #e0e0e0; border: 1px solid rgba(167, 139, 250, 0.3); border-radius: 6px; padding: 6px 10px; font-size: 12px; }
#thumbnailLabel { border: 1px solid rgba(167, 139, 250, 0.2); border-radius: 6px; background: rgba(30, 27, 75, 0.4); }
#headerBar { background: rgba(15, 12, 41, 0.4); border-bottom: 1px solid rgba(167, 139, 250, 0.12); min-height: 52px; }
#pageTitle { font-size: 18px; font-weight: 700; color: #ffffff; letter-spacing: 0.5px; }
#settingsPanel { background: rgba(15, 12, 41, 0.95); border-left: 1px solid rgba(167, 139, 250, 0.2); }
#settingsPanel QListWidget { background: rgba(30, 27, 75, 0.6); border: 1px solid rgba(167, 139, 250, 0.2); border-radius: 8px; padding: 4px; font-size: 11px; color: #c4b5fd; min-height: 100px; }
#settingsPanel QListWidget::item:selected { background: rgba(99, 102, 241, 0.25); color: #e0e0e0; }
#settingsPanel QListWidget::item:hover { background: rgba(99, 102, 241, 0.12); }
#btnSettingsAdd { background: rgba(99, 102, 241, 0.2); color: #a78bfa; border: 1px solid rgba(99, 102, 241, 0.3); border-radius: 8px; padding: 8px 8px; font-size: 12px; }
#btnSettingsAdd:hover { background: rgba(99, 102, 241, 0.35); color: #ffffff; }
#btnSettingsAdd:pressed { background: #4338ca; }
#btnSettingsRemove { background: rgba(239, 68, 68, 0.12); color: #f87171; border: 1px solid rgba(239, 68, 68, 0.25); border-radius: 8px; padding: 8px 16px; font-size: 12px; }
#btnSettingsRemove:hover { background: rgba(239, 68, 68, 0.22); color: #ffffff; }
#btnSettingsRemove:pressed { background: #b91c1c; }
QGroupBox { background: rgba(30, 27, 75, 0.3); border: 1px solid rgba(167, 139, 250, 0.15); border-radius: 10px; margin-top: 12px; padding: 16px 10px 10px 10px; font-size: 13px; font-weight: 600; color: #a78bfa; }
QGroupBox::title { subcontrol-origin: margin; subcontrol-position: top left; padding: 2px 10px; color: #c4b5fd; }
QScrollArea { background: transparent; border: none; }
/* FIX: a QScrollArea's viewport is a plain QWidget that keeps auto-filling
   with the PALETTE Window color captured when it was first polished — after a
   theme switch it renders the OLD theme's color (dark bands in light mode /
   light blocks in dark mode). Force scroll contents transparent so the themed
   parent background (#sidebar / #settingsPanel) shows through instead. */
QScrollArea > QWidget > QWidget { background: transparent; }
#btnGlobalMute, #btnSettingsToggle { background: rgba(167, 139, 250, 0.15); color: #c4b5fd; border: 1px solid rgba(167, 139, 250, 0.3); border-radius: 8px; padding: 0px; font-size: 16px; }
#btnGlobalMute:hover, #btnSettingsToggle:hover { background: rgba(167, 139, 250, 0.3); color: #ffffff; }
#btnGlobalMute:pressed, #btnSettingsToggle:pressed { background: rgba(99, 102, 241, 0.4); }
#btnHelp { background: rgba(167, 139, 250, 0.15); color: #c4b5fd; border: 1px solid rgba(167, 139, 250, 0.3); border-radius: 18px; padding: 0px; font-size: 16px; font-weight: bold; }
#btnHelp:hover { background: rgba(167, 139, 250, 0.3); color: #ffffff; }
#btnHelp:pressed { background: rgba(99, 102, 241, 0.4); }
#btnCloseSettings, #btnClosePreview { background: rgba(239, 68, 68, 0.15); color: #f87171; border: 1px solid rgba(239, 68, 68, 0.3); border-radius: 6px; padding: 0px; font-weight: bold; font-size: 12px; }
#btnCloseSettings:hover, #btnClosePreview:hover { background: rgba(239, 68, 68, 0.3); color: #ffffff; }
#btnCloseSettings:pressed, #btnClosePreview:pressed { background: #b91c1c; }
#btnAdvancedFilter { background: rgba(255, 255, 255, 0.05); color: #c4b5fd; border: 1px solid rgba(167, 139, 250, 0.2); padding: 6px 12px; font-size: 11px; }
#btnAdvancedFilter:hover { background: rgba(167, 139, 250, 0.15); border: 1px solid rgba(167, 139, 250, 0.3); color: #ffffff; }
#btnAdvancedFilter:checked { background: rgba(139, 92, 246, 0.2); border: 1px solid #8b5cf6; color: #ffffff; }
#btnAddSmartFolder { background: rgba(99, 102, 241, 0.2); color: #a78bfa; border: 1px solid rgba(99, 102, 241, 0.3); border-radius: 4px; padding: 0px; font-size: 14px; font-weight: bold; }
#btnAddSmartFolder:hover { background: rgba(99, 102, 241, 0.4); color: #ffffff; }
#btnAddSmartFolder:pressed { background: #4338ca; }
#btnSaveSearch { background: rgba(167, 139, 250, 0.15); color: #c4b5fd; border: 1px solid rgba(167, 139, 250, 0.3); border-radius: 6px; padding: 0px; font-size: 14px; }
#btnSaveSearch:hover { background: rgba(167, 139, 250, 0.3); color: #ffffff; }
#btnSaveSearch:pressed { background: rgba(99, 102, 241, 0.4); }
#btnPlay, #btnMute { background: rgba(167, 139, 250, 0.15); color: #c4b5fd; border: 1px solid rgba(167, 139, 250, 0.3); border-radius: 6px; padding: 0px; font-size: 14px; }
#btnPlay:hover, #btnMute:hover { background: rgba(167, 139, 250, 0.3); color: #ffffff; }
#btnPlay:pressed, #btnMute:pressed { background: rgba(99, 102, 241, 0.4); }
#btnClearVP, #btnClearIO, #btnClearAP, #btnClearFF { background: rgba(239, 68, 68, 0.15); color: #f87171; border: 1px solid rgba(239, 68, 68, 0.3); border-radius: 6px; padding: 0px; }
#btnClearVP:hover, #btnClearIO:hover, #btnClearAP:hover, #btnClearFF:hover { background: rgba(239, 68, 68, 0.3); color: #ffffff; }
#btnClearVP:pressed, #btnClearIO:pressed, #btnClearAP:pressed, #btnClearFF:pressed { background: #b91c1c; }
#appPathLabel { font-size: 13px; color: #ffffff; font-weight: 600; }
QLabel[heading="true"] { font-size: 12px; font-weight: 700; color: #a78bfa; text-transform: uppercase; letter-spacing: 1px; margin-top: 6px; }
"""

LIGHT_STYLESHEET = """
QMainWindow { background: #f8fafc; }
QWidget { color: #0f172a; font-family: 'Segoe UI', 'Inter', sans-serif; }
#sidebar { background: #ffffff; border-right: 1px solid #e2e8f0; min-width: 220px; max-width: 220px; }
#titleLabel { font-size: 20px; font-weight: 800; color: #0f172a; letter-spacing: 2px; margin-top: 10px; }
#subtitleLabel { font-size: 10px; font-weight: 700; color: #6366f1; letter-spacing: 1.5px; text-transform: uppercase; margin-top: 2px; }
#smartSidebarTitle { font-size: 11px; font-weight: 700; color: #64748b; letter-spacing: 1.5px; text-transform: uppercase; margin-left: 12px; }
#navButton { background: transparent; color: #475569; text-align: left; padding: 12px 24px; font-size: 13px; font-weight: 600; letter-spacing: 0.5px; border-radius: 8px; margin: 4px 16px; border: 1px solid transparent; }
#navButton:hover { background: #f1f5f9; color: #0f172a; border: 1px solid #cbd5e1; }
#navButton[active="true"] { background: #e0e7ff; color: #4338ca; border: 1px solid #c7d2fe; font-weight: 700; }
#controlPanel { background: #ffffff; border: 1px solid #e2e8f0; border-radius: 16px; padding: 16px 20px; }
#filterPanel { background: #f8fafc; border: 1px solid #e2e8f0; border-radius: 12px; padding: 10px 16px; margin-bottom: 8px; }
#advancedFilterPanel { background: #f8fafc; border: 1px solid #e2e8f0; border-radius: 12px; padding: 10px 16px; margin-bottom: 8px; }
#statsPanel { background: #ffffff; border: 1px solid #e2e8f0; border-left: 4px solid #6366f1; border-radius: 8px; padding: 0px; }
#statValue { font-size: 18px; font-weight: 800; color: #0f172a; }
#statLabel { font-size: 9px; color: #6366f1; text-transform: uppercase; letter-spacing: 1px; font-weight: bold; }
QPushButton { border: none; border-radius: 8px; padding: 10px 24px; font-size: 13px; font-weight: 600; letter-spacing: 0.5px; }
#btnSelectFolder { background: #6366f1; color: white; min-width: 180px; }
/* Compact padding for control-panel action buttons — the generic 24px h-padding made six-button rows overflow at minimum window width */
#btnLoadFiles, #btnStopLoading, #btnClearAll, #btnWatch, #btnViewMode, #btnTogglePreview, #btnToggleStats, #btnBatchEdit, #btnBatchTag, #btnFindDuplicates, #btnDelete, #btnProcessAll, #btnUndo, #btnRedo { padding-left: 14px; padding-right: 14px; }

#btnSelectFolder:hover { background: #4f46e5; }
#btnSelectFolder:pressed { background: #3730a3; }
#btnSelectFolder:disabled { background: #cbd5e1; color: #94a3b8; }
#btnProcessAll { background: #10b981; color: white; min-width: 130px; font-size: 14px; padding: 12px 22px; }
#btnProcessAll:hover { background: #059669; }
#btnProcessAll:pressed { background: #047857; }
#btnProcessAll:disabled { background: #e2e8f0; color: #94a3b8; }
#btnClearAll { background: #fee2e2; color: #dc2626; border: 1px solid #fecaca; min-width: 100px; }
#btnClearAll:hover { background: #fca5a5; color: #991b1b; border: 1px solid #fca5a5; }
#btnClearAll:pressed { background: #ef4444; }
#btnClearAll:disabled { background: #f1f5f9; color: #94a3b8; }
#btnLoadFiles { background: #3b82f6; color: white; min-width: 120px; }
#btnLoadFiles:hover { background: #2563eb; }
#btnLoadFiles:pressed { background: #1d4ed8; }
#btnLoadFiles:disabled { background: #cbd5e1; color: #94a3b8; }
#btnStopLoading { background: #fee2e2; color: #dc2626; border: 1px solid #fecaca; min-width: 120px; }
#btnStopLoading:hover { background: #fca5a5; color: #991b1b; }
#btnStopLoading:pressed { background: #ef4444; }
#btnStopLoading:disabled { background: #f1f5f9; color: #94a3b8; }
#btnBatchEdit { background: #f59e0b; color: white; min-width: 115px; }
#btnBatchEdit:hover { background: #d97706; }
#btnBatchEdit:pressed { background: #b45309; }
#btnBatchEdit:disabled { background: #cbd5e1; color: #94a3b8; }
#btnFindDuplicates { background: #e0f2fe; color: #0284c7; border: 1px solid #bae6fd; min-width: 105px; }
#btnFindDuplicates:hover { background: #bae6fd; color: #0369a1; border: 1px solid #7dd3fc; }
#btnFindDuplicates:pressed { background: #0284c7; }
#btnFindDuplicates:disabled { background: #f1f5f9; color: #94a3b8; border: 1px solid #cbd5e1; }
#btnViewMode, #btnTogglePreview, #btnToggleStats { background: #f1f5f9; color: #475569; border: 1px solid #cbd5e1; min-width: 100px; padding: 6px 12px; font-size: 11px; border-radius: 6px; }
#btnViewMode:hover, #btnTogglePreview:hover, #btnToggleStats:hover { background: #e2e8f0; color: #0f172a; }
#btnViewMode:pressed, #btnTogglePreview:pressed, #btnToggleStats:pressed { background: #cbd5e1; }
#btnViewMode:checked, #btnTogglePreview:checked, #btnToggleStats:checked { background: #e0e7ff; color: #4338ca; border: 1px solid #c7d2fe; }
#previewPanel { background: #ffffff; border: 1px solid #e2e8f0; border-radius: 12px; }
#btnUndo, #btnRedo { background: #f3e8ff; color: #7e22ce; border: 1px solid #e9d5ff; min-width: 100px; }
#btnUndo:hover, #btnRedo:hover { background: #e9d5ff; color: #6b21a8; border: 1px solid #d8b4fe; }
#btnUndo:pressed, #btnRedo:pressed { background: #7e22ce; }
#btnUndo:disabled, #btnRedo:disabled { background: #f1f5f9; color: #94a3b8; border: 1px solid #e2e8f0; }
#btnDelete { background: #fee2e2; color: #dc2626; border: 1px solid #fecaca; min-width: 105px; }
#btnDelete:hover { background: #fecaca; color: #991b1b; border: 1px solid #fca5a5; }
#btnDelete:pressed { background: #ef4444; }
#btnDelete:disabled { background: #f1f5f9; color: #94a3b8; border: 1px solid #e2e8f0; }
QTableWidget { background: #ffffff; border: 1px solid #e2e8f0; border-radius: 14px; gridline-color: #f1f5f9; selection-background-color: #e0e7ff; font-size: 12px; outline: none; }
QTableWidget::item { padding: 6px 10px; border-bottom: 1px solid #f1f5f9; }
QTableWidget::item:selected { background: #e0e7ff; color: #0f172a; }
QHeaderView::section { background: #f8fafc; color: #475569; font-weight: 700; font-size: 10px; text-transform: uppercase; letter-spacing: 1.5px; padding: 12px 14px; border: none; border-bottom: 2px solid #cbd5e1; border-right: 1px solid #f1f5f9; }
QScrollBar:vertical { background: transparent; width: 8px; margin: 4px 2px; }
QScrollBar::handle:vertical { background: #cbd5e1; border-radius: 4px; min-height: 30px; }
QScrollBar::handle:vertical:hover { background: #94a3b8; }
QScrollBar:horizontal { background: transparent; height: 8px; margin: 2px 4px; }
QScrollBar::handle:horizontal { background: #cbd5e1; border-radius: 4px; min-width: 30px; }
QScrollBar::handle:horizontal:hover { background: #94a3b8; }
QLineEdit { background: #ffffff; border: 1px solid #cbd5e1; border-radius: 6px; padding: 4px 8px; color: #0f172a; font-size: 12px; }
QLineEdit:focus { border: 1px solid #6366f1; }
QComboBox { background: #ffffff; border: 1px solid #cbd5e1; border-radius: 6px; padding: 4px 8px; color: #0f172a; font-size: 12px; min-width: 55px; }
#searchComboBox { background: #ffffff; border: 1px solid #cbd5e1; border-radius: 6px; }
#searchComboBox QLineEdit { background: transparent; border: none; padding: 4px 8px; color: #0f172a; font-size: 12px; }
QComboBox QAbstractItemView { background: #ffffff; border: 1px solid #cbd5e1; selection-background-color: #e0e7ff; color: #0f172a; }
QProgressBar { background: #e2e8f0; border: none; border-radius: 8px; text-align: center; color: #4338ca; font-size: 11px; font-weight: 600; height: 18px; }
QProgressBar::chunk { background: #6366f1; border-radius: 7px; }
#statusBar { background: #f8fafc; border-top: 1px solid #e2e8f0; padding: 6px 16px; font-size: 11px; color: #64748b; }
#statusLabelReady { color: #059669; } #statusLabelWarning { color: #d97706; } #statusLabelError { color: #dc2626; }
#folderPathLabel { color: #64748b; font-size: 12px; padding: 0 8px; }
QToolTip { background: #1e293b; color: #f8fafc; border: 1px solid #334155; border-radius: 6px; padding: 6px 10px; font-size: 12px; }
#thumbnailLabel { border: 1px solid #cbd5e1; border-radius: 6px; background: #f1f5f9; }
#headerBar { background: #ffffff; border-bottom: 1px solid #e2e8f0; min-height: 52px; }
#pageTitle { font-size: 18px; font-weight: 700; color: #0f172a; letter-spacing: 0.5px; }
#settingsPanel { background: #f8fafc; border-left: 1px solid #e2e8f0; }
#settingsPanel QListWidget { background: #ffffff; border: 1px solid #e2e8f0; border-radius: 8px; padding: 4px; font-size: 11px; color: #0f172a; min-height: 100px; }
#settingsPanel QListWidget::item:selected { background: #e0e7ff; color: #0f172a; }
#settingsPanel QListWidget::item:hover { background: #f1f5f9; }
#btnSettingsAdd { background: #e0e7ff; color: #4338ca; border: 1px solid #c7d2fe; border-radius: 8px; padding: 8px 8px; font-size: 12px; }
#btnSettingsAdd:hover { background: #c7d2fe; color: #3730a3; }
#btnSettingsAdd:pressed { background: #4338ca; }
#btnSettingsRemove { background: #fee2e2; color: #dc2626; border: 1px solid #fecaca; border-radius: 8px; padding: 8px 16px; font-size: 12px; }
#btnSettingsRemove:hover { background: #fca5a5; color: #b91c1c; }
#btnSettingsRemove:pressed { background: #ef4444; }
QGroupBox { background: #ffffff; border: 1px solid #e2e8f0; border-radius: 10px; margin-top: 12px; padding: 16px 10px 10px 10px; font-size: 13px; font-weight: 600; color: #334155; }
QGroupBox::title { subcontrol-origin: margin; subcontrol-position: top left; padding: 2px 10px; color: #4338ca; }
QScrollArea { background: transparent; border: none; }
/* FIX: see matching rule in DARK_STYLESHEET — prevents stale viewport
   backgrounds after theme switches */
QScrollArea > QWidget > QWidget { background: transparent; }
#btnGlobalMute, #btnSettingsToggle { background: #f1f5f9; color: #475569; border: 1px solid #cbd5e1; border-radius: 8px; padding: 0px; font-size: 16px; }
#btnGlobalMute:hover, #btnSettingsToggle:hover { background: #e2e8f0; color: #0f172a; }
#btnGlobalMute:pressed, #btnSettingsToggle:pressed { background: #cbd5e1; }
#btnHelp { background: #f1f5f9; color: #475569; border: 1px solid #cbd5e1; border-radius: 18px; padding: 0px; font-size: 16px; font-weight: bold; }
#btnHelp:hover { background: #e2e8f0; color: #0f172a; }
#btnHelp:pressed { background: #cbd5e1; }
#btnCloseSettings, #btnClosePreview { background: #fee2e2; color: #dc2626; border: 1px solid #fecaca; border-radius: 6px; padding: 0px; font-weight: bold; font-size: 12px; }
#btnCloseSettings:hover, #btnClosePreview:hover { background: #fca5a5; color: #b91c1c; }
#btnCloseSettings:pressed, #btnClosePreview:pressed { background: #ef4444; }
#btnAdvancedFilter { background: #f1f5f9; color: #64748b; border: 1px solid #cbd5e1; padding: 6px 12px; font-size: 11px; }
#btnAdvancedFilter:hover { background: #e2e8f0; border: 1px solid #94a3b8; color: #334155; }
#btnAdvancedFilter:checked { background: #e0e7ff; border: 1px solid #6366f1; color: #4338ca; }
#btnAddSmartFolder { background: #e0e7ff; color: #4338ca; border: 1px solid #c7d2fe; border-radius: 4px; padding: 0px; font-size: 14px; font-weight: bold; }
#btnAddSmartFolder:hover { background: #c7d2fe; color: #3730a3; }
#btnAddSmartFolder:pressed { background: #4338ca; }
#btnSaveSearch { background: #f1f5f9; color: #475569; border: 1px solid #cbd5e1; border-radius: 6px; padding: 0px; font-size: 14px; }
#btnSaveSearch:hover { background: #e2e8f0; color: #0f172a; }
#btnSaveSearch:pressed { background: #cbd5e1; }
#btnPlay, #btnMute { background: #f1f5f9; color: #475569; border: 1px solid #cbd5e1; border-radius: 6px; padding: 0px; font-size: 14px; }
#btnPlay:hover, #btnMute:hover { background: #e2e8f0; color: #0f172a; }
#btnPlay:pressed, #btnMute:pressed { background: #cbd5e1; }
#btnClearVP, #btnClearIO, #btnClearAP, #btnClearFF { background: #fee2e2; color: #dc2626; border: 1px solid #fecaca; border-radius: 6px; padding: 0px; }
#btnClearVP:hover, #btnClearIO:hover, #btnClearAP:hover, #btnClearFF:hover { background: #fca5a5; color: #b91c1c; }
#btnClearVP:pressed, #btnClearIO:pressed, #btnClearAP:pressed, #btnClearFF:pressed { background: #ef4444; }
#appPathLabel { font-size: 13px; color: #0f172a; font-weight: 600; }
QLabel[heading="true"] { font-size: 12px; font-weight: 700; color: #4338ca; text-transform: uppercase; letter-spacing: 1px; margin-top: 6px; }
"""

def scale_stylesheet(css: str, scale: float) -> str:
    """Scale every explicit font-size in a stylesheet.

    Qt px-based stylesheet rules ignore QApplication.setFont(), so the UI-size
    setting must rewrite them. Keeps at least 8px for legibility.
    """
    if not scale or scale == 1.0:
        return css
    return re.sub(r'font-size:\s*(\d+(?:\.\d+)?)px',
                  lambda m: f"font-size: {max(8, round(float(m.group(1)) * scale))}px",
                  css)

def _scale_stylesheet(css: str, scale: float) -> str:  # legacy alias
    return scale_stylesheet(css, scale)

class ThemeManager:
    @staticmethod
    def get_system_theme():
        try:
            scheme = QGuiApplication.styleHints().colorScheme()
            if scheme == Qt.ColorScheme.Dark: return "dark"
            elif scheme == Qt.ColorScheme.Light: return "light"
        except AttributeError:
            pass
        app = QApplication.instance()
        if app:
            palette = app.palette()
            window_color = palette.color(QPalette.ColorRole.Window)
            if window_color.lightness() < 128: return "dark"
        return "light"

    @staticmethod
    def apply_theme(window, theme_choice, ui_scale=None):
        app = QApplication.instance()
        if theme_choice == "System (Auto)":
            actual_theme = ThemeManager.get_system_theme()
        else:
            actual_theme = "dark" if "Dark" in theme_choice else "light"

        window.current_theme = actual_theme
        is_dark = (actual_theme == "dark")
        scale = ui_scale if ui_scale is not None else float(getattr(window, 'ui_scale', 1.0) or 1.0)

        app.setStyleSheet(scale_stylesheet(DARK_STYLESHEET if is_dark else LIGHT_STYLESHEET, scale))
        
        palette = QPalette()
        if is_dark:
            palette.setColor(QPalette.ColorRole.Window, QColor("#0f0c29"))
            palette.setColor(QPalette.ColorRole.WindowText, QColor("#e0e0e0"))
            palette.setColor(QPalette.ColorRole.Base, QColor("#0f0c29"))
            palette.setColor(QPalette.ColorRole.AlternateBase, QColor("#1e1b4b"))
            palette.setColor(QPalette.ColorRole.ToolTipBase, QColor("#1e1b4b"))
            palette.setColor(QPalette.ColorRole.ToolTipText, QColor("#e0e0e0"))
            palette.setColor(QPalette.ColorRole.Text, QColor("#e0e0e0"))
            palette.setColor(QPalette.ColorRole.Button, QColor("#1e1b4b"))
            palette.setColor(QPalette.ColorRole.ButtonText, QColor("#e0e0e0"))
            palette.setColor(QPalette.ColorRole.BrightText, QColor("#a78bfa"))
            palette.setColor(QPalette.ColorRole.Highlight, QColor("#6366f1"))
            palette.setColor(QPalette.ColorRole.HighlightedText, QColor("#ffffff"))
            palette.setColor(QPalette.ColorRole.Link, QColor("#6dd5ed"))
        else:
            palette.setColor(QPalette.ColorRole.Window, QColor("#f8fafc"))
            palette.setColor(QPalette.ColorRole.WindowText, QColor("#0f172a"))
            palette.setColor(QPalette.ColorRole.Base, QColor("#ffffff"))
            palette.setColor(QPalette.ColorRole.AlternateBase, QColor("#f1f5f9"))
            palette.setColor(QPalette.ColorRole.ToolTipBase, QColor("#ffffff"))
            palette.setColor(QPalette.ColorRole.ToolTipText, QColor("#0f172a"))
            palette.setColor(QPalette.ColorRole.Text, QColor("#0f172a"))
            palette.setColor(QPalette.ColorRole.Button, QColor("#ffffff"))
            palette.setColor(QPalette.ColorRole.ButtonText, QColor("#0f172a"))
            palette.setColor(QPalette.ColorRole.BrightText, QColor("#dc2626"))
            palette.setColor(QPalette.ColorRole.Highlight, QColor("#6366f1"))
            palette.setColor(QPalette.ColorRole.HighlightedText, QColor("#ffffff"))
            palette.setColor(QPalette.ColorRole.Link, QColor("#2563eb"))
        app.setPalette(palette)
        
        # Regenerate Vector Icons dynamically to match theme colors:
        if hasattr(window, 'btn_nav_videos') and window.btn_nav_videos:
            window.btn_nav_videos.setIcon(get_vector_icon('video', is_dark))
        if hasattr(window, 'btn_nav_images') and window.btn_nav_images:
            window.btn_nav_images.setIcon(get_vector_icon('image', is_dark))
        if hasattr(window, 'btn_nav_audio') and window.btn_nav_audio:
            window.btn_nav_audio.setIcon(get_vector_icon('audio', is_dark))
        if hasattr(window, 'btn_nav_pdfs') and window.btn_nav_pdfs:
            window.btn_nav_pdfs.setIcon(get_vector_icon('pdf', is_dark))
        if hasattr(window, 'btn_add_smart') and window.btn_add_smart:
            window.btn_add_smart.setIcon(get_vector_icon('plus', is_dark))
        if hasattr(window, 'btn_global_mute') and window.btn_global_mute:
            window.btn_global_mute.setIcon(get_vector_icon('mute' if window.global_mute else 'unmute', is_dark))
        if hasattr(window, 'btn_settings') and window.btn_settings:
            window.btn_settings.setIcon(get_vector_icon('settings', is_dark))
            
        tabs = []
        if hasattr(window, 'video_tab') and window.video_tab: tabs.append(window.video_tab)
        if hasattr(window, 'image_tab') and window.image_tab: tabs.append(window.image_tab)
        if hasattr(window, 'audio_tab') and window.audio_tab: tabs.append(window.audio_tab)
        if hasattr(window, 'pdf_tab') and window.pdf_tab: tabs.append(window.pdf_tab)
        if hasattr(window, 'smart_folder_tabs') and window.smart_folder_tabs:
            tabs.extend(window.smart_folder_tabs.values())
            
        for tab in tabs:
            if hasattr(tab, 'btn_load') and tab.btn_load:
                tab.btn_load.setIcon(get_vector_icon('sync', is_dark))
            if hasattr(tab, 'btn_stop') and tab.btn_stop:
                tab.btn_stop.setIcon(get_vector_icon('stop', is_dark))
            if hasattr(tab, 'btn_clear') and tab.btn_clear:
                tab.btn_clear.setIcon(get_vector_icon('clear', is_dark))
            if hasattr(tab, 'btn_view_mode') and tab.btn_view_mode:
                tab.btn_view_mode.setIcon(get_vector_icon('list' if tab.btn_view_mode.isChecked() else 'grid', is_dark))
            if hasattr(tab, 'btn_toggle_preview') and tab.btn_toggle_preview:
                tab.btn_toggle_preview.setIcon(get_vector_icon('preview', is_dark))
            if hasattr(tab, 'btn_undo') and tab.btn_undo:
                tab.btn_undo.setIcon(get_vector_icon('undo', is_dark))
            if hasattr(tab, 'btn_redo') and tab.btn_redo:
                tab.btn_redo.setIcon(get_vector_icon('redo', is_dark))
            if hasattr(tab, 'btn_find_dupes') and tab.btn_find_dupes:
                tab.btn_find_dupes.setIcon(get_vector_icon('search', is_dark))
            if hasattr(tab, 'btn_batch_edit') and tab.btn_batch_edit:
                tab.btn_batch_edit.setIcon(get_vector_icon('edit', is_dark))
            if hasattr(tab, 'btn_relocate') and tab.btn_relocate:
                tab.btn_relocate.setIcon(get_vector_icon('relocate', is_dark))
            if hasattr(tab, 'btn_delete') and tab.btn_delete:
                tab.btn_delete.setIcon(get_vector_icon('delete', is_dark))
            if hasattr(tab, 'btn_process') and tab.btn_process:
                tab.btn_process.setIcon(get_vector_icon('process', is_dark))
            if hasattr(tab, 'btn_save_search') and tab.btn_save_search:
                tab.btn_save_search.setIcon(get_vector_icon('save', is_dark))
            if hasattr(tab, 'btn_play') and tab.btn_play:
                tab.btn_play.setIcon(get_vector_icon('pause' if tab.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState else 'play', is_dark))
            if hasattr(tab, 'btn_mute') and tab.btn_mute:
                tab.btn_mute.setIcon(get_vector_icon('mute' if tab.audio_output.isMuted() else 'unmute', is_dark))
            if hasattr(tab, 'btn_close_preview') and tab.btn_close_preview:
                tab.btn_close_preview.setIcon(get_vector_icon('close', is_dark))
                
        if hasattr(window, 'btn_close_settings') and window.btn_close_settings:
            window.btn_close_settings.setIcon(get_vector_icon('close', is_dark))
            
        for btn_attr, icon_name in [('btn_browse_vp', 'folder'), ('btn_clear_vp', 'clear'),
                                   ('btn_browse_io', 'folder'), ('btn_clear_io', 'clear'),
                                   ('btn_browse_ap', 'folder'), ('btn_clear_ap', 'clear'),
                                   ('btn_browse_po', 'folder'), ('btn_clear_po', 'clear'),
                                   ('btn_browse_ff', 'folder'), ('btn_clear_ff', 'clear'),
                                   ('btn_add_video_folder', 'plus'), ('btn_remove_video_folder', 'delete'),
                                   ('btn_add_image_folder', 'plus'), ('btn_remove_image_folder', 'delete'),
                                   ('btn_add_audio_folder', 'plus'), ('btn_remove_audio_folder', 'delete'),
                                   ('btn_add_pdf_folder', 'plus'), ('btn_remove_pdf_folder', 'delete')]:
            if hasattr(window, btn_attr):
                btn = getattr(window, btn_attr)
                if btn: btn.setIcon(get_vector_icon(icon_name, is_dark))
        
        ThemeManager._update_inline_styles(window, is_dark)
        if hasattr(window, 'hover_overlay') and window.hover_overlay:
            window.hover_overlay.update_theme()
        
        window.ensurePolished()
        # NOTE: Removed the O(all-widgets) unpolish/polish loop — setStyleSheet
        # above already triggers a style refresh on every widget. The global
        # loop caused UI freezes of 0.3-2s on populated windows and could
        # re-enter apply_theme via processEvents().
        # Also removed app.processEvents() for the same re-entrancy reason.

    @staticmethod
    def _update_inline_styles(window, is_dark):
        grid_style = """
            QListWidget { background: rgba(15, 12, 41, 0.5); border: 1px solid rgba(167, 139, 250, 0.15); border-radius: 12px; padding: 12px; color: #e0e0e0; }
            QListWidget::item { background: rgba(30, 27, 75, 0.4); border: 1px solid rgba(167, 139, 250, 0.1); border-radius: 8px; padding: 8px; margin: 4px; }
            QListWidget::item:hover { background: rgba(99, 102, 241, 0.15); border: 1px solid rgba(99, 102, 241, 0.3); }
            QListWidget::item:selected { background: rgba(99, 102, 241, 0.35); border: 1px solid rgba(99, 102, 241, 0.6); color: #ffffff; }
        """ if is_dark else """
            QListWidget { background: #ffffff; border: 1px solid #e2e8f0; border-radius: 12px; padding: 12px; color: #0f172a; }
            QListWidget::item { background: #f8fafc; border: 1px solid #e2e8f0; border-radius: 8px; padding: 8px; margin: 4px; }
            QListWidget::item:hover { background: #f1f5f9; border: 1px solid #cbd5e1; }
            QListWidget::item:selected { background: #e0e7ff; border: 1px solid #c7d2fe; color: #0f172a; }
        """
        
        menu_style = """
            QMenu { background-color: #1e1b4b; color: #e0e0e0; border: 1px solid rgba(99, 102, 241, 0.4); border-radius: 8px; padding: 4px; }
            QMenu::item { padding: 6px 20px; border-radius: 4px; }
            QMenu::item:selected { background-color: rgba(99, 102, 241, 0.4); color: #ffffff; }
        """ if is_dark else """
            QMenu { background-color: #ffffff; color: #0f172a; border: 1px solid #e2e8f0; border-radius: 8px; padding: 4px; }
            QMenu::item { padding: 6px 20px; border-radius: 4px; }
            QMenu::item:selected { background-color: #e0e7ff; color: #0f172a; }
        """

        tabs = [window.video_tab, window.image_tab, window.audio_tab, window.pdf_tab] + list(getattr(window, 'smart_folder_tabs', {}).values())
        for tab in tabs:
            if hasattr(tab, 'grid_view'): tab.grid_view.setStyleSheet(grid_style)
            if hasattr(tab, 'dupe_menu'): tab.dupe_menu.setStyleSheet(menu_style)
            if hasattr(tab, 'header_menu'): tab.header_menu.setStyleSheet(menu_style)
            if hasattr(tab, 'table'):
                for row in range(tab.table.rowCount()):
                    rating_widget = tab.table.cellWidget(row, tab.COL_RATING)
                    if isinstance(rating_widget, QComboBox):
                        tab._style_rating_combo(rating_widget, rating_widget.currentText())
                if hasattr(tab, '_update_row_colors'):
                    tab._update_row_colors()
            
        for nav_item in getattr(window, 'smart_folder_nav_items', {}).values():
            nav_item.update_theme(is_dark)

# ─── Media Metadata Extraction ──────────────────────────────────────────────────

class MediaInfo:
    def __init__(self, filepath: str, media_type: str = 'video', cached_data: dict = None):
        self.filepath = filepath
        self.filename = os.path.basename(filepath)
        self.extension = os.path.splitext(filepath)[1].lower()
        self.media_type = media_type
        if media_type == 'all':
            if self.extension in VIDEO_EXTENSIONS: self.media_type = 'video'
            elif self.extension in AUDIO_EXTENSIONS: self.media_type = 'audio'
            elif self.extension in PDF_EXTENSIONS: self.media_type = 'pdf'
            else: self.media_type = 'image'
        if cached_data:
            self.width = cached_data.get('width', 0)
            self.height = cached_data.get('height', 0)
            self.duration_seconds = cached_data.get('duration_seconds', 0.0)
            self.duration_formatted = cached_data.get('duration_formatted', "")
            self.resolution_tag = cached_data.get('resolution_tag', "")
            self.duration_compact = cached_data.get('duration_compact', "")
            self.is_valid = cached_data.get('is_valid', False)
            self.error_message = cached_data.get('error_message', "")
            self.size_bytes = cached_data.get('size_bytes', 0)
            self.size_formatted = cached_data.get('size_formatted', "—")
            self.tags = cached_data.get('tags', [])
            self.mtime = float(cached_data.get('mtime', 0) or 0)
            self.ctime = float(cached_data.get('ctime', 0) or 0)
            # Backfill for old caches that never stored ctime
            if self.ctime == 0.0:
                try:
                    self.ctime = float(os.stat(filepath).st_ctime)
                except OSError:
                    pass
        else:
            self.width = 0
            self.height = 0
            self.duration_seconds = 0.0
            self.duration_formatted = ""
            self.resolution_tag = ""
            self.duration_compact = ""
            self.is_valid = False
            self.error_message = ""
            self.size_bytes = 0
            self.size_formatted = "—"
            self.tags = []
            self.mtime = 0.0
            self.ctime = 0.0
            try:
                if os.path.exists(filepath):
                    st_ = os.stat(filepath)
                    self.mtime = float(st_.st_mtime)
                    self.ctime = float(getattr(st_, 'st_ctime', 0))
                    self.size_bytes = st_.st_size
                    if self.size_bytes >= 1024**3: self.size_formatted = f"{self.size_bytes / (1024**3):.2f} GB"
                    elif self.size_bytes >= 1024**2: self.size_formatted = f"{self.size_bytes / (1024**2):.1f} MB"
                    elif self.size_bytes >= 1024: self.size_formatted = f"{self.size_bytes / 1024:.0f} KB"
                    else: self.size_formatted = f"{self.size_bytes} B"
            except Exception: pass
            self._extract_metadata()

    def _extract_metadata(self):
        try:
            if self.media_type == 'video':
                cap = None
                try:
                    with _CV_LOCK:
                        cap = cv2.VideoCapture(self.filepath)
                        if not cap.isOpened():
                            self.error_message = "Cannot open video file"; return
                        self.width = int(cap.get(cv2.CAP_PROP_FRAME_WIDTH))
                        self.height = int(cap.get(cv2.CAP_PROP_FRAME_HEIGHT))
                        fps = cap.get(cv2.CAP_PROP_FPS)
                        frame_count = cap.get(cv2.CAP_PROP_FRAME_COUNT)
                        if fps > 0 and frame_count > 0:
                            self.duration_seconds = frame_count / fps
                        else:
                            # Duration unknown — but width/height may still be valid
                            self.error_message = "Cannot determine duration"
                            self.is_valid = (self.width > 0 and self.height > 0)
                            if self.is_valid:
                                self.resolution_tag = get_resolution_tag(self.width, self.height)
                            return
                finally:
                    if cap is not None:
                        cap.release()
                self.duration_compact = format_duration_compact(self.duration_seconds)
                total_sec = int(round(self.duration_seconds))
                h = total_sec // 3600; m = (total_sec % 3600) // 60; s = total_sec % 60
                if h > 0: self.duration_formatted = f"{h}h {m:02d}m {s:02d}s"
                else: self.duration_formatted = f"{m}m {s:02d}s"
            elif self.media_type == 'audio':
                self.width = 0; self.height = 0; self.resolution_tag = ""
                cap = None
                duration_ok = False
                try:
                    with _CV_LOCK:
                        cap = cv2.VideoCapture(self.filepath)
                        if cap.isOpened():
                            fps = cap.get(cv2.CAP_PROP_FPS)
                            frame_count = cap.get(cv2.CAP_PROP_FRAME_COUNT)
                            if fps > 0 and frame_count > 0:
                                self.duration_seconds = frame_count / fps; duration_ok = True
                finally:
                    if cap is not None:
                        cap.release()
                if not duration_ok and self.extension == '.wav':
                    try:
                        import wave
                        with wave.open(self.filepath, 'rb') as f:
                            frames = f.getnframes(); rate = f.getframerate()
                            if rate > 0: self.duration_seconds = frames / float(rate); duration_ok = True
                    except Exception: pass
                # Try ffprobe for audio duration (more accurate than file-size heuristics)
                if not duration_ok:
                    try:
                        deep = get_file_deep_metadata(self.filepath)
                        if deep and deep.get('duration_seconds', 0) > 0:
                            self.duration_seconds = deep['duration_seconds']; duration_ok = True
                    except Exception: pass
                # Try mutagen for MP3/FLAC/OGG/M4A as a fallback
                if not duration_ok:
                    try:
                        import mutagen
                        mfile = mutagen.File(self.filepath, easy=True)
                        if mfile is not None and hasattr(mfile, 'info') and getattr(mfile.info, 'length', 0) > 0:
                            self.duration_seconds = float(mfile.info.length); duration_ok = True
                    except ImportError:
                        pass  # mutagen not installed
                    except Exception:
                        pass
                if not duration_ok:
                    # Do NOT fabricate a duration from file size — that produces wildly
                    # wrong numbers (the old code assumed a 24 kbps constant bitrate).
                    self.error_message = "Cannot determine audio duration (install mutagen or ffprobe for accurate duration)"
                    return
                self.duration_compact = format_duration_compact(self.duration_seconds)
                total_sec = int(round(self.duration_seconds))
                h = total_sec // 3600; m = (total_sec % 3600) // 60; s = total_sec % 60
                if h > 0: self.duration_formatted = f"{h}h {m:02d}m {s:02d}s"
                else: self.duration_formatted = f"{m}m {s:02d}s"
            elif self.media_type == 'pdf':
                self.width = 0; self.height = 0; self.resolution_tag = ""
                self.duration_seconds = 0.0; self.duration_compact = ""; self.duration_formatted = "—"
            else:
                reader = QImageReader(self.filepath)
                if not reader.canRead():
                    self.error_message = "Cannot open image file"
                    return
                sz = reader.size()
                if not sz.isValid() or sz.width() <= 0 or sz.height() <= 0:
                    with _CV_LOCK:
                        img = cv2.imdecode(np.fromfile(self.filepath, dtype=np.uint8), cv2.IMREAD_COLOR)
                    if img is None:
                        self.error_message = "Cannot open image file"
                        return
                    self.height, self.width = img.shape[:2]
                else:
                    self.width = sz.width()
                    self.height = sz.height()
                self.duration_seconds = 0.0; self.duration_compact = ""; self.duration_formatted = "—"
            if self.media_type not in ['audio', 'pdf']: self.resolution_tag = get_resolution_tag(self.width, self.height)
            else: self.resolution_tag = ""
            self.is_valid = True
        except Exception as e:
            self.error_message = str(e)
            logger.warning("metadata extraction failed for %s: %s", self.filepath, e)

class ScannerThread(QThread):
    progress = pyqtSignal(int, int)
    file_found = pyqtSignal(object)
    scan_complete = pyqtSignal(int)
    status_update = pyqtSignal(str)

    def __init__(self, directories: list[str], media_type: str, exclude_patterns: list[str] = None, force_full: bool = False):
        super().__init__()
        self.directories = directories
        self.media_type = media_type
        self.exclude_patterns = exclude_patterns or []
        self.force_full = force_full

    def _should_exclude(self, filepath: str) -> bool:
        filename = os.path.basename(filepath).lower()
        for pattern in self.exclude_patterns:
            pattern = pattern.lower().strip()
            if not pattern: continue
            if pattern.startswith('*') and pattern.endswith('*'):
                if pattern[1:-1] in filename: return True
            elif pattern.startswith('*'):
                if filename.endswith(pattern[1:]): return True
            elif pattern.endswith('*'):
                if filename.startswith(pattern[:-1]): return True
            elif pattern in filename: return True
        return False

    @staticmethod
    def _process_scan_item(item, cache, force_full, media_type):
        """Decide cached-vs-fresh for one scanned file.

        Returns (MediaInfo, entry_data|None): entry_data None means the cache
        was used. Size must match exactly AND mtime within tolerance (JSON
        round-trips lose ns precision); any mismatch re-extracts fresh.
        """
        vpath, size, mtime = item
        cached_entry = cache.get(vpath)
        use_cache = (
            not force_full
            and cached_entry is not None
            and cached_entry.get('size') == size
            # mtime tolerance: JSON round-trips may lose ns precision vs stat;
            # a real modification falls through to fresh extraction below.
            and abs(float(cached_entry.get('mtime', -1) or -1) - float(mtime)) < 0.001
        )
        if use_cache:
            info = MediaInfo(vpath, media_type, cached_data=cached_entry)
            return info, None

        info = MediaInfo(vpath, media_type)
        entry_data = {
            'size': size,
            'mtime': mtime,
            'ctime': float(getattr(info, 'ctime', 0) or 0),
            'width': info.width,
            'height': info.height,
            'duration_seconds': info.duration_seconds,
            'duration_formatted': info.duration_formatted,
            'resolution_tag': info.resolution_tag,
            'duration_compact': info.duration_compact,
            'is_valid': info.is_valid,
            'error_message': info.error_message,
            'size_bytes': info.size_bytes,
            'size_formatted': info.size_formatted
        }
        return info, entry_data

    def run(self):
        paths_with_stats = []
        self.status_update.emit("Scanning directories…")
        if self.media_type == 'video': valid_exts = VIDEO_EXTENSIONS
        elif self.media_type == 'audio': valid_exts = AUDIO_EXTENSIONS
        elif self.media_type == 'image': valid_exts = IMAGE_EXTENSIONS
        elif self.media_type == 'pdf': valid_exts = PDF_EXTENSIONS
        else: valid_exts = VIDEO_EXTENSIONS | AUDIO_EXTENSIONS | IMAGE_EXTENSIONS | PDF_EXTENSIONS
        
        seen_paths = set()
        for directory in self.directories:
            if not os.path.isdir(directory): continue
            stack = [directory]
            while stack:
                if self.isInterruptionRequested(): self.scan_complete.emit(0); return
                current_dir = stack.pop()
                try:
                    for entry in os.scandir(current_dir):
                        if self.isInterruptionRequested(): self.scan_complete.emit(0); return
                        if entry.is_dir(follow_symlinks=False):
                            stack.append(entry.path)
                        elif entry.is_file(follow_symlinks=False):
                            ext = os.path.splitext(entry.name)[1].lower()
                            # Include files without extensions as requested
                            if ext in valid_exts or ext == '':
                                full_path = os.path.normpath(entry.path)
                                if full_path not in seen_paths:
                                    if not self._should_exclude(full_path):
                                        try:
                                            st = entry.stat(follow_symlinks=False)
                                            paths_with_stats.append((full_path, st.st_size, st.st_mtime))
                                            seen_paths.add(full_path)
                                        except Exception as e:
                                            logger.warning("stat failed for %s: %s", full_path, e)
                except Exception as e:
                    logger.warning("scandir failed for %s: %s", current_dir, e)

        total = len(paths_with_stats)
        self.status_update.emit(f"Found {total} files. Reading metadata…")

        cache_path = os.path.join(CONFIG_DIR, 'scan_cache.json')
        cache = {}
        try:
            if os.path.exists(cache_path):
                with open(cache_path, 'r', encoding='utf-8') as f:
                    cache = json.load(f)
        except Exception:
            pass

        new_entries = {}
        from concurrent.futures import ThreadPoolExecutor, as_completed

        # Use a safe worker pool for CPU/IO operations
        num_workers = min(8, os.cpu_count() or 4)
        with ThreadPoolExecutor(max_workers=num_workers) as executor:
            futures = {executor.submit(self._process_scan_item, item, cache, self.force_full, self.media_type): idx for idx, item in enumerate(paths_with_stats)}
            for idx, future in enumerate(as_completed(futures)):
                if self.isInterruptionRequested():
                    executor.shutdown(wait=False, cancel_futures=True)
                    if new_entries:
                        update_metadata_cache(new_entries)
                    # Emit count of files actually processed (idx + 1), not 0-based idx
                    self.scan_complete.emit(idx + 1)
                    return
                try:
                    info, entry_data = future.result()
                    if entry_data:
                        new_entries[info.filepath] = entry_data
                    self.file_found.emit(info)
                    self.progress.emit(idx + 1, total)
                except Exception as e:
                    # Don't silently swallow per-file errors — log them so users
                    # can diagnose codec/path/permission issues.
                    failed_path = paths_with_stats[futures[future]][0] if futures[future] < len(paths_with_stats) else '<unknown>'
                    logger.warning("Failed to process %s: %s", failed_path, e)
                    self.status_update.emit(f"Skipped: {os.path.basename(failed_path)} ({e})")

        # O(N×M) -> O(N) cache cleanup using normalized directory prefixes
        norm_dirs = [os.path.normpath(d).rstrip(os.sep) + os.sep for d in self.directories]
        deleted_paths = []
        for cached_path in cache:
            cached_norm = os.path.normpath(cached_path) + os.sep if not cached_path.endswith(os.sep) else cached_path
            is_under_scanned = any(cached_norm.startswith(nd) for nd in norm_dirs)
            if is_under_scanned and cached_path not in seen_paths:
                deleted_paths.append(cached_path)

        if new_entries or deleted_paths:
            update_metadata_cache(new_entries, deleted_paths)

        self.scan_complete.emit(total)

# ─── Dialogs ────────────────────────────────────────────────────────────────────

class AboutDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("About MediaFlow")
        self.setMinimumSize(600, 500)
        self._build_ui()

    def _build_ui(self):
        layout = QVBoxLayout(self)
        layout.setContentsMargins(24, 24, 24, 24)
        layout.setSpacing(16)
        
        # Logo + Title Header
        header = QHBoxLayout()
        logo_label = QLabel()
        logo_pix = QPixmap(get_resource_path("logo.png"))
        if not logo_pix.isNull():
            logo_label.setPixmap(logo_pix.scaled(64, 64, Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation))
        header.addWidget(logo_label)
        
        title_layout = QVBoxLayout()
        title_layout.setSpacing(2)
        title_lbl = QLabel("MediaFlow")
        title_lbl.setStyleSheet("font-size: 24px; font-weight: 700; color: #a78bfa;")
        subtitle_lbl = QLabel("Multimedia Manager & Renamer")
        subtitle_lbl.setStyleSheet("font-size: 13px; color: #9ca3af;")
        title_layout.addWidget(title_lbl)
        title_layout.addWidget(subtitle_lbl)
        header.addLayout(title_layout)
        header.addStretch()
        layout.addLayout(header)
        
        # Detailed Information scroll area
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setStyleSheet("QScrollArea { border: none; background: transparent; }")
        
        content = QWidget()
        content_layout = QVBoxLayout(content)
        content_layout.setContentsMargins(0, 0, 0, 0)
        content_layout.setSpacing(16)
        
        # About text block
        about_lbl = QLabel(
            "<b>MediaFlow</b> is a premium desktop utility designed to organize and rename your video, "
            "image, and audio libraries using dynamic, custom-defined naming templates. It provides "
            "real-time previews, instant directory scanning with an optimized metadata cache, "
            "a native player, and advanced multithreaded operations."
        )
        about_lbl.setWordWrap(True)
        about_lbl.setStyleSheet("font-size: 13px; line-height: 1.5; color: #e0e0e0;")
        content_layout.addWidget(about_lbl)
        
        # Divider line
        divider = QFrame()
        divider.setFrameShape(QFrame.Shape.HLine)
        divider.setFrameShadow(QFrame.Shadow.Sunken)
        divider.setStyleSheet("background-color: rgba(167, 139, 250, 0.15); height: 1px; border: none;")
        content_layout.addWidget(divider)
        
        # Media Decoding Warning Box
        codec_group = QGroupBox("⚠️  Media Decoding & Codec Support Warning")
        codec_group.setStyleSheet(
            "QGroupBox { background: rgba(239, 68, 68, 0.08); border: 1px solid rgba(239, 68, 68, 0.25); "
            "border-radius: 8px; font-weight: 700; color: #f87171; padding: 12px; margin-top: 10px; }"
        )
        codec_layout = QVBoxLayout(codec_group)
        codec_layout.setSpacing(8)
        
        explanation_lbl = QLabel(
            "MediaFlow uses the native PyQt6 QMediaPlayer which relies on the OS's system media backend "
            "(Windows Media Foundation / WMF) to decode files.<br><br>"
            "If a video is compressed with a codec that is not natively supported or licensed on your Windows machine by default "
            "(such as HEVC/H.265, VP9, or AV1), the Windows media pipeline can decode the audio track but cannot decode "
            "the video stream, resulting in a <b>black screen with audio playing</b>."
        )
        explanation_lbl.setWordWrap(True)
        explanation_lbl.setStyleSheet("font-size: 12.5px; line-height: 1.4; color: #e5e7eb; font-weight: normal;")
        codec_layout.addWidget(explanation_lbl)
        
        resolution_lbl = QLabel(
            "<b>How to resolve this:</b><br><br>"
            "1. <b>Install Codecs:</b> Install a free codec pack (like the K-Lite Codec Pack) or the official HEVC Video Extensions "
            "from the Microsoft Store. This will register the video decoder on your system, allowing QMediaPlayer to play them natively.<br><br>"
            "2. <b>Change Default Player in Settings:</b> In MediaFlow settings under 'Default Applications', click Browse next to "
            "Video Player to use a powerful player like VLC or MPC-HC as your default player instead of the native system player. "
            "These players package their own codecs and can decode all formats out-of-the-box."
        )
        resolution_lbl.setWordWrap(True)
        resolution_lbl.setStyleSheet("font-size: 12.5px; line-height: 1.4; color: #e5e7eb; font-weight: normal;")
        codec_layout.addWidget(resolution_lbl)
        
        content_layout.addWidget(codec_group)
        
        # FFprobe Metadata Configuration Box
        ff_group = QGroupBox("🔍  Deep Metadata & FFprobe Requirement")
        ff_group.setStyleSheet(
            "QGroupBox { background: rgba(167, 139, 250, 0.05); border: 1px solid rgba(167, 139, 250, 0.2); "
            "border-radius: 8px; font-weight: 700; color: #a78bfa; padding: 12px; margin-top: 10px; }"
        )
        ff_layout = QVBoxLayout(ff_group)
        ff_layout.setSpacing(8)
        
        ff_explanation_lbl = QLabel(
            "To view advanced, deep metadata details for files (such as codecs, audio tracks, bitrates, format specifications, "
            "and subtitle streams) using the <b>Detailed Info</b> right-click option, <b>FFprobe</b> (part of the FFmpeg suite) "
            "must be installed on your system."
        )
        ff_explanation_lbl.setWordWrap(True)
        ff_explanation_lbl.setStyleSheet("font-size: 12.5px; line-height: 1.4; color: #e5e7eb; font-weight: normal;")
        ff_layout.addWidget(ff_explanation_lbl)
        
        ff_config_lbl = QLabel(
            "<b>How to install and configure FFprobe:</b><br><br>"
            "1. <b>Download FFmpeg/FFprobe:</b> Download the FFmpeg package from the official website (ffmpeg.org) or install it via your package manager (e.g. run <code>winget install Gnu.FFmpeg</code> in Windows Terminal).<br><br>"
            "2. <b>Add to System PATH:</b> Extract the files and add the bin folder to your Windows System Environment Variables (PATH) to let MediaFlow detect it automatically.<br><br>"
            "3. <b>Configure Custom Path in Settings:</b> Alternatively, open MediaFlow settings, scroll to the 'Deep Metadata (FFprobe)' section, and click Browse to select your <code>ffprobe.exe</code> binary manually."
        )
        ff_config_lbl.setWordWrap(True)
        ff_config_lbl.setStyleSheet("font-size: 12.5px; line-height: 1.4; color: #e5e7eb; font-weight: normal;")
        ff_layout.addWidget(ff_config_lbl)
        
        content_layout.addWidget(ff_group)
        content_layout.addStretch()
        
        scroll.setWidget(content)
        layout.addWidget(scroll, 1)
        
        # Close Button
        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Close)
        buttons.rejected.connect(self.reject)
        buttons.setStyleSheet(
            "QPushButton { background: rgba(99, 102, 241, 0.2); color: #c4b5fd; border: 1px solid rgba(99, 102, 241, 0.4); "
            "border-radius: 6px; padding: 6px 14px; font-weight: 600; min-width: 80px; }"
            "QPushButton:hover { background: rgba(99, 102, 241, 0.35); color: #ffffff; }"
            "QPushButton:pressed { background: #4338ca; }"
        )
        layout.addWidget(buttons)

class ConfigureOpenWithDialog(QDialog):
    def __init__(self, apps_list: list, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Configure 'Open With' Applications")
        self.setMinimumWidth(500)
        self.setMinimumHeight(400)
        self.apps = list(apps_list)
        self._build_ui()

    def _build_ui(self):
        layout = QVBoxLayout(self)
        layout.setSpacing(12)
        layout.setContentsMargins(20, 20, 20, 20)
        
        lbl = QLabel("Manage custom applications for the 'Open with...' right-click menu:")
        lbl.setStyleSheet("font-weight: 600; color: #a78bfa;")
        layout.addWidget(lbl)
        
        self.table = QTableWidget()
        self.table.setColumnCount(2)
        self.table.setHorizontalHeaderLabels(["Name", "Executable Path"])
        self.table.horizontalHeader().setSectionResizeMode(0, QHeaderView.ResizeMode.Interactive)
        self.table.horizontalHeader().setSectionResizeMode(1, QHeaderView.ResizeMode.Stretch)
        self.table.setColumnWidth(0, 150)
        self.table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.table.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.table.setAlternatingRowColors(False)
        self.table.setShowGrid(False)
        layout.addWidget(self.table)
        
        self._populate_table()
        
        btn_layout = QHBoxLayout()
        self.btn_add = QPushButton("Add Application...")
        self.btn_add.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_add.clicked.connect(self._on_add)
        self.btn_remove = QPushButton("Remove Selected")
        self.btn_remove.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_remove.clicked.connect(self._on_remove)
        btn_layout.addWidget(self.btn_add)
        btn_layout.addWidget(self.btn_remove)
        btn_layout.addStretch()
        layout.addLayout(btn_layout)
        
        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        layout.addWidget(buttons)

    def _populate_table(self):
        self.table.setRowCount(len(self.apps))
        for idx, app in enumerate(self.apps):
            self.table.setItem(idx, 0, QTableWidgetItem(app.get('name', '')))
            self.table.setItem(idx, 1, QTableWidgetItem(app.get('path', '')))

    def _on_add(self):
        # Cross-platform start dir & filter (was Windows-only hardcoded)
        if sys.platform == "win32":
            start_dir = "C:\\Program Files"
            file_filter = "Executable Files (*.exe)"
        elif sys.platform == "darwin":
            start_dir = "/Applications"
            file_filter = "Applications (*.app);;All Files (*)"
        else:
            start_dir = os.path.expanduser("~")
            file_filter = "All Files (*)"
        file_path, _ = QFileDialog.getOpenFileName(
            self,
            "Select Application Executable",
            start_dir,
            file_filter
        )
        if not file_path:
            return
        
        file_path = os.path.normpath(file_path)
        base_name = os.path.splitext(os.path.basename(file_path))[0]
        default_name = base_name.replace('-', ' ').replace('_', ' ').title()
        
        from PyQt6.QtWidgets import QInputDialog
        app_name, ok = QInputDialog.getText(
            self, 
            "Application Name", 
            "Enter name for the menu item:", 
            text=default_name
        )
        if ok and app_name.strip():
            self.apps.append({'name': app_name.strip(), 'path': file_path})
            self._populate_table()

    def _on_remove(self):
        selected = self.table.currentRow()
        if selected >= 0:
            self.apps.pop(selected)
            self._populate_table()

    def get_apps(self) -> list:
        return self.apps

class BatchEditDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Batch Edit Selected Files")
        self.setMinimumWidth(400)
        layout = QVBoxLayout(self)
        layout.setSpacing(12)
        artist_group = QGroupBox("Name")
        artist_layout = QFormLayout(artist_group)
        self.artist_input = QLineEdit()
        self.artist_input.setPlaceholderText("Enter name to apply to all selected...")
        artist_layout.addRow("Name:", self.artist_input)
        layout.addWidget(artist_group)
        rating_group = QGroupBox("Rating")
        rating_layout = QFormLayout(rating_group)
        self.rating_combo = QComboBox()
        self.rating_combo.addItems(["—"] + [str(i) for i in range(1, 11)])
        rating_layout.addRow("Rating:", self.rating_combo)
        layout.addWidget(rating_group)
        self.apply_artist = QCheckBox("Apply Name")
        self.apply_artist.setChecked(True)
        self.apply_rating = QCheckBox("Apply Rating")
        self.apply_rating.setChecked(True)
        options_layout = QHBoxLayout()
        options_layout.addWidget(self.apply_artist)
        options_layout.addWidget(self.apply_rating)
        layout.addLayout(options_layout)
        layout.addStretch()
        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        layout.addWidget(buttons)
    def get_values(self) -> tuple[str | None, str | None]:
        artist = self.artist_input.text().strip() if self.apply_artist.isChecked() else None
        # Return None instead of "—" so callers can distinguish "clear rating" from "no selection"
        if self.apply_rating.isChecked():
            rating_text = self.rating_combo.currentText()
            rating = None if rating_text == "—" else rating_text
        else:
            rating = None
        return artist, rating

class SmartRelocateDialog(QDialog):
    def __init__(self, media_infos: list, selected_rows: set, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Smart Relocate Files")
        self.setMinimumSize(600, 450)
        self.media_infos = media_infos
        self.selected_rows = selected_rows
        
        layout = QVBoxLayout(self)
        
        # 1. Source Selection
        source_group = QGroupBox("1. What to Move?")
        source_layout = QVBoxLayout(source_group)
        self.radio_selected = QRadioButton(f"Move Selected Files ({len(selected_rows)} files)")
        self.radio_query = QRadioButton("Move by Smart Query")
        self.radio_selected.setChecked(True)
        
        self.query_input = QLineEdit()
        self.query_input.setPlaceholderText("e.g. rating:>=8 and tag:nature")
        self.query_input.setEnabled(False)
        
        self.radio_query.toggled.connect(lambda checked: self.query_input.setEnabled(checked))
        
        source_layout.addWidget(self.radio_selected)
        source_layout.addWidget(self.radio_query)
        source_layout.addWidget(self.query_input)
        layout.addWidget(source_group)
        
        # 2. Destination Template
        dest_group = QGroupBox("2. Destination Template")
        dest_layout = QVBoxLayout(dest_group)
        help_lbl = QLabel("Use variables: <b>{type}</b>, <b>{name}</b>, <b>{rating}</b>, <b>{resolution}</b>, <b>{tag}</b>, <b>{tags}</b>")
        help_lbl.setWordWrap(True)
        
        path_row = QHBoxLayout()
        self.template_input = QLineEdit()
        self.btn_browse = QPushButton("Browse Base...")
        self.btn_browse.clicked.connect(self._browse_base_folder)
        
        path_row.addWidget(self.template_input, 1)
        path_row.addWidget(self.btn_browse)
        
        dest_layout.addWidget(help_lbl)
        dest_layout.addLayout(path_row)
        layout.addWidget(dest_group)
        
        # 3. Preview
        preview_group = QGroupBox("3. Preview (First 10 Files)")
        preview_layout = QVBoxLayout(preview_group)
        self.preview_list = QListWidget()
        preview_layout.addWidget(self.preview_list)
        layout.addWidget(preview_group, 1)
        
        # Buttons
        btn_row = QHBoxLayout()
        self.btn_preview = QPushButton("🔄 Update Preview")
        self.btn_preview.clicked.connect(self._generate_preview)
        self.btn_execute = QPushButton("🚀 Execute Move")
        self.btn_execute.clicked.connect(self.accept)
        btn_cancel = QPushButton("Cancel")
        btn_cancel.clicked.connect(self.reject)
        
        btn_row.addWidget(self.btn_preview)
        btn_row.addStretch()
        btn_row.addWidget(btn_cancel)
        btn_row.addWidget(self.btn_execute)
        layout.addLayout(btn_row)
        
        # Fallback to user home if media_infos is empty (was "" which produced
        # relative paths that could land in CWD — e.g. System32 when elevated)
        if media_infos:
            base_dir = os.path.dirname(media_infos[0].filepath)
        else:
            base_dir = os.path.expanduser("~")
            # Disable execute button to prevent acting on an empty selection
            self.btn_execute.setEnabled(False)
        self.template_input.setText(os.path.join(base_dir, "{type}", "{name}"))
        
        self._generate_preview()

    def _browse_base_folder(self):
        folder = QFileDialog.getExistingDirectory(self, "Select Base Destination Folder")
        if folder:
            folder = os.path.normpath(folder)
            self.template_input.setText(os.path.join(folder, "{type}", "{name}"))
            self._generate_preview()

    def _generate_preview(self):
        self.preview_list.clear()
        target_infos = self._get_target_infos()
        
        for info in target_infos[:10]:
            tags = getattr(info, 'tags', [])
            dest_dir = parse_destination_template(self.template_input.text(), info, tags)
            final_path = os.path.join(dest_dir, info.filename)
            self.preview_list.addItem(f"{info.filename}  ➔  {final_path}")
            
        if len(target_infos) > 10:
            self.preview_list.addItem(f"... and {len(target_infos) - 10} more files.")

    def _get_target_infos(self) -> list:
        if self.radio_selected.isChecked():
            return [self.media_infos[r] for r in self.selected_rows if r < len(self.media_infos)]
        else:
            query = self.query_input.text().strip()
            return [info for info in self.media_infos if matches_query(info, query)]

    def get_config(self) -> tuple[list, str]:
        return self._get_target_infos(), self.template_input.text()

class BatchTagDialog(QDialog):
    def __init__(self, selected_infos: list, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Batch Tag Editor")
        self.setMinimumWidth(500)
        self.selected_infos = selected_infos

        layout = QVBoxLayout(self)
        layout.setSpacing(12)

        form_layout = QFormLayout()
        
        self.mode_combo = QComboBox()
        self.mode_combo.addItems(["Add Tags", "Remove Tags", "Replace All Tags"])
        self.mode_combo.currentIndexChanged.connect(self._update_preview)
        form_layout.addRow("Action:", self.mode_combo)

        self.tag_input = QLineEdit()
        self.tag_input.setPlaceholderText("Enter tags separated by commas...")
        self.tag_input.textChanged.connect(self._update_preview)
        form_layout.addRow("Tags:", self.tag_input)
        
        layout.addLayout(form_layout)

        layout.addWidget(QLabel("Preview:"))
        self.preview_list = QListWidget()
        layout.addWidget(self.preview_list)

        btn_layout = QHBoxLayout()
        btn_layout.addStretch()
        self.btn_ok = QPushButton("Apply")
        self.btn_ok.clicked.connect(self.accept)
        self.btn_cancel = QPushButton("Cancel")
        self.btn_cancel.clicked.connect(self.reject)
        btn_layout.addWidget(self.btn_cancel)
        btn_layout.addWidget(self.btn_ok)
        layout.addLayout(btn_layout)

        self._update_preview()

    def _update_preview(self):
        self.preview_list.clear()
        mode = self.mode_combo.currentText()
        input_tags = [t.strip() for t in self.tag_input.text().split(',') if t.strip()]
        
        for info in self.selected_infos[:10]:
            current_tags = getattr(info, 'tags', [])
            new_tags = list(current_tags)
            
            if mode == "Add Tags":
                for t in input_tags:
                    if t not in new_tags:
                        new_tags.append(t)
            elif mode == "Remove Tags":
                new_tags = [t for t in new_tags if t not in input_tags]
            elif mode == "Replace All Tags":
                new_tags = input_tags
                
            curr_str = ", ".join(current_tags) if current_tags else "(none)"
            new_str = ", ".join(new_tags) if new_tags else "(none)"
            self.preview_list.addItem(f"{info.filename}: [{curr_str}] → [{new_str}]")
            
        if len(self.selected_infos) > 10:
            self.preview_list.addItem(f"... and {len(self.selected_infos) - 10} more files.")

    def get_result(self) -> tuple[str, list]:
        mode = self.mode_combo.currentText()
        input_tags = [t.strip() for t in self.tag_input.text().split(',') if t.strip()]
        return mode, input_tags


class TrimRangeSlider(QWidget):
    in_changed = pyqtSignal(int)
    out_changed = pyqtSignal(int)
    position_changed = pyqtSignal(int)

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setMinimumHeight(44)
        self.setCursor(Qt.CursorShape.PointingHandCursor)
        self._min = 0
        self._max = 1000
        self._in_pos = 0
        self._out_pos = 1000
        self._cur_pos = 0
        self._dragging_handle = None
        self.setMouseTracking(True)

    def set_range(self, min_val: int, max_val: int):
        self._min = min_val
        self._max = max(max_val, min_val + 1)
        self._in_pos = max(self._min, min(self._in_pos, self._max))
        self._out_pos = max(self._in_pos, min(self._out_pos, self._max))
        self._cur_pos = max(self._min, min(self._cur_pos, self._max))
        self.update()

    def set_in_pos(self, val: int):
        self._in_pos = max(self._min, min(val, self._out_pos))
        self.update()

    def set_out_pos(self, val: int):
        self._out_pos = max(self._in_pos, min(val, self._max))
        self.update()

    def set_cur_pos(self, val: int):
        self._cur_pos = max(self._min, min(val, self._max))
        self.update()

    def _val_to_x(self, val: int) -> int:
        track_w = self.width() - 32
        if self._max <= self._min: return 16
        ratio = (val - self._min) / (self._max - self._min)
        return int(16 + ratio * track_w)

    def _x_to_val(self, x: int) -> int:
        track_w = self.width() - 32
        if track_w <= 0: return self._min
        ratio = max(0.0, min(1.0, (x - 16) / track_w))
        return int(self._min + ratio * (self._max - self._min))

    def paintEvent(self, event):
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        w = self.width()
        h = self.height()
        track_y = h // 2 - 4
        track_h = 8

        # Background track
        painter.setPen(Qt.PenStyle.NoPen)
        painter.setBrush(QColor("#1e1b4b"))
        painter.drawRoundedRect(16, track_y, w - 32, track_h, 4, 4)

        # Highlighted selected range
        in_x = self._val_to_x(self._in_pos)
        out_x = self._val_to_x(self._out_pos)
        if out_x > in_x:
            grad = QLinearGradient(in_x, 0, out_x, 0)
            grad.setColorAt(0, QColor("#6366f1"))
            grad.setColorAt(1, QColor("#a855f7"))
            painter.setBrush(grad)
            painter.drawRoundedRect(in_x, track_y, out_x - in_x, track_h, 4, 4)

        # Current playback position marker
        cur_x = self._val_to_x(self._cur_pos)
        painter.setPen(QPen(QColor("#fbbf24"), 2))
        painter.drawLine(cur_x, 4, cur_x, h - 4)

        # IN handle (Left flag/knob)
        painter.setPen(QPen(QColor("#ffffff"), 1.5))
        painter.setBrush(QColor("#38bdf8"))
        in_poly = QPolygon([
            QPoint(in_x - 10, h // 2 - 12),
            QPoint(in_x, h // 2 - 12),
            QPoint(in_x, h // 2 + 12),
            QPoint(in_x - 10, h // 2 + 12),
            QPoint(in_x - 5, h // 2)
        ])
        painter.drawPolygon(in_poly)

        # OUT handle (Right flag/knob)
        painter.setPen(QPen(QColor("#ffffff"), 1.5))
        painter.setBrush(QColor("#ec4899"))
        out_poly = QPolygon([
            QPoint(out_x, h // 2 - 12),
            QPoint(out_x + 10, h // 2 - 12),
            QPoint(out_x + 5, h // 2),
            QPoint(out_x + 10, h // 2 + 12),
            QPoint(out_x, h // 2 + 12)
        ])
        painter.drawPolygon(out_poly)

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            x = event.pos().x()
            in_x = self._val_to_x(self._in_pos)
            out_x = self._val_to_x(self._out_pos)
            if abs(x - in_x) <= 12:
                self._dragging_handle = 'in'
            elif abs(x - out_x) <= 12:
                self._dragging_handle = 'out'
            else:
                self._dragging_handle = 'cur'
                val = self._x_to_val(x)
                self._cur_pos = val
                self.position_changed.emit(val)
                self.update()

    def mouseMoveEvent(self, event):
        x = event.pos().x()
        if self._dragging_handle:
            val = self._x_to_val(x)
            if self._dragging_handle == 'in':
                self._in_pos = max(self._min, min(val, self._out_pos))
                self.in_changed.emit(self._in_pos)
            elif self._dragging_handle == 'out':
                self._out_pos = max(self._in_pos, min(val, self._max))
                self.out_changed.emit(self._out_pos)
            elif self._dragging_handle == 'cur':
                self._cur_pos = val
                self.position_changed.emit(val)
            self.update()

    def mouseReleaseEvent(self, event):
        self._dragging_handle = None


class TrimExportWorker(QThread):
    # NOTE: renamed from 'finished' — that name shadows QThread.finished with
    # an incompatible signature (fragile/undefined behavior in PyQt).
    trim_finished = pyqtSignal(bool, str, str)  # success, output_path, error_msg

    def __init__(self, filepath: str, in_sec: float, out_sec: float, output_path: str, custom_ffmpeg: str = None, parent=None):
        super().__init__(parent)
        self.filepath = filepath
        self.in_sec = in_sec
        self.out_sec = out_sec
        self.output_path = output_path
        self.custom_ffmpeg = custom_ffmpeg

    def run(self):
        ffmpeg_cmd = get_ffmpeg_command(self.custom_ffmpeg)
        if not ffmpeg_cmd:
            self.trim_finished.emit(False, "", "FFmpeg executable not found. Please ensure FFmpeg is installed.")
            return

        cmd = [
            ffmpeg_cmd,
            "-y",
            "-ss", f"{self.in_sec:.3f}",
            "-to", f"{self.out_sec:.3f}",
            "-i", os.path.abspath(self.filepath),
            "-c", "copy",
            "-avoid_negative_ts", "make_zero",
            os.path.abspath(self.output_path)
        ]

        startupinfo = None
        if sys.platform == "win32":
            startupinfo = subprocess.STARTUPINFO()
            startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW

        try:
            proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, encoding='utf-8', startupinfo=startupinfo, timeout=120)
            if proc.returncode == 0 and os.path.exists(self.output_path) and os.path.getsize(self.output_path) > 0:
                self.trim_finished.emit(True, self.output_path, "")
            else:
                err = proc.stderr or "FFmpeg failed with unknown error."
                self.trim_finished.emit(False, "", err)
        except Exception as e:
            self.trim_finished.emit(False, "", str(e))


class QuickTrimDialog(QDialog):
    def __init__(self, filepath: str, parent_tab=None, parent=None):
        super().__init__(parent)
        self.filepath = filepath
        self.parent_tab = parent_tab
        self.duration_ms = 0
        self.in_ms = 0
        self.out_ms = 0
        self._playing_selection = False
        
        self.setWindowTitle(f"✂️ Quick Trim — {os.path.basename(filepath)}")
        self.resize(780, 580)

        layout = QVBoxLayout(self)
        layout.setContentsMargins(16, 16, 16, 16)
        layout.setSpacing(10)

        # Video preview widget
        self.video_widget = DoubleClickVideoWidget(self)
        self.video_widget.setMinimumHeight(240)
        self.video_widget.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)
        self.video_widget.setStyleSheet("background: #000000; border-radius: 8px;")
        layout.addWidget(self.video_widget, 1)

        # Media player backend
        self.player = QMediaPlayer(self)
        self.audio_output = QAudioOutput(self)
        self.player.setAudioOutput(self.audio_output)
        self.player.setVideoOutput(self.video_widget)
        self.audio_output.setVolume(0.7)

        # Playback control bar
        controls_layout = QHBoxLayout()
        controls_layout.setSpacing(8)
        
        self.btn_play = QPushButton("▶")
        self.btn_play.setFixedSize(32, 32)
        self.btn_play.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_play.clicked.connect(self._toggle_playback)
        controls_layout.addWidget(self.btn_play)

        self.time_label = QLabel("00:00.000 / 00:00.000")
        self.time_label.setStyleSheet("font-family: monospace; font-size: 11px; color: #a78bfa;")
        controls_layout.addWidget(self.time_label)

        controls_layout.addStretch()

        self.btn_play_selection = QPushButton("▶️ Play Selection")
        self.btn_play_selection.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_play_selection.clicked.connect(self._play_selection)
        controls_layout.addWidget(self.btn_play_selection)

        self.btn_mute = QPushButton("🔊")
        self.btn_mute.setFixedSize(32, 32)
        self.btn_mute.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_mute.clicked.connect(self._toggle_mute)
        controls_layout.addWidget(self.btn_mute)

        layout.addLayout(controls_layout)

        # Dual-handle range slider
        self.range_slider = TrimRangeSlider(self)
        self.range_slider.in_changed.connect(self._on_slider_in_changed)
        self.range_slider.out_changed.connect(self._on_slider_out_changed)
        self.range_slider.position_changed.connect(self._on_slider_pos_changed)
        layout.addWidget(self.range_slider)

        # IN / OUT point controls
        points_group = QGroupBox("Trim Points")
        points_layout = QGridLayout(points_group)
        points_layout.setContentsMargins(12, 12, 12, 12)
        points_layout.setSpacing(8)

        # Start (IN) row
        lbl_in = QLabel("Start (IN):")
        lbl_in.setStyleSheet("color: #38bdf8; font-weight: bold;")
        points_layout.addWidget(lbl_in, 0, 0)
        
        self.in_edit = QLineEdit("00:00:00.000")
        self.in_edit.setFixedWidth(110)
        self.in_edit.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.in_edit.editingFinished.connect(self._on_in_text_edited)
        points_layout.addWidget(self.in_edit, 0, 1)

        btn_in_minus1 = QPushButton("-1s")
        btn_in_minus1.clicked.connect(lambda: self._nudge_in(-1000))
        btn_in_plus1 = QPushButton("+1s")
        btn_in_plus1.clicked.connect(lambda: self._nudge_in(1000))
        btn_in_minus5 = QPushButton("-5s")
        btn_in_minus5.clicked.connect(lambda: self._nudge_in(-5000))
        btn_in_plus5 = QPushButton("+5s")
        btn_in_plus5.clicked.connect(lambda: self._nudge_in(5000))
        btn_set_in_cur = QPushButton("📌 Set to Current")
        btn_set_in_cur.clicked.connect(self._set_in_to_current)

        points_layout.addWidget(btn_in_minus5, 0, 2)
        points_layout.addWidget(btn_in_minus1, 0, 3)
        points_layout.addWidget(btn_in_plus1, 0, 4)
        points_layout.addWidget(btn_in_plus5, 0, 5)
        points_layout.addWidget(btn_set_in_cur, 0, 6)

        # End (OUT) row
        lbl_out = QLabel("End (OUT):")
        lbl_out.setStyleSheet("color: #ec4899; font-weight: bold;")
        points_layout.addWidget(lbl_out, 1, 0)
        
        self.out_edit = QLineEdit("00:00:00.000")
        self.out_edit.setFixedWidth(110)
        self.out_edit.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.out_edit.editingFinished.connect(self._on_out_text_edited)
        points_layout.addWidget(self.out_edit, 1, 1)

        btn_out_minus1 = QPushButton("-1s")
        btn_out_minus1.clicked.connect(lambda: self._nudge_out(-1000))
        btn_out_plus1 = QPushButton("+1s")
        btn_out_plus1.clicked.connect(lambda: self._nudge_out(1000))
        btn_out_minus5 = QPushButton("-5s")
        btn_out_minus5.clicked.connect(lambda: self._nudge_out(-5000))
        btn_out_plus5 = QPushButton("+5s")
        btn_out_plus5.clicked.connect(lambda: self._nudge_out(5000))
        btn_set_out_cur = QPushButton("📌 Set to Current")
        btn_set_out_cur.clicked.connect(self._set_out_to_current)

        points_layout.addWidget(btn_out_minus5, 1, 2)
        points_layout.addWidget(btn_out_minus1, 1, 3)
        points_layout.addWidget(btn_out_plus1, 1, 4)
        points_layout.addWidget(btn_out_plus5, 1, 5)
        points_layout.addWidget(btn_set_out_cur, 1, 6)

        # Trimmed duration label
        self.trim_dur_label = QLabel("⏱ Clip Duration: 00:00.000")
        self.trim_dur_label.setStyleSheet("font-weight: bold; color: #a78bfa; font-size: 12px;")
        points_layout.addWidget(self.trim_dur_label, 2, 0, 1, 7)

        layout.addWidget(points_group)

        # Output destination
        out_layout = QHBoxLayout()
        out_layout.addWidget(QLabel("Output File:"))
        
        base, ext = os.path.splitext(self.filepath)
        default_out = f"{base}_trimmed{ext}"
        self.output_edit = QLineEdit(default_out)
        out_layout.addWidget(self.output_edit, 1)
        
        btn_browse = QPushButton("Browse...")
        btn_browse.clicked.connect(self._browse_output)
        out_layout.addWidget(btn_browse)
        layout.addLayout(out_layout)

        # Action buttons
        btn_box = QHBoxLayout()
        btn_box.addStretch()
        self.btn_cancel = QPushButton("Cancel")
        self.btn_cancel.clicked.connect(self.reject)
        btn_box.addWidget(self.btn_cancel)

        self.btn_export = QPushButton("✂️ Export Trimmed Clip")
        self.btn_export.setObjectName("btnProcessAll")
        self.btn_export.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_export.clicked.connect(self._start_export)
        btn_box.addWidget(self.btn_export)
        layout.addLayout(btn_box)

        # Connect media player events
        self.player.durationChanged.connect(self._on_duration_changed)
        self.player.positionChanged.connect(self._on_position_changed)
        self.player.playbackStateChanged.connect(self._on_playback_state_changed)

        # Load video
        self.player.setSource(QUrl.fromLocalFile(self.filepath))
        self.player.pause()

    def _ms_to_str(self, ms: int) -> str:
        ms = max(0, ms)
        total_sec = ms // 1000
        rem_ms = ms % 1000
        hrs = total_sec // 3600
        mins = (total_sec % 3600) // 60
        secs = total_sec % 60
        return f"{hrs:02d}:{mins:02d}:{secs:02d}.{rem_ms:03d}"

    def _str_to_ms(self, s: str) -> int | None:
        try:
            s = s.strip()
            parts = s.split(':')
            if len(parts) == 3:
                hrs = int(parts[0])
                mins = int(parts[1])
                secs_parts = parts[2].split('.')
                secs = int(secs_parts[0])
                ms = int(secs_parts[1].ljust(3, '0')[:3]) if len(secs_parts) > 1 else 0
                return (hrs * 3600 + mins * 60 + secs) * 1000 + ms
            elif len(parts) == 2:
                mins = int(parts[0])
                secs_parts = parts[1].split('.')
                secs = int(secs_parts[0])
                ms = int(secs_parts[1].ljust(3, '0')[:3]) if len(secs_parts) > 1 else 0
                return (mins * 60 + secs) * 1000 + ms
        except Exception:
            pass
        return None

    def _on_duration_changed(self, dur: int):
        if dur > 0:
            self.duration_ms = dur
            self.out_ms = dur
            self.range_slider.set_range(0, dur)
            self.range_slider.set_out_pos(dur)
            self.out_edit.setText(self._ms_to_str(dur))
            self._update_time_display(self.player.position())
            self._update_clip_duration_label()

    def _on_position_changed(self, pos: int):
        self.range_slider.set_cur_pos(pos)
        self._update_time_display(pos)
        if self._playing_selection and pos >= self.out_ms:
            self.player.pause()
            self._playing_selection = False

    def _update_time_display(self, pos: int):
        self.time_label.setText(f"{self._ms_to_str(pos)} / {self._ms_to_str(self.duration_ms)}")

    def _update_clip_duration_label(self):
        clip_ms = max(0, self.out_ms - self.in_ms)
        self.trim_dur_label.setText(f"⏱ Clip Duration: {self._ms_to_str(clip_ms)}")

    def _toggle_playback(self):
        if self.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState:
            self.player.pause()
            self._playing_selection = False
        else:
            self.player.play()

    def _on_playback_state_changed(self, state):
        if state == QMediaPlayer.PlaybackState.PlayingState:
            self.btn_play.setText("⏸")
        else:
            self.btn_play.setText("▶")

    def _play_selection(self):
        self._playing_selection = True
        self.player.setPosition(self.in_ms)
        self.player.play()

    def _toggle_mute(self):
        is_muted = self.audio_output.isMuted()
        self.audio_output.setMuted(not is_muted)
        self.btn_mute.setText("🔇" if not is_muted else "🔊")

    def _on_slider_in_changed(self, val: int):
        self.in_ms = val
        self.in_edit.setText(self._ms_to_str(val))
        self.player.setPosition(val)
        self._update_clip_duration_label()

    def _on_slider_out_changed(self, val: int):
        self.out_ms = val
        self.out_edit.setText(self._ms_to_str(val))
        self.player.setPosition(val)
        self._update_clip_duration_label()

    def _on_slider_pos_changed(self, val: int):
        self.player.setPosition(val)

    def _on_in_text_edited(self):
        val = self._str_to_ms(self.in_edit.text())
        if val is not None:
            val = max(0, min(val, self.out_ms))
            self.in_ms = val
            self.range_slider.set_in_pos(val)
            self.in_edit.setText(self._ms_to_str(val))
            self._update_clip_duration_label()
        else:
            self.in_edit.setText(self._ms_to_str(self.in_ms))

    def _on_out_text_edited(self):
        val = self._str_to_ms(self.out_edit.text())
        if val is not None:
            val = max(self.in_ms, min(val, self.duration_ms))
            self.out_ms = val
            self.range_slider.set_out_pos(val)
            self.out_edit.setText(self._ms_to_str(val))
            self._update_clip_duration_label()
        else:
            self.out_edit.setText(self._ms_to_str(self.out_ms))

    def _nudge_in(self, delta_ms: int):
        val = max(0, min(self.in_ms + delta_ms, self.out_ms))
        self.in_ms = val
        self.range_slider.set_in_pos(val)
        self.in_edit.setText(self._ms_to_str(val))
        self.player.setPosition(val)
        self._update_clip_duration_label()

    def _nudge_out(self, delta_ms: int):
        val = max(self.in_ms, min(self.out_ms + delta_ms, self.duration_ms))
        self.out_ms = val
        self.range_slider.set_out_pos(val)
        self.out_edit.setText(self._ms_to_str(val))
        self.player.setPosition(val)
        self._update_clip_duration_label()

    def _set_in_to_current(self):
        self._nudge_in(self.player.position() - self.in_ms)

    def _set_out_to_current(self):
        self._nudge_out(self.player.position() - self.out_ms)

    def _browse_output(self):
        current_path = self.output_edit.text().strip() or self.filepath
        new_path, _ = QFileDialog.getSaveFileName(self, "Select Output File", current_path, "Video Files (*.mp4 *.mkv *.avi *.mov *.webm);;All Files (*.*)")
        if new_path:
            self.output_edit.setText(new_path)

    def _start_export(self):
        output_path = self.output_edit.text().strip()
        if not output_path:
            QMessageBox.warning(self, "Invalid Output", "Please specify an output file path.")
            return

        if os.path.abspath(output_path) == os.path.abspath(self.filepath):
            QMessageBox.warning(self, "Invalid Output", "Output file cannot be the same as the original input file.")
            return

        in_sec = self.in_ms / 1000.0
        out_sec = self.out_ms / 1000.0
        if out_sec <= in_sec:
            QMessageBox.warning(self, "Invalid Range", "End point (OUT) must be greater than Start point (IN).")
            return

        self.btn_export.setEnabled(False)
        self.btn_export.setText("⏳ Trimming clip...")

        self.worker = TrimExportWorker(self.filepath, in_sec, out_sec, output_path, parent=self)
        self.worker.trim_finished.connect(self._on_export_finished)
        self.worker.start()

    def _on_export_finished(self, success: bool, output_path: str, err: str):
        if getattr(self, '_suppress_export_result', False):
            self._suppress_export_result = False
            return
        self.btn_export.setEnabled(True)
        self.btn_export.setText("✂️ Export Trimmed Clip")
        
        if success:
            if self.parent_tab and hasattr(self.parent_tab, '_show_toast'):
                self.parent_tab._show_toast(f"Trimmed clip saved: {os.path.basename(output_path)}", 'success')
            
            # Check if output is in one of the loaded directories, auto-add if so
            if self.parent_tab and hasattr(self.parent_tab, 'directories'):
                out_dir = os.path.normcase(os.path.dirname(os.path.abspath(output_path)))
                for d in self.parent_tab.directories:
                    d_norm = os.path.normcase(os.path.abspath(d))
                    try:
                        is_inside = os.path.commonpath([d_norm, out_dir]) == d_norm
                    except ValueError:
                        # Different drives (e.g. C:\ vs F:\) — commonpath raises
                        continue
                    if is_inside:
                        new_info = MediaInfo(output_path, 'video')
                        if new_info.is_valid:
                            self.parent_tab._on_file_found(new_info)
                        break

            self._release_player()
            self.accept()
        else:
            QMessageBox.critical(self, "Export Failed", f"Failed to trim video:\n\n{err}")

    def _release_player(self):
        """Release media sources so the file handle isn't locked after close.

        done() (accept/reject) does NOT trigger closeEvent on QDialog, so both
        paths must clean up — otherwise QMediaPlayer keeps the source open.
        """
        self.player.stop()
        self.player.setSource(QUrl())
        self.player.setVideoOutput(None)

    def done(self, result):
        # accept()/reject() funnel through here; release before hiding
        self._release_player()
        # If the export worker is still running when the dialog closes, drop its
        # late result instead of popping dialogs/toasts on a hidden window.
        worker = getattr(self, 'worker', None)
        if worker is not None and worker.isRunning():
            self._suppress_export_result = True
        super().done(result)

    def closeEvent(self, event):
        self._release_player()
        super().closeEvent(event)


class CreateSmartFolderDialog(QDialog):
    def __init__(self, media_type: str = "all", query: str = "", parent=None):
        super().__init__(parent)
        self.setWindowTitle("Create Smart Folder")
        self.setMinimumWidth(400)
        layout = QVBoxLayout(self)
        layout.setSpacing(12)
        layout.setContentsMargins(20, 20, 20, 20)
        form_group = QGroupBox("Smart Folder Settings")
        form_layout = QFormLayout(form_group)
        self.name_input = QLineEdit()
        self.name_input.setPlaceholderText("e.g. Favorites")
        self.type_combo = QComboBox()
        self.type_combo.addItems(["All", "Videos", "Images", "Audio", "PDFs"])
        type_map = {"all": 0, "video": 1, "image": 2, "audio": 3, "pdf": 4}
        self.type_combo.setCurrentIndex(type_map.get(media_type, 0))
        self.query_input = QLineEdit()
        self.query_input.setText(query)
        self.query_input.setPlaceholderText("e.g. rating:9,10 or rating:>=9")
        form_layout.addRow("Folder Name:", self.name_input)
        form_layout.addRow("Media Type:", self.type_combo)
        form_layout.addRow("Search Query:", self.query_input)
        layout.addWidget(form_group)
        help_label = QLabel(
            "<b>Advanced Query Syntax:</b><br/>"
            "• <code>rating:9,10</code> - Matches ratings 9 or 10<br/>"
            "• <code>rating:>=9</code> - Matches ratings 9 and 10<br/>"
            "• <code>artist:John</code> - Matches artist 'John'<br/>"
            "• <code>resolution:4K</code> - Matches 4K resolution<br/>"
            "• <code>type:video</code> - Filters only videos"
        )
        help_label.setWordWrap(True)
        layout.addWidget(help_label)
        layout.addStretch()
        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        buttons.accepted.connect(self._validate_and_accept)
        buttons.rejected.connect(self.reject)
        layout.addWidget(buttons)
    def _validate_and_accept(self):
        if not self.name_input.text().strip():
            QMessageBox.warning(self, "Invalid Name", "Please enter a name for the Smart Folder."); return
        if not self.query_input.text().strip():
            QMessageBox.warning(self, "Invalid Query", "Please enter a search query."); return
        self.accept()
    def get_values(self) -> tuple[str, str, str]:
        type_idx = self.type_combo.currentIndex()
        type_map = {0: "all", 1: "video", 2: "image", 3: "audio", 4: "pdf"}
        return (self.name_input.text().strip(), type_map.get(type_idx, "all"), self.query_input.text().strip())

class SmartFolderNavItem(QWidget):
    clicked = pyqtSignal(str)
    delete_clicked = pyqtSignal(str)
    def __init__(self, name: str, active: bool = False, parent=None):
        super().__init__(parent)
        self.name = name
        self.active = active
        layout = QHBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(4)
        
        self.btn_nav = QPushButton(name)
        self.btn_nav.setObjectName("navButtonSmart")
        self.btn_nav.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_nav.setProperty("active", active)
        self.btn_nav.clicked.connect(lambda: self.clicked.emit(self.name))
        self.btn_nav.setIconSize(QSize(16, 16))
        layout.addWidget(self.btn_nav, 1)
        self.btn_delete = QPushButton("")
        self.btn_delete.setIconSize(QSize(14, 14))
        self.btn_delete.setObjectName("btnDeleteSmart")
        self.btn_delete.setFixedSize(20, 20)
        self.btn_delete.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_delete.setToolTip("Delete Smart Folder")
        self.btn_delete.clicked.connect(lambda: self.delete_clicked.emit(self.name))
        layout.addWidget(self.btn_delete)
        self.update_theme(True) # Default dark
    def set_active(self, active: bool):
        self.active = active
        self.btn_nav.setProperty("active", active)
        self.btn_nav.style().unpolish(self.btn_nav)
        self.btn_nav.style().polish(self.btn_nav)
    def update_theme(self, is_dark):
        if is_dark:
            self.btn_nav.setStyleSheet("""
                QPushButton { background: transparent; color: #9ca3af; text-align: left; padding: 10px 12px; font-size: 13px; font-weight: 600; border-radius: 6px; border: none; }
                QPushButton:hover { background: rgba(167, 139, 250, 0.1); color: #e0e0e0; }
                QPushButton[active="true"] { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #4f46e5, stop:1 #7c3aed); color: #ffffff; }
            """)
            self.btn_delete.setStyleSheet("""
                QPushButton { background: transparent; color: #ef4444; font-size: 11px; font-weight: bold; border: none; border-radius: 10px; padding: 0; }
                QPushButton:hover { background: rgba(239, 68, 68, 0.2); color: #f87171; }
            """)
        else:
            self.btn_nav.setStyleSheet("""
                QPushButton { background: transparent; color: #475569; text-align: left; padding: 10px 12px; font-size: 13px; font-weight: 600; border-radius: 6px; border: none; }
                QPushButton:hover { background: #f1f5f9; color: #0f172a; }
                QPushButton[active="true"] { background: #e0e7ff; color: #4338ca; font-weight: bold; }
            """)
            self.btn_delete.setStyleSheet("""
                QPushButton { background: transparent; color: #dc2626; font-size: 11px; font-weight: bold; border: none; border-radius: 10px; padding: 0; }
                QPushButton:hover { background: #fee2e2; color: #ef4444; }
            """)
        self.btn_nav.setIcon(get_vector_icon('star', is_dark))
        self.btn_delete.setIcon(get_vector_icon('close', is_dark))
        self.btn_nav.style().unpolish(self.btn_nav)
        self.btn_nav.style().polish(self.btn_nav)

class DeepMetadataWorker(QThread):
    """Background worker for ffprobe — prevents UI freezes up to 10s."""
    metadata_ready = pyqtSignal(dict or None)

    def __init__(self, filepath: str, ffprobe_path: str = None, parent=None):
        super().__init__(parent)
        self.filepath = filepath
        self.ffprobe_path = ffprobe_path

    def run(self):
        try:
            meta = get_file_deep_metadata(self.filepath, self.ffprobe_path)
            self.metadata_ready.emit(meta)
        except Exception as e:
            logger.warning("DeepMetadataWorker failed for %s: %s", self.filepath, e)
            self.metadata_ready.emit(None)


class AudioTagEditorDialog(QDialog):
    """Edit embedded audio tags (ID3/Vorbis/MP4) via mutagen's easy API.

    Writes title/artist/album/genre/date straight back into the file so the
    changes are visible in every other player, too.
    """
    FIELDS = ("title", "artist", "album", "genre", "date")

    def __init__(self, filepath: str, parent=None):
        super().__init__(parent)
        self.filepath = filepath
        self.setWindowTitle(f"Edit Audio Tags \u2014 {os.path.basename(filepath)}")
        self.setMinimumWidth(430)
        layout = QVBoxLayout(self)
        layout.setSpacing(12)

        self._edits = {}
        form = QFormLayout()
        labels = {"title": "Title:", "artist": "Artist:", "album": "Album:",
                  "genre": "Genre:", "date": "Year / Date:"}
        for key in self.FIELDS:
            edit = QLineEdit()
            self._edits[key] = edit
            form.addRow(labels[key], edit)
        layout.addLayout(form)

        self.status_lbl = QLabel("")
        self.status_lbl.setStyleSheet("color: #9ca3af; font-size: 11px;")
        layout.addWidget(self.status_lbl)

        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok |
                                   QDialogButtonBox.StandardButton.Cancel)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        layout.addWidget(buttons)

        self._mutagen_ok = True
        self._load_tags()

    def _load_tags(self):
        try:
            from mutagen import File as MutagenFile
            mfile = MutagenFile(self.filepath, easy=True)
            if mfile is None:
                raise ValueError("Unsupported audio format for tagging.")
            for key in self.FIELDS:
                vals = mfile.get(key, [])
                self._edits[key].setText(str(vals[0]) if vals else "")
            self.status_lbl.setText(os.path.basename(self.filepath))
        except ImportError:
            self._mutagen_ok = False
            self.status_lbl.setText("mutagen is not installed \u2014 run: pip install mutagen")
            self.status_lbl.setStyleSheet("color: #f87171; font-size: 11px;")
        except Exception as e:
            self._mutagen_ok = False
            self.status_lbl.setText(f"Could not read tags: {e}")
            self.status_lbl.setStyleSheet("color: #f87171; font-size: 11px;")

    def get_values(self) -> dict:
        return {k: self._edits[k].text().strip() for k in self.FIELDS}

    def save(self):
        if not self._mutagen_ok:
            raise RuntimeError("mutagen is not installed")
        from mutagen import File as MutagenFile
        mfile = MutagenFile(self.filepath, easy=True)
        if mfile is None:
            raise ValueError("Unsupported audio format for tagging.")
        values = self.get_values()
        for key in self.FIELDS:
            val = values[key]
            if val:
                mfile[key] = [val]
            else:
                mfile.pop(key, None)  # emptied field clears the tag on purpose
        mfile.save()


class DetailedInfoDialog(QDialog):
    def __init__(self, filepath: str, custom_ffprobe_path: str = None, parent=None):
        super().__init__(parent)
        self.filepath = filepath
        self.custom_ffprobe_path = custom_ffprobe_path
        self.setWindowTitle("Detailed Media Information")
        self.setMinimumWidth(500)
        layout = QVBoxLayout(self)
        layout.setContentsMargins(20, 20, 20, 20)
        layout.setSpacing(14)
        
        is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark' if self.window() else True
        accent_color = "#a78bfa" if is_dark else "#4338ca"
        text_color = "#e0e0e0" if is_dark else "#0f172a"
        sub_text_color = "#7c7c9a" if is_dark else "#64748b"
        
        filename = os.path.basename(filepath)
        header_label = QLabel(filename)
        header_label.setStyleSheet(f"font-size: 16px; font-weight: bold; color: {accent_color};")
        header_label.setWordWrap(True)
        layout.addWidget(header_label)
        path_label = QLabel(filepath)
        path_label.setStyleSheet(f"font-size: 11px; color: {sub_text_color};")
        path_label.setWordWrap(True)
        layout.addWidget(path_label)
        sep = QFrame()
        sep.setFrameShape(QFrame.Shape.HLine)
        sep.setStyleSheet(f"background: {accent_color}; opacity: 0.3;")
        layout.addWidget(sep)
        if not get_ffprobe_command(custom_ffprobe_path):
            warning_banner = QFrame()
            warning_banner.setStyleSheet(f"QFrame {{ background: rgba(239, 68, 68, 0.15); border: 1px solid rgba(239, 68, 68, 0.3); border-radius: 8px; padding: 8px; }}")
            warn_layout = QVBoxLayout(warning_banner)
            warn_title = QLabel("⚠️ Deep Metadata Unavailable")
            warn_title.setStyleSheet(f"font-weight: bold; color: #f87171; font-size: 12px;")
            warn_desc = QLabel("Detailed video/audio codecs and HDR detection require FFprobe.\nConfigure the path to ffprobe.exe in settings.")
            warn_desc.setStyleSheet(f"color: #fca5a5; font-size: 11px;")
            warn_desc.setWordWrap(True)
            warn_layout.addWidget(warn_title)
            warn_layout.addWidget(warn_desc)
            layout.addWidget(warning_banner)
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setStyleSheet("background: transparent; border: none;")
        self.scroll_widget = QWidget()
        self.scroll_widget.setStyleSheet("background: transparent;")
        self.scroll_layout = QVBoxLayout(self.scroll_widget)
        self.scroll_layout.setContentsMargins(0, 0, 0, 0)
        self.scroll_layout.setSpacing(12)
        # Loading placeholder shown until background worker returns
        self._loading_label = QLabel("Loading metadata…")
        self._loading_label.setStyleSheet(f"color: {sub_text_color}; font-style: italic; padding: 20px;")
        self._loading_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.scroll_layout.addWidget(self._loading_label)
        scroll.setWidget(self.scroll_widget)
        layout.addWidget(scroll, 1)
        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok)
        buttons.accepted.connect(self.accept)
        layout.addWidget(buttons)
        # Cache theme colors for the populate step
        self._theme = (accent_color, text_color, sub_text_color)
        # Start background worker (was: blocking call up to 10s on UI thread)
        self._worker = DeepMetadataWorker(filepath, custom_ffprobe_path, parent=self)
        self._worker.metadata_ready.connect(self._on_metadata_ready)
        self._worker.start()

    def _on_metadata_ready(self, meta):
        # Remove loading placeholder
        self._loading_label.setParent(None)
        self._loading_label.deleteLater()
        accent_color, text_color, sub_text_color = self._theme
        filepath = self.filepath
        if meta:
            gen_group = QGroupBox("📋 General Info")
            gen_layout = QFormLayout(gen_group)
            gen_layout.addRow(self._make_label("Format:", sub_text_color), self._make_value(meta['format'], text_color))
            size_str = "Unknown"
            if meta['size_bytes'] > 0:
                sb = meta['size_bytes']
                if sb >= 1024**3: size_str = f"{sb/(1024**3):.2f} GB"
                elif sb >= 1024**2: size_str = f"{sb/(1024**2):.1f} MB"
                elif sb >= 1024: size_str = f"{sb/1024:.0f} KB"
                else: size_str = f"{sb} B"
            gen_layout.addRow(self._make_label("Size:", sub_text_color), self._make_value(size_str, text_color))
            dur_str = "Unknown"
            if meta['duration_seconds'] > 0:
                ds = int(meta['duration_seconds'])
                dur_str = f"{ds // 60}m {ds % 60}s"
            gen_layout.addRow(self._make_label("Duration:", sub_text_color), self._make_value(dur_str, text_color))
            if meta['bitrate_kbps'] > 0:
                gen_layout.addRow(self._make_label("Overall Bitrate:", sub_text_color), self._make_value(f"{meta['bitrate_kbps']} kbps", text_color))
            self.scroll_layout.addWidget(gen_group)
            if meta['video']:
                v = meta['video']
                v_group = QGroupBox("🎬 Video Stream")
                v_layout = QFormLayout(v_group)
                v_layout.addRow(self._make_label("Codec:", sub_text_color), self._make_value(v['codec'], text_color))
                if v['profile']: v_layout.addRow(self._make_label("Profile:", sub_text_color), self._make_value(v['profile'], text_color))
                v_layout.addRow(self._make_label("Resolution:", sub_text_color), self._make_value(f"{v['width']}x{v['height']}", text_color))
                if v['fps'] > 0: v_layout.addRow(self._make_label("Frame Rate:", sub_text_color), self._make_value(f"{v['fps']} fps", text_color))
                if v['bitrate_kbps'] > 0: v_layout.addRow(self._make_label("Bitrate:", sub_text_color), self._make_value(f"{v['bitrate_kbps']} kbps", text_color))
                if v['pix_fmt']: v_layout.addRow(self._make_label("Pixel Format:", sub_text_color), self._make_value(v['pix_fmt'], text_color))
                hdr_color = "#34d399" if meta['hdr_type'] == 'SDR' else "#f59e0b"
                if meta['hdr_type'] == 'Dolby Vision': hdr_color = "#ec4899"
                hdr_lbl = QLabel(meta['hdr_type'])
                hdr_lbl.setStyleSheet(f"font-weight: bold; color: {hdr_color};")
                v_layout.addRow(self._make_label("HDR Standard:", sub_text_color), hdr_lbl)
                self.scroll_layout.addWidget(v_group)
            if meta['audio']:
                a = meta['audio']
                a_group = QGroupBox("🎵 Audio Stream")
                a_layout = QFormLayout(a_group)
                a_layout.addRow(self._make_label("Codec:", sub_text_color), self._make_value(a['codec'], text_color))
                a_layout.addRow(self._make_label("Channels:", sub_text_color), self._make_value(a['channel_layout'], text_color))
                if a['sample_rate_hz'] > 0: a_layout.addRow(self._make_label("Sample Rate:", sub_text_color), self._make_value(f"{a['sample_rate_hz'] / 1000:.1f} kHz", text_color))
                if a['bitrate_kbps'] > 0: a_layout.addRow(self._make_label("Bitrate:", sub_text_color), self._make_value(f"{a['bitrate_kbps']} kbps", text_color))
                self.scroll_layout.addWidget(a_group)
        else:
            fallback_group = QGroupBox("📋 General Info (Basic)")
            fallback_layout = QFormLayout(fallback_group)
            try:
                sb = os.path.getsize(filepath)
                if sb >= 1024**3: size_str = f"{sb/(1024**3):.2f} GB"
                elif sb >= 1024**2: size_str = f"{sb/(1024**2):.1f} MB"
                elif sb >= 1024: size_str = f"{sb/1024:.0f} KB"
                else: size_str = f"{sb} B"
                fallback_layout.addRow(self._make_label("Size:", sub_text_color), self._make_value(size_str, text_color))
            except Exception: pass
            ext = os.path.splitext(filepath)[1].lower()
            if ext in ['.mp4', '.mkv', '.avi', '.mov', '.wmv']:
                cap = None
                try:
                    with _CV_LOCK:
                        cap = cv2.VideoCapture(filepath)
                        if cap.isOpened():
                            w = int(cap.get(cv2.CAP_PROP_FRAME_WIDTH))
                            h = int(cap.get(cv2.CAP_PROP_FRAME_HEIGHT))
                            fps = cap.get(cv2.CAP_PROP_FPS)
                            fc = cap.get(cv2.CAP_PROP_FRAME_COUNT)
                            fallback_layout.addRow(self._make_label("Resolution:", sub_text_color), self._make_value(f"{w}x{h}", text_color))
                            if fps > 0: fallback_layout.addRow(self._make_label("Frame Rate:", sub_text_color), self._make_value(f"{round(fps, 2)} fps", text_color))
                            if fps > 0 and fc > 0:
                                ds = int(fc / fps)
                                fallback_layout.addRow(self._make_label("Duration:", sub_text_color), self._make_value(f"{ds // 60}m {ds % 60}s", text_color))
                except Exception: pass
                finally:
                    if cap is not None:
                        cap.release()
            self.scroll_layout.addWidget(fallback_group)

    def _make_label(self, text: str, color: str) -> QLabel:
        lbl = QLabel(text)
        lbl.setStyleSheet(f"color: {color}; font-weight: bold;")
        return lbl
    def _make_value(self, text: str, color: str) -> QLabel:
        lbl = QLabel(str(text))
        lbl.setStyleSheet(f"color: {color};")
        lbl.setWordWrap(True)
        return lbl

class ClickToSeekSlider(QSlider):
    def mousePressEvent(self, event):
        super().mousePressEvent(event)
        if event.button() == Qt.MouseButton.LeftButton:
            val = QStyle.sliderValueFromPosition(
                self.minimum(), self.maximum(), int(event.position().x()), self.width()
            )
            self.setValue(val)

class HoverPreviewOverlay(QWidget):
    def __init__(self, parent_window):
        super().__init__(parent_window)
        self.parent_window = parent_window
        self.setWindowFlags(Qt.WindowType.FramelessWindowHint | Qt.WindowType.SubWindow)
        self.setAttribute(Qt.WidgetAttribute.WA_NoSystemBackground, True)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground, True)
        
        self.backdrop_color = QColor(0, 0, 0, 160)
        
        # Central preview container
        self.container = QFrame(self)
        self.container.setObjectName("hoverPreviewContainer")
        
        container_layout = QVBoxLayout(self.container)
        container_layout.setContentsMargins(6, 6, 6, 6)
        
        self.video_widget = QVideoWidget(self.container)
        self.video_widget.setStyleSheet("border-radius: 8px; background: black;")
        container_layout.addWidget(self.video_widget)
        
        self.player = QMediaPlayer(self)
        self.audio_output = QAudioOutput(self)
        self.player.setAudioOutput(self.audio_output)
        self.player.setVideoOutput(self.video_widget)
        
        self.segment_timer = QTimer(self)
        self.segment_timer.timeout.connect(self._on_segment_timeout)
        
        # Mouse-check timer created ONCE in __init__ (was recreated in show_preview,
        # leaking a QTimer on every call)
        self.mouse_check_timer = QTimer(self)
        self.mouse_check_timer.timeout.connect(self._check_mouse_position)
        
        self.player.mediaStatusChanged.connect(self._on_media_status_changed)
        
        self._duration = 0.0
        self.has_started = False
        self.info = None
        self.target_global_rect = QRect()
        
        # Install event filters to catch clicks on container and video widget
        self.container.installEventFilter(self)
        self.video_widget.installEventFilter(self)
        
        self.update_theme()
        self.hide()

    def update_theme(self):
        is_dark = getattr(self.parent_window, 'current_theme', 'dark') == 'dark'
        if is_dark:
            self.container.setStyleSheet("""
                QFrame#hoverPreviewContainer {
                    background: #0f0c29;
                    border: 2px solid rgba(167, 139, 250, 0.6);
                    border-radius: 12px;
                }
            """)
            self.backdrop_color = QColor(0, 0, 0, 160)
        else:
            self.container.setStyleSheet("""
                QFrame#hoverPreviewContainer {
                    background: #ffffff;
                    border: 2px solid rgba(99, 102, 241, 0.6);
                    border-radius: 12px;
                }
            """)
            self.backdrop_color = QColor(0, 0, 0, 100)

    def paintEvent(self, event):
        painter = QPainter(self)
        painter.fillRect(self.rect(), self.backdrop_color)

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self.adjust_layout()

    def adjust_layout(self):
        self.setGeometry(self.parent_window.rect())
        p_width = self.width()
        p_height = self.height()
        if p_width <= 0 or p_height <= 0:
            return
            
        w = p_width // 2
        h = (w * 9) // 16
        if h > p_height // 2:
            h = p_height // 2
            w = (h * 16) // 9
            
        w = max(480, min(w, 854))
        h = (w * 9) // 16
        
        x = (p_width - w) // 2
        y = (p_height - h) // 2
        self.container.setGeometry(x, y, w, h)

    def eventFilter(self, watched, event):
        if event.type() == QEvent.Type.MouseButtonPress:
            if event.button() in (Qt.MouseButton.LeftButton, Qt.MouseButton.RightButton):
                active_tab = self.parent_window.stacked_widget.currentWidget()
                if active_tab and hasattr(active_tab, '_dismissed_info'):
                    active_tab._dismissed_info = self.info
                self.hide_preview()
                return True
        return super().eventFilter(watched, event)

    def mousePressEvent(self, event):
        if event.button() in (Qt.MouseButton.LeftButton, Qt.MouseButton.RightButton):
            active_tab = self.parent_window.stacked_widget.currentWidget()
            if active_tab and hasattr(active_tab, '_dismissed_info'):
                active_tab._dismissed_info = self.info
            self.hide_preview()

    def show_preview(self, info, target_global_rect):
        # Pause background player if playing
        active_tab = self.parent_window.stacked_widget.currentWidget()
        if active_tab and hasattr(active_tab, 'player'):
            try:
                if active_tab.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState:
                    active_tab.player.pause()
            except Exception:
                pass

        self.info = info
        self.target_global_rect = target_global_rect
        self.has_started = False
        
        # Store duration for continuous random segments
        self._duration = info.duration_seconds or 0.0
            
        self.update_theme()
        self.adjust_layout()
        
        # Audio setting based on global volume button
        is_globally_muted = getattr(self.parent_window, 'global_mute', False)
        self.audio_output.setMuted(is_globally_muted)
        
        self.player.setSource(QUrl.fromLocalFile(info.filepath))
        
        self.show()
        self.raise_()
        
        # Reuse the single mouse_check_timer created in __init__
        self.mouse_check_timer.start(50)

    def hide_preview(self):
        self.segment_timer.stop()
        # mouse_check_timer is now created in __init__, always exists
        if hasattr(self, 'mouse_check_timer'):
            self.mouse_check_timer.stop()
        self.player.stop()
        self.player.setSource(QUrl())
        self.hide()

    def _check_mouse_position(self):
        # Hide if cursor left the target thumbnail cell.
        if not self.target_global_rect.contains(QCursor.pos()):
            self.hide_preview()

    def _get_random_position(self):
        if self._duration < 2.0:
            return 0
        return int(random.uniform(0.0, self._duration - 2.0) * 1000)

    def _on_media_status_changed(self, status):
        if not self.has_started and status in (QMediaPlayer.MediaStatus.LoadedMedia, QMediaPlayer.MediaStatus.BufferedMedia):
            self.has_started = True
            self.player.setPosition(self._get_random_position())
            self.player.play()
            self.segment_timer.start(2000)

    def _on_segment_timeout(self):
        if not self.has_started or not self.isVisible():
            return
        self.player.setPosition(self._get_random_position())
        self.player.play()

class ToastNotification(QWidget):
    def __init__(self, message: str, toast_type: str = 'info', parent=None):
        super().__init__(parent)
        self.setWindowFlags(Qt.WindowType.FramelessWindowHint | Qt.WindowType.Tool | Qt.WindowType.WindowStaysOnTopHint)
        self.setAttribute(Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose)
        
        self.toast_type = toast_type
        self.message = message
        self.parent_window = parent

        is_dark = getattr(parent, 'current_theme', 'dark') == 'dark'
        if toast_type == 'success':
            icon = "✅"
            bg_color = "#34d399" if is_dark else "#059669"
        elif toast_type == 'warning':
            icon = "⚠️"
            bg_color = "#fbbf24" if is_dark else "#d97706"
        elif toast_type == 'error':
            icon = "❌"
            bg_color = "#f87171" if is_dark else "#dc2626"
        else: # info
            icon = "ℹ️"
            bg_color = "#60a5fa" if is_dark else "#3b82f6"

        layout = QHBoxLayout(self)
        layout.setContentsMargins(15, 10, 15, 10)
        layout.setSpacing(10)

        icon_label = QLabel(icon)
        icon_label.setStyleSheet("font-size: 16px; background: transparent;")
        
        msg_label = QLabel(message)
        msg_label.setWordWrap(True)
        msg_label.setStyleSheet("color: white; font-weight: bold; background: transparent;")

        layout.addWidget(icon_label)
        layout.addWidget(msg_label, 1)

        self.setFixedWidth(320)
        self.setStyleSheet(f"""
            ToastNotification {{
                background-color: {bg_color};
                border-radius: 10px;
                border: 1px solid rgba(255, 255, 255, 0.2);
            }}
        """)
        
        self.pos_anim = QPropertyAnimation(self, b"pos")
        self.pos_anim.setDuration(300)
        self.pos_anim.setEasingCurve(QEasingCurve.Type.OutCubic)

        self.opacity_anim = QPropertyAnimation(self, b"windowOpacity")
        self.opacity_anim.setDuration(300)
        
        self.timer = QTimer(self)
        self.timer.setSingleShot(True)
        self.timer.timeout.connect(self.hide_toast)

    def _motion_reduced(self):
        return bool(getattr(self.parent(), 'reduced_motion', False))

    def show_toast(self, target_pos):
        if self._motion_reduced():
            # Reduced motion: appear in place, no slide/fade
            self.setWindowOpacity(0.9)
            self.move(target_pos)
            self.show()
            self.timer.start(3000)
            return
        self.setWindowOpacity(0.0)
        self.move(target_pos.x(), target_pos.y() + 20)
        self.show()

        self.pos_anim.setStartValue(self.pos())
        self.pos_anim.setEndValue(target_pos)
        self.opacity_anim.setStartValue(0.0)
        self.opacity_anim.setEndValue(0.9)

        self.pos_anim.start()
        self.opacity_anim.start()

        self.timer.start(3000)

    def hide_toast(self):
        if self._motion_reduced():
            self.close(); return
        try:
            self.opacity_anim.finished.disconnect()
        except TypeError:
            pass
        self.opacity_anim.finished.connect(self.close)
        self.opacity_anim.setStartValue(self.windowOpacity())
        self.opacity_anim.setEndValue(0.0)
        self.opacity_anim.start()

class DoubleClickVideoWidget(QVideoWidget):
    double_clicked = pyqtSignal()
    mouse_moved = pyqtSignal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setMouseTracking(True)

    def mouseDoubleClickEvent(self, event):
        super().mouseDoubleClickEvent(event)
        if event.button() == Qt.MouseButton.LeftButton:
            self.double_clicked.emit()

    def mouseMoveEvent(self, event):
        super().mouseMoveEvent(event)
        self.mouse_moved.emit()


class NativeImagePlayerWindow(QMainWindow):
    def __init__(self, filepath, parent=None):
        super().__init__(parent)
        self.filepath = filepath
        self.setWindowTitle(f"MediaFlow Image Viewer — {os.path.basename(filepath)}")
        self.resize(800, 600)
        self.setWindowFlags(Qt.WindowType.Window)
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose)
        
        is_dark = getattr(parent, 'current_theme', 'dark') == 'dark' if parent else True
        
        central = QWidget(self)
        self.setCentralWidget(central)
        layout = QVBoxLayout(central)
        layout.setContentsMargins(10, 10, 10, 10)
        
        self.label = QLabel(central)
        self.label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        
        pixmap = QPixmap(filepath)
        if not pixmap.isNull():
            self.label.setPixmap(pixmap.scaled(780, 580, Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation))
        else:
            self.label.setText("Failed to load image.")
            
        layout.addWidget(self.label, 1)
        
        if is_dark:
            self.setStyleSheet("QMainWindow { background-color: #0f0c29; } QLabel { color: #f3f4f6; }")
        else:
            self.setStyleSheet("QMainWindow { background-color: #f1f5f9; } QLabel { color: #1e293b; }")

    def closeEvent(self, event):
        if hasattr(self, 'label') and self.label:
            self.label.clear()
        super().closeEvent(event)

class NativeAudioPlayerWindow(QMainWindow):
    def __init__(self, filepath, parent=None):
        super().__init__(parent)
        self.filepath = filepath
        self.setWindowTitle(f"MediaFlow Audio Player — {os.path.basename(filepath)}")
        self.resize(450, 160)
        self.setWindowFlags(Qt.WindowType.Window)
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose)
        
        is_dark = getattr(parent, 'current_theme', 'dark') == 'dark' if parent else True
        
        central = QWidget(self)
        self.setCentralWidget(central)
        layout = QVBoxLayout(central)
        layout.setContentsMargins(20, 20, 20, 20)
        layout.setSpacing(12)
        
        self.player = QMediaPlayer(self)
        self.audio_output = QAudioOutput(self)
        self.player.setAudioOutput(self.audio_output)
        
        title_lbl = QLabel(os.path.basename(filepath), self)
        title_lbl.setStyleSheet("font-size: 13px; font-weight: bold;")
        title_lbl.setAlignment(Qt.AlignmentFlag.AlignCenter)
        layout.addWidget(title_lbl)
        
        self.slider = QSlider(Qt.Orientation.Horizontal, self)
        self.slider.setRange(0, 1000)
        self.slider.setCursor(Qt.CursorShape.PointingHandCursor)
        self.slider.sliderMoved.connect(self._set_position)
        layout.addWidget(self.slider)
        
        btn_row = QHBoxLayout()
        self.btn_play = QPushButton("Play", self)
        self.btn_play.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_play.clicked.connect(self._toggle_playback)
        self.btn_mute = QPushButton("Mute", self)
        self.btn_mute.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_mute.clicked.connect(self._toggle_mute)
        
        btn_row.addWidget(self.btn_play)
        btn_row.addWidget(self.btn_mute)
        layout.addLayout(btn_row)
        
        self.player.positionChanged.connect(self._position_changed)
        self.player.setSource(QUrl.fromLocalFile(filepath))
        self.player.play()
        self._update_play_button_text()
        
        if is_dark:
            self.setStyleSheet("""
                QMainWindow { background-color: #0f0c29; }
                QLabel { color: #f3f4f6; }
                QPushButton { background-color: #312e81; color: #f3f4f6; border: 1px solid #4f46e5; border-radius: 4px; padding: 6px 12px; }
                QPushButton:hover { background-color: #4338ca; }
            """)
        else:
            self.setStyleSheet("""
                QMainWindow { background-color: #f1f5f9; }
                QLabel { color: #1e293b; }
                QPushButton { background-color: #e2e8f0; color: #1e293b; border: 1px solid #cbd5e1; border-radius: 4px; padding: 6px 12px; }
                QPushButton:hover { background-color: #cbd5e1; }
            """)

    def _toggle_playback(self):
        if self.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState:
            self.player.pause()
        else:
            self.player.play()
        self._update_play_button_text()

    def _update_play_button_text(self):
        playing = self.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState
        self.btn_play.setText("Pause" if playing else "Play")

    def _toggle_mute(self):
        muted = not self.audio_output.isMuted()
        self.audio_output.setMuted(muted)
        self.btn_mute.setText("Unmute" if muted else "Mute")

    def _position_changed(self, position):
        duration = self.player.duration()
        if duration > 0:
            val = int((position / duration) * 1000)
            self.slider.setValue(val)

    def _set_position(self, value):
        duration = self.player.duration()
        if duration > 0:
            pos = int((value / 1000) * duration)
            self.player.setPosition(pos)

    def closeEvent(self, event):
        self.player.stop()
        self.player.setSource(QUrl())
        super().closeEvent(event)

class NativeVideoPlayerWindow(QMainWindow):
    def __init__(self, filepath, parent=None):
        super().__init__(parent)
        self.parent_window = parent
        self.setWindowFlags(Qt.WindowType.Window)
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose)
        self.setWindowTitle(f"MediaFlow Player — {os.path.basename(filepath)}")
        self.resize(854, 480)
        
        # Controls auto-hide timer
        self.controls_timer = QTimer(self)
        self.controls_timer.setSingleShot(True)
        self.controls_timer.timeout.connect(self._hide_controls_if_fullscreen)
        
        # Central widget and layout
        central = QWidget(self)
        self.setCentralWidget(central)
        layout = QVBoxLayout(central)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)
        
        # Video Widget
        self.video_widget = DoubleClickVideoWidget(central)
        self.video_widget.double_clicked.connect(self.toggle_fullscreen)
        self.video_widget.mouse_moved.connect(self.show_controls_temporarily)
        layout.addWidget(self.video_widget, 1)
        
        # Controls widget
        self.controls_widget = QWidget(central)
        self.controls_widget.setFixedHeight(60)
        is_dark = getattr(parent, 'current_theme', 'dark') == 'dark' if parent else True
        self.controls_widget.setStyleSheet(
            "background: #09071c; border-top: 1px solid rgba(167, 139, 250, 0.2);" if is_dark else
            "background: #f8fafc; border-top: 1px solid #e2e8f0;"
        )
        
        controls_layout = QVBoxLayout(self.controls_widget)
        controls_layout.setContentsMargins(12, 4, 12, 4)
        controls_layout.setSpacing(4)
        
        # Seek slider and time label row
        seek_layout = QHBoxLayout()
        seek_layout.setContentsMargins(0, 0, 0, 0)
        seek_layout.setSpacing(10)
        
        self.seek_slider = ClickToSeekSlider(Qt.Orientation.Horizontal, self.controls_widget)
        self.seek_slider.setRange(0, 1000)
        self.seek_slider.setCursor(Qt.CursorShape.PointingHandCursor)
        self.seek_slider.setFixedHeight(12)
        seek_layout.addWidget(self.seek_slider, 1)
        
        self.time_label = QLabel("00:00 / 00:00", self.controls_widget)
        self.time_label.setFixedWidth(100)
        self.time_label.setAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
        self.time_label.setStyleSheet("font-size: 11px;")
        seek_layout.addWidget(self.time_label)
        controls_layout.addLayout(seek_layout)
        
        # Buttons row
        buttons_layout = QHBoxLayout()
        buttons_layout.setContentsMargins(0, 0, 0, 0)
        buttons_layout.setSpacing(12)
        
        self.btn_play = QPushButton(self.controls_widget)
        self.btn_play.setFixedSize(30, 30)
        self.btn_play.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_play.clicked.connect(self._toggle_playback)
        self.btn_play.setIcon(get_vector_icon('play', is_dark))
        buttons_layout.addWidget(self.btn_play)
        
        self.btn_mute = QPushButton(self.controls_widget)
        self.btn_mute.setFixedSize(30, 30)
        self.btn_mute.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_mute.clicked.connect(self._toggle_mute)
        self.btn_mute.setIcon(get_vector_icon('unmute', is_dark))
        buttons_layout.addWidget(self.btn_mute)
        
        self.volume_slider = QSlider(Qt.Orientation.Horizontal, self.controls_widget)
        self.volume_slider.setRange(0, 100)
        self.volume_slider.setValue(70)
        self.volume_slider.setFixedWidth(100)
        self.volume_slider.setCursor(Qt.CursorShape.PointingHandCursor)
        self.volume_slider.valueChanged.connect(self._on_volume_changed)
        buttons_layout.addWidget(self.volume_slider)
        
        buttons_layout.addStretch()
        
        self.btn_fullscreen = QPushButton(self.controls_widget)
        self.btn_fullscreen.setFixedSize(30, 30)
        self.btn_fullscreen.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_fullscreen.clicked.connect(self.toggle_fullscreen)
        self.btn_fullscreen.setIcon(get_vector_icon('preview', is_dark))
        self.btn_fullscreen.setToolTip("Toggle Fullscreen")
        buttons_layout.addWidget(self.btn_fullscreen)
        
        controls_layout.addLayout(buttons_layout)
        layout.addWidget(self.controls_widget)
        
        # Player setup
        self.player = QMediaPlayer(self)
        self.audio_output = QAudioOutput(self)
        self.player.setAudioOutput(self.audio_output)
        self.player.setVideoOutput(self.video_widget)
        
        # Connect signals
        self.player.positionChanged.connect(self._on_player_position_changed)
        self.player.durationChanged.connect(self._on_player_duration_changed)
        self.player.playbackStateChanged.connect(self._on_player_state_changed)
        self.seek_slider.valueChanged.connect(self._on_slider_moved)
        
        # Load and play media
        self.player.setSource(QUrl.fromLocalFile(filepath))
        
        global_mute = getattr(parent, 'global_mute', False) if parent else False
        self.audio_output.setMuted(global_mute)
        self.audio_output.setVolume(0.7)
        self.btn_mute.setIcon(get_vector_icon('mute' if global_mute else 'unmute', is_dark))
        
        self.player.play()
        # Removed dead field `_is_slider_pressed` — never read or updated anywhere
        # else in the class. The slider-press state is already correctly tracked
        # by `self.seek_slider.isSliderDown()` in _on_player_position_changed.
        self.filepath = filepath

        # Set Focus Policies to prevent stealing arrow key presses
        self.btn_play.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.btn_mute.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.volume_slider.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.btn_fullscreen.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.seek_slider.setFocusPolicy(Qt.FocusPolicy.NoFocus)

        # Enable mouse tracking recursively and install event filters for auto-hiding controls
        self._enable_mouse_tracking_recursive(central)
        self.setMouseTracking(True)
        central.installEventFilter(self)
        for child in central.findChildren(QWidget):
            child.installEventFilter(self)

    def _enable_mouse_tracking_recursive(self, widget):
        widget.setMouseTracking(True)
        for child in widget.findChildren(QWidget):
            child.setMouseTracking(True)

    def eventFilter(self, watched, event):
        if event.type() in (QEvent.Type.MouseMove, QEvent.Type.MouseButtonPress):
            self.show_controls_temporarily()
        elif event.type() == QEvent.Type.Wheel:
            delta = event.angleDelta().y()
            if delta > 0:
                new_vol = min(100, self.volume_slider.value() + 5)
                self.volume_slider.setValue(new_vol)
            elif delta < 0:
                new_vol = max(0, self.volume_slider.value() - 5)
                self.volume_slider.setValue(new_vol)
            self.show_controls_temporarily()
            return True
        return super().eventFilter(watched, event)


    def mouseMoveEvent(self, event):
        super().mouseMoveEvent(event)
        self.show_controls_temporarily()

    def show_controls_temporarily(self):
        self.setCursor(Qt.CursorShape.ArrowCursor)
        self.controls_widget.show()
        if self.isFullScreen():
            self.controls_timer.start(2000)

    def _hide_controls_if_fullscreen(self):
        if self.isFullScreen():
            self.controls_widget.hide()
            self.setCursor(Qt.CursorShape.BlankCursor)

    def toggle_fullscreen(self):
        if self.isFullScreen():
            self.showNormal()
            self.controls_widget.show()
            self.setCursor(Qt.CursorShape.ArrowCursor)
            self.controls_timer.stop()
        else:
            self.showFullScreen()
            self.show_controls_temporarily()

    def _toggle_playback(self):
        if self.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState:
            self.player.pause()
        else:
            self.player.play()

    def _toggle_mute(self):
        is_muted = self.audio_output.isMuted()
        self.audio_output.setMuted(not is_muted)
        is_dark = getattr(self.parent_window, 'current_theme', 'dark') == 'dark' if self.parent_window else True
        self.btn_mute.setIcon(get_vector_icon('mute' if not is_muted else 'unmute', is_dark))

    def _on_volume_changed(self, value):
        self.audio_output.setVolume(value / 100.0)
        if value > 0 and self.audio_output.isMuted():
            self._toggle_mute()

    def _on_player_state_changed(self, state):
        is_dark = getattr(self.parent_window, 'current_theme', 'dark') == 'dark' if self.parent_window else True
        if state == QMediaPlayer.PlaybackState.PlayingState:
            self.btn_play.setIcon(get_vector_icon('pause', is_dark))
        else:
            self.btn_play.setIcon(get_vector_icon('play', is_dark))

    def _on_player_position_changed(self, position):
        if not self.seek_slider.isSliderDown():
            self.seek_slider.blockSignals(True)
            duration = self.player.duration()
            if duration > 0:
                self.seek_slider.setValue(int(position * 1000 / duration))
            self.seek_slider.blockSignals(False)
        self._update_time_label(position, self.player.duration())

    def _on_player_duration_changed(self, duration):
        self._update_time_label(self.player.position(), duration)

    def _update_time_label(self, position, duration):
        pos_sec = position // 1000
        dur_sec = duration // 1000
        pos_str = f"{pos_sec // 60:02d}:{pos_sec % 60:02d}"
        dur_str = f"{dur_sec // 60:02d}:{dur_sec % 60:02d}"
        self.time_label.setText(f"{pos_str} / {dur_str}")

    def _on_slider_moved(self, value):
        duration = self.player.duration()
        if duration > 0:
            pos = int(value * duration / 1000)
            self.player.setPosition(pos)


    def keyPressEvent(self, event):
        if event.key() == Qt.Key.Key_Space:
            self._toggle_playback()
            self.show_controls_temporarily()
        elif event.key() == Qt.Key.Key_Escape:
            if self.isFullScreen():
                self.toggle_fullscreen()
        elif event.key() == Qt.Key.Key_M:
            self._toggle_mute()
            self.show_controls_temporarily()
        elif event.key() == Qt.Key.Key_Left:
            new_pos = max(0, self.player.position() - 10000)
            self.player.setPosition(new_pos)
            self.show_controls_temporarily()
        elif event.key() == Qt.Key.Key_Right:
            duration = self.player.duration()
            new_pos = min(duration, self.player.position() + 10000) if duration > 0 else self.player.position() + 10000
            self.player.setPosition(new_pos)
            self.show_controls_temporarily()
        elif event.key() == Qt.Key.Key_Up:
            new_vol = min(100, self.volume_slider.value() + 5)
            self.volume_slider.setValue(new_vol)
            self.show_controls_temporarily()
        elif event.key() == Qt.Key.Key_Down:
            new_vol = max(0, self.volume_slider.value() - 5)
            self.volume_slider.setValue(new_vol)
            self.show_controls_temporarily()
        else:
            super().keyPressEvent(event)


    def closeEvent(self, event):
        self.controls_timer.stop()
        self.player.stop()
        self.player.setSource(QUrl())
        self.player.setVideoOutput(None)
        super().closeEvent(event)


class SingleVideoSubPlayer(QWidget):
    def __init__(self, filepath, parent_window):
        super().__init__(parent_window)
        self.parent_window = parent_window
        self.filepath = filepath
        
        layout = QVBoxLayout(self)
        layout.setContentsMargins(2, 2, 2, 2)
        layout.setSpacing(2)
        
        # Video Widget
        self.video_widget = DoubleClickVideoWidget(self)
        self.video_widget.double_clicked.connect(self.parent_window.toggle_fullscreen)
        self.video_widget.mouse_moved.connect(self.parent_window.show_controls_temporarily)
        layout.addWidget(self.video_widget, 1)
        
        # Controls panel
        self.controls_widget = QWidget(self)
        self.controls_widget.setFixedHeight(48)
        # Use self.window() (Qt's top-level window) instead of fragile 2-hop chain
        top_win = self.window() if hasattr(self, 'window') else (parent_window.parent_window if parent_window else None)
        is_dark = getattr(top_win, 'current_theme', 'dark') == 'dark' if top_win else True
        self.controls_widget.setStyleSheet(
            "background: #09071c; border-top: 1px solid rgba(167, 139, 250, 0.2);" if is_dark else
            "background: #f8fafc; border-top: 1px solid #e2e8f0;"
        )
        
        controls_layout = QVBoxLayout(self.controls_widget)
        controls_layout.setContentsMargins(6, 2, 6, 2)
        controls_layout.setSpacing(2)
        
        # Seek slider and time label row
        seek_layout = QHBoxLayout()
        seek_layout.setContentsMargins(0, 0, 0, 0)
        seek_layout.setSpacing(6)
        
        self.seek_slider = ClickToSeekSlider(Qt.Orientation.Horizontal, self.controls_widget)
        self.seek_slider.setRange(0, 1000)
        self.seek_slider.setCursor(Qt.CursorShape.PointingHandCursor)
        self.seek_slider.setFixedHeight(10)
        self.seek_slider.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        seek_layout.addWidget(self.seek_slider, 1)
        
        self.time_label = QLabel("00:00 / 00:00", self.controls_widget)
        self.time_label.setStyleSheet("font-size: 10px;")
        seek_layout.addWidget(self.time_label)
        controls_layout.addLayout(seek_layout)
        
        # Buttons row
        buttons_layout = QHBoxLayout()
        buttons_layout.setContentsMargins(0, 0, 0, 0)
        buttons_layout.setSpacing(6)
        
        self.btn_play = QPushButton(self.controls_widget)
        self.btn_play.setFixedSize(24, 24)
        self.btn_play.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_play.clicked.connect(self._toggle_playback)
        self.btn_play.setIcon(get_vector_icon('play', is_dark))
        self.btn_play.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        buttons_layout.addWidget(self.btn_play)
        
        self.btn_mute = QPushButton(self.controls_widget)
        self.btn_mute.setFixedSize(24, 24)
        self.btn_mute.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_mute.clicked.connect(self._toggle_mute)
        self.btn_mute.setIcon(get_vector_icon('unmute', is_dark))
        self.btn_mute.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        buttons_layout.addWidget(self.btn_mute)
        
        self.volume_slider = QSlider(Qt.Orientation.Horizontal, self.controls_widget)
        self.volume_slider.setRange(0, 100)
        self.volume_slider.setValue(70)
        self.volume_slider.setFixedWidth(60)
        self.volume_slider.setCursor(Qt.CursorShape.PointingHandCursor)
        self.volume_slider.valueChanged.connect(self._on_volume_changed)
        self.volume_slider.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        buttons_layout.addWidget(self.volume_slider)
        
        buttons_layout.addStretch()
        controls_layout.addLayout(buttons_layout)
        layout.addWidget(self.controls_widget)
        
        # Player setup
        self.player = QMediaPlayer(self)
        self.audio_output = QAudioOutput(self)
        self.player.setAudioOutput(self.audio_output)
        self.player.setVideoOutput(self.video_widget)
        
        # Connect signals
        self.player.positionChanged.connect(self._on_player_position_changed)
        self.player.durationChanged.connect(self._on_player_duration_changed)
        self.player.playbackStateChanged.connect(self._on_player_state_changed)
        self.seek_slider.valueChanged.connect(self._on_slider_moved)
        
        # Load and play
        self.player.setSource(QUrl.fromLocalFile(filepath))
        
        global_mute = getattr(self.window(), 'global_mute', False) if self.window() else False
        self.audio_output.setMuted(global_mute)
        self.audio_output.setVolume(0.7)
        self.btn_mute.setIcon(get_vector_icon('mute' if global_mute else 'unmute', is_dark))
        
        self.player.play()
        self.filepath = filepath

    def _toggle_playback(self):
        if self.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState:
            self.player.pause()
        else:
            self.player.play()

    def _toggle_mute(self):
        is_muted = self.audio_output.isMuted()
        self.audio_output.setMuted(not is_muted)
        is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark' if self.window() else True
        self.btn_mute.setIcon(get_vector_icon('mute' if not is_muted else 'unmute', is_dark))

    def _on_volume_changed(self, value):
        self.audio_output.setVolume(value / 100.0)
        if value > 0 and self.audio_output.isMuted():
            self._toggle_mute()

    def _on_player_state_changed(self, state):
        is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark' if self.window() else True
        if state == QMediaPlayer.PlaybackState.PlayingState:
            self.btn_play.setIcon(get_vector_icon('pause', is_dark))
        else:
            self.btn_play.setIcon(get_vector_icon('play', is_dark))

    def _on_player_position_changed(self, position):
        if not self.seek_slider.isSliderDown():
            self.seek_slider.blockSignals(True)
            duration = self.player.duration()
            if duration > 0:
                self.seek_slider.setValue(int(position * 1000 / duration))
            self.seek_slider.blockSignals(False)
        self._update_time_label(position, self.player.duration())

    def _on_player_duration_changed(self, duration):
        self._update_time_label(self.player.position(), duration)

    def _update_time_label(self, position, duration):
        pos_sec = position // 1000
        dur_sec = duration // 1000
        pos_str = f"{pos_sec // 60:02d}:{pos_sec % 60:02d}"
        dur_str = f"{dur_sec // 60:02d}:{dur_sec % 60:02d}"
        self.time_label.setText(f"{pos_str} / {dur_str}")

    def _on_slider_moved(self, value):
        duration = self.player.duration()
        if duration > 0:
            pos = int(value * duration / 1000)
            self.player.setPosition(pos)


class SplitVideoPlayerWindow(QMainWindow):
    def __init__(self, filepaths, parent=None):
        super().__init__(parent)
        self.parent_window = parent
        self.setWindowFlags(Qt.WindowType.Window)
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose)
        self.setWindowTitle("MediaFlow Player — Split View (4 Videos)")
        self.resize(1120, 630)
        
        self.hovered_sub_player = None
        
        # Controls auto-hide timer
        self.controls_timer = QTimer(self)
        self.controls_timer.setSingleShot(True)
        self.controls_timer.timeout.connect(self._hide_controls_if_fullscreen)
        
        central = QWidget(self)
        self.setCentralWidget(central)
        
        grid_layout = QGridLayout(central)
        grid_layout.setContentsMargins(2, 2, 2, 2)
        grid_layout.setSpacing(2)
        
        self.sub_players = []
        for i, path in enumerate(filepaths[:4]):
            sp = SingleVideoSubPlayer(path, self)
            self.sub_players.append(sp)
            row = i // 2
            col = i % 2
            grid_layout.addWidget(sp, row, col)
            
        self._enable_mouse_tracking_recursive(central)
        self.setMouseTracking(True)
        central.installEventFilter(self)
        for child in central.findChildren(QWidget):
            child.installEventFilter(self)

    def _enable_mouse_tracking_recursive(self, widget):
        widget.setMouseTracking(True)
        for child in widget.findChildren(QWidget):
            child.setMouseTracking(True)

    def eventFilter(self, watched, event):
        if event.type() in (QEvent.Type.MouseMove, QEvent.Type.MouseButtonPress):
            # Clear hovered_sub_player when no quadrant matches — was retaining
            # stale value, causing keyboard shortcuts (M, Up, Down) to affect
            # the wrong quadrant after the mouse left.
            self.hovered_sub_player = None
            for sp in self.sub_players:
                if sp.rect().contains(sp.mapFromGlobal(QCursor.pos())):
                    self.hovered_sub_player = sp
                    break
            self.show_controls_temporarily()
        elif event.type() == QEvent.Type.Wheel:
            target = self.hovered_sub_player if self.hovered_sub_player else (self.sub_players[0] if self.sub_players else None)
            if target:
                delta = event.angleDelta().y()
                if delta > 0:
                    new_vol = min(100, target.volume_slider.value() + 5)
                    target.volume_slider.setValue(new_vol)
                elif delta < 0:
                    new_vol = max(0, target.volume_slider.value() - 5)
                    target.volume_slider.setValue(new_vol)
            self.show_controls_temporarily()
            return True
        return super().eventFilter(watched, event)

    def mouseMoveEvent(self, event):
        super().mouseMoveEvent(event)
        self.show_controls_temporarily()

    def show_controls_temporarily(self):
        self.setCursor(Qt.CursorShape.ArrowCursor)
        for sp in self.sub_players:
            sp.controls_widget.show()
        if self.isFullScreen():
            self.controls_timer.start(2000)

    def _hide_controls_if_fullscreen(self):
        if self.isFullScreen():
            for sp in self.sub_players:
                sp.controls_widget.hide()
            self.setCursor(Qt.CursorShape.BlankCursor)

    def toggle_fullscreen(self):
        if self.isFullScreen():
            self.showNormal()
            for sp in self.sub_players:
                sp.controls_widget.show()
            self.setCursor(Qt.CursorShape.ArrowCursor)
            self.controls_timer.stop()
        else:
            self.showFullScreen()
            self.show_controls_temporarily()

    def keyPressEvent(self, event):
        if event.key() == Qt.Key.Key_Space:
            any_playing = any(sp.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState for sp in self.sub_players)
            for sp in self.sub_players:
                if any_playing:
                    sp.player.pause()
                else:
                    sp.player.play()
            self.show_controls_temporarily()
        elif event.key() == Qt.Key.Key_Escape:
            if self.isFullScreen():
                self.toggle_fullscreen()
        elif event.key() == Qt.Key.Key_M:
            target = self.hovered_sub_player
            if target:
                target._toggle_mute()
            else:
                for sp in self.sub_players:
                    sp._toggle_mute()
            self.show_controls_temporarily()
        elif event.key() == Qt.Key.Key_Left:
            for sp in self.sub_players:
                new_pos = max(0, sp.player.position() - 10000)
                sp.player.setPosition(new_pos)
            self.show_controls_temporarily()
        elif event.key() == Qt.Key.Key_Right:
            for sp in self.sub_players:
                duration = sp.player.duration()
                new_pos = min(duration, sp.player.position() + 10000) if duration > 0 else sp.player.position() + 10000
                sp.player.setPosition(new_pos)
            self.show_controls_temporarily()
        elif event.key() == Qt.Key.Key_Up:
            target = self.hovered_sub_player
            if target:
                new_vol = min(100, target.volume_slider.value() + 5)
                target.volume_slider.setValue(new_vol)
            else:
                for sp in self.sub_players:
                    new_vol = min(100, sp.volume_slider.value() + 5)
                    sp.volume_slider.setValue(new_vol)
            self.show_controls_temporarily()
        elif event.key() == Qt.Key.Key_Down:
            target = self.hovered_sub_player
            if target:
                new_vol = max(0, target.volume_slider.value() - 5)
                target.volume_slider.setValue(new_vol)
            else:
                for sp in self.sub_players:
                    new_vol = max(0, sp.volume_slider.value() - 5)
                    sp.volume_slider.setValue(new_vol)
            self.show_controls_temporarily()
        else:
            super().keyPressEvent(event)

    def closeEvent(self, event):
        self.controls_timer.stop()
        # Mirror NativeVideoPlayerWindow.closeEvent cleanup — was only stopping
        # the players, leaking file handles (esp. on Windows where backends keep
        # source files locked until the source is cleared).
        for sp in self.sub_players:
            sp.player.stop()
            sp.player.setSource(QUrl())
            sp.player.setVideoOutput(None)
        super().closeEvent(event)


class _ComparisonPane(QWidget):
    delete_requested = pyqtSignal(object)  # emits MediaInfo

    def __init__(self, info: MediaInfo, title_text: str, is_left: bool, parent_window=None):
        super().__init__(parent_window)
        self.info = info
        self.title_text = title_text
        self.is_left = is_left
        self.parent_window = parent_window

        self.player = None
        self.audio_output = None
        self.video_widget = None
        self.seek_slider = None
        self.time_label = None
        self.btn_play = None
        self.btn_mute = None
        self.volume_slider = None

        layout = QVBoxLayout(self)
        layout.setContentsMargins(8, 8, 8, 8)
        layout.setSpacing(8)

        # Header bar
        header = QHBoxLayout()
        title_lbl = QLabel(title_text)
        title_lbl.setStyleSheet("font-weight: 800; font-size: 13px; color: #a78bfa; text-transform: uppercase; letter-spacing: 1px;")
        header.addWidget(title_lbl)
        header.addStretch()

        btn_delete = QPushButton("🗑 Delete File")
        btn_delete.setObjectName("btnDelete")
        btn_delete.setCursor(Qt.CursorShape.PointingHandCursor)
        btn_delete.clicked.connect(lambda: self.delete_requested.emit(self.info))
        header.addWidget(btn_delete)
        layout.addLayout(header)

        # Media area
        if info.media_type == 'video':
            self.video_widget = DoubleClickVideoWidget(self)
            self.video_widget.setMinimumHeight(240)
            self.video_widget.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)
            self.video_widget.setStyleSheet("background: #000000; border-radius: 8px;")
            layout.addWidget(self.video_widget, 1)

            self.player = QMediaPlayer(self)
            self.audio_output = QAudioOutput(self)
            self.player.setAudioOutput(self.audio_output)
            self.player.setVideoOutput(self.video_widget)
            self.audio_output.setVolume(0.7)

            # Controls
            ctrls = QVBoxLayout()
            ctrls.setSpacing(4)
            
            slider_row = QHBoxLayout()
            self.seek_slider = ClickToSeekSlider(Qt.Orientation.Horizontal, self)
            self.seek_slider.setRange(0, 1000)
            self.seek_slider.sliderMoved.connect(self._on_seek)
            slider_row.addWidget(self.seek_slider, 1)

            self.time_label = QLabel("00:00 / 00:00")
            self.time_label.setStyleSheet("font-family: monospace; font-size: 10px; color: #a78bfa;")
            slider_row.addWidget(self.time_label)
            ctrls.addLayout(slider_row)

            btns_row = QHBoxLayout()
            self.btn_play = QPushButton("▶")
            self.btn_play.setFixedSize(28, 28)
            self.btn_play.setCursor(Qt.CursorShape.PointingHandCursor)
            self.btn_play.clicked.connect(self._toggle_playback)
            btns_row.addWidget(self.btn_play)

            self.btn_mute = QPushButton("🔊")
            self.btn_mute.setFixedSize(28, 28)
            self.btn_mute.setCursor(Qt.CursorShape.PointingHandCursor)
            self.btn_mute.clicked.connect(self._toggle_mute)
            btns_row.addWidget(self.btn_mute)

            self.volume_slider = QSlider(Qt.Orientation.Horizontal, self)
            self.volume_slider.setRange(0, 100)
            self.volume_slider.setValue(70)
            self.volume_slider.setFixedWidth(70)
            self.volume_slider.valueChanged.connect(self._on_volume_changed)
            btns_row.addWidget(self.volume_slider)
            btns_row.addStretch()
            ctrls.addLayout(btns_row)

            layout.addLayout(ctrls)

            self.player.positionChanged.connect(self._on_position_changed)
            self.player.durationChanged.connect(self._on_duration_changed)
            self.player.playbackStateChanged.connect(self._on_playback_state_changed)

            self.player.setSource(QUrl.fromLocalFile(info.filepath))
            self.player.pause()

        elif info.media_type == 'image':
            img_label = QLabel(self)
            img_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
            img_label.setMinimumHeight(240)
            img_label.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)
            pix = QPixmap(info.filepath)
            if not pix.isNull():
                img_label.setPixmap(pix.scaled(540, 360, Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation))
            else:
                img_label.setText("Failed to load image")
            img_label.setStyleSheet("background: #09071c; border-radius: 8px; border: 1px solid rgba(167, 139, 250, 0.15);")
            layout.addWidget(img_label, 1)

        else:
            other_box = QFrame(self)
            other_box.setMinimumHeight(200)
            other_box.setStyleSheet("background: #09071c; border-radius: 8px;")
            o_layout = QVBoxLayout(other_box)
            icon_lbl = QLabel("🎵" if info.media_type == 'audio' else "📄")
            icon_lbl.setAlignment(Qt.AlignmentFlag.AlignCenter)
            icon_lbl.setStyleSheet("font-size: 48px;")
            o_layout.addWidget(icon_lbl)
            name_lbl = QLabel(info.filename)
            name_lbl.setAlignment(Qt.AlignmentFlag.AlignCenter)
            name_lbl.setWordWrap(True)
            o_layout.addWidget(name_lbl)
            layout.addWidget(other_box, 1)

            if info.media_type == 'audio':
                self.player = QMediaPlayer(self)
                self.audio_output = QAudioOutput(self)
                self.player.setAudioOutput(self.audio_output)
                self.player.setSource(QUrl.fromLocalFile(info.filepath))

        # Metadata Card
        meta_group = QGroupBox("Properties")
        meta_group.setStyleSheet("QGroupBox { font-size: 11px; font-weight: bold; margin-top: 8px; } QGroupBox::title { color: #c4b5fd; }")
        self.meta_form = QFormLayout(meta_group)
        self.meta_form.setContentsMargins(10, 12, 10, 10)
        self.meta_form.setSpacing(6)

        self.lbl_filename = QLabel(info.filename)
        self.lbl_filename.setWordWrap(True)
        self.lbl_folder = QLabel(os.path.dirname(info.filepath))
        self.lbl_folder.setWordWrap(True)
        self.lbl_folder.setStyleSheet("color: #9ca3af; font-size: 10px;")

        res_str = f"{info.width} × {info.height}" if info.width and info.height else (getattr(info, 'resolution', '') or "—")
        self.lbl_res = QLabel(res_str)
        
        self.lbl_size = QLabel(format_size(getattr(info, 'size_bytes', 0)))
        dur_str = format_duration(info.duration_seconds) if getattr(info, 'duration_seconds', 0) > 0 else "—"
        self.lbl_dur = QLabel(dur_str)

        # NOTE: MediaInfo carries no codec/bitrate fields (deep metadata needs a
        # separate ffprobe call), so show file type instead of dead "—" fields.
        _, parsed_rating = parse_naming_format(info.filename)
        self.lbl_rating = QLabel(parsed_rating if parsed_rating else "Unrated")
        tags_list = getattr(info, 'tags', [])
        self.lbl_tags = QLabel(", ".join(tags_list) if tags_list else "—")

        self.meta_form.addRow("Filename:", self.lbl_filename)
        self.meta_form.addRow("Folder:", self.lbl_folder)
        self.meta_form.addRow("Resolution:", self.lbl_res)
        self.meta_form.addRow("File Size:", self.lbl_size)
        self.meta_form.addRow("Duration:", self.lbl_dur)
        self.meta_form.addRow("Rating:", self.lbl_rating)
        self.meta_form.addRow("Tags:", self.lbl_tags)

        layout.addWidget(meta_group)

    def highlight_diffs(self, other_info: MediaInfo):
        diff_style = "color: #fbbf24; font-weight: bold; background: rgba(245, 158, 11, 0.15); border-radius: 4px; padding: 1px 4px;"
        same_style = "color: #e0e0e0; font-weight: normal; background: transparent; padding: 1px 4px;"

        # Resolution
        my_res = (self.info.width, self.info.height)
        other_res = (other_info.width, other_info.height)
        self.lbl_res.setStyleSheet(diff_style if my_res != other_res and (my_res[0] or other_res[0]) else same_style)

        # Size
        self.lbl_size.setStyleSheet(diff_style if self.info.size_bytes != other_info.size_bytes else same_style)

        # Duration
        dur1 = round(getattr(self.info, 'duration_seconds', 0), 1)
        dur2 = round(getattr(other_info, 'duration_seconds', 0), 1)
        self.lbl_dur.setStyleSheet(diff_style if dur1 != dur2 and (dur1 > 0 or dur2 > 0) else same_style)

        # Rating (parsed from filename convention)
        _, r1 = parse_naming_format(self.info.filename)
        _, r2 = parse_naming_format(other_info.filename)
        r1 = r1 if r1 else 'Unrated'
        r2 = r2 if r2 else 'Unrated'
        self.lbl_rating.setStyleSheet(diff_style if r1 != r2 else same_style)

        # Tags
        t1 = set(getattr(self.info, 'tags', []))
        t2 = set(getattr(other_info, 'tags', []))
        self.lbl_tags.setStyleSheet(diff_style if t1 != t2 else same_style)

    def _toggle_playback(self):
        if not self.player: return
        if self.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState:
            self.player.pause()
            if self.parent_window and self.parent_window.is_synced():
                self.parent_window.sync_pause(self)
        else:
            self.player.play()
            if self.parent_window and self.parent_window.is_synced():
                self.parent_window.sync_play(self)

    def _toggle_mute(self):
        if not self.audio_output: return
        is_muted = self.audio_output.isMuted()
        self.audio_output.setMuted(not is_muted)
        self.btn_mute.setText("🔇" if not is_muted else "🔊")

    def _on_volume_changed(self, val):
        if self.audio_output:
            self.audio_output.setVolume(val / 100.0)

    def _on_seek(self, slider_pos):
        if not self.player: return
        dur = self.player.duration()
        if dur > 0:
            pos = int((slider_pos / 1000.0) * dur)
            self.player.setPosition(pos)
            if self.parent_window and self.parent_window.is_synced():
                self.parent_window.sync_seek(self, slider_pos)

    def _on_position_changed(self, pos):
        dur = self.player.duration() if self.player else 0
        if dur > 0 and self.seek_slider and not self.seek_slider.isSliderDown():
            self.seek_slider.setValue(int((pos / dur) * 1000))
        if self.time_label:
            self.time_label.setText(f"{self._format_ms(pos)} / {self._format_ms(dur)}")

    def _on_duration_changed(self, dur):
        pos = self.player.position() if self.player else 0
        if self.time_label:
            self.time_label.setText(f"{self._format_ms(pos)} / {self._format_ms(dur)}")

    def _on_playback_state_changed(self, state):
        if self.btn_play:
            self.btn_play.setText("⏸" if state == QMediaPlayer.PlaybackState.PlayingState else "▶")

    def _format_ms(self, ms: int) -> str:
        s = max(0, ms // 1000)
        return f"{s // 60:02d}:{s % 60:02d}"

    def cleanup(self):
        if self.player:
            self.player.stop()
            self.player.setSource(QUrl())
            self.player.setVideoOutput(None)


class ComparisonViewWindow(QMainWindow):
    def __init__(self, info_left: MediaInfo, info_right: MediaInfo, parent_tab=None, parent=None):
        super().__init__(parent)
        self.info_left = info_left
        self.info_right = info_right
        self.parent_tab = parent_tab

        self.setWindowTitle(f"MediaFlow — Comparison: {info_left.filename} vs {info_right.filename}")
        self.resize(1200, 750)
        self.setMinimumSize(900, 600)
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose)

        central = QWidget(self)
        self.setCentralWidget(central)
        root_layout = QVBoxLayout(central)
        root_layout.setContentsMargins(12, 12, 12, 12)
        root_layout.setSpacing(10)

        # Top Action Bar
        top_bar = QHBoxLayout()
        top_bar.setSpacing(10)

        self.btn_sync = QPushButton("🔗 Synced Playback")
        self.btn_sync.setObjectName("btnWatch")
        self.btn_sync.setCheckable(True)
        is_both_videos = (info_left.media_type == 'video' and info_right.media_type == 'video')
        self.btn_sync.setChecked(is_both_videos)
        self.btn_sync.setEnabled(is_both_videos)
        top_bar.addWidget(self.btn_sync)

        self.btn_swap = QPushButton("🔄 Swap Sides")
        self.btn_swap.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_swap.clicked.connect(self._swap_sides)
        top_bar.addWidget(self.btn_swap)

        top_bar.addStretch()

        btn_keep_both = QPushButton("✓ Keep Both (Close)")
        btn_keep_both.setCursor(Qt.CursorShape.PointingHandCursor)
        btn_keep_both.clicked.connect(self.close)
        top_bar.addWidget(btn_keep_both)

        root_layout.addLayout(top_bar)

        # Splitter with Left and Right Panes
        self.splitter = QSplitter(Qt.Orientation.Horizontal, self)
        self.splitter.setChildrenCollapsible(False)

        self.pane_left = _ComparisonPane(self.info_left, "Left File", is_left=True, parent_window=self)
        self.pane_right = _ComparisonPane(self.info_right, "Right File", is_left=False, parent_window=self)

        self.pane_left.delete_requested.connect(self._delete_file)
        self.pane_right.delete_requested.connect(self._delete_file)

        self.splitter.addWidget(self.pane_left)
        self.splitter.addWidget(self.pane_right)
        self.splitter.setSizes([600, 600])

        root_layout.addWidget(self.splitter, 1)

        # Highlight metadata differences
        self.pane_left.highlight_diffs(self.info_right)
        self.pane_right.highlight_diffs(self.info_left)

    def is_synced(self) -> bool:
        return self.btn_sync.isChecked()

    def sync_play(self, source_pane: _ComparisonPane):
        target = self.pane_right if source_pane is self.pane_left else self.pane_left
        if target.player and target.player.playbackState() != QMediaPlayer.PlaybackState.PlayingState:
            target.player.play()

    def sync_pause(self, source_pane: _ComparisonPane):
        target = self.pane_right if source_pane is self.pane_left else self.pane_left
        if target.player and target.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState:
            target.player.pause()

    def sync_seek(self, source_pane: _ComparisonPane, slider_pos: int):
        target = self.pane_right if source_pane is self.pane_left else self.pane_left
        if target.player:
            dur = target.player.duration()
            if dur > 0:
                pos = int((slider_pos / 1000.0) * dur)
                target.player.setPosition(pos)

    def _swap_sides(self):
        self.pane_left.cleanup()
        self.pane_right.cleanup()

        self.info_left, self.info_right = self.info_right, self.info_left
        self.setWindowTitle(f"MediaFlow — Comparison: {self.info_left.filename} vs {self.info_right.filename}")

        # Replace panes
        self.pane_left.deleteLater()
        self.pane_right.deleteLater()

        self.pane_left = _ComparisonPane(self.info_left, "Left File", is_left=True, parent_window=self)
        self.pane_right = _ComparisonPane(self.info_right, "Right File", is_left=False, parent_window=self)

        self.pane_left.delete_requested.connect(self._delete_file)
        self.pane_right.delete_requested.connect(self._delete_file)

        self.splitter.addWidget(self.pane_left)
        self.splitter.addWidget(self.pane_right)
        self.splitter.setSizes([600, 600])

        self.pane_left.highlight_diffs(self.info_right)
        self.pane_right.highlight_diffs(self.info_left)

    def _delete_file(self, info: MediaInfo):
        ret = QMessageBox.question(
            self,
            "Confirm Delete",
            f"Are you sure you want to send this file to the Recycle Bin?\n\n{info.filename}",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No
        )
        if ret != QMessageBox.StandardButton.Yes:
            return

        # Cleanup players first to release locks
        self.pane_left.cleanup()
        self.pane_right.cleanup()

        success = send_to_recycle_bin(info.filepath)
        if success:
            if self.parent_tab:
                # Find row in table and remove
                for row in range(self.parent_tab.table.rowCount()):
                    row_info = self.parent_tab._get_row_info(row)
                    if row_info and row_info.filepath == info.filepath:
                        self.parent_tab._remove_row_from_list(row)
                        break
                if hasattr(self.parent_tab, '_show_toast'):
                    self.parent_tab._show_toast(f"Deleted {info.filename}", 'success')
            self.close()
        else:
            QMessageBox.warning(self, "Delete Failed", f"Could not send {info.filename} to the Recycle Bin.")

    def closeEvent(self, event):
        self.pane_left.cleanup()
        self.pane_right.cleanup()
        super().closeEvent(event)


# ─── Main Window Tab ─────────────────────────────────────────────────────────────

from PyQt6.QtCore import QRunnable, pyqtSlot, QObject


class _ThumbnailWorkerSignals(QObject):
    """Holds Qt signals for a thumbnail worker — QRunnable can't emit signals directly."""
    finished = pyqtSignal(int, object, object, object)  # row, info, label, QImage


class _ThumbnailRunnable(QRunnable):
    """Background thumbnail generator. Runs generate_thumbnail() off the GUI
    thread and emits the result for the main thread to apply to the QLabel."""
    def __init__(self, row: int, info, label, parent_tab):
        super().__init__()
        self.row = row
        self.info = info
        self.label = label
        self.parent_tab = parent_tab
        self.signals = _ThumbnailWorkerSignals()
        # Auto-delete so the runnable is cleaned up after run() finishes
        self.setAutoDelete(True)

    @pyqtSlot()
    def run(self):
        try:
            tw_, th_ = self.parent_tab._thumb_dims()
            image = generate_thumbnail(self.info.filepath, self.info.media_type, width=tw_, height=th_)
        except Exception as e:
            logger.warning("Thumbnail generation failed for %s: %s", self.info.filepath, e)
            image = None
        # Emit signal — Qt cross-thread connection will queue it on the main thread
        try:
            self.signals.finished.emit(self.row, self.info, self.label, image)
        except RuntimeError:
            # Parent tab or label was destroyed before we finished — silently drop
            pass


class _MediaInfoWorkerSignals(QObject):
    ready = pyqtSignal(object)  # MediaInfo or None


class _MediaInfoRunnable(QRunnable):
    """Extracts MediaInfo metadata for one file OFF the GUI thread.

    Used by watch mode: constructing MediaInfo can block on cv2/ffprobe for
    seconds, which previously froze the whole UI when new files appeared.
    """
    def __init__(self, filepath: str, media_type: str, parent_tab):
        super().__init__()
        self.filepath = filepath
        self.media_type = media_type
        self.parent_tab = parent_tab
        self.signals = _MediaInfoWorkerSignals()
        self.setAutoDelete(True)

    @pyqtSlot()
    def run(self):
        info = None
        try:
            info = MediaInfo(self.filepath, self.media_type)
        except Exception as e:
            logger.warning("Watch metadata extraction failed for %s: %s", self.filepath, e)
        try:
            self.signals.ready.emit(info)
        except RuntimeError:
            pass

class MediaTab(QWidget):
    COL_THUMB      = 0
    COL_STATUS     = 1
    COL_FILENAME   = 2
    COL_SIZE       = 3
    COL_RESOLUTION = 4
    COL_DURATION   = 5
    COL_ARTIST     = 6
    COL_RATING     = 7
    COL_TAGS       = 8
    COL_PREVIEW    = 9
    COL_DATE_MOD   = 10   # optional â€” hidden by default, toggle via header menu
    COL_DATE_CREATED = 11 # optional â€” hidden by default
    NUM_COLS       = 12
    HEADERS = ["Preview", "Status", "File Name", "Size", "Resolution", "Duration", "Name", "Rating", "Tags", "New Name Preview", "Modified", "Created"]

    def __init__(self, media_type: str, smart_query: str = "", is_smart_folder: bool = False):
        super().__init__()
        self.media_type = media_type
        self.smart_query = smart_query
        self.is_smart_folder = is_smart_folder
        self.directories: list[str] = []
        self.default_player: str = ""
        self.media_infos: list[MediaInfo] = []
        self.filtered_rows: set[int] = set()
        self.scanner_thread: ScannerThread | None = None
        self._updating_table = False
        self._saved_file_data = {}
        self._rename_history: list[dict] = []
        self._redo_history: list[dict] = []
        self._exclude_patterns: list[str] = []
        self._syncing_selection = False
        self._exclude_timer = QTimer(self)  # parent prevents crash on tab close
        self._exclude_timer.setSingleShot(True)
        self._exclude_timer.setInterval(500)
        self._exclude_timer.timeout.connect(self._apply_exclude_and_scan)
        # Debounce timer for search field (was running full table scan per keystroke)
        self._filter_timer = QTimer(self)
        self._filter_timer.setSingleShot(True)
        self._filter_timer.setInterval(250)
        self._filter_timer.timeout.connect(self._apply_filter)
        
        self.hover_timer = QTimer(self)
        self.hover_timer.setSingleShot(True)
        self.hover_timer.setInterval(1500)
        self.hover_timer.timeout.connect(self._on_hover_timeout)
        self._hovered_info = None
        self._hovered_global_rect = None
        self._hovered_grid_info = None
        self._dismissed_info = None
        
        self._watch_timer = QTimer(self)
        self._watch_timer.setInterval(3000)
        self._watch_timer.timeout.connect(self._check_for_changes)
        self._watch_enabled = False
        self._known_files = {}
        
        self._search_history = []
        self._stats_dirty = True
        
        self._build_ui()
        if self.is_smart_folder: self.btn_load.setEnabled(True)

    def _build_ui(self):
        root_layout = QVBoxLayout(self)
        root_layout.setContentsMargins(24, 24, 24, 12)
        root_layout.setSpacing(12)
        control_panel = QFrame()
        control_panel.setObjectName("controlPanel")
        ctrl_layout = QVBoxLayout(control_panel)
        ctrl_layout.setContentsMargins(12, 10, 12, 10)
        ctrl_layout.setSpacing(10)
        row1_layout = QHBoxLayout()
        row1_layout.setContentsMargins(0, 0, 0, 0)
        row1_layout.setSpacing(12)
        self.btn_load = QPushButton("Sync Files")
        self.btn_load.setObjectName("btnLoadFiles")
        self.btn_load.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_load.clicked.connect(self._on_load_files)
        self.btn_load.setEnabled(False)
        self.btn_load.setIconSize(QSize(16, 16))
        self.btn_stop = QPushButton("Stop Loading")
        self.btn_stop.setObjectName("btnStopLoading")
        self.btn_stop.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_stop.clicked.connect(self._on_stop_loading)
        self.btn_stop.setVisible(False)
        self.btn_stop.setIconSize(QSize(16, 16))
        self.btn_clear = QPushButton("Clear List")
        self.btn_clear.setObjectName("btnClearAll")
        self.btn_clear.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_clear.clicked.connect(self._on_clear)
        self.btn_clear.setVisible(False)
        self.btn_clear.setIconSize(QSize(16, 16))
        
        self.btn_watch = QPushButton("👁️ Watch")
        self.btn_watch.setObjectName("btnWatch")
        self.btn_watch.setCheckable(True)
        self.btn_watch.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_watch.toggled.connect(self._toggle_watch)
        
        row1_layout.addWidget(self.btn_load)
        row1_layout.addWidget(self.btn_stop)
        row1_layout.addWidget(self.btn_clear)
        row1_layout.addWidget(self.btn_watch)
        row1_layout.addStretch()
        self.btn_view_mode = QPushButton("Grid View")
        self.btn_view_mode.setObjectName("btnViewMode")
        self.btn_view_mode.setCheckable(True)
        self.btn_view_mode.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_view_mode.clicked.connect(self._toggle_view_mode)
        self.btn_view_mode.setIconSize(QSize(16, 16))
        self.btn_toggle_preview = QPushButton("Preview")
        self.btn_toggle_preview.setObjectName("btnTogglePreview")
        self.btn_toggle_preview.setCheckable(True)
        self.btn_toggle_preview.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_toggle_preview.clicked.connect(self._toggle_preview)
        self.btn_toggle_preview.setIconSize(QSize(16, 16))
        self.btn_toggle_stats = QPushButton("📊 Stats")
        self.btn_toggle_stats.setObjectName("btnToggleStats")
        self.btn_toggle_stats.setCheckable(True)
        self.btn_toggle_stats.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_toggle_stats.clicked.connect(self._toggle_stats)
        row1_layout.addWidget(self.btn_view_mode)
        row1_layout.addWidget(self.btn_toggle_preview)
        row1_layout.addWidget(self.btn_toggle_stats)
        row2_layout = QHBoxLayout()
        row2_layout.setContentsMargins(0, 0, 0, 0)
        row2_layout.setSpacing(12)
        self.stat_total = self._make_stat_card("0", "TOTAL FILES")
        self.stat_valid = self._make_stat_card("0", "VALID")
        self.stat_unsupported = self._make_stat_card("0", "UNSUPPORTED")
        self.stat_size = self._make_stat_card("0 B", "TOTAL SIZE")
        row2_layout.addWidget(self.stat_total)
        row2_layout.addWidget(self.stat_valid)
        row2_layout.addWidget(self.stat_unsupported)
        row2_layout.addWidget(self.stat_size)
        row2_layout.addStretch()
        ctrl_layout.addLayout(row1_layout)
        ctrl_layout.addLayout(row2_layout)
        root_layout.addWidget(control_panel)
        filter_panel = QFrame()
        filter_panel.setObjectName("filterPanel")
        filter_layout = QHBoxLayout(filter_panel)
        filter_layout.setContentsMargins(12, 8, 12, 8)
        filter_layout.setSpacing(12)
        filter_layout.addWidget(QLabel("🔍"))
        self.search_input = QComboBox()
        self.search_input.setObjectName("searchComboBox")
        self.search_input.setEditable(True)
        self.search_input.setInsertPolicy(QComboBox.InsertPolicy.NoInsert)
        self.search_input.lineEdit().setPlaceholderText("Filter by filename, name, or rating...")
        self.search_input.lineEdit().textChanged.connect(self._on_filter_changed)
        self.search_input.lineEdit().returnPressed.connect(self._on_search_return_pressed)
        self.search_input.activated.connect(self._on_search_history_activated)
        self.search_input.setMaxVisibleItems(15)
        self.search_input.text = lambda: self.search_input.currentText()
        filter_layout.addWidget(self.search_input, 1)
        if not self.is_smart_folder:
            self.btn_save_search = QPushButton("")
            self.btn_save_search.setObjectName("btnSaveSearch")
            self.btn_save_search.setFixedSize(28, 28)
            self.btn_save_search.setToolTip("Save search filter as Smart Folder")
            self.btn_save_search.setCursor(Qt.CursorShape.PointingHandCursor)
            self.btn_save_search.clicked.connect(self._on_save_search_clicked)
            self.btn_save_search.setIconSize(QSize(16, 16))
            filter_layout.addWidget(self.btn_save_search)
        filter_layout.addWidget(QLabel("⛔"))
        self.exclude_input = QLineEdit()
        self.exclude_input.setPlaceholderText("Exclude patterns (comma-separated, e.g., *sample*, temp*)")
        self.exclude_input.textChanged.connect(self._on_exclude_changed)
        filter_layout.addWidget(self.exclude_input, 1)
        
        self.btn_advanced_filter = QPushButton("▼ Advanced")
        self.btn_advanced_filter.setObjectName("btnAdvancedFilter")
        self.btn_advanced_filter.setCheckable(True)
        self.btn_advanced_filter.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_advanced_filter.toggled.connect(lambda checked: self.advanced_filter_panel.setVisible(checked))
        filter_layout.addWidget(self.btn_advanced_filter)
        
        root_layout.addWidget(filter_panel)
        
        self.advanced_filter_panel = QFrame()
        self.advanced_filter_panel.setObjectName("advancedFilterPanel")
        self.advanced_filter_panel.setVisible(False)
        advanced_layout = QHBoxLayout(self.advanced_filter_panel)
        advanced_layout.setContentsMargins(12, 8, 12, 8)
        advanced_layout.setSpacing(12)
        
        self.adv_res = QComboBox()
        self.adv_res.addItems(["All Resolutions", "8K (4320p+)", "4K (2160p)", "1440p", "1080p", "720p", "480p", "Below 480p"])
        self.adv_res.currentIndexChanged.connect(lambda: self._filter_timer.start())
        advanced_layout.addWidget(QLabel("Resolution:"))
        advanced_layout.addWidget(self.adv_res)
        
        self.adv_dur_min = QSpinBox()
        self.adv_dur_min.setRange(0, 99999)
        self.adv_dur_min.valueChanged.connect(lambda: self._filter_timer.start())
        self.adv_dur_max = QSpinBox()
        self.adv_dur_max.setRange(0, 99999)
        self.adv_dur_max.setValue(0)
        self.adv_dur_max.valueChanged.connect(lambda: self._filter_timer.start())
        advanced_layout.addWidget(QLabel("Duration (s):"))
        advanced_layout.addWidget(self.adv_dur_min)
        advanced_layout.addWidget(QLabel("-"))
        advanced_layout.addWidget(self.adv_dur_max)

        # Modified-date range — 'Any' sentinels sit at the min/max bounds
        advanced_layout.addWidget(QLabel("Modified:"))
        self.adv_date_from = QDateEdit()
        self.adv_date_from.setCalendarPopup(True)
        self.adv_date_from.setDisplayFormat("yyyy-MM-dd")
        self.adv_date_from.setMinimumDate(QDate(2000, 1, 1))
        self.adv_date_from.setMaximumDate(QDate(9999, 12, 31))
        self.adv_date_from.setDate(self.adv_date_from.minimumDate())
        self.adv_date_from.setSpecialValueText("Any")
        self.adv_date_from.setToolTip("Only show files modified on/after this date ('Any' disables)")
        self.adv_date_from.dateChanged.connect(lambda: self._filter_timer.start())
        advanced_layout.addWidget(self.adv_date_from)
        advanced_layout.addWidget(QLabel("\u2192"))
        self.adv_date_to = QDateEdit()
        self.adv_date_to.setCalendarPopup(True)
        self.adv_date_to.setDisplayFormat("yyyy-MM-dd")
        self.adv_date_to.setMinimumDate(QDate(2000, 1, 1))
        self.adv_date_to.setMaximumDate(QDate(9999, 12, 31))
        self.adv_date_to.setDate(self.adv_date_to.maximumDate())
        self.adv_date_to.setSpecialValueText("Any")
        self.adv_date_to.setToolTip("Only show files modified on/before this date ('Any' disables)")
        self.adv_date_to.dateChanged.connect(lambda: self._filter_timer.start())
        advanced_layout.addWidget(self.adv_date_to)
        
        self.adv_size_min = QDoubleSpinBox()
        self.adv_size_min.setRange(0, 99999)
        self.adv_size_min.valueChanged.connect(lambda: self._filter_timer.start())
        self.adv_size_max = QDoubleSpinBox()
        self.adv_size_max.setRange(0, 99999)
        self.adv_size_max.setValue(0)
        self.adv_size_max.valueChanged.connect(lambda: self._filter_timer.start())
        self.adv_size_unit = QComboBox()
        self.adv_size_unit.addItems(["MB", "KB", "GB"])
        self.adv_size_unit.currentIndexChanged.connect(lambda: self._filter_timer.start())
        advanced_layout.addWidget(QLabel("Size:"))
        advanced_layout.addWidget(self.adv_size_min)
        advanced_layout.addWidget(QLabel("-"))
        advanced_layout.addWidget(self.adv_size_max)
        advanced_layout.addWidget(self.adv_size_unit)
        
        self.adv_rating = QComboBox()
        self.adv_rating.addItems(["All Ratings", "Unrated"] + [f"≥{i}" for i in range(1, 11)])
        self.adv_rating.currentIndexChanged.connect(lambda: self._filter_timer.start())
        advanced_layout.addWidget(QLabel("Rating:"))
        advanced_layout.addWidget(self.adv_rating)
        
        self.btn_clear_adv = QPushButton("Clear")
        self.btn_clear_adv.clicked.connect(self._clear_advanced_filters)
        advanced_layout.addWidget(self.btn_clear_adv)
        advanced_layout.addStretch()
        
        root_layout.addWidget(self.advanced_filter_panel)
        self.table = QTableWidget()
        self.table.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        self.table.setColumnCount(self.NUM_COLS)
        self.table.setHorizontalHeaderLabels(self.HEADERS)
        if self.media_type == 'image': self.table.setColumnHidden(self.COL_DURATION, True)
        elif self.media_type == 'audio': self.table.setColumnHidden(self.COL_RESOLUTION, True)
        elif self.media_type == 'pdf':
            self.table.setColumnHidden(self.COL_DURATION, True)
            self.table.setColumnHidden(self.COL_RESOLUTION, True)
        self.table.setAlternatingRowColors(False)
        self.table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.table.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)
        self.table.verticalHeader().setVisible(False)
        self.table.setShowGrid(False)
        self.table.horizontalHeader().setStretchLastSection(True)
        self.table.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.table.customContextMenuRequested.connect(self._on_table_context_menu)
        header = self.table.horizontalHeader()
        header.setSectionResizeMode(self.COL_THUMB, QHeaderView.ResizeMode.Fixed)
        self.table.setColumnWidth(self.COL_THUMB, 130)
        header.setSectionResizeMode(self.COL_STATUS, QHeaderView.ResizeMode.Fixed)
        self.table.setColumnWidth(self.COL_STATUS, 90)
        header.setSectionResizeMode(self.COL_FILENAME, QHeaderView.ResizeMode.Interactive)
        self.table.setColumnWidth(self.COL_FILENAME, 300)
        header.setSectionResizeMode(self.COL_SIZE, QHeaderView.ResizeMode.Fixed)
        self.table.setColumnWidth(self.COL_SIZE, 95)
        header.setSectionResizeMode(self.COL_RESOLUTION, QHeaderView.ResizeMode.Fixed)
        self.table.setColumnWidth(self.COL_RESOLUTION, 110)
        header.setSectionResizeMode(self.COL_DURATION, QHeaderView.ResizeMode.Fixed)
        self.table.setColumnWidth(self.COL_DURATION, 120)
        header.setSectionResizeMode(self.COL_ARTIST, QHeaderView.ResizeMode.Fixed)
        self.table.setColumnWidth(self.COL_ARTIST, 160)
        header.setSectionResizeMode(self.COL_RATING, QHeaderView.ResizeMode.Fixed)
        self.table.setColumnWidth(self.COL_RATING, 80)
        header.setSectionResizeMode(self.COL_TAGS, QHeaderView.ResizeMode.Interactive)
        self.table.setColumnWidth(self.COL_TAGS, 180)
        header.setSectionResizeMode(self.COL_PREVIEW, QHeaderView.ResizeMode.Interactive)
        self.table.setColumnWidth(self.COL_PREVIEW, 300)
        header.setSectionResizeMode(self.COL_DATE_MOD, QHeaderView.ResizeMode.Interactive)
        self.table.setColumnWidth(self.COL_DATE_MOD, 140)
        header.setSectionResizeMode(self.COL_DATE_CREATED, QHeaderView.ResizeMode.Interactive)
        self.table.setColumnWidth(self.COL_DATE_CREATED, 140)
        # Optional metadata columns â€” off until the user enables them
        self.table.setColumnHidden(self.COL_DATE_MOD, True)
        self.table.setColumnHidden(self.COL_DATE_CREATED, True)
        header.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        header.customContextMenuRequested.connect(self._on_header_context_menu)
        self.table.setItemDelegateForColumn(self.COL_ARTIST, NoTextDelegate(self))
        self.table.setItemDelegateForColumn(self.COL_RATING, NoTextDelegate(self))
        self.table.setItemDelegateForColumn(self.COL_TAGS, NoTextDelegate(self))
        self.table.setItemDelegateForColumn(self.COL_STATUS, StatusBadgeDelegate(self))
        self.table.setVerticalScrollMode(QAbstractItemView.ScrollMode.ScrollPerPixel)
        self.table.setHorizontalScrollMode(QAbstractItemView.ScrollMode.ScrollPerPixel)
        self.table.setEditTriggers(QAbstractItemView.EditTrigger.SelectedClicked | QAbstractItemView.EditTrigger.EditKeyPressed)
        self.table.cellDoubleClicked.connect(self._on_cell_double_clicked)
        self.table.itemChanged.connect(self._on_item_changed)
        self.table.setSortingEnabled(True)
        self.table.itemSelectionChanged.connect(self._on_selection_changed)
        self.table.verticalScrollBar().valueChanged.connect(self._load_visible_widgets)
        self.table.verticalScrollBar().rangeChanged.connect(lambda min_val, max_val: self._load_visible_widgets())
        header.sectionClicked.connect(lambda: QTimer.singleShot(50, self._load_visible_widgets))
        self.view_stack = QStackedWidget()
        self.view_stack.addWidget(self.table)
        self.grid_view = QListWidget()
        self.grid_view.setViewMode(QListWidget.ViewMode.IconMode)
        self.grid_view.setResizeMode(QListWidget.ResizeMode.Adjust)
        self.grid_view.setSpacing(16)
        # Thumbnail box width — Appearance slider adjusts; drives table rows,
        # grid icons and worker-generated pixmaps alike.
        self.thumb_size = 130
        _ts_w, _ts_h = self.thumb_size, int(round(self.thumb_size * 0.567))
        self.grid_view.setIconSize(QSize(_ts_w, _ts_h))
        self.grid_view.setGridSize(QSize(_ts_w + 20, _ts_h + 50))
        self.grid_view.setWordWrap(True)
        self.grid_view.itemSelectionChanged.connect(self._on_grid_selection_changed)
        self.grid_view.itemDoubleClicked.connect(self._on_grid_item_double_clicked)
        self.grid_view.setContextMenuPolicy(Qt.ContextMenuPolicy.CustomContextMenu)
        self.grid_view.customContextMenuRequested.connect(self._on_grid_context_menu)
        self.grid_view.setMouseTracking(True)
        self.grid_view.viewport().installEventFilter(self)
        self.view_stack.addWidget(self.grid_view)
        self.content_layout = QHBoxLayout()
        self.content_layout.setContentsMargins(0, 0, 0, 0)
        self.content_layout.setSpacing(12)
        self.content_layout.addWidget(self.view_stack, 1)
        self._build_preview_pane()
        self._build_stats_panel()
        self.content_layout.addWidget(self.preview_panel)
        self.content_layout.addWidget(self.stats_panel)
        root_layout.addLayout(self.content_layout, 1)
        bottom_layout = QVBoxLayout()
        bottom_layout.setContentsMargins(0, 0, 0, 0)
        bottom_layout.setSpacing(8)
        bottom_row1 = QHBoxLayout()
        bottom_row1.setContentsMargins(0, 0, 0, 0)
        bottom_row1.setSpacing(12)
        self.status_label = QLabel("Ready")
        self.status_label.setObjectName("statusLabelReady")
        self.btn_undo = QPushButton("Undo Last")
        self.btn_undo.setObjectName("btnUndo")
        self.btn_undo.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_undo.clicked.connect(self._on_undo_rename)
        self.btn_undo.setEnabled(False)
        self.btn_undo.setIconSize(QSize(16, 16))
        self.btn_redo = QPushButton("Redo Last")
        self.btn_redo.setObjectName("btnRedo")
        self.btn_redo.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_redo.clicked.connect(self._on_redo_rename)
        self.btn_redo.setEnabled(False)
        self.btn_redo.setIconSize(QSize(16, 16))
        bottom_row1.addWidget(self.status_label, 1)
        bottom_row1.addWidget(self.btn_undo)
        bottom_row1.addWidget(self.btn_redo)
        # Live selection summary ("N selected · size") for quick bulk sanity
        self.sel_stats_label = QLabel("")
        self.sel_stats_label.setObjectName("folderPathLabel")
        bottom_row1.addWidget(self.sel_stats_label)
        bottom_row2 = QHBoxLayout()
        bottom_row2.setContentsMargins(0, 0, 0, 0)
        bottom_row2.setSpacing(8)
        self.btn_find_dupes = QPushButton("Find Dupes")
        self.btn_find_dupes.setObjectName("btnFindDuplicates")
        self.btn_find_dupes.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_find_dupes.setEnabled(False)
        self.btn_find_dupes.setIconSize(QSize(16, 16))
        self.btn_find_dupes.setToolTip("Scan the current list for exact (MD5) or visual (pHash) duplicates")
        self.dupe_menu = QMenu(self)
        self.header_menu = QMenu(self)
        action_exact = QAction("Exact Duplicates (MD5)", self)
        action_exact.triggered.connect(self._find_exact_duplicates)
        self.dupe_menu.addAction(action_exact)
        action_visual = QAction("Visual Duplicates (pHash)", self)
        action_visual.triggered.connect(self._find_visual_duplicates)
        self.dupe_menu.addAction(action_visual)
        self.btn_find_dupes.setMenu(self.dupe_menu)
        self.btn_batch_edit = QPushButton("Batch Edit")
        self.btn_batch_edit.setObjectName("btnBatchEdit")
        self.btn_batch_edit.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_batch_edit.clicked.connect(self._on_batch_edit)
        self.btn_batch_edit.setEnabled(False)
        self.btn_batch_edit.setToolTip("Bulk-edit Name/Rating for selected files")
        self.btn_batch_edit.setIconSize(QSize(16, 16))
        self.btn_batch_tag = QPushButton("🏷️ Batch Tag")
        self.btn_batch_tag.setObjectName("btnBatchTag")
        self.btn_batch_tag.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_batch_tag.clicked.connect(self._on_batch_tag)
        self.btn_batch_tag.setEnabled(False)
        self.btn_relocate = QPushButton("Relocate")
        self.btn_relocate.setObjectName("btnBatchEdit")
        self.btn_relocate.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_relocate.clicked.connect(self._on_smart_relocate)
        self.btn_relocate.setEnabled(False)
        self.btn_relocate.setIconSize(QSize(16, 16))
        self.btn_relocate.setToolTip("Move selected files into folders built from a path template")
        self.btn_delete = QPushButton("Delete")
        self.btn_delete.setObjectName("btnDelete")
        self.btn_delete.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_delete.clicked.connect(self._on_delete_selected)
        self.btn_delete.setEnabled(False)
        self.btn_delete.setToolTip("Send selected files to the Recycle Bin")
        self.btn_delete.setIconSize(QSize(16, 16))
        self.btn_process = QPushButton("Process All")  # full label lives in tooltip — old text forced the bottom bar to overflow at min window width
        self.btn_process.setObjectName("btnProcessAll")
        self.btn_process.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_process.setEnabled(False)
        self.btn_process.clicked.connect(self._on_process_all)
        self.btn_process.setToolTip("Process all ready files — applies the naming template and renames them")
        self.btn_process.setIconSize(QSize(18, 18))
        bottom_row2.addWidget(self.btn_find_dupes)
        bottom_row2.addWidget(self.btn_batch_edit)
        bottom_row2.addWidget(self.btn_batch_tag)
        bottom_row2.addWidget(self.btn_relocate)
        bottom_row2.addWidget(self.btn_delete)
        bottom_row2.addStretch()
        bottom_row2.addWidget(self.btn_process)
        bottom_layout.addLayout(bottom_row1)
        bottom_layout.addLayout(bottom_row2)
        root_layout.addLayout(bottom_layout)

    def _make_stat_card(self, value: str, label: str) -> QFrame:
        card = QFrame()
        card.setObjectName("statsPanel")
        card.setFixedSize(140, 46)
        layout = QVBoxLayout(card)
        layout.setContentsMargins(12, 4, 12, 4)
        layout.setSpacing(0)
        val = QLabel(value)
        val.setObjectName("statValue")
        val.setAlignment(Qt.AlignmentFlag.AlignLeft)
        lbl = QLabel(label)
        lbl.setObjectName("statLabel")
        lbl.setAlignment(Qt.AlignmentFlag.AlignLeft)
        layout.addWidget(val)
        layout.addWidget(lbl)
        card._value_label = val
        return card

    def _style_rating_combo(self, combo: QComboBox, text: str):
        is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark'
        if text in ["1", "2", "3"]:
            if is_dark:
                combo.setStyleSheet("QComboBox { background-color: rgba(239, 68, 68, 0.15); border: 1px solid rgba(239, 68, 68, 0.4); border-radius: 6px; color: #f87171; font-weight: bold; padding-left: 8px; } QComboBox::drop-down { border: none; width: 16px; } QComboBox::down-arrow { border-top: 4px solid #f87171; border-left: 3px solid transparent; border-right: 3px solid transparent; }")
            else:
                combo.setStyleSheet("QComboBox { background-color: rgba(239, 68, 68, 0.10); border: 1px solid rgba(239, 68, 68, 0.3); border-radius: 6px; color: #dc2626; font-weight: bold; padding-left: 8px; } QComboBox::drop-down { border: none; width: 16px; } QComboBox::down-arrow { border-top: 4px solid #dc2626; border-left: 3px solid transparent; border-right: 3px solid transparent; }")
        elif text in ["4", "5", "6", "7"]:
            if is_dark:
                combo.setStyleSheet("QComboBox { background-color: rgba(234, 179, 8, 0.15); border: 1px solid rgba(234, 179, 8, 0.4); border-radius: 6px; color: #facc15; font-weight: bold; padding-left: 8px; } QComboBox::drop-down { border: none; width: 16px; } QComboBox::down-arrow { border-top: 4px solid #facc15; border-left: 3px solid transparent; border-right: 3px solid transparent; }")
            else:
                combo.setStyleSheet("QComboBox { background-color: rgba(234, 179, 8, 0.10); border: 1px solid rgba(234, 179, 8, 0.3); border-radius: 6px; color: #b45309; font-weight: bold; padding-left: 8px; } QComboBox::drop-down { border: none; width: 16px; } QComboBox::down-arrow { border-top: 4px solid #b45309; border-left: 3px solid transparent; border-right: 3px solid transparent; }")
        elif text in ["8", "9", "10"]:
            if is_dark:
                combo.setStyleSheet("QComboBox { background-color: rgba(16, 185, 129, 0.15); border: 1px solid rgba(16, 185, 129, 0.4); border-radius: 6px; color: #34d399; font-weight: bold; padding-left: 8px; } QComboBox::drop-down { border: none; width: 16px; } QComboBox::down-arrow { border-top: 4px solid #34d399; border-left: 3px solid transparent; border-right: 3px solid transparent; }")
            else:
                combo.setStyleSheet("QComboBox { background-color: rgba(16, 185, 129, 0.10); border: 1px solid rgba(16, 185, 129, 0.3); border-radius: 6px; color: #059669; font-weight: bold; padding-left: 8px; } QComboBox::drop-down { border: none; width: 16px; } QComboBox::down-arrow { border-top: 4px solid #059669; border-left: 3px solid transparent; border-right: 3px solid transparent; }")
        else:
            if is_dark:
                combo.setStyleSheet("QComboBox { background-color: rgba(45, 40, 90, 0.5); border: 1px solid rgba(167, 139, 250, 0.2); border-radius: 6px; color: #9ca3af; padding-left: 8px; } QComboBox::drop-down { border: none; width: 16px; } QComboBox::down-arrow { border-top: 4px solid #a78bfa; border-left: 3px solid transparent; border-right: 3px solid transparent; }")
            else:
                combo.setStyleSheet("QComboBox { background-color: #f8fafc; border: 1px solid #cbd5e1; border-radius: 6px; color: #64748b; padding-left: 8px; } QComboBox::drop-down { border: none; width: 16px; } QComboBox::down-arrow { border-top: 4px solid #6366f1; border-left: 3px solid transparent; border-right: 3px solid transparent; }")

    def _on_search_return_pressed(self):
        query = self.search_input.currentText().strip()
        if query:
            self._save_search_to_history(query)
        self._apply_filter()

    def _save_search_to_history(self, query: str):
        query = query.strip()
        if not query: return
        if query in self._search_history:
            self._search_history.remove(query)
        self._search_history.insert(0, query)
        self._search_history = self._search_history[:20]
        self._refresh_search_combobox_items()

    def _refresh_search_combobox_items(self):
        if not hasattr(self, 'search_input') or not isinstance(self.search_input, QComboBox):
            return
        curr = self.search_input.currentText()
        self.search_input.blockSignals(True)
        self.search_input.clear()
        if self._search_history:
            for item in self._search_history:
                self.search_input.addItem(item)
            self.search_input.insertSeparator(self.search_input.count())
            self.search_input.addItem("✕ Clear Search History")
        self.search_input.setEditText(curr)
        self.search_input.blockSignals(False)

    def _on_search_history_activated(self, index: int):
        text = self.search_input.itemText(index)
        if text == "✕ Clear Search History":
            self._search_history.clear()
            self._refresh_search_combobox_items()
            self._show_toast("Search history cleared", 'info')
            return
        self.search_input.setEditText(text)
        self._save_search_to_history(text)
        self._apply_filter()

    def _on_filter_changed(self, text: str):
        # Debounce: kick off the timer; if the user keeps typing, the timer
        # keeps resetting. Only when they pause for 250ms does _apply_filter run.
        self._filter_timer.start()

    def _apply_filter(self):
        text = self.search_input.currentText() if hasattr(self.search_input, 'currentText') else self.search_input.text()
        search_lower = text.lower().strip()
        self.filtered_rows.clear()
        for row in range(self.table.rowCount()):
            info = self._get_row_info(row)
            if not info: continue
            if self.is_smart_folder:
                if not matches_query(info, self.smart_query):
                    self.table.setRowHidden(row, True)
                    if hasattr(info, 'grid_item') and info.grid_item: info.grid_item.setHidden(True)
                    continue
            filename = self.table.item(row, self.COL_FILENAME).text().lower()
            artist_item = self.table.item(row, self.COL_ARTIST)
            artist = artist_item.text().lower() if artist_item else ""
            rating_item = self.table.item(row, self.COL_RATING)
            rating = rating_item.text().lower() if rating_item else ""
            preview_item = self.table.item(row, self.COL_PREVIEW)
            preview = preview_item.text().lower() if preview_item else ""
            if not search_lower or matches_query(info, search_lower, preview):
                self.filtered_rows.add(row)
                self.table.setRowHidden(row, False)
                if hasattr(info, 'grid_item') and info.grid_item: info.grid_item.setHidden(False)
            else:
                self.table.setRowHidden(row, True)
                if hasattr(info, 'grid_item') and info.grid_item: info.grid_item.setHidden(True)
        self._apply_advanced_filters()
        self._update_stats()
        self._load_visible_widgets()

    def _clear_advanced_filters(self):
        self.adv_res.setCurrentIndex(0)
        self.adv_date_from.setDate(self.adv_date_from.minimumDate())
        self.adv_date_to.setDate(self.adv_date_to.maximumDate())
        self.adv_dur_min.setValue(0)
        self.adv_dur_max.setValue(0)
        self.adv_size_min.setValue(0)
        self.adv_size_max.setValue(0)
        self.adv_rating.setCurrentIndex(0)
        self._filter_timer.start()

    def _apply_advanced_filters(self):
        # Quick check if any advanced filters are active
        res_idx = self.adv_res.currentIndex()
        dur_min = self.adv_dur_min.value()
        dur_max = self.adv_dur_max.value()
        sz_min = self.adv_size_min.value()
        sz_max = self.adv_size_max.value()
        rat_idx = self.adv_rating.currentIndex()
        date_from = self.adv_date_from.date()
        date_to = self.adv_date_to.date()
        date_active = (date_from != self.adv_date_from.minimumDate()
                       or date_to != self.adv_date_to.maximumDate())

        if res_idx == 0 and dur_min == 0 and dur_max == 0 and sz_min == 0 and sz_max == 0 \
                and rat_idx <= 0 and not date_active:
            return

        sz_multiplier = 1024 * 1024
        if self.adv_size_unit.currentText() == "KB":
            sz_multiplier = 1024
        elif self.adv_size_unit.currentText() == "GB":
            sz_multiplier = 1024 * 1024 * 1024

        rows_to_remove = []
        for row in self.filtered_rows:
            info = self._get_row_info(row)
            if not info: continue
            
            keep = True
            
            # Resolution
            if res_idx > 0 and info.height > 0:
                h = info.height
                if res_idx == 1 and h < 4320: keep = False # 8K+
                elif res_idx == 2 and (h < 2160 or h >= 4320): keep = False # 4K
                elif res_idx == 3 and (h < 1440 or h >= 2160): keep = False # 1440p
                elif res_idx == 4 and (h < 1080 or h >= 1440): keep = False # 1080p
                elif res_idx == 5 and (h < 720 or h >= 1080): keep = False # 720p
                elif res_idx == 6 and (h < 480 or h >= 720): keep = False # 480p
                elif res_idx == 7 and h >= 480: keep = False # Below 480p

            # Duration
            if keep and dur_max > 0:
                d = info.duration_seconds
                if d < dur_min or d > dur_max: keep = False
            elif keep and dur_min > 0:
                if info.duration_seconds < dur_min: keep = False

            # Modified date range (local time, matches os.stat display)
            if keep and date_active:
                m_ts = float(getattr(info, 'mtime', 0) or 0)
                if m_ts > 0:
                    m_date = QDateTime.fromSecsSinceEpoch(int(m_ts)).date()
                    if m_date < date_from or m_date > date_to:
                        keep = False

            # Size
            if keep and sz_max > 0:
                s = info.size_bytes
                if s < sz_min * sz_multiplier or s > sz_max * sz_multiplier: keep = False
            elif keep and sz_min > 0:
                if info.size_bytes < sz_min * sz_multiplier: keep = False

            # Rating
            if keep and rat_idx > 0:
                rating_widget = self.table.cellWidget(row, self.COL_RATING)
                if rating_widget:
                    r_text = rating_widget.currentText()
                else:
                    rating_item = self.table.item(row, self.COL_RATING)
                    r_text = rating_item.text().strip() if rating_item else ""
                
                if rat_idx == 1: # Unrated
                    if r_text and r_text != "—":
                        keep = False
                else:
                    thresh = rat_idx - 1
                    try:
                        if not r_text or r_text == "—" or float(r_text) < thresh:
                            keep = False
                    except ValueError:
                        keep = False

            if not keep:
                rows_to_remove.append(row)
                self.table.setRowHidden(row, True)
                if hasattr(info, 'grid_item') and info.grid_item: info.grid_item.setHidden(True)

        for row in rows_to_remove:
            self.filtered_rows.remove(row)

    def _focus_search(self):
        """Helper for keyboard shortcut — safely focuses the search input."""
        if hasattr(self, 'search_input') and self.search_input:
            self.search_input.setFocus()
            if hasattr(self.search_input, 'lineEdit') and self.search_input.lineEdit():
                self.search_input.lineEdit().selectAll()
            elif hasattr(self.search_input, 'selectAll'):
                self.search_input.selectAll()

    def _on_save_search_clicked(self):
        query = self.search_input.currentText().strip() if hasattr(self.search_input, 'currentText') else self.search_input.text().strip()
        if not query:
            QMessageBox.warning(self, "Empty Filter", "Please type a search query first to save it as a Smart Folder."); return
        main_win = self.window()
        if hasattr(main_win, 'create_smart_folder_from_query'):
            main_win.create_smart_folder_from_query(self.media_type, query)

    def _on_exclude_changed(self, text: str):
        self._exclude_timer.start()

    def _apply_exclude_and_scan(self):
        text = self.exclude_input.text()
        patterns = [p.strip() for p in text.split(',') if p.strip()]
        self._exclude_patterns = patterns
        if self.directories: self._start_scan(self.directories)

    def _should_exclude(self, filepath: str) -> bool:
        if not self._exclude_patterns: return False
        filename = os.path.basename(filepath).lower()
        for pattern in self._exclude_patterns:
            pattern = pattern.lower().strip()
            if not pattern: continue
            if pattern.startswith('*') and pattern.endswith('*'):
                if pattern[1:-1] in filename: return True
            elif pattern.startswith('*'):
                if filename.endswith(pattern[1:]): return True
            elif pattern.endswith('*'):
                if filename.startswith(pattern[:-1]): return True
            elif pattern in filename: return True
        return False

    def _start_scan(self, folders: list[str], force_full: bool = False):
        old = getattr(self, 'scanner_thread', None)
        if old is not None and old.isRunning():
            old.requestInterruption()
            # NOTE: no quit() here — ScannerThread.run() has no event loop; it
            # polls isInterruptionRequested() instead.
            if not old.wait(2000):
                # Still busy (blocked in cv2/ffprobe work). Detach its signals
                # so late emissions can't corrupt the new scan, keep a Python
                # reference so Qt never destroys a running QThread, and clean
                # it up automatically once run() actually returns.
                for sig in (old.progress, old.file_found, old.scan_complete, old.status_update):
                    try:
                        sig.disconnect()
                    except TypeError:
                        pass
                if not hasattr(self, '_orphaned_scanners'):
                    self._orphaned_scanners = []
                self._orphaned_scanners.append(old)
                old.finished.connect(old.deleteLater)
                
        was_watch = getattr(self, '_watch_enabled', False)
        self._on_clear(keep_watch=was_watch)
        self._watch_enabled = was_watch
        self.directories = folders
        if self.directories: self.btn_load.setEnabled(True)
        else: self.btn_load.setEnabled(False)
        self.btn_load.setVisible(False)
        self.btn_stop.setVisible(True)
        self.btn_process.setEnabled(False)
        self.btn_relocate.setEnabled(False)
        self.btn_find_dupes.setEnabled(False)
        self.btn_undo.setEnabled(False)
        self.btn_redo.setEnabled(False)
        self.progress_bar.setVisible(True)
        self.progress_bar.setValue(0)
        self.status_label.setText("Scanning…")
        self.table.setSortingEnabled(False)
        self.table.setUpdatesEnabled(False)
        self.grid_view.setUpdatesEnabled(False)
        self.scanner_thread = ScannerThread(folders, self.media_type, self._exclude_patterns, force_full=force_full)
        self.scanner_thread.progress.connect(self._on_scan_progress)
        self.scanner_thread.file_found.connect(self._on_file_found)
        self.scanner_thread.scan_complete.connect(self._on_scan_complete)
        self.scanner_thread.status_update.connect(lambda msg: self.status_label.setText(msg))
        self.scanner_thread.start()

    def _toggle_watch(self, checked: bool):
        if checked and not self.directories:
            self.btn_watch.setChecked(False)
            self._show_toast("Please add/select folders first before enabling watch.", 'warning')
            return
        self._watch_enabled = checked
        if checked:
            self._known_files = {os.path.normcase(os.path.normpath(info.filepath)): info.filepath for info in self.media_infos}
            self._watch_timer.start(3000)
            self._show_toast(f"👁️ Watching {len(self.directories)} folder(s)...", 'success')
        else:
            self._watch_timer.stop()
            self._show_toast("Watch folder disabled.", 'info')

    def _check_for_changes(self):
        if not getattr(self, '_watch_enabled', False) or not self.directories:
            return
        if getattr(self, 'scanner_thread', None) is not None and self.scanner_thread.isRunning():
            return
        # Renames/deletes moved files to new paths since the last tick —
        # rebuild the baseline so old paths don't count as "removed" while
        # their new paths are already known (prevents duplicate rows).
        if getattr(self, '_known_files_dirty', False):
            self._known_files = {os.path.normcase(os.path.normpath(info.filepath)): info.filepath for info in self.media_infos}
            self._known_files_dirty = False
            
        valid_exts = get_extensions_for_type(self.media_type)
        current_files = {}

        for directory in self.directories:
            if not os.path.isdir(directory): continue
            stack = [directory]
            while stack:
                current_dir = stack.pop()
                try:
                    for entry in os.scandir(current_dir):
                        try:
                            if entry.is_dir(follow_symlinks=False):
                                stack.append(entry.path)
                            elif entry.is_file(follow_symlinks=False):
                                ext = os.path.splitext(entry.name)[1].lower()
                                # Match ScannerThread semantics: known extensions
                                # plus extensionless files only ('all' already
                                # unions every supported set).
                                if ext == '' or ext in valid_exts:
                                    full_path = os.path.normpath(entry.path)
                                    norm_case = os.path.normcase(full_path)
                                    if not self._should_exclude(full_path):
                                        current_files[norm_case] = full_path
                        except Exception:
                            pass
                except Exception:
                    pass

        if not hasattr(self, '_known_files') or not isinstance(self._known_files, dict):
            self._known_files = {os.path.normcase(os.path.normpath(info.filepath)): info.filepath for info in self.media_infos}

        current_keys = set(current_files.keys())
        known_keys = set(self._known_files.keys())

        added_keys = current_keys - known_keys
        removed_keys = known_keys - current_keys

        if not added_keys and not removed_keys:
            return

        # 1. Handle removals safely by table row lookup
        if removed_keys:
            rows_to_remove = []
            for r in range(self.table.rowCount()):
                row_info = self._get_row_info(r)
                if row_info and os.path.normcase(os.path.normpath(row_info.filepath)) in removed_keys:
                    rows_to_remove.append(r)

            was_sorting = self.table.isSortingEnabled()
            self.table.setSortingEnabled(False)
            for r in sorted(rows_to_remove, reverse=True):
                self._remove_row_from_list(r)
            self.table.setSortingEnabled(was_sorting)

        # 2. Handle additions — extract metadata OFF the GUI thread (each
        # MediaInfo can block on cv2/ffprobe for seconds); results are batched
        # through _flush_pending_watch_infos() so the UI stays responsive.
        if added_keys:
            if not hasattr(self, '_watch_info_pool'):
                self._watch_info_pool = QThreadPool(self)
                self._watch_info_pool.setMaxThreadCount(2)
            for k in added_keys:
                runnable = _MediaInfoRunnable(current_files[k], self.media_type, self)
                # Cross-thread queued connection — handler runs on main thread
                runnable.signals.ready.connect(self._on_watch_info_ready)
                self._watch_info_pool.start(runnable)

        self._known_files = current_files
        if added_keys or removed_keys:
            self.status_label.setText(f"Watch: +{len(added_keys)} added, -{len(removed_keys)} removed ({len(self.media_infos)} files total)")
            self._show_toast(f"👁️ Watch: +{len(added_keys)} added, -{len(removed_keys)} removed", 'info')

    def _on_watch_info_ready(self, info):
        """Called on the main thread when a watch-mode MediaInfo worker finishes."""
        if info is None:
            return
        if not hasattr(self, '_pending_watch_infos'):
            self._pending_watch_infos = []
        self._pending_watch_infos.append(info)
        if not hasattr(self, '_watch_flush_timer'):
            self._watch_flush_timer = QTimer(self)
            self._watch_flush_timer.setSingleShot(True)
            self._watch_flush_timer.setInterval(250)
            self._watch_flush_timer.timeout.connect(self._flush_pending_watch_infos)
        self._watch_flush_timer.start()

    def _flush_pending_watch_infos(self):
        pending = getattr(self, '_pending_watch_infos', [])
        if not pending:
            return
        self._pending_watch_infos = []
        was_sorting = self.table.isSortingEnabled()
        self.table.setSortingEnabled(False)
        try:
            for info in pending:
                if info.is_valid:
                    row = self.table.rowCount()
                    self._on_file_found(info)
                    # Apply persisted artist/rating/tags for files restored from config
                    self._apply_saved_file_data_to_row(row)
        finally:
            self.table.setSortingEnabled(was_sorting)
        self._apply_filter()
        self._update_stats()
        self._load_visible_widgets()

    def _on_clear(self, keep_watch: bool = False):
        if not keep_watch:
            self._watch_timer.stop()
            self._watch_enabled = False
            if hasattr(self, 'btn_watch'):
                self.btn_watch.setChecked(False)
        self._known_files = {}
        # Invalidate rename history — undoing across a cleared/reloaded list
        # would rename files from the previous session on disk.
        self._rename_history.clear()
        self._redo_history.clear()
        self._release_file_locks()
        self.table.setSortingEnabled(False)
        self.table.setUpdatesEnabled(True)
        self.grid_view.setUpdatesEnabled(True)
        self.table.setRowCount(0)
        self.grid_view.clear()
        self.media_infos.clear()
        self.filtered_rows.clear()
        if self.directories: self.btn_load.setEnabled(True)
        else: self.btn_load.setEnabled(False)
        self.btn_clear.setVisible(False)
        self.btn_load.setVisible(True)
        self.btn_stop.setVisible(False)
        self.btn_process.setEnabled(False)
        self.btn_batch_edit.setEnabled(False)
        self.btn_batch_tag.setEnabled(False)
        self.btn_relocate.setEnabled(False)
        self.btn_find_dupes.setEnabled(False)
        self.btn_undo.setEnabled(False)
        self.btn_redo.setEnabled(False)
        self.progress_bar.setVisible(False)
        self.status_label.setText("Ready")
        self.status_label.setObjectName("statusLabelReady")
        self._update_stats()

    def _on_load_files(self):
        if self.is_smart_folder:
            main_win = self.window()
            dirs = []; exclude = []
            if self.media_type in ['video', 'all'] and hasattr(main_win, 'video_tab'):
                dirs.extend(main_win.video_tab.directories); exclude.extend(main_win.video_tab._exclude_patterns)
            if self.media_type in ['image', 'all'] and hasattr(main_win, 'image_tab'):
                dirs.extend(main_win.image_tab.directories); exclude.extend(main_win.image_tab._exclude_patterns)
            if self.media_type in ['audio', 'all'] and hasattr(main_win, 'audio_tab'):
                dirs.extend(main_win.audio_tab.directories); exclude.extend(main_win.audio_tab._exclude_patterns)
            self.directories = list(set(dirs))
            self._exclude_patterns = list(set(exclude))
            if self.directories: self._start_scan(self.directories, force_full=True)
        else:
            if self.directories: self._start_scan(self.directories, force_full=True)

    def _on_stop_loading(self):
        if self.scanner_thread and self.scanner_thread.isRunning():
            self.scanner_thread.requestInterruption()
            self.status_label.setText("Stopping scan…")

    def set_directories(self, directories: list[str]):
        self.directories = directories
        if self.directories: self.btn_load.setEnabled(True)
        else: self.btn_load.setEnabled(False)

    def update_directories(self, directories: list[str]):
        self.directories = directories
        if self.directories:
            self.btn_load.setEnabled(True)
            self._start_scan(self.directories)
        else:
            self.btn_load.setEnabled(False)
            self._on_clear()

    def _show_toast(self, message, toast_type='info'):
        if hasattr(self.window(), 'show_toast'):
            self.window().show_toast(message, toast_type)


    def get_state_dict(self) -> dict:
        state = {
            'exclude_patterns': self._exclude_patterns,
            'search_history': self._search_history,
            'files': {},
            'column_visibility': {}
        }
        for col in range(self.NUM_COLS):
            state['column_visibility'][str(col)] = not self.table.isColumnHidden(col)
        for row in range(self.table.rowCount()):
            info = self._get_row_info(row)
            if not info: continue
            artist_widget = self.table.cellWidget(row, self.COL_ARTIST)
            rating_widget = self.table.cellWidget(row, self.COL_RATING)
            tags_widget = self.table.cellWidget(row, self.COL_TAGS)
            
            artist = artist_widget.text().strip() if artist_widget else (self.table.item(row, self.COL_ARTIST).text().strip() if self.table.item(row, self.COL_ARTIST) else "")
            rating = rating_widget.currentText() if rating_widget else (self.table.item(row, self.COL_RATING).text().strip() if self.table.item(row, self.COL_RATING) else "—")
            
            if tags_widget:
                tags_str = tags_widget.text().strip()
                tags = [t.strip() for t in tags_str.split(',') if t.strip()]
            else:
                tags_item = self.table.item(row, self.COL_TAGS)
                tags_str = tags_item.text().strip() if tags_item else ""
                tags = [t.strip() for t in tags_str.split(',') if t.strip()] if tags_str else getattr(info, 'tags', [])
                
            if artist or rating != "—" or tags:
                state['files'][os.path.normpath(info.filepath)] = {'artist': artist, 'rating': rating, 'tags': tags}
        return state

    def load_state_dict(self, state: dict):
        if not state: return
        self._exclude_patterns = state.get('exclude_patterns', [])
        if self._exclude_patterns and hasattr(self, 'exclude_input'):
            self.exclude_input.setText(', '.join(self._exclude_patterns))
        self._search_history = state.get('search_history', [])
        self._refresh_search_combobox_items()
        col_visibility = state.get('column_visibility', {})
        for col_str, is_visible in col_visibility.items():
            col = int(col_str)
            if 0 <= col < self.NUM_COLS:
                self.table.setColumnHidden(col, not is_visible)
        raw_files = state.get('files', {})
        self._saved_file_data = {os.path.normpath(k): v for k, v in raw_files.items()}

    def _on_scan_progress(self, current: int, total: int):
        if total > 0:
            self.progress_bar.setMaximum(total)
            self.progress_bar.setValue(current)
            self.progress_bar.setFormat(f"Processing {current}/{total}…")

    def _on_file_found(self, info: MediaInfo):
        self._updating_table = True
        self.media_infos.append(info)
        row = self.table.rowCount()
        self.table.insertRow(row)
        grid_item = QListWidgetItem(info.filename)
        grid_item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
        grid_item.setData(Qt.ItemDataRole.UserRole, info)
        if not info.is_valid: grid_item.setToolTip(info.error_message)
        pw, ph = self._thumb_dims()
        placeholder_pix = QPixmap(pw, ph)
        placeholder_pix.fill(QColor("#1e1b4b"))
        with QPainter(placeholder_pix) as painter:
            painter.setRenderHint(QPainter.RenderHint.Antialiasing)
            painter.setFont(QFont(BASE_FONT_FAMILY, 20))
            painter.setPen(QColor("#a78bfa"))
            emoji = "🎬" if info.media_type == 'video' else ("🎵" if info.media_type == 'audio' else ("📄" if info.media_type == 'pdf' else "🖼️"))
            painter.drawText(QRect(0, 0, pw, ph), Qt.AlignmentFlag.AlignCenter, emoji)
        grid_item.setIcon(QIcon(placeholder_pix))
        info.grid_item = grid_item
        search_text = (self.search_input.currentText() if hasattr(self.search_input, 'currentText') else self.search_input.text()).lower().strip()
        is_hidden = False
        if self.is_smart_folder and not matches_query(info, self.smart_query): is_hidden = True
        elif search_text and not matches_query(info, search_text): is_hidden = True
        if is_hidden:
            grid_item.setHidden(True)
            self.table.setRowHidden(row, True)
        self.grid_view.addItem(grid_item)
        if info.is_valid:
            thumb_label = QLabel()
            thumb_label.setObjectName("thumbnailLabel")
            thumb_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
            emoji_txt = "🎬" if info.media_type == 'video' else ("🎵" if info.media_type == 'audio' else ("📄" if info.media_type == 'pdf' else "🖼️"))
            thumb_label.setProperty("emoji", emoji_txt)
            thumb_label.setText(emoji_txt)
            lw, lh = self._thumb_dims()
            thumb_label.setFixedSize(lw, lh)
            self.table.setCellWidget(row, self.COL_THUMB, thumb_label)
            if info.media_type == 'video':
                thumb_label.setProperty("media_info", info)
                thumb_label.installEventFilter(self)
        else:
            empty = QLabel("—")
            empty.setAlignment(Qt.AlignmentFlag.AlignCenter)
            self.table.setCellWidget(row, self.COL_THUMB, empty)
        is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark'
        if info.is_valid:
            status_item = NumericTableWidgetItem("✓ Valid")
            status_item.setForeground(QColor("#34d399") if is_dark else QColor("#059669"))
        else:
            status_item = NumericTableWidgetItem("⚠ Unsupported")
            status_item.setForeground(QColor("#f87171") if is_dark else QColor("#dc2626"))
            status_item.setToolTip(info.error_message)
        status_item.setFlags(status_item.flags() & ~Qt.ItemFlag.ItemIsEditable)
        status_item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
        self.table.setItem(row, self.COL_STATUS, status_item)
        
        meta_font = QFont(BASE_FONT_FAMILY, 9, QFont.Weight.Light)
        bold_meta_font = QFont(BASE_FONT_FAMILY, 9, QFont.Weight.Bold)
        
        fname_item = NumericTableWidgetItem(info.filename)
        fname_item.setData(Qt.ItemDataRole.UserRole, info)
        fname_item.setToolTip(info.filepath)
        fname_item.setFont(QFont(BASE_FONT_FAMILY, 10, QFont.Weight.Bold))
        fname_item.setForeground(QColor("#c4b5fd") if is_dark else QColor("#1e3a8a"))
        self.table.setItem(row, self.COL_FILENAME, fname_item)
        
        size_item = NumericTableWidgetItem(info.size_formatted, sort_key=info.size_bytes)
        size_item.setFlags(size_item.flags() & ~Qt.ItemFlag.ItemIsEditable)
        size_item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
        size_item.setFont(bold_meta_font)
        size_item.setForeground(QColor("#9ca3af") if is_dark else QColor("#64748b"))
        self.table.setItem(row, self.COL_SIZE, size_item)
        
        if info.is_valid:
            res_text = f"{info.width}×{info.height}\n({info.resolution_tag})"
            res_key = info.height
        else:
            res_text = "—"
            res_key = -1
        res_item = NumericTableWidgetItem(res_text, sort_key=res_key)
        res_item.setFlags(res_item.flags() & ~Qt.ItemFlag.ItemIsEditable)
        res_item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
        res_item.setFont(bold_meta_font)
        res_item.setForeground(QColor("#9ca3af") if is_dark else QColor("#64748b"))
        self.table.setItem(row, self.COL_RESOLUTION, res_item)
        
        if info.is_valid:
            dur_text = info.duration_formatted
            dur_key = info.duration_seconds
        else:
            dur_text = "—"
            dur_key = -1.0
        dur_item = NumericTableWidgetItem(dur_text, sort_key=dur_key)
        dur_item.setFlags(dur_item.flags() & ~Qt.ItemFlag.ItemIsEditable)
        dur_item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
        dur_item.setFont(bold_meta_font)
        dur_item.setForeground(QColor("#9ca3af") if is_dark else QColor("#64748b"))
        self.table.setItem(row, self.COL_DURATION, dur_item)

        for col, attr in ((self.COL_DATE_MOD, 'mtime'), (self.COL_DATE_CREATED, 'ctime')):
            ts = float(getattr(info, attr, 0) or 0)
            dt_item = NumericTableWidgetItem(format_timestamp(ts), sort_key=ts)
            dt_item.setFlags(dt_item.flags() & ~Qt.ItemFlag.ItemIsEditable)
            dt_item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
            dt_item.setFont(bold_meta_font)
            dt_item.setForeground(QColor("#9ca3af") if is_dark else QColor("#64748b"))
            self.table.setItem(row, col, dt_item)
        parsed_artist, parsed_rating = parse_naming_format(info.filename)
        is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark'
        text_color = QColor("#e0e0e0") if is_dark else QColor("#0f172a")
        
        if info.is_valid:
            artist_item = NumericTableWidgetItem(parsed_artist or "")
            artist_item.setFont(meta_font)
            artist_item.setForeground(text_color)
            self.table.setItem(row, self.COL_ARTIST, artist_item)
            
            rating_val = parsed_rating or "—"
            rating_item = NumericTableWidgetItem(rating_val, sort_key=int(parsed_rating) if parsed_rating else 0)
            rating_item.setFont(meta_font)
            rating_item.setForeground(text_color)
            rating_item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
            self.table.setItem(row, self.COL_RATING, rating_item)
            
            tags_str = ", ".join(info.tags) if hasattr(info, 'tags') and info.tags else ""
            tags_item = NumericTableWidgetItem(tags_str)
            tags_item.setFont(meta_font)
            tags_item.setForeground(text_color)
            self.table.setItem(row, self.COL_TAGS, tags_item)
        else:
            empty_artist = NumericTableWidgetItem("—")
            empty_artist.setFlags(empty_artist.flags() & ~Qt.ItemFlag.ItemIsEditable)
            empty_artist.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
            self.table.setItem(row, self.COL_ARTIST, empty_artist)
            
            empty_rating = NumericTableWidgetItem("—", sort_key=-1)
            empty_rating.setFlags(empty_rating.flags() & ~Qt.ItemFlag.ItemIsEditable)
            empty_rating.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
            self.table.setItem(row, self.COL_RATING, empty_rating)
            
            empty_tags = NumericTableWidgetItem("—")
            empty_tags.setFlags(empty_tags.flags() & ~Qt.ItemFlag.ItemIsEditable)
            empty_tags.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
            self.table.setItem(row, self.COL_TAGS, empty_tags)

        preview_item = NumericTableWidgetItem("—")
        preview_item.setFlags(preview_item.flags() & ~Qt.ItemFlag.ItemIsEditable)
        preview_item.setForeground(QColor("#7c7c9a"))
        self.table.setItem(row, self.COL_PREVIEW, preview_item)
        _, row_h = self._thumb_dims()
        self.table.setRowHeight(row, row_h + 8)
        self._updating_table = False
        self._update_row_preview(row)

    def _generate_thumbnail_async(self, row: int, info: MediaInfo, label: QLabel):
        """Schedules thumbnail generation on a background thread to avoid
        freezing the GUI. Uses a per-tab QThreadPool to limit concurrency."""
        if row >= self.table.rowCount(): return
        # Lazily create a per-tab thread pool (limits concurrency to 4 workers
        # so we don't spawn hundreds of threads for hundreds of files).
        if not hasattr(self, '_thumb_pool'):
            from PyQt6.QtCore import QThreadPool
            self._thumb_pool = QThreadPool(self)
            self._thumb_pool.setMaxThreadCount(4)
        runnable = _ThumbnailRunnable(row, info, label, self)
        # Cross-thread queued connection — _on_thumbnail_ready runs on main thread
        runnable.signals.finished.connect(self._on_thumbnail_ready)
        self._thumb_pool.start(runnable)

    def _on_thumbnail_ready(self, row: int, info: MediaInfo, label: QLabel, image):
        """Called on the main thread when a thumbnail worker finishes."""
        if row >= self.table.rowCount(): return
        # Worker threads produce QImage; QPixmap is only safe on the GUI thread
        pixmap = QPixmap.fromImage(image) if image is not None else None
        if pixmap and not pixmap.isNull():
            current_widget = self.table.cellWidget(row, self.COL_THUMB)
            if current_widget is label:
                cw, ch = self._thumb_dims()
                label.setFixedSize(cw, ch)
                label.setPixmap(pixmap.scaled(cw, ch, Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation))
            if hasattr(info, 'grid_item') and info.grid_item: info.grid_item.setIcon(QIcon(pixmap))

    @property
    def progress_bar(self):
        main_win = self.window()
        if main_win and hasattr(main_win, 'progress_bar'):
            return main_win.progress_bar
        if not hasattr(self, '_dummy_progress_bar'):
            self._dummy_progress_bar = QProgressBar()
        return self._dummy_progress_bar

    def eventFilter(self, watched, event):
        if watched is self.grid_view.viewport():
            if event.type() == QEvent.Type.MouseMove:
                pos = event.pos() if hasattr(event, 'pos') else event.position().toPoint()
                item = self.grid_view.itemAt(pos)
                if item:
                    info = item.data(Qt.ItemDataRole.UserRole)
                    if info and info.media_type == 'video' and info.is_valid:
                        if self._hovered_grid_info != info:
                            self._hovered_grid_info = info
                            rect = self.grid_view.visualItemRect(item)
                            viewport_widget = self.grid_view.viewport()
                            top_left_global = viewport_widget.mapToGlobal(rect.topLeft())
                            global_rect = QRect(top_left_global, rect.size())
                            self._start_hover_timer(info, global_rect)
                    else:
                        self._stop_hover_timer()
                        self._hovered_grid_info = None
                else:
                    self._stop_hover_timer()
                    self._hovered_grid_info = None
            elif event.type() == QEvent.Type.Leave:
                self._stop_hover_timer()
                self._hovered_grid_info = None
        elif isinstance(watched, QLabel) and watched.objectName() == "thumbnailLabel":
            if event.type() == QEvent.Type.Enter:
                info = watched.property("media_info")
                if info and info.media_type == 'video' and info.is_valid:
                    top_left_global = watched.mapToGlobal(watched.rect().topLeft())
                    global_rect = QRect(top_left_global, watched.rect().size())
                    self._start_hover_timer(info, global_rect)
            elif event.type() == QEvent.Type.Leave:
                info = watched.property("media_info")
                if info and info.media_type == 'video' and info.is_valid:
                    self._stop_hover_timer()
        return super().eventFilter(watched, event)

    def _start_hover_timer(self, info, global_rect):
        if self.btn_toggle_preview.isChecked():
            return
        main_win = self.window()
        if main_win and hasattr(main_win, 'hover_overlay') and main_win.hover_overlay.isVisible():
            return
        if info == self._dismissed_info:
            return
        self._hovered_info = info
        self._hovered_global_rect = global_rect
        self.hover_timer.start()

    def _stop_hover_timer(self):
        self.hover_timer.stop()
        self._hovered_info = None
        self._hovered_global_rect = None
        self._dismissed_info = None

    def _on_hover_timeout(self):
        if self._hovered_info and self._hovered_global_rect:
            main_win = self.window()
            if main_win and hasattr(main_win, 'hover_overlay'):
                main_win.hover_overlay.show_preview(self._hovered_info, self._hovered_global_rect)

    def _on_scan_complete(self, total: int):
        self.btn_load.setVisible(True)
        self.btn_load.setEnabled(True)
        self.btn_stop.setVisible(False)
        self.btn_process.setEnabled(total > 0)
        self.btn_relocate.setEnabled(total > 0)
        self.btn_find_dupes.setEnabled(total > 0)
        self.btn_clear.setVisible(total > 0)
        self.progress_bar.setVisible(False)
        self.table.setUpdatesEnabled(True)
        self.grid_view.setUpdatesEnabled(True)
        self.table.setSortingEnabled(True)
        loaded = len(self.media_infos)
        if self.media_type == 'video': media_word = "video"
        elif self.media_type == 'audio': media_word = "audio"
        else: media_word = "image"
        self.status_label.setText(f"Scan complete — {loaded} {media_word} file{'s' if loaded != 1 else ''} found.")
        self._update_stats()
        if self._saved_file_data:
            self._restore_file_data()
            self._saved_file_data = {}
        if getattr(self, '_watch_enabled', False):
            self._known_files = {os.path.normcase(os.path.normpath(info.filepath)): info.filepath for info in self.media_infos}
            if not self._watch_timer.isActive():
                self._watch_timer.start(3000)
        self._load_visible_widgets()

    def _ensure_widgets_for_row(self, row: int):
        info = self._get_row_info(row)
        if not info or not info.is_valid: return
        
        if not hasattr(info, 'parsed_artist'):
            info.parsed_artist, info.parsed_rating = parse_naming_format(info.filename)
            
        # Lazy Thumbnail Generation
        if not getattr(info, 'thumb_queued', False):
            info.thumb_queued = True
            thumb_label = self.table.cellWidget(row, self.COL_THUMB)
            if thumb_label and thumb_label.objectName() == "thumbnailLabel":
                self._generate_thumbnail_async(row, info, thumb_label)
                

        # Artist widget
        if not self.table.cellWidget(row, self.COL_ARTIST):
            artist_item = self.table.item(row, self.COL_ARTIST)
            val = artist_item.text().strip() if artist_item else ""
            if not val: val = info.parsed_artist
            artist_input = QLineEdit()
            artist_input.setPlaceholderText("Enter name…")
            artist_input.setMaxLength(100)
            if val: artist_input.setText(val)
            artist_input.textChanged.connect(self._on_input_changed_sender)
            artist_input.editingFinished.connect(self._on_artist_editing_finished)
            self.table.setCellWidget(row, self.COL_ARTIST, artist_input)
            
        # Rating widget
        if not self.table.cellWidget(row, self.COL_RATING):
            rating_item = self.table.item(row, self.COL_RATING)
            val = rating_item.text().strip() if rating_item else "—"
            if val == "—" or not val:
                val = info.parsed_rating or "—"
            rating_combo = QComboBox()
            rating_combo.addItems(["—"] + [str(i) for i in range(1, 11)])
            idx = rating_combo.findText(val)
            if idx >= 0: rating_combo.setCurrentIndex(idx)
            rating_combo.currentTextChanged.connect(self._on_input_changed_sender)
            rating_combo.currentTextChanged.connect(self._on_rating_changed)
            rating_combo.currentTextChanged.connect(lambda text, cb=rating_combo: self._style_rating_combo(cb, text))
            self._style_rating_combo(rating_combo, rating_combo.currentText())
            self.table.setCellWidget(row, self.COL_RATING, rating_combo)
            
        # Tags widget
        if not self.table.cellWidget(row, self.COL_TAGS):
            tags_item = self.table.item(row, self.COL_TAGS)
            val = tags_item.text().strip() if tags_item else ""
            if not val and hasattr(info, 'tags') and info.tags:
                val = ", ".join(info.tags)
            tag_input = QLineEdit()
            tag_input.setPlaceholderText("e.g. nature, 4k, favorite")
            if val: tag_input.setText(val)
            tag_input.editingFinished.connect(self._on_tags_edited)
            self.table.setCellWidget(row, self.COL_TAGS, tag_input)

    def _thumb_dims(self):
        """Inner thumbnail label size derived from the thumb_size setting."""
        w = int(getattr(self, 'thumb_size', 130))
        return w, max(50, round(w * 0.567))

    def apply_thumbnail_size(self, size: int):
        """Resize thumbnails across table + grid and re-render visible ones."""
        size = max(90, min(200, int(size)))
        self.thumb_size = size
        w, h = self._thumb_dims()
        was_sorting = self.table.isSortingEnabled()
        self.table.setSortingEnabled(False)
        try:
            self.table.setColumnWidth(self.COL_THUMB, size)
            self.grid_view.setIconSize(QSize(w, h))
            self.grid_view.setGridSize(QSize(w + 20, h + 50))
            for row in range(self.table.rowCount()):
                self.table.setRowHeight(row, h + 8)
                wdg = self.table.cellWidget(row, self.COL_THUMB)
                if isinstance(wdg, QLabel) and wdg.objectName() == "thumbnailLabel":
                    wdg.setFixedSize(w, h)
                    if wdg.pixmap() is not None and not wdg.pixmap().isNull():
                        # Reset to placeholder; _load_visible_widgets() will
                        # regenerate at the new resolution (thumb_queued reset).
                        emoji = wdg.property("emoji")
                        wdg.setPixmap(QPixmap())
                        if emoji:
                            wdg.setText(emoji)
                info = self._get_row_info(row)
                if info is not None:
                    info.thumb_queued = False
        finally:
            self.table.setSortingEnabled(was_sorting)
        self._load_visible_widgets()

    def _load_visible_widgets(self):
        if self._updating_table: return
        scrollbar = self.table.verticalScrollBar()
        first = self.table.rowAt(0)
        if first < 0: first = 0
        last = self.table.rowAt(self.table.viewport().height())
        if last < 0: last = self.table.rowCount() - 1
        
        # Buffer of 10 rows above and below visible area
        first = max(0, first - 10)
        last = min(self.table.rowCount() - 1, last + 10)
        
        for row in range(first, last + 1):
            self._ensure_widgets_for_row(row)

    def _on_rating_changed(self, text: str):
        sender = self.sender()
        if not sender: return
        for row in range(self.table.rowCount()):
            if self.table.cellWidget(row, self.COL_RATING) is sender:
                rating_item = self.table.item(row, self.COL_RATING)
                if rating_item:
                    was_sorting = self.table.isSortingEnabled()
                    self.table.setSortingEnabled(False)
                    rating_item.setText(text)
                    rating_item.sort_key = int(text) if text.isdigit() else 0
                    self.table.setSortingEnabled(was_sorting)
                break

    def _get_row_info(self, row: int) -> MediaInfo | None:
        item = self.table.item(row, self.COL_FILENAME)
        if item: return item.data(Qt.ItemDataRole.UserRole)
        return None

    def _on_input_changed_sender(self):
        sender = self.sender()
        if not sender: return
        # O(1) lookup via viewport mapping instead of O(N) scan
        pos = self.table.viewport().mapFromGlobal(sender.mapToGlobal(QPoint(0, 0)))
        index = self.table.indexAt(pos)
        row = index.row() if index.isValid() else None
        if row is not None:
            if row in self.filtered_rows or not self.filtered_rows: self._update_row_preview(row)

    def _on_artist_editing_finished(self):
        sender = self.sender()
        if not sender: return
        pos = self.table.viewport().mapFromGlobal(sender.mapToGlobal(QPoint(0, 0)))
        index = self.table.indexAt(pos)
        row = index.row() if index.isValid() else None
        if row is not None:
            artist_item = self.table.item(row, self.COL_ARTIST)
            if artist_item:
                was_sorting = self.table.isSortingEnabled()
                self.table.setSortingEnabled(False)
                artist_item.setText(sender.text().strip())
                self.table.setSortingEnabled(was_sorting)
            # Also persist via debounced save_state (artist edits previously didn't save)
            main_win = self.window()
            if main_win and hasattr(main_win, '_debounced_save_state'):
                main_win._debounced_save_state()

    def _on_tags_edited(self):
        sender = self.sender()
        if not sender: return
        # Resolve the row dynamically by widget identity — a stored row index
        # goes stale after sorting (widgets move rows, the int doesn't), which
        # wrote tags onto the WRONG file's info.
        row = None
        for r in range(self.table.rowCount()):
            if self.table.cellWidget(r, self.COL_TAGS) is sender:
                row = r
                break
        if row is None: return
        info = self._get_row_info(row)
        if not info: return
        raw_text = sender.text()
        tags = [t.strip() for t in raw_text.split(',') if t.strip()]
        info.tags = tags
        tags_item = self.table.item(row, self.COL_TAGS)
        if tags_item:
            was_sorting = self.table.isSortingEnabled()
            self.table.setSortingEnabled(False)
            tags_item.setText(", ".join(tags))
            self.table.setSortingEnabled(was_sorting)
        main_win = self.window()
        if main_win and hasattr(main_win, '_debounced_save_state'):
            main_win._debounced_save_state()

    def _update_date_items(self, row: int, info):
        """Keep the optional Modified/Created cells accurate after renames."""
        for col, attr in ((self.COL_DATE_MOD, 'mtime'), (self.COL_DATE_CREATED, 'ctime')):
            it = self.table.item(row, col)
            if it is not None:
                ts = float(getattr(info, attr, 0) or 0)
                it.setText(format_timestamp(ts))
                it.sort_key = ts

    def _move_sidecars(self, old_path: str, new_path: str) -> list:
        """Move sibling subtitle/NFO files along with their media file.

        Returns the list of (old, new) pairs so undo/redo can revert them.
        Per-file failures are logged but never block the main rename.
        """
        moved = []
        old_stem = os.path.basename(os.path.splitext(old_path)[0])
        new_stem = os.path.splitext(new_path)[0]
        for sidecar in find_sidecars(old_path):
            rel = os.path.basename(sidecar)[len(old_stem):]
            target = new_stem + rel
            try:
                if os.path.exists(target):
                    b, x = os.path.splitext(target)
                    counter = 1
                    while os.path.exists(target):
                        target = f"{b}_{counter}{x}"
                        counter += 1
                shutil.move(sidecar, target)
                moved.append((sidecar, target))
            except OSError as e:
                logger.warning("Sidecar move failed (%s -> %s): %s", sidecar, target, e)
        return moved

    @staticmethod
    def _refresh_row_dates(info):
        """Re-stat a file after rename/move so Modified/Created stay accurate."""
        try:
            st_ = os.stat(info.filepath)
            info.mtime = float(st_.st_mtime)
            info.ctime = float(getattr(st_, 'st_ctime', 0))
        except OSError:
            pass

    def _get_templated_name(self, artist: str, rating: str, info) -> str:
        main_win = self.window()
        if not main_win:
            return ""
        fields_ordered = getattr(main_win, 'naming_all_fields_ordered', ["Name", "Duration", "Resolution", "Rating", "Tags"])
        fields_checked = getattr(main_win, 'naming_fields', ["name", "duration", "resolution", "rating", "tags"])
        separator = getattr(main_win, 'naming_separator', ' ')
        parts = []
        for f_name in fields_ordered:
            config_key = FIELD_MAP.get(f_name)
            if config_key not in fields_checked:
                continue
            if config_key == "name":
                if artist:
                    parts.append(artist)
            elif config_key == "duration":
                if self.media_type != 'image' and info.duration_compact and info.duration_compact != "—":
                    parts.append(info.duration_compact)
            elif config_key == "resolution":
                if self.media_type != 'audio' and info.resolution_tag and info.resolution_tag != "—":
                    parts.append(info.resolution_tag)
            elif config_key == "rating":
                if rating and rating != "—":
                    parts.append(rating)
            elif config_key == "tags":
                tags = getattr(info, 'tags', [])
                if tags:
                    parts.append(" ".join(tags))
            elif config_key in ("date_taken", "ym"):
                dt = get_media_datetime(info)
                if dt is not None:
                    parts.append(dt.strftime("%Y-%m-%d") if config_key == "date_taken" else dt.strftime("%Y%m"))
        return separator.join(parts)

    def _is_naming_data_complete(self, artist: str, rating: str, info=None) -> bool:
        main_win = self.window()
        if not main_win:
            return False
        fields_checked = getattr(main_win, 'naming_fields', ["name", "duration", "resolution", "rating", "tags"])
        if not fields_checked:
            return False
        if "name" in fields_checked and not artist:
            return False
        if "rating" in fields_checked and (not rating or rating == "—"):
            return False
        if info is not None and ("date_taken" in fields_checked or "ym" in fields_checked):
            if get_media_datetime(info) is None:
                return False
        return True

    def _update_row_preview(self, row: int):
        info = self._get_row_info(row)
        if not info or not info.is_valid: return
        # Mark stats dirty so the next _update_stats call will recompute ready_count
        self._stats_dirty = True
        artist_widget = self.table.cellWidget(row, self.COL_ARTIST)
        rating_widget = self.table.cellWidget(row, self.COL_RATING)
        artist = artist_widget.text().strip() if artist_widget else (self.table.item(row, self.COL_ARTIST).text().strip() if self.table.item(row, self.COL_ARTIST) else "")
        rating_text = rating_widget.currentText() if rating_widget else (self.table.item(row, self.COL_RATING).text().strip() if self.table.item(row, self.COL_RATING) else "—")
        if rating_widget:
            rating_item = self.table.item(row, self.COL_RATING)
            if rating_item:
                rating_item.setText(rating_text)
                rating_item.sort_key = int(rating_text) if rating_text.isdigit() else 0
        preview_item = self.table.item(row, self.COL_PREVIEW)
        if not preview_item: return
        
        main_win = self.window()
        keep_ext = getattr(main_win, 'naming_keep_extension', True)
        
        is_complete = self._is_naming_data_complete(artist, rating_text, info)
        new_name = self._get_templated_name(artist, rating_text, info) if is_complete else ""
        
        current_display_name = self.table.item(row, self.COL_FILENAME).text().strip() if self.table.item(row, self.COL_FILENAME) else ""
        target_display = new_name + (info.extension if keep_ext else "") if new_name else ""
        
        is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark'
        if not is_complete or not new_name or target_display == current_display_name:
            preview_item.setText("—")
            preview_item.setFont(QFont(BASE_FONT_FAMILY, 10, QFont.Weight.Normal))
            preview_item.setForeground(QColor("#7c7c9a") if is_dark else QColor("#64748b"))
            if hasattr(info, 'grid_item') and info.grid_item: info.grid_item.setToolTip("")
        else:
            preview_item.setText(f"➜  {target_display}")
            preview_item.setFont(QFont(BASE_FONT_FAMILY, 10, QFont.Weight.Bold))
            preview_item.setForeground(QColor("#34d399") if is_dark else QColor("#059669"))
            if hasattr(info, 'grid_item') and info.grid_item: info.grid_item.setToolTip(f"Rename to: {target_display}")
        self._update_stats()

    def _on_selection_changed(self):
        if self._syncing_selection: return
        self._syncing_selection = True
        try:
            selected_rows = set()
            for rng in self.table.selectedRanges():
                for row in range(rng.topRow(), rng.bottomRow() + 1): selected_rows.add(row)
            self.grid_view.blockSignals(True)
            self.grid_view.clearSelection()
            for row in selected_rows:
                info = self._get_row_info(row)
                if info and hasattr(info, 'grid_item') and info.grid_item: info.grid_item.setSelected(True)
            self.grid_view.blockSignals(False)
        finally:
            self._syncing_selection = False
        # Selection stats: count + combined size of visible selected files (>1 only)
        n_sel, total = 0, 0
        for rng in self.table.selectedRanges():
            for r in range(rng.topRow(), rng.bottomRow() + 1):
                if self.table.isRowHidden(r):
                    continue
                inf = self._get_row_info(r)
                if inf is not None:
                    n_sel += 1
                    total += int(getattr(inf, 'size_bytes', 0))
        self.sel_stats_label.setText(f"{n_sel} selected \u00b7 {format_size(total)}" if n_sel > 1 else "")
        self._update_selection_buttons_and_preview()

    def _on_batch_edit(self):
        selected_rows = set()
        for rng in self.table.selectedRanges():
            for row in range(rng.topRow(), rng.bottomRow() + 1):
                if row in self.filtered_rows or not self.filtered_rows:
                    info = self._get_row_info(row)
                    if info and info.is_valid: selected_rows.add(row)
        if not selected_rows:
            QMessageBox.information(self, "No Valid Selection", "Please select at least one valid file."); return
        dialog = BatchEditDialog(self)
        if dialog.exec() == QDialog.DialogCode.Accepted:
            artist, rating = dialog.get_values()
            self._apply_batch_edit(selected_rows, artist, rating)

    def _on_batch_tag(self):
        selected_rows = set()
        for rng in self.table.selectedRanges():
            for row in range(rng.topRow(), rng.bottomRow() + 1):
                if row in self.filtered_rows or not self.filtered_rows:
                    info = self._get_row_info(row)
                    if info and info.is_valid: selected_rows.add(row)
        if len(selected_rows) < 2:
            QMessageBox.information(self, "Selection Required", "Please select at least 2 valid files."); return
            
        selected_infos = [self._get_row_info(r) for r in selected_rows]
        dialog = BatchTagDialog(selected_infos, self)
        
        if dialog.exec() == QDialog.DialogCode.Accepted:
            mode, input_tags = dialog.get_result()
            was_sorting = self.table.isSortingEnabled()
            self.table.setSortingEnabled(False)
            self._updating_table = True
            try:
                for row, info in zip(selected_rows, selected_infos):
                    current_tags = getattr(info, 'tags', [])
                    new_tags = list(current_tags)

                    if mode == "Add Tags":
                        for t in input_tags:
                            if t not in new_tags:
                                new_tags.append(t)
                    elif mode == "Remove Tags":
                        new_tags = [t for t in new_tags if t not in input_tags]
                    elif mode == "Replace All Tags":
                        new_tags = input_tags

                    info.tags = new_tags
                    # FIX: was self._update_table_item(...) — that method never
                    # existed, so batch-tagging crashed with AttributeError after
                    # mutating tags. Update item AND cell widget (the widget is
                    # what the user actually sees), then refresh the preview.
                    tags_text = ", ".join(new_tags)
                    tags_item = self.table.item(row, self.COL_TAGS)
                    if tags_item:
                        tags_item.setText(tags_text)
                    tags_widget = self.table.cellWidget(row, self.COL_TAGS)
                    if tags_widget and tags_widget.text() != tags_text:
                        tags_widget.setText(tags_text)
                    if hasattr(info, 'grid_item') and info.grid_item:
                        tag_str = tags_text if new_tags else ""
                        info.grid_item.setToolTip(f"{info.filename}\nTags: {tag_str}" if tag_str else info.filename)
            finally:
                self._updating_table = False
                self.table.setSortingEnabled(was_sorting)

            for row, info in zip(selected_rows, selected_infos):
                self._update_row_preview(row)

            if hasattr(self.window(), '_debounced_save_state'):
                self.window()._debounced_save_state()
            self._show_toast(f"Updated tags for {len(selected_rows)} files.", 'success')

    def _apply_batch_edit(self, rows: set[int], artist: str | None, rating: str | None):
        was_sorting = self.table.isSortingEnabled()
        self.table.setSortingEnabled(False)
        self._updating_table = True
        for row in rows:
            if artist is not None:
                artist_item = self.table.item(row, self.COL_ARTIST)
                if artist_item: artist_item.setText(artist)
                artist_widget = self.table.cellWidget(row, self.COL_ARTIST)
                if artist_widget:
                    artist_widget.setText(artist)
            if rating is not None:
                rating_item = self.table.item(row, self.COL_RATING)
                if rating_item:
                    rating_item.setText(rating)
                    rating_item.sort_key = int(rating) if rating.isdigit() else 0
                rating_widget = self.table.cellWidget(row, self.COL_RATING)
                if rating_widget:
                    idx = rating_widget.findText(rating)
                    if idx >= 0: rating_widget.setCurrentIndex(idx)
            self._update_row_preview(row)
        self._updating_table = False
        self.table.setSortingEnabled(was_sorting)
        self._update_stats()

    def _on_smart_relocate(self):
        """Opens the Smart Relocate Dialog and executes the move."""
        selected_rows = set()
        for rng in self.table.selectedRanges():
            for row in range(rng.topRow(), rng.bottomRow() + 1):
                selected_rows.add(row)

        dialog = SmartRelocateDialog(self.media_infos, selected_rows, self)
        if dialog.exec() != QDialog.DialogCode.Accepted:
            return

        target_infos, template = dialog.get_config()
        if not target_infos:
            QMessageBox.information(self, "No Files", "No files matched your criteria.")
            return

        reply = QMessageBox.question(
            self, "Confirm Relocation",
            f"This will move {len(target_infos)} files to new directories.\n\nContinue?",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No
        )
        if reply != QMessageBox.StandardButton.Yes:
            return

        # Compute the allowed root (everything before the first {variable})
        # so we can validate each resolved dest_dir stays inside it.
        # NOTE: allowed_root stays None when the template starts with a
        # {variable} or contains none — that's still safe because
        # parse_destination_template strips all separators/'..' from every
        # substituted value, so traversal can only come from template literals
        # the user typed deliberately.
        first_var = template.find('{')
        allowed_root = os.path.normcase(os.path.abspath(template[:first_var])) if first_var > 0 else None

        success_count = 0
        error_count = 0
        error_details = []  # capture for the completion dialog

        was_sorting = self.table.isSortingEnabled()
        self.table.setSortingEnabled(False)
        self._updating_table = True

        # Build id(info) -> row map ONCE for O(1) lookup (was O(N·M))
        id_to_row = {}
        for r in range(self.table.rowCount()):
            ri = self._get_row_info(r)
            if ri is not None:
                id_to_row[id(ri)] = r

        # Show a progress dialog so the user can see what's happening during
        # long cross-filesystem moves (which can take seconds per GB).
        progress = QProgressDialog("Moving files…", "Cancel", 0, len(target_infos), self)
        progress.setWindowModality(Qt.WindowModality.ApplicationModal)
        progress.setMinimumDuration(0)
        progress.setValue(0)

        for idx, info in enumerate(target_infos):
            if progress.wasCanceled():
                error_details.append(f"Cancelled by user after {success_count} files moved.")
                break
            src = info.filepath
            tags = getattr(info, 'tags', [])
            dest_dir = parse_destination_template(template, info, tags)

            # Path-traversal safety: ensure resolved dest_dir stays under allowed_root
            if allowed_root:
                abs_dest = os.path.normcase(os.path.abspath(dest_dir))
                try:
                    if os.path.commonpath([allowed_root, abs_dest]) != allowed_root:
                        error_count += 1
                        error_details.append(f"{info.filename}: destination escapes allowed root")
                        continue
                except ValueError:
                    error_count += 1
                    error_details.append(f"{info.filename}: cannot validate destination path")
                    continue

            try:
                os.makedirs(dest_dir, exist_ok=True)

                dest_file = os.path.join(dest_dir, info.filename)
                same_file = os.path.normcase(os.path.abspath(src)) == os.path.normcase(os.path.abspath(dest_file))
                if os.path.exists(dest_file) and not same_file:
                    base, ext = os.path.splitext(info.filename)
                    counter = 1
                    while os.path.exists(dest_file):
                        dest_file = os.path.join(dest_dir, f"{base}_{counter}{ext}")
                        counter += 1

                shutil.move(src, dest_file)

                # Update info and matching table items
                info.filepath = dest_file
                info.filename = os.path.basename(dest_file)

                row_idx = id_to_row.get(id(info), -1)

                # Sidecars + dates + history must happen even when row_idx==-1
                # (cross-tab source, stale id_to_row) — disk state already moved
                moved_extra = self._move_sidecars(src, dest_file)
                self._refresh_row_dates(info)
                if row_idx >= 0:
                    fname_item = self.table.item(row_idx, self.COL_FILENAME)
                    if fname_item:
                        fname_item.setText(info.filename)
                        fname_item.setToolTip(dest_file)
                    # Keep the grid card in sync (was stale until next rescan)
                    if hasattr(info, 'grid_item') and info.grid_item:
                        info.grid_item.setText(info.filename)
                        info.grid_item.setToolTip(dest_file)
                    self._update_date_items(row_idx, info)
                self._add_to_history(src, dest_file, row_idx, extra=moved_extra)

                success_count += 1

            except Exception as e:
                error_count += 1
                error_details.append(f"{info.filename}: {e}")
                logger.exception("Failed to move %s", info.filename)

            progress.setValue(idx + 1)
            QApplication.processEvents()

        progress.close()

        self._updating_table = False
        self.table.setSortingEnabled(was_sorting)
        if success_count > 0:
            self._known_files_dirty = True

        self.table.viewport().update()
        self.btn_undo.setEnabled(len(self._rename_history) > 0)

        # Include error details in the completion dialog so users can diagnose
        # why specific files failed (was: just a count via silent print()).
        msg = f"Relocation complete.\nSuccess: {success_count}\nFailed: {error_count}"
        if error_details:
            msg += "\n\nErrors (first 10):\n" + "\n".join(error_details[:10])
            if len(error_details) > 10:
                msg += f"\n…and {len(error_details) - 10} more"
        QMessageBox.information(
            self, "Relocation Complete",
            msg
        )

    def _on_cell_double_clicked(self, row: int, col: int):
        if col == self.COL_FILENAME: return
        self._play_video(row)

    def _play_video(self, row: int):
        info = self._get_row_info(row)
        if not info: return
        filepath = os.path.abspath(info.filepath)
        
        main_win = self.window()
        player_path = ""
        if main_win:
            if info.media_type == 'video' and hasattr(main_win, 'video_tab'):
                player_path = main_win.video_tab.default_player
            elif info.media_type == 'image' and hasattr(main_win, 'image_tab'):
                player_path = main_win.image_tab.default_player
            elif info.media_type == 'audio' and hasattr(main_win, 'audio_tab'):
                player_path = main_win.audio_tab.default_player
            elif info.media_type == 'pdf' and hasattr(main_win, 'pdf_tab'):
                player_path = main_win.pdf_tab.default_player
        else:
            player_path = self.default_player

        if player_path == "native":
            if main_win:
                if not hasattr(main_win, '_native_players'):
                    main_win._native_players = []
                prune_native_players(main_win)
                if info.media_type == 'video':
                    player_win = NativeVideoPlayerWindow(filepath, parent=main_win)
                elif info.media_type == 'image':
                    player_win = NativeImagePlayerWindow(filepath, parent=main_win)
                elif info.media_type == 'audio':
                    player_win = NativeAudioPlayerWindow(filepath, parent=main_win)
                elif info.media_type == 'pdf':
                    player_win = None
                else:
                    player_win = None
                if player_win:
                    player_win.show()
                    main_win._native_players.append(player_win)
            return

        if player_path and os.path.exists(player_path):
            try: subprocess.Popen([player_path, filepath]); return
            except Exception as e: QMessageBox.warning(self, "Player Error", f"Cannot open with selected player:\n{e}\nFalling back to system default.")
        try:
            if sys.platform == "win32": os.startfile(filepath)
            elif sys.platform == "darwin": subprocess.run(["open", filepath])
            else: subprocess.run(["xdg-open", filepath])
        except Exception as e: QMessageBox.warning(self, "Playback Error", f"Cannot open file:\n{e}")

    def _play_four_videos(self, filepaths):
        # Inform the user if more than 4 were passed (only first 4 will play).
        # The context-menu gating already restricts to exactly 4, but this
        # guards against any other call path that passes a longer list.
        if len(filepaths) > 4:
            QMessageBox.information(
                self, "Split Screen Limited to 4",
                f"Only the first 4 of {len(filepaths)} selected videos will be shown."
            )
            filepaths = filepaths[:4]
        main_win = self.window()
        if main_win:
            if not hasattr(main_win, '_native_players'):
                main_win._native_players = []
            prune_native_players(main_win)
            player_win = SplitVideoPlayerWindow(filepaths, parent=main_win)
            player_win.show()
            main_win._native_players.append(player_win)

    def _on_table_context_menu(self, pos):

        row = self.table.rowAt(pos.y())
        if row < 0: return
        global_pos = self.table.mapToGlobal(pos)
        self._show_context_menu_at_pos(row, global_pos)

    def _on_grid_context_menu(self, pos):
        item = self.grid_view.itemAt(pos)
        if not item: return
        info = item.data(Qt.ItemDataRole.UserRole)
        if not info: return
        row = -1
        for r in range(self.table.rowCount()):
            if self._get_row_info(r) is info: row = r; break
        if row >= 0:
            global_pos = self.grid_view.mapToGlobal(pos)
            self._show_context_menu_at_pos(row, global_pos)

    def _show_context_menu_at_pos(self, row: int, global_pos):
        info = self._get_row_info(row)
        if not info: return
        
        selected_rows = set()
        for rng in self.table.selectedRanges():
            for r in range(rng.topRow(), rng.bottomRow() + 1):
                selected_rows.add(r)
                
        is_four_videos = False
        selected_video_paths = []
        if row in selected_rows and len(selected_rows) == 4:
            all_videos = True
            for r in selected_rows:
                r_info = self._get_row_info(r)
                if not r_info or r_info.media_type != 'video':
                    all_videos = False
                    break
                selected_video_paths.append(os.path.abspath(r_info.filepath))
            if all_videos:
                is_four_videos = True

        menu = QMenu(self)
        if is_four_videos:
            play4_action = QAction("📺  Play 4 (Split Screen)", self)
            play4_action.triggered.connect(lambda: self._play_four_videos(selected_video_paths))
            menu.addAction(play4_action)
            menu.addSeparator()

        if len(selected_rows) == 2:
            compare_action = QAction("🔍  Compare Selected (2 Files)", self)
            compare_action.triggered.connect(self._on_compare_selected)
            menu.addAction(compare_action)
            menu.addSeparator()

        play_action = QAction("▶️  Play / Open", self)
        play_action.triggered.connect(lambda: self._play_video(row))
        menu.addAction(play_action)

        if info.media_type == 'video':
            trim_action = QAction("✂️  Quick Trim / Cut Video", self)
            trim_action.triggered.connect(lambda checked=False, r=row: self._on_quick_trim(r))
            menu.addAction(trim_action)

        # ─── Open With Submenu ───
        open_with_menu = menu.addMenu("🌐  Open with…")
        win_dialog_action = QAction("System open with...", self)
        win_dialog_action.triggered.connect(lambda checked=False, fp=info.filepath: self._open_with_system(fp))
        open_with_menu.addAction(win_dialog_action)
        
        if self.media_type != 'pdf':
            native_player_action = QAction("MediaFlow Native Player", self)
            native_player_action.triggered.connect(lambda checked=False, fp=info.filepath: self._play_native(fp))
            open_with_menu.addAction(native_player_action)
        
        main_win = self.window()
        custom_apps = getattr(main_win, 'open_with_apps', [])
        if custom_apps:
            open_with_menu.addSeparator()
            for app in custom_apps:
                app_name = app.get('name', 'Unknown')
                app_path = app.get('path', '')
                action = QAction(app_name, self)
                action.triggered.connect(lambda checked=False, ap=app_path, fp=info.filepath: self._open_with_custom(ap, fp))
                open_with_menu.addAction(action)
                
        open_with_menu.addSeparator()
        config_action = QAction("⚙️  Configure Applications...", self)
        config_action.triggered.connect(self._configure_open_with_apps)
        open_with_menu.addAction(config_action)

        info_action = QAction("🔍  Detailed Info", self)
        info_action.triggered.connect(lambda: self._show_detailed_info(row))
        menu.addAction(info_action)
        open_folder = QAction("📁  Open Containing Folder", self)
        open_folder.triggered.connect(lambda: self._open_folder_for_row(row))
        menu.addAction(open_folder)
        menu.addSeparator()
        sel_infos = []
        for r in sorted(selected_rows):
            if self.filtered_rows and r not in self.filtered_rows: continue
            r_info = self._get_row_info(r)
            if r_info is not None: sel_infos.append(r_info)
        if len(sel_infos) > 1:
            copy_paths = QAction(f"📋  Copy {len(sel_infos)} File Paths", self)
            copy_paths.triggered.connect(
                lambda: QApplication.clipboard().setText("\n".join(i.filepath for i in sel_infos)))
            menu.addAction(copy_paths)
            copy_names = QAction(f"📋  Copy {len(sel_infos)} File Names", self)
            copy_names.triggered.connect(
                lambda: QApplication.clipboard().setText("\n".join(i.filename for i in sel_infos)))
            menu.addAction(copy_names)
        else:
            copy_path = QAction("📋  Copy File Path", self)
            copy_path.triggered.connect(lambda: self._copy_path_for_row(row))
            menu.addAction(copy_path)
        remove_action = QAction("✕  Remove From List", self)
        remove_action.triggered.connect(lambda: self._remove_row_from_list(row))
        menu.addAction(remove_action)
        delete_action = QAction("🗑️  Delete from Disk...", self)
        delete_action.triggered.connect(lambda: self._on_delete_selected(row))
        menu.addAction(delete_action)
        menu.addSeparator()
        export_csv_action = QAction("⬇️  Export List to CSV", self)
        export_csv_action.setToolTip("Export the visible rows (current filters/duplicate view) to a CSV file")
        export_csv_action.triggered.connect(self._export_list_csv)
        menu.addAction(export_csv_action)
        if info.media_type == 'audio':
            audio_tags_action = QAction("🏷️  Edit Audio Tags\u2026", self)
            audio_tags_action.triggered.connect(lambda checked=False, r=row: self._edit_audio_tags(r))
            menu.addAction(audio_tags_action)
        if info.is_valid:
            menu.addSeparator()
            rating_menu = menu.addMenu("⭐  Set Rating")
            for r in ["—"] + [str(i) for i in range(1, 11)]:
                action = QAction(r if r != "—" else "Clear", self)
                action.triggered.connect(lambda checked, rr=r: self._set_rating_for_row(row, rr))
                rating_menu.addAction(action)
        menu.exec(global_pos)

    def _export_list_csv(self):
        """Export the CURRENTLY VISIBLE rows to CSV.

        Respects search/advanced filters and the duplicate view; the Status
        column carries 'Dup Group N' badges so a dupe scan can be exported
        directly as a report. UTF-8 BOM keeps Excel happy with unicode names.
        """
        path, _ = QFileDialog.getSaveFileName(self, "Export List to CSV",
                                              "mediaflow_export.csv", "CSV files (*.csv)")
        if not path:
            return
        try:
            import csv as _csv
            with open(path, 'w', encoding='utf-8-sig', newline='') as f:
                wr = _csv.writer(f)
                wr.writerow(list(self.HEADERS) + ["Path"])
                count = 0
                for row in range(self.table.rowCount()):
                    if self.table.isRowHidden(row): continue
                    vals = []
                    for col in range(self.NUM_COLS):
                        it = self.table.item(row, col)
                        vals.append(it.text() if it else "")
                    info = self._get_row_info(row)
                    vals.append(info.filepath if info else "")
                    wr.writerow(vals)
                    count += 1
            self._show_toast(f"Exported {count} rows \u2192 {os.path.basename(path)}", 'success')
        except OSError as e:
            QMessageBox.warning(self, "Export Failed", f"Could not write CSV:\n{e}")

    def _show_detailed_info(self, row: int):
        info = self._get_row_info(row)
        if not info: return
        main_win = self.window()
        ffprobe_path = getattr(main_win, 'ffprobe_path', None)
        dialog = DetailedInfoDialog(info.filepath, ffprobe_path, self)
        dialog.exec()

    def _show_file_info_dialog(self):
        """Ctrl+I handler — shows detailed info for the current row."""
        row = self.table.currentRow()
        if row >= 0:
            self._show_detailed_info(row)

    def _edit_audio_tags(self, row: int):
        """B2: edit embedded tags of an audio file (writes via mutagen)."""
        info = self._get_row_info(row)
        if not info: return
        dlg = AudioTagEditorDialog(info.filepath, self)
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        try:
            dlg.save()
        except Exception as e:
            QMessageBox.critical(self, "Tag Save Failed", f"Could not write tags:\n{e}")
            return
        # Reflect a freshly-set Artist into the table when the cell was empty
        artist = dlg.get_values().get('artist', '').strip()
        if artist:
            was_sorting = self.table.isSortingEnabled()
            self.table.setSortingEnabled(False)
            widget = self.table.cellWidget(row, self.COL_ARTIST)
            item = self.table.item(row, self.COL_ARTIST)
            if widget is not None and not widget.text().strip():
                widget.setText(artist)
            elif item is not None and not item.text().strip():
                item.setText(artist)
            self.table.setSortingEnabled(was_sorting)
        self._show_toast("Audio tags saved.", 'success')

    def _on_compare_selected(self):
        selected_rows = []
        for rng in self.table.selectedRanges():
            for r in range(rng.topRow(), rng.bottomRow() + 1):
                if r not in selected_rows:
                    selected_rows.append(r)
        if len(selected_rows) != 2:
            QMessageBox.information(self, "Comparison Selection", "Please select exactly 2 files to compare.")
            return
        info1 = self._get_row_info(selected_rows[0])
        info2 = self._get_row_info(selected_rows[1])
        if not info1 or not info2: return
        main_win = self.window()
        comp_win = ComparisonViewWindow(info1, info2, parent_tab=self, parent=main_win)
        if main_win:
            if not hasattr(main_win, '_native_players') or main_win._native_players is None:
                main_win._native_players = []
            main_win._native_players.append(comp_win)
        comp_win.show()

    def _on_quick_trim(self, row: int = -1):
        if row == -1:
            row = self.table.currentRow()
        if row < 0: return
        info = self._get_row_info(row)
        if not info or not os.path.exists(info.filepath): return
        main_win = self.window()
        dialog = QuickTrimDialog(info.filepath, parent_tab=self, parent=main_win)
        dialog.exec()

    def _open_with_system(self, filepath: str):
        if sys.platform == 'win32':
            try:
                os.startfile(os.path.abspath(filepath), "openas")
            except Exception as e:
                try:
                    import subprocess
                    subprocess.Popen(['rundll32.exe', 'shell32.dll,OpenAs_RunDLL', os.path.abspath(filepath)])
                except Exception:
                    QMessageBox.critical(self, "Error", f"Failed to open Windows Open With dialog:\n{e}")
        else:
            QMessageBox.information(self, "Information", "Open With System is only supported on Windows.")

    def _play_native(self, filepath: str):
        filepath = os.path.abspath(filepath)
        main_win = self.window()
        if main_win:
            if not hasattr(main_win, '_native_players'):
                main_win._native_players = []
            prune_native_players(main_win)
            if self.media_type == 'video':
                player_win = NativeVideoPlayerWindow(filepath, parent=main_win)
            elif self.media_type == 'image':
                player_win = NativeImagePlayerWindow(filepath, parent=main_win)
            elif self.media_type == 'audio':
                player_win = NativeAudioPlayerWindow(filepath, parent=main_win)
            elif self.media_type == 'pdf':
                player_win = None
            else:
                player_win = None
            if player_win:
                player_win.show()
                main_win._native_players.append(player_win)

    def _on_header_context_menu(self, pos: QPoint):
        """Show a context menu to toggle column visibility."""
        self.header_menu.clear()
        
        # Create a checkable action for every column
        for col in range(self.NUM_COLS):
            action = QAction(self.HEADERS[col], self)
            action.setCheckable(True)
            action.setChecked(not self.table.isColumnHidden(col))
            # Use default argument 'c=col' to capture the correct index in the lambda
            action.triggered.connect(lambda checked, c=col: self._toggle_column_visibility(c, checked))
            self.header_menu.addAction(action)
            
        self.header_menu.exec(self.table.horizontalHeader().mapToGlobal(pos))

    def _toggle_column_visibility(self, col: int, visible: bool):
        """Toggle the visibility of a specific column and save the state."""
        self.table.setColumnHidden(col, not visible)
        self._save_column_state()

    def _save_column_state(self):
        """Trigger the main window to save the current state to config.json."""
        main_win = self.window()
        if main_win and hasattr(main_win, '_save_state'):
            main_win._save_state()

    def _open_with_custom(self, app_path: str, filepath: str):
        import subprocess
        if not os.path.exists(app_path):
            QMessageBox.critical(self, "Error", f"Application executable not found at:\n{app_path}")
            return
        try:
            subprocess.Popen([app_path, os.path.abspath(filepath)])
        except Exception as e:
            QMessageBox.critical(self, "Error", f"Failed to launch application:\n{e}")

    def _configure_open_with_apps(self):
        main_win = self.window()
        if hasattr(main_win, '_manage_open_with_apps'):
            main_win._manage_open_with_apps()

    def _open_folder_for_row(self, row: int):
        info = self._get_row_info(row)
        if info:
            folder = os.path.dirname(info.filepath)
            if sys.platform == "win32":
                # SECURITY: use list form to bypass shell parsing — the previous
                # f-string form broke on filenames containing quotes / shell
                # metacharacters like "My "Best" Video.mp4".
                subprocess.run(["explorer", "/select,", os.path.normpath(info.filepath)], shell=False)
            elif sys.platform == "darwin": subprocess.run(["open", folder])
            else: subprocess.run(["xdg-open", folder])

    def _copy_path_for_row(self, row: int):
        info = self._get_row_info(row)
        if info:
            QApplication.clipboard().setText(info.filepath)
            self.status_label.setText("📋 Path copied to clipboard")
            self._show_toast("📋 Path copied to clipboard", 'success')
            QTimer.singleShot(2000, lambda: self.status_label.setText("Ready"))

    def _remove_row_from_list(self, row: int):
        info = self._get_row_info(row)
        if info:
            self.media_infos = [v for v in self.media_infos if v.filepath != info.filepath]
            self.table.removeRow(row)
            if hasattr(info, 'grid_item') and info.grid_item:
                row_item = self.grid_view.row(info.grid_item)
                if row_item >= 0: self.grid_view.takeItem(row_item)
            # Keep filtered_rows consistent: every index above the removed row
            # shifts down by one (prevents later bulk ops targeting stale rows).
            self.filtered_rows.discard(row)
            self.filtered_rows = {r - 1 if r > row else r for r in self.filtered_rows}
            # Renames/deletes invalidate the watch-mode path baseline
            self._known_files_dirty = True
            self._update_stats()

    def _on_remove_selected(self):
        selected_rows = set()
        for rng in self.table.selectedRanges():
            for row in range(rng.topRow(), rng.bottomRow() + 1): selected_rows.add(row)
        for row in sorted(list(selected_rows), reverse=True):
            if row < self.table.rowCount(): self._remove_row_from_list(row)

    def _on_delete_selected(self, target_row: int = -1):
        if isinstance(target_row, bool):
            target_row = -1
        selected_rows = {}
        if target_row != -1:
            info = self._get_row_info(target_row)
            if info: selected_rows[target_row] = info
        else:
            for rng in self.table.selectedRanges():
                for row in range(rng.topRow(), rng.bottomRow() + 1):
                    info = self._get_row_info(row)
                    if info: selected_rows[row] = info
        if not selected_rows:
            QMessageBox.information(self, "No Selection", "Please select files to delete."); return
        msg_box = QMessageBox(self)
        msg_box.setWindowTitle("Delete Files")
        msg_box.setText(f"Are you sure you want to send {len(selected_rows)} file(s) to the Recycle Bin?")
        recycle_btn = msg_box.addButton("♻️  Send to Recycle Bin", QMessageBox.ButtonRole.YesRole)
        cancel_btn = msg_box.addButton("Cancel", QMessageBox.ButtonRole.RejectRole)
        msg_box.setDefaultButton(recycle_btn)
        msg_box.exec()
        clicked = msg_box.clickedButton()
        if clicked == cancel_btn: return
        was_sorting = self.table.isSortingEnabled()
        self.table.setSortingEnabled(False)
        self._updating_table = True
        sorted_selected = sorted(list(selected_rows.items()), key=lambda x: x[0], reverse=True)
        self._release_file_locks([info.filepath for _, info in sorted_selected])
        success_count = 0
        error_files = []
        for row, info in sorted_selected:
            filepath = info.filepath
            if send_to_recycle_bin(filepath):
                self._remove_row_from_list(row)
                success_count += 1
            else: error_files.append(f"{info.filename}: Could not recycle")
        self._updating_table = False
        self.table.setSortingEnabled(was_sorting)
        self._update_stats()
        if error_files:
            QMessageBox.warning(self, "Deletion Errors", f"Failed to delete {len(error_files)} file(s):\n\n" + "\n".join(error_files[:10]))
        else:
            self.status_label.setText(f"Deleted {success_count} file(s).")
            self._show_toast(f"Deleted {success_count} file(s).", 'success')

    def _set_rating_for_row(self, row: int, rating: str):
        self._ensure_widgets_for_row(row)
        rating_widget = self.table.cellWidget(row, self.COL_RATING)
        if rating_widget:
            idx = rating_widget.findText(rating)
            if idx >= 0:
                rating_widget.setCurrentIndex(idx)
        rating_item = self.table.item(row, self.COL_RATING)
        if rating_item:
            rating_item.setText(rating)
            rating_item.sort_key = int(rating) if rating.isdigit() else 0
        self._update_row_preview(row)

    def _on_item_changed(self, item: QTableWidgetItem):
        if self._updating_table: return
        if item.column() != self.COL_FILENAME: return
        row = item.row()
        info = self._get_row_info(row)
        if not info: return
        new_text = item.text().strip()
        old_text = info.filename
        if not new_text or new_text == old_text: return
        src = info.filepath
        # Only strip the extension if the typed text actually ends with it.
        # The old splitext() approach truncated names containing inner dots
        # ("Ep 1.5 Pilot.mp4" became "Ep 1.mp4").
        if info.extension and new_text.lower().endswith(info.extension.lower()):
            new_name_no_ext = new_text[:-len(info.extension)]
        else:
            new_name_no_ext = new_text
        dst = os.path.join(os.path.dirname(src), new_name_no_ext + info.extension)
        # normcase: on Windows the FS is case-insensitive, so renaming
        # ABC.mp4 -> abc.mp4 must NOT be treated as a collision.
        same_file = os.path.normcase(os.path.abspath(src)) == os.path.normcase(os.path.abspath(dst))
        if os.path.exists(dst) and not same_file:
            base = new_name_no_ext
            ext = info.extension
            counter = 1
            while os.path.exists(dst):
                dst = os.path.join(os.path.dirname(src), f"{base}_{counter}{ext}")
                counter += 1
        was_sorting = self.table.isSortingEnabled()
        self.table.setSortingEnabled(False)
        self._release_file_locks([src])
        try:
            os.rename(src, dst)
            info.filepath = dst
            info.filename = os.path.basename(dst)
            item.setToolTip(dst)
            self._updating_table = True
            item.setText(info.filename)
            self._updating_table = False
            if hasattr(info, 'grid_item') and info.grid_item:
                info.grid_item.setText(info.filename)
                info.grid_item.setToolTip(dst)
            self._known_files_dirty = True
            moved_extra = self._move_sidecars(src, dst)
            self._refresh_row_dates(info)
            self._update_date_items(row, info)
            self._add_to_history(src, dst, row, extra=moved_extra)
        except Exception as e:
            QMessageBox.warning(self, "Rename Error", f"Cannot rename file:\n{e}")
            self._updating_table = True
            item.setText(old_text)
            self._updating_table = False
        finally:
            self.table.setSortingEnabled(was_sorting)

    def _on_process_all(self):
        ready_rows = []
        main_win = self.window()
        keep_ext = getattr(main_win, 'naming_keep_extension', True)
        
        for row in range(self.table.rowCount()):
            if row not in self.filtered_rows and self.filtered_rows: continue
            info = self._get_row_info(row)
            if not info or not info.is_valid: continue
            artist_widget = self.table.cellWidget(row, self.COL_ARTIST)
            rating_widget = self.table.cellWidget(row, self.COL_RATING)
            artist = artist_widget.text().strip() if artist_widget else (self.table.item(row, self.COL_ARTIST).text().strip() if self.table.item(row, self.COL_ARTIST) else "")
            rating = rating_widget.currentText() if rating_widget else (self.table.item(row, self.COL_RATING).text().strip() if self.table.item(row, self.COL_RATING) else "—")
            if self._is_naming_data_complete(artist, rating, info):
                new_name = self._get_templated_name(artist, rating, info)
                current_display_name = self.table.item(row, self.COL_FILENAME).text().strip() if self.table.item(row, self.COL_FILENAME) else ""
                target_display = new_name + (info.extension if keep_ext else "") if new_name else ""
                if target_display and target_display != current_display_name:
                    ready_rows.append((row, info, target_display))
        if not ready_rows:
            QMessageBox.information(self, "Nothing to Process", "No files are ready to rename."); return
        reply = QMessageBox.question(self, "Confirm Rename", f"This will rename {len(ready_rows)} file{'s' if len(ready_rows) != 1 else ''}.\n\nYou can undo via Ctrl+Z. Continue?", QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No, QMessageBox.StandardButton.No)
        if reply != QMessageBox.StandardButton.Yes: return
        success_count = 0
        error_count = 0
        errors = []
        was_sorting = self.table.isSortingEnabled()
        self.table.setSortingEnabled(False)
        self._release_file_locks([info.filepath for _, info, _ in ready_rows])
        try:
            for row, info, target_display in ready_rows:
                src = info.filepath
                dst = os.path.join(os.path.dirname(src), target_display)
                # normcase: case-only renames on Windows are not collisions
                same_file = os.path.normcase(os.path.abspath(src)) == os.path.normcase(os.path.abspath(dst))
                if os.path.exists(dst) and not same_file:
                    base, ext = os.path.splitext(target_display)
                    counter = 1
                    while os.path.exists(dst):
                        dst = os.path.join(os.path.dirname(src), f"{base}_{counter}{ext}")
                        counter += 1
                try:
                    os.rename(src, dst)
                    info.filepath = dst
                    info.filename = os.path.basename(dst)
                    info.extension = os.path.splitext(dst)[1]
                    self._updating_table = True
                    self.table.item(row, self.COL_FILENAME).setText(info.filename)
                    self.table.item(row, self.COL_FILENAME).setToolTip(dst)
                    status_item = self.table.item(row, self.COL_STATUS)
                    status_item.setText("✓ Renamed")
                    status_item.setForeground(QColor("#6dd5ed"))
                    self._updating_table = False
                    if hasattr(info, 'grid_item') and info.grid_item: info.grid_item.setText(info.filename)
                    moved_extra = self._move_sidecars(src, dst)
                    self._refresh_row_dates(info)
                    self._update_date_items(row, info)
                    self._add_to_history(src, dst, row, extra=moved_extra)
                    success_count += 1
                except Exception as e:
                    error_count += 1
                    errors.append(f"{info.filename}: {e}")
                    status_item = self.table.item(row, self.COL_STATUS)
                    if status_item:
                        status_item.setText("✕ Error")
                        status_item.setForeground(QColor("#f87171"))
                        status_item.setToolTip(str(e))
            if success_count > 0:
                self._known_files_dirty = True
        finally:
            self._updating_table = False
            self.table.setSortingEnabled(was_sorting)
        msg = f"✅ Successfully renamed {success_count} file{'s' if success_count != 1 else ''}."
        if error_count > 0:
            msg += f"\n\n❌ {error_count} error{'s' if error_count != 1 else ''}:\n"
            msg += "\n".join(errors[:10])
            if len(errors) > 10: msg += f"\n… and {len(errors) - 10} more."
        self.status_label.setText(f"Done — {success_count} renamed, {error_count} errors.")
        if success_count > 0:
            self._show_toast(f"Done — {success_count} renamed, {error_count} errors.", 'success' if error_count == 0 else 'warning')
        else:
            self._show_toast(f"Rename failed: {error_count} errors.", 'error')
        self._update_stats()
        self.btn_undo.setEnabled(len(self._rename_history) > 0)
        QMessageBox.information(self, "Rename Complete", msg)

    def _add_to_history(self, src: str, dst: str, row: int, clear_redo=True, extra=None):
        extra = list(extra or [])
        self._rename_history.append({'timestamp': datetime.now().isoformat(), 'src': src, 'dst': dst, 'row': row,
                                     'filename': os.path.basename(dst), 'extra': extra})
        # C3: append-only audit trail (forward renames; undo/redo are implied)
        append_rename_audit([(src, dst)] + extra)
        if len(self._rename_history) > 50: self._rename_history.pop(0)
        self.btn_undo.setEnabled(True)
        if clear_redo:
            self._redo_history.clear()
            self.btn_redo.setEnabled(False)

    def _on_undo_rename(self):
        if not self._rename_history: return
        last = self._rename_history.pop()
        src = last['src']
        dst = last['dst']
        if os.path.exists(dst) and not os.path.exists(src):
            self._release_file_locks([dst, src])
            try:
                shutil.move(dst, src)
                # Revert sidecar moves (best-effort; failures never block undo)
                extra_done = []
                for o_, n_ in reversed(last.get('extra') or []):
                    if os.path.exists(n_) and not os.path.exists(o_):
                        try:
                            shutil.move(n_, o_)
                            extra_done.append((o_, n_))
                        except OSError as e_:
                            logger.warning("Undo sidecar (%s -> %s): %s", n_, o_, e_)
                row = last['row']
                try:
                    if row < self.table.rowCount():
                        info = self._get_row_info(row)
                        if info and info.filepath == dst:
                            self._updating_table = True
                            info.filepath = src
                            info.filename = os.path.basename(src)
                            self.table.item(row, self.COL_FILENAME).setText(info.filename)
                            self.table.item(row, self.COL_FILENAME).setToolTip(src)
                            self.table.item(row, self.COL_STATUS).setText("✓ Valid")
                            self.table.item(row, self.COL_STATUS).setForeground(QColor("#34d399"))
                            if hasattr(info, 'grid_item') and info.grid_item: info.grid_item.setText(info.filename)
                except Exception as te:
                    # Table update failed after successful move — attempt to roll
                    # back the move so disk state and table state stay in sync.
                    logger.exception("Table update failed after move; rolling back")
                    try:
                        shutil.move(src, dst)
                    except Exception:
                        # Rollback failed — disk state is now different from
                        # table. Log loudly so the user knows.
                        logger.error("ROLLBACK FAILED for %s -> %s; filesystem and UI are out of sync", src, dst)
                        QMessageBox.critical(self, "Fatal Desync", f"Filesystem and UI out of sync. Please reload folder.\n\nFailed to revert:\n{src}\nto\n{dst}")
                        return
                    for p_, q_ in reversed(extra_done):
                        try:
                            shutil.move(p_, q_)
                        except OSError as e_:
                            logger.error("Undo sidecar rollback failed (%s -> %s): %s", p_, q_, e_)
                    self._rename_history.append(last)
                    return
                finally:
                    self._updating_table = False
                self.status_label.setText(f"↩️ Undone: {os.path.basename(dst)}")
                self._show_toast(f"↩️ Undone: {os.path.basename(dst)}", 'success')
                self._update_stats()
                self._known_files_dirty = True
                self._redo_history.append(last)
                self.btn_redo.setEnabled(True)
            except Exception as e:
                QMessageBox.warning(self, "Undo Failed", f"Cannot undo rename:\n{e}")
                # Note: only re-append if not already re-appended by the table-update rollback
                if not self._rename_history or self._rename_history[-1] is not last:
                    self._rename_history.append(last)
        else:
            QMessageBox.warning(self, "Undo Unavailable", "Cannot undo: file has been moved or renamed again.")
        self.btn_undo.setEnabled(len(self._rename_history) > 0)
        self.btn_redo.setEnabled(len(self._redo_history) > 0)

    def _on_redo_rename(self):
        if not self._redo_history: return
        last = self._redo_history.pop()
        src = last['src']
        dst = last['dst']
        if os.path.exists(src) and not os.path.exists(dst):
            self._release_file_locks([src, dst])
            try:
                shutil.move(src, dst)
                extra_done = []
                for o_, n_ in (last.get('extra') or []):
                    if os.path.exists(o_) and not os.path.exists(n_):
                        try:
                            shutil.move(o_, n_)
                            extra_done.append((o_, n_))
                        except OSError as e_:
                            logger.warning("Redo sidecar (%s -> %s): %s", o_, n_, e_)
                row = last['row']
                try:
                    if row < self.table.rowCount():
                        info = self._get_row_info(row)
                        if info and info.filepath == src:
                            self._updating_table = True
                            info.filepath = dst
                            info.filename = os.path.basename(dst)
                            self.table.item(row, self.COL_FILENAME).setText(info.filename)
                            self.table.item(row, self.COL_FILENAME).setToolTip(dst)
                            self.table.item(row, self.COL_STATUS).setText("✓ Renamed")
                            self.table.item(row, self.COL_STATUS).setForeground(QColor("#6dd5ed"))
                            if hasattr(info, 'grid_item') and info.grid_item: info.grid_item.setText(info.filename)
                except Exception as te:
                    # Table update failed after successful move — roll the move
                    # back so disk state and table state stay in sync (mirrors
                    # the undo path; previously a failure here re-queued an
                    # already-applied entry and lost the undo history).
                    logger.exception("Table update failed after redo move; rolling back")
                    try:
                        shutil.move(dst, src)
                    except Exception:
                        logger.error("ROLLBACK FAILED for %s -> %s; filesystem and UI are out of sync", dst, src)
                        QMessageBox.critical(self, "Fatal Desync", f"Filesystem and UI out of sync. Please reload folder.\n\nFailed to revert:\n{dst}\nto\n{src}")
                        return
                    for p_, q_ in reversed(extra_done):
                        try:
                            shutil.move(q_, p_)
                        except OSError as e_:
                            logger.error("Redo sidecar rollback failed (%s -> %s): %s", q_, p_, e_)
                    self._redo_history.append(last)
                    return
                finally:
                    self._updating_table = False
                self.status_label.setText(f"🔁 Redone: {os.path.basename(dst)}")
                self._show_toast(f"🔁 Redone: {os.path.basename(dst)}", 'success')
                self._update_stats()
                self._known_files_dirty = True
                # Carry sidecar pairs forward — a later undo must revert them too
                self._add_to_history(src, dst, row, clear_redo=False, extra=last.get('extra'))
            except Exception as e:
                QMessageBox.warning(self, "Redo Failed", f"Cannot redo rename:\n{e}")
                self._redo_history.append(last)
        else:
            QMessageBox.warning(self, "Redo Unavailable", "Cannot redo: file has been deleted, moved, or renamed again.")
        self.btn_redo.setEnabled(len(self._redo_history) > 0)
        self.btn_undo.setEnabled(len(self._rename_history) > 0)

    def _apply_saved_file_data_to_row(self, row: int):
        """Apply persisted artist/rating/tags (from config) to a single row."""
        info = self._get_row_info(row)
        if not info: return
        data = self._saved_file_data.get(os.path.normpath(info.filepath))
        if not data: return

        artist = data.get('artist', '')
        if artist:
            artist_item = self.table.item(row, self.COL_ARTIST)
            if artist_item: artist_item.setText(artist)
            artist_widget = self.table.cellWidget(row, self.COL_ARTIST)
            if artist_widget: artist_widget.setText(artist)

        rating = data.get('rating', '—')
        if rating != '—':
            rating_item = self.table.item(row, self.COL_RATING)
            if rating_item:
                rating_item.setText(rating)
                rating_item.sort_key = int(rating) if rating.isdigit() else 0
            rating_widget = self.table.cellWidget(row, self.COL_RATING)
            if rating_widget:
                idx = rating_widget.findText(rating)
                if idx >= 0: rating_widget.setCurrentIndex(idx)

        tags = data.get('tags', [])
        if tags:
            info.tags = tags
            tags_item = self.table.item(row, self.COL_TAGS)
            if tags_item: tags_item.setText(", ".join(tags))
            tags_widget = self.table.cellWidget(row, self.COL_TAGS)
            if tags_widget: tags_widget.setText(", ".join(tags))

    def _restore_file_data(self):
        was_sorting = self.table.isSortingEnabled()
        self.table.setSortingEnabled(False)
        self._updating_table = True
        try:
            for row in range(self.table.rowCount()):
                info = self._get_row_info(row)
                if not info: continue
                self._apply_saved_file_data_to_row(row)
                self._update_row_preview(row)
        finally:
            self._updating_table = False
            self.table.setSortingEnabled(was_sorting)

    def _find_exact_duplicates(self): self._find_duplicates_logic(mode='exact')
    def _find_visual_duplicates(self): self._find_duplicates_logic(mode='visual')

    def _find_duplicates_logic(self, mode='exact'):
        if mode == 'visual' and self.media_type == 'audio':
            QMessageBox.warning(self, "Unsupported", "Visual duplicates scanning is not supported for Audio files."); return
        self._clear_highlights()
        # Collect info OBJECTS (not row indices) — rows can shift during the
        # scan, but object identity is stable. Rows are resolved fresh at
        # highlight time via id(info) -> current row.
        valid_infos = []
        for r in range(self.table.rowCount()):
            info = self._get_row_info(r)
            if info and info.is_valid:
                valid_infos.append(info)
        if not valid_infos:
            QMessageBox.information(self, "No Files", "No valid files loaded to scan for duplicates."); return
        self.progress_bar.setVisible(True)
        self.progress_bar.setMaximum(len(valid_infos))
        self.progress_bar.setValue(0)
        task_name = "MD5 exact" if mode == 'exact' else "pHash visual"
        self.progress_bar.setFormat(f"Scanning duplicates ({task_name}): %v/%m…")
        self.status_label.setText(f"Scanning duplicates ({task_name})…")
        hashes = {}  # id(info) -> hash string
        # Suspend watch mode: its 3s timer mutates rows and would corrupt the
        # id->row mapping resolved below.
        watch_was_active = False
        if getattr(self, '_watch_timer', None) is not None and self._watch_timer.isActive():
            watch_was_active = True
            self._watch_timer.stop()
        # Disable duplicate buttons during scan to prevent re-entrancy from
        # processEvents() mid-loop. The old code's processEvents() allowed the
        # user to trigger another scan mid-scan, corrupting table state.
        self.btn_find_dupes.setEnabled(False)
        try:
            for idx, info in enumerate(valid_infos):
                # Use head-only hashing for large files to avoid minutes-long
                # full-file MD5 on multi-GB videos.
                if mode == 'exact': h = calculate_file_hash(info.filepath, head_only=True)
                else: h = calculate_perceptual_hash(info.filepath, self.media_type)
                if h: hashes[id(info)] = h
                self.progress_bar.setValue(idx + 1)
                # Keep UI responsive while EXCLUDING user input events — plain
                # processEvents() let sort clicks / Delete shortcut mutate rows
                # mid-hash, which mislabeled the wrong files as duplicates.
                QApplication.processEvents(QEventLoop.ProcessEventsFlag.ExcludeUserInputEvents)
        finally:
            self.btn_find_dupes.setEnabled(True)
            if watch_was_active and getattr(self, '_watch_enabled', False):
                self._watch_timer.start(3000)
        self.progress_bar.setVisible(False)
        self.status_label.setText("Processing duplicates list…")
        QApplication.processEvents(QEventLoop.ProcessEventsFlag.ExcludeUserInputEvents)
        groups = []  # each group is a list of id(info)
        if mode == 'exact':
            hash_to_ids = {}
            for i, h in hashes.items(): hash_to_ids.setdefault(h, []).append(i)
            for h, grp in hash_to_ids.items():
                if len(grp) > 1: groups.append(grp)
        else:
            # Single-linkage grouping: compare against ANY member of the group,
            # not just the representative. The old code tested each candidate
            # only against the first element, so chained near-duplicates
            # (A≈B≈C where A≁C) silently escaped grouping.
            visited = set()
            ids_list = list(hashes.keys())
            for i in range(len(ids_list)):
                seed = ids_list[i]
                if seed in visited: continue
                current_group = [seed]
                visited.add(seed)
                grew = True
                while grew:  # grow until transitive closure
                    grew = False
                    for cand in ids_list:
                        if cand in visited: continue
                        if any(hamming_distance(hashes[m], hashes[cand]) <= 10 for m in current_group):
                            current_group.append(cand)
                            visited.add(cand)
                            grew = True
                if len(current_group) > 1: groups.append(current_group)
        # Resolve CURRENT rows for the flagged infos (sort-proof)
        id_to_row = {}
        for r in range(self.table.rowCount()):
            ri = self._get_row_info(r)
            if ri is not None: id_to_row[id(ri)] = r
        if not groups:
            self.status_label.setText("No duplicates found.")
            QMessageBox.information(self, "No Duplicates", f"No {mode} duplicates found in the current list.")
            for row in range(self.table.rowCount()):
                self.table.setRowHidden(row, False)
                info = self._get_row_info(row)
                if info and hasattr(info, 'grid_item') and info.grid_item: info.grid_item.setHidden(False)
            self._update_stats()
            return
        was_sorting = self.table.isSortingEnabled()
        self.table.setSortingEnabled(False)
        self.filtered_rows.clear()
        for row in range(self.table.rowCount()):
            self.table.setRowHidden(row, True)
            info = self._get_row_info(row)
            if info and hasattr(info, 'grid_item') and info.grid_item: info.grid_item.setHidden(True)
        total_dupes = 0
        for group_idx, grp in enumerate(groups):
            bg_color = QColor(239, 68, 68, 38) if group_idx % 2 == 0 else QColor(245, 158, 11, 38)
            for iid in grp:
                row = id_to_row.get(iid, -1)
                if row < 0: continue
                total_dupes += 1
                self.filtered_rows.add(row)
                self.table.setRowHidden(row, False)
                info = self._get_row_info(row)
                if info and hasattr(info, 'grid_item') and info.grid_item: info.grid_item.setHidden(False)
                status_item = self.table.item(row, self.COL_STATUS)
                if status_item:
                    status_item.setText(f"⚠️ Dup Group {group_idx + 1}")
                    status_item.setForeground(QColor("#f87171"))
                    status_item.sort_key = group_idx
                for col in range(self.table.columnCount()):
                    item = self.table.item(row, col)
                    if item: item.setBackground(bg_color)
        self.table.setSortingEnabled(True)
        self.table.sortByColumn(self.COL_STATUS, Qt.SortOrder.AscendingOrder)
        self.table.setSortingEnabled(was_sorting)
        self.status_label.setText(f"Found {len(groups)} duplicate group(s) ({total_dupes} files total). Click 'Sync Files' to reset view.")
        self._update_stats()

    def _clear_highlights(self):
        for row in range(self.table.rowCount()):
            info = self._get_row_info(row)
            if info:
                status_item = self.table.item(row, self.COL_STATUS)
                if status_item:
                    if info.is_valid:
                        status_item.setText("✓ Valid"); status_item.setForeground(QColor("#34d399"))
                    else:
                        status_item.setText("⚠ Unsupported"); status_item.setForeground(QColor("#f87171"))
                    status_item.sort_key = None
                for col in range(self.table.columnCount()):
                    item = self.table.item(row, col)
                    if item: item.setBackground(QBrush(Qt.BrushStyle.NoBrush))

    def _toggle_view_mode(self, checked):
        if checked:
            self.view_stack.setCurrentIndex(1)
            self.btn_view_mode.setText("List View")
        else:
            self.view_stack.setCurrentIndex(0)
            self.btn_view_mode.setText("Grid View")

    def _toggle_preview(self, checked):
        self.preview_panel.setVisible(checked)
        self.btn_toggle_preview.setChecked(checked)
        # Symmetric exclusivity: opening the preview closes the stats panel
        # (stats already closed preview; previously one-directional)
        if checked and self.btn_toggle_stats.isChecked():
            self._toggle_stats(False)
        self._update_preview_pane()

    def _close_preview_pane(self): self._toggle_preview(False)

    def _build_stats_panel(self):
        self.stats_panel = QFrame()
        self.stats_panel.setObjectName("statsPanel")
        self.stats_panel.setFixedWidth(320)
        self.stats_panel.setVisible(False)
        layout = QVBoxLayout(self.stats_panel)
        layout.setContentsMargins(12, 12, 12, 12)
        layout.setSpacing(12)

        header_layout = QHBoxLayout()
        title = QLabel("📊 Library Statistics")
        title.setStyleSheet("font-weight: bold; font-size: 14px;")
        header_layout.addWidget(title)
        header_layout.addStretch()
        
        btn_close = QPushButton("✕")
        btn_close.setObjectName("btnClosePreview")
        btn_close.setFixedSize(24, 24)
        btn_close.setCursor(Qt.CursorShape.PointingHandCursor)
        btn_close.clicked.connect(lambda: self._toggle_stats(False))
        header_layout.addWidget(btn_close)
        layout.addLayout(header_layout)

        scroll_area = QScrollArea()
        scroll_area.setWidgetResizable(True)
        scroll_area.setFrameShape(QFrame.Shape.NoFrame)
        scroll_area.setStyleSheet("background: transparent;")
        
        self.stats_content = QWidget()
        self.stats_layout = QVBoxLayout(self.stats_content)
        self.stats_layout.setContentsMargins(0, 0, 0, 0)
        self.stats_layout.setSpacing(16)
        
        scroll_area.setWidget(self.stats_content)
        layout.addWidget(scroll_area)

    def _toggle_stats(self, checked):
        self.btn_toggle_stats.setChecked(checked)
        self.stats_panel.setVisible(checked)
        if checked:
            if self.btn_toggle_preview.isChecked():
                self._toggle_preview(False)
            self._update_stats_dashboard()

    def _update_stats_dashboard(self):
        if not hasattr(self, 'stats_panel') or not self.stats_panel.isVisible():
            return
            
        # Clear old stats
        while self.stats_layout.count():
            item = self.stats_layout.takeAt(0)
            if item.widget():
                item.widget().deleteLater()
                
        if not self.media_infos:
            self.stats_layout.addWidget(QLabel("No media loaded."))
            self.stats_layout.addStretch()
            return
            
        total_files = len(self.media_infos)
        valid_files = sum(1 for i in self.media_infos if i.is_valid)
        invalid_files = total_files - valid_files
        total_size = sum(i.size_bytes for i in self.media_infos if getattr(i, 'size_bytes', 0))
        
        def add_section(title, content_dict):
            group = QGroupBox(title)
            group.setStyleSheet("QGroupBox { font-weight: bold; padding-top: 15px; margin-top: 10px; }")
            l = QFormLayout(group)
            l.setContentsMargins(10, 15, 10, 10)
            for k, v in content_dict.items():
                lbl = QLabel(str(v))
                lbl.setWordWrap(True)
                l.addRow(k + ":", lbl)
            self.stats_layout.addWidget(group)

        # Overview
        add_section("Overview", {
            "Total Files": total_files,
            "Valid Files": valid_files,
            "Invalid/Errors": invalid_files,
            "Total Size": format_size(total_size)
        })

        # Formats
        formats = {}
        for i in self.media_infos:
            if not i.is_valid: continue
            ext = os.path.splitext(i.filename)[1].lower() or "Unknown"
            formats[ext] = formats.get(ext, 0) + 1
            
        format_stats = {k: f"{v} ({(v/valid_files*100):.1f}%)" for k, v in sorted(formats.items(), key=lambda x: x[1], reverse=True)[:10]}
        if format_stats:
            add_section("Format Breakdown", format_stats)

        # Resolutions
        if self.media_type in ('video', 'image', 'all'):
            res = {}
            for i in self.media_infos:
                if not i.is_valid: continue
                tag = getattr(i, 'resolution_tag', '') or (f"{i.width}x{i.height}" if i.width and i.height else "")
                if tag:
                    res[tag] = res.get(tag, 0) + 1
            res_stats = {k: str(v) for k, v in sorted(res.items(), key=lambda x: x[1], reverse=True)[:10]}
            if res_stats:
                add_section("Resolutions", res_stats)
                
        # Durations
        if self.media_type in ('video', 'audio', 'all'):
            durs = [i.duration_seconds for i in self.media_infos if i.is_valid and hasattr(i, 'duration_seconds') and i.duration_seconds > 0]
            if durs:
                add_section("Duration", {
                    "Total": format_duration(sum(durs)),
                    "Average": format_duration(sum(durs)/len(durs)),
                    "Shortest": format_duration(min(durs)),
                    "Longest": format_duration(max(durs))
                })

        # Ratings
        ratings = {}
        for i in self.media_infos:
            if not i.is_valid: continue
            _, parsed_rating = parse_naming_format(i.filename)
            r = parsed_rating or "Unrated"
            ratings[r] = ratings.get(r, 0) + 1
        rat_stats = {k: str(v) for k, v in sorted(ratings.items(), key=lambda x: (x[0] != "Unrated", float(x[0]) if x[0].replace('.','',1).isdigit() else 0), reverse=True)[:10]}
        if rat_stats:
            add_section("Ratings", rat_stats)
            
        # Tags
        tags = {}
        for i in self.media_infos:
            if not i.is_valid: continue
            for t in getattr(i, 'tags', []):
                tags[t] = tags.get(t, 0) + 1
        tag_stats = {k: str(v) for k, v in sorted(tags.items(), key=lambda x: x[1], reverse=True)[:10]}
        if tag_stats:
            add_section("Top Tags", tag_stats)

        self.stats_layout.addStretch()

    def _build_preview_pane(self):
        self.preview_panel = QFrame()
        self.preview_panel.setObjectName("previewPanel")
        self.preview_panel.setFixedWidth(320)
        self.preview_panel.setVisible(False)
        preview_layout = QVBoxLayout(self.preview_panel)
        preview_layout.setContentsMargins(12, 12, 12, 12)
        preview_layout.setSpacing(12)
        header_layout = QHBoxLayout()
        self.preview_title = QLabel("Preview")
        self.preview_title.setStyleSheet("font-size: 13px; font-weight: bold; color: #a78bfa;")
        self.preview_title.setWordWrap(True)
        self.btn_close_preview = QPushButton("")
        self.btn_close_preview.setObjectName("btnClosePreview")
        self.btn_close_preview.setFixedSize(24, 24)
        self.btn_close_preview.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_close_preview.clicked.connect(self._close_preview_pane)
        self.btn_close_preview.setIconSize(QSize(16, 16))
        header_layout.addWidget(self.preview_title, 1)
        header_layout.addWidget(self.btn_close_preview)
        preview_layout.addLayout(header_layout)
        self.preview_stack = QStackedWidget()
        self.preview_stack.setMinimumHeight(240)
        self.preview_image = QLabel()
        self.preview_image.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.preview_image.setStyleSheet("background: rgba(10, 10, 20, 0.6); border-radius: 8px;")
        self.video_widget = QVideoWidget()
        self.video_widget.setStyleSheet("background: rgba(10, 10, 20, 0.6); border-radius: 8px;")
        self.no_preview_label = QLabel("Select a file to preview")
        self.no_preview_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.no_preview_label.setStyleSheet("color: #7c7c9a; font-size: 12px; background: rgba(10, 10, 20, 0.4); border-radius: 8px;")
        self.preview_stack.addWidget(self.preview_image)
        self.preview_stack.addWidget(self.video_widget)
        self.preview_stack.addWidget(self.no_preview_label)
        self.preview_stack.setCurrentIndex(2)
        preview_layout.addWidget(self.preview_stack)
        self.preview_controls = QFrame()
        self.preview_controls.setVisible(False)
        controls_layout = QVBoxLayout(self.preview_controls)
        controls_layout.setContentsMargins(6, 6, 6, 6)
        controls_layout.setSpacing(6)
        self.seek_slider = ClickToSeekSlider(Qt.Orientation.Horizontal)
        controls_layout.addWidget(self.seek_slider)
        btn_layout = QHBoxLayout()
        btn_layout.setSpacing(8)
        self.btn_play = QPushButton("")
        self.btn_play.setObjectName("btnPlay")
        self.btn_play.setFixedSize(32, 32)
        self.btn_play.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_play.clicked.connect(self._toggle_playback)
        self.btn_play.setIconSize(QSize(18, 18))
        self.btn_mute = QPushButton("")
        self.btn_mute.setObjectName("btnMute")
        self.btn_mute.setFixedSize(32, 32)
        self.btn_mute.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_mute.clicked.connect(self._toggle_mute)
        self.btn_mute.setIconSize(QSize(18, 18))
        self.time_label = QLabel("00:00 / 00:00")
        self.time_label.setAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
        btn_layout.addWidget(self.btn_play)
        btn_layout.addWidget(self.btn_mute)
        btn_layout.addStretch()
        btn_layout.addWidget(self.time_label)
        controls_layout.addLayout(btn_layout)
        preview_layout.addWidget(self.preview_controls)
        self.player = QMediaPlayer()
        self.audio_output = QAudioOutput()
        self.player.setAudioOutput(self.audio_output)
        self.player.setVideoOutput(self.video_widget)
        self.player.positionChanged.connect(self._on_player_position_changed)
        self.player.durationChanged.connect(self._on_player_duration_changed)
        self.player.playbackStateChanged.connect(self._on_player_state_changed)
        self.seek_slider.valueChanged.connect(self._on_slider_moved)

    def _stop_and_clear_media_player(self):
        if hasattr(self, 'player') and self.player:
            if self.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState:
                self.player.stop()
            self.player.setSource(QUrl())
        if hasattr(self, 'preview_image') and self.preview_image:
            self.preview_image.clear()

    def _release_file_locks(self, target_filepaths: list[str] = None):
        self._stop_and_clear_media_player()
        main_win = self.window()
        if main_win:
            if hasattr(main_win, 'hover_overlay') and main_win.hover_overlay:
                overlay_info = getattr(main_win.hover_overlay, 'info', None)
                if not target_filepaths or overlay_info is None or overlay_info.filepath in target_filepaths:
                    main_win.hover_overlay.hide_preview()
            if hasattr(main_win, '_native_players') and main_win._native_players:
                target_set = set(target_filepaths) if target_filepaths else None
                for player_win in list(main_win._native_players):
                    try:
                        if player_win.isVisible():
                            p_path = getattr(player_win, 'filepath', None)
                            info_l = getattr(player_win, 'info_left', None)
                            info_r = getattr(player_win, 'info_right', None)
                            paths = set()
                            if p_path: paths.add(p_path)
                            if info_l: paths.add(info_l.filepath)
                            if info_r: paths.add(info_r.filepath)
                            if target_set is None or (paths & target_set):
                                player_win.close()
                    except Exception:
                        pass

    def _update_preview_pane(self):
        if not self.btn_toggle_preview.isChecked():
            self._stop_and_clear_media_player()
            return
        selected_rows = []
        for rng in self.table.selectedRanges():
            for row in range(rng.topRow(), rng.bottomRow() + 1): selected_rows.append(row)
        selected_rows = list(set(selected_rows))
        if len(selected_rows) != 1:
            self._stop_and_clear_media_player()
            self.preview_stack.setCurrentIndex(2)
            self.preview_controls.setVisible(False)
            if len(selected_rows) > 1: self.no_preview_label.setText("Multiple files selected\nSelect a single file to preview")
            else: self.no_preview_label.setText("Select a file to preview")
            self.preview_title.setText("Preview")
            return
        row = selected_rows[0]
        info = self._get_row_info(row)
        if not info or not info.is_valid:
            self._stop_and_clear_media_player()
            self.preview_stack.setCurrentIndex(2)
            self.preview_controls.setVisible(False)
            self.no_preview_label.setText("No preview available\nfor invalid files")
            self.preview_title.setText(info.filename if info else "Preview")
            return
        self.preview_title.setText(info.filename)
        filepath = info.filepath
        if info.media_type == 'image':
            self._stop_and_clear_media_player()
            self.preview_controls.setVisible(False)
            self.preview_stack.setCurrentIndex(0)
            pixmap = QPixmap(filepath)
            if not pixmap.isNull():
                scaled_pix = pixmap.scaled(290, 220, Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation)
                self.preview_image.setPixmap(scaled_pix)
            else: self.preview_image.setText("Failed to load image")
        elif info.media_type == 'video':
            self.preview_image.clear()
            self.preview_stack.setCurrentIndex(1)
            self.preview_controls.setVisible(True)
            self.player.setSource(QUrl.fromLocalFile(filepath))
            main_win = self.window()
            is_globally_muted = getattr(main_win, 'global_mute', False)
            self.audio_output.setMuted(is_globally_muted)
            is_dark = getattr(main_win, 'current_theme', 'dark') == 'dark'
            self.btn_mute.setIcon(get_vector_icon('mute' if is_globally_muted else 'unmute', is_dark))
            self.btn_mute.setText("")
            self.player.play()
        elif info.media_type == 'audio':
            self.preview_stack.setCurrentIndex(0)
            self.preview_controls.setVisible(True)
            placeholder_pix = QPixmap(290, 220)
            placeholder_pix.fill(QColor("#1e1b4b"))
            with QPainter(placeholder_pix) as painter:
                painter.setRenderHint(QPainter.RenderHint.Antialiasing)
                painter.setFont(QFont(BASE_FONT_FAMILY, 48))
                painter.setPen(QColor("#a78bfa"))
                painter.drawText(QRect(0, 0, 290, 220), Qt.AlignmentFlag.AlignCenter, "🎵")
            self.preview_image.setPixmap(placeholder_pix)
            self.player.setSource(QUrl.fromLocalFile(filepath))
            main_win = self.window()
            is_globally_muted = getattr(main_win, 'global_mute', False)
            self.audio_output.setMuted(is_globally_muted)
            is_dark = getattr(main_win, 'current_theme', 'dark') == 'dark'
            self.btn_mute.setIcon(get_vector_icon('mute' if is_globally_muted else 'unmute', is_dark))
            self.btn_mute.setText("")
            self.player.play()
        elif info.media_type == 'pdf':
            self._stop_and_clear_media_player()
            self.preview_controls.setVisible(False)
            self.preview_stack.setCurrentIndex(2)
            self.no_preview_label.setText("No preview available\nDouble-click to open with system default")

    def _on_grid_selection_changed(self):
        if self._syncing_selection: return
        self._syncing_selection = True
        try:
            self.table.blockSignals(True)
            self.table.clearSelection()
            selected_items = self.grid_view.selectedItems()
            for row in range(self.table.rowCount()):
                info = self._get_row_info(row)
                if info and hasattr(info, 'grid_item') and info.grid_item in selected_items:
                    for col in range(self.table.columnCount()):
                        item = self.table.item(row, col)
                        if item: item.setSelected(True)
            self.table.blockSignals(False)
        finally:
            self._syncing_selection = False
        self._update_selection_buttons_and_preview()

    def _on_grid_item_double_clicked(self, item):
        info = item.data(Qt.ItemDataRole.UserRole)
        if not info: return
        for row in range(self.table.rowCount()):
            if self._get_row_info(row) is info: self._play_video(row); break

    def _update_selection_buttons_and_preview(self):
        selected_ranges = self.table.selectedRanges()
        selected_valid_count = 0
        for rng in selected_ranges:
            for row in range(rng.topRow(), rng.bottomRow() + 1):
                info = self._get_row_info(row)
                if info and info.is_valid:
                    selected_valid_count += 1
        self.btn_batch_edit.setEnabled(selected_valid_count > 0)
        self.btn_batch_tag.setEnabled(selected_valid_count >= 2)
        self.btn_delete.setEnabled(len(selected_ranges) > 0)
        self._update_preview_pane()

    def _toggle_playback(self):
        if self.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState: self.player.pause()
        else: self.player.play()

    def _toggle_mute(self):
        main_win = self.window()
        if main_win and hasattr(main_win, '_toggle_global_mute'): main_win._toggle_global_mute()
        else:
            is_muted = self.audio_output.isMuted()
            self.audio_output.setMuted(not is_muted)
            is_dark = getattr(main_win, 'current_theme', 'dark') == 'dark' if main_win else True
            self.btn_mute.setIcon(get_vector_icon('mute' if not is_muted else 'unmute', is_dark))
            self.btn_mute.setText("")

    def _on_player_state_changed(self, state):
        is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark'
        if state == QMediaPlayer.PlaybackState.PlayingState:
            self.btn_play.setIcon(get_vector_icon('pause', is_dark))
        else:
            self.btn_play.setIcon(get_vector_icon('play', is_dark))
        self.btn_play.setText("")

    def _on_player_position_changed(self, position):
        if not self.seek_slider.isSliderDown():
            self.seek_slider.blockSignals(True)
            self.seek_slider.setValue(position)
            self.seek_slider.blockSignals(False)
            self._update_time_label(position, self.player.duration())

    def _on_player_duration_changed(self, duration):
        self.seek_slider.blockSignals(True)
        self.seek_slider.setRange(0, duration)
        self.seek_slider.blockSignals(False)
        self._update_time_label(self.player.position(), duration)

    def _on_slider_moved(self, position): self.player.setPosition(position)

    def _update_time_label(self, position, duration):
        pos_sec = position // 1000
        dur_sec = duration // 1000
        pos_min = pos_sec // 60; pos_s = pos_sec % 60
        dur_min = dur_sec // 60; dur_s = dur_sec % 60
        self.time_label.setText(f"{pos_min:02d}:{pos_s:02d} / {dur_min:02d}:{dur_s:02d}")

    def _update_stats(self):
        visible_count = len([r for r in range(self.table.rowCount()) if not self.table.isRowHidden(r)])
        valid = sum(1 for v in self.media_infos if v.is_valid)
        unsupported = len(self.media_infos) - valid
        total_bytes = sum(v.size_bytes for v in self.media_infos if v.is_valid)
        if total_bytes >= 1024**3: size_str = f"{total_bytes / (1024**3):.2f} GB"
        elif total_bytes >= 1024**2: size_str = f"{total_bytes / (1024**2):.1f} MB"
        elif total_bytes >= 1024: size_str = f"{total_bytes / 1024:.0f} KB"
        else: size_str = f"{total_bytes} B"
        self.stat_total._value_label.setText(str(visible_count))
        self.stat_valid._value_label.setText(str(valid))
        self.stat_unsupported._value_label.setText(str(unsupported))
        self.stat_size._value_label.setText(size_str)
        if hasattr(self, '_update_stats_dashboard'):
            self._update_stats_dashboard()

        # Enable or disable process renaming button dynamically based on whether renaming targets are ready
        # Optimization: short-circuit if btn_process is already enabled AND we
        # haven't been marked dirty — avoids O(rows) scan on every selection
        # change, filter keystroke, etc. The dirty flag is set in
        # _update_row_preview / _on_input_changed_sender / _on_file_found.
        if hasattr(self, 'btn_process') and self.btn_process:
            if not getattr(self, '_stats_dirty', True) and self.btn_process.isEnabled():
                return
            ready_count = 0
            main_win = self.window()
            keep_ext = getattr(main_win, 'naming_keep_extension', True) if main_win else True
            for row in range(self.table.rowCount()):
                info = self._get_row_info(row)
                if not info or not info.is_valid: continue
                artist_widget = self.table.cellWidget(row, self.COL_ARTIST)
                rating_widget = self.table.cellWidget(row, self.COL_RATING)
                if not artist_widget or not rating_widget: continue
                artist = artist_widget.text().strip()
                rating = rating_widget.currentText()
                if self._is_naming_data_complete(artist, rating, info):
                    new_name = self._get_templated_name(artist, rating, info)
                    current_display_name = self.table.item(row, self.COL_FILENAME).text().strip() if self.table.item(row, self.COL_FILENAME) else ""
                    target_display = new_name + (info.extension if keep_ext else "") if new_name else ""
                    if target_display and target_display != current_display_name:
                        ready_count += 1
            self.btn_process.setEnabled(ready_count > 0)
            self._stats_dirty = False

    def _update_row_colors(self):
        is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark'
        meta_font = QFont(BASE_FONT_FAMILY, 9, QFont.Weight.Light)
        bold_meta_font = QFont(BASE_FONT_FAMILY, 9, QFont.Weight.Bold)
        for row in range(self.table.rowCount()):
            fname_item = self.table.item(row, self.COL_FILENAME)
            if fname_item:
                fname_item.setFont(QFont(BASE_FONT_FAMILY, 10, QFont.Weight.Bold))
                fname_item.setForeground(QColor("#c4b5fd") if is_dark else QColor("#1e3a8a"))
            size_item = self.table.item(row, self.COL_SIZE)
            if size_item:
                size_item.setFont(bold_meta_font)
                size_item.setForeground(QColor("#9ca3af") if is_dark else QColor("#64748b"))
            res_item = self.table.item(row, self.COL_RESOLUTION)
            if res_item:
                res_item.setFont(bold_meta_font)
                res_item.setForeground(QColor("#9ca3af") if is_dark else QColor("#64748b"))
            dur_item = self.table.item(row, self.COL_DURATION)
            if dur_item:
                dur_item.setFont(bold_meta_font)
                dur_item.setForeground(QColor("#9ca3af") if is_dark else QColor("#64748b"))
            preview_item = self.table.item(row, self.COL_PREVIEW)
            if preview_item:
                if preview_item.text() != "—":
                    preview_item.setFont(QFont(BASE_FONT_FAMILY, 10, QFont.Weight.Bold))
                    preview_item.setForeground(QColor("#34d399") if is_dark else QColor("#059669"))
                else:
                    preview_item.setFont(QFont(BASE_FONT_FAMILY, 10, QFont.Weight.Normal))
                    preview_item.setForeground(QColor("#7c7c9a") if is_dark else QColor("#64748b"))

    def keyPressEvent(self, event):
        if self.view_stack.currentIndex() == 0:  # table view
            if event.key() == Qt.Key.Key_Up:
                row = self.table.currentRow()
                if row > 0:
                    self.table.selectRow(row - 1)
                elif row == -1 and self.table.rowCount() > 0:
                    self.table.selectRow(0)
                return
            elif event.key() == Qt.Key.Key_Down:
                row = self.table.currentRow()
                if row < self.table.rowCount() - 1:
                    self.table.selectRow(row + 1 if row != -1 else 0)
                return
            elif event.key() in (Qt.Key.Key_Enter, Qt.Key.Key_Return):
                row = self.table.currentRow()
                if row >= 0:
                    self._play_video(row)
                return
            elif event.key() == Qt.Key.Key_A and (event.modifiers() & Qt.KeyboardModifier.ControlModifier):
                # FIX: selectRow() clears the previous selection on every call,
                # so the old loop left only the LAST visible row selected.
                # setRangeSelected(..., True) accumulates instead.
                for i in range(self.table.rowCount()):
                    if not self.table.isRowHidden(i):
                        self.table.setRangeSelected(
                            QTableWidgetSelectionRange(i, 0, i, self.table.columnCount() - 1), True)
                return
        super().keyPressEvent(event)

# ─── Main App Window ─────────────────────────────────────────────────────────────

def prune_native_players(main_win):
    """Drop closed player windows from the tracked list, safely.

    Player/comparison dialogs use WA_DeleteOnClose, so their Python wrappers
    can outlive the C++ objects; calling isVisible() on such a wrapper raises
    RuntimeError and (unhandled) silently broke all native playback afterwards.
    """
    players = getattr(main_win, '_native_players', None)
    if not players:
        return
    alive = []
    for p in players:
        try:
            if p.isVisible():
                alive.append(p)
        except RuntimeError:
            pass  # wrapper of an already-deleted window
    main_win._native_players = alive


class MediaFlowWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("MediaFlow — Multimedia Manager & Renamer")
        self.setMinimumSize(1300, 810)
        # FIX: was resize(1120, 630) which Qt clamps up to the 1300x810
        # minimum every launch — use a default at/above the minimum.
        self.resize(1400, 900)
        self._settings_visible = False
        self.setAcceptDrops(True)
        self.global_mute = False
        # Accessibility / comfort settings (overridden by _load_state)
        self.ui_scale = 1.0
        self.reduced_motion = False
        self.ffprobe_path = ""
        self.current_theme = "dark"
        self.naming_separator = ' '
        # Use module-level DEFAULT_NAMING_FIELDS constants for consistency
        # with _load_state (was inconsistent: __init__ had no "Tags", _load_state did).
        self.naming_fields = list(DEFAULT_NAMING_FIELDS)
        self.naming_all_fields_ordered = list(DEFAULT_NAMING_FIELDS_ORDERED)
        self.naming_keep_extension = True
        self.open_with_apps = []
        self._build_ui()

        self.hover_overlay = HoverPreviewOverlay(self)
        self._setup_shortcuts()
        self._active_toasts = []
        self._load_state()
        if not os.path.exists(CONFIG_FILE): self._center_on_screen()

    def show_toast(self, message, toast_type='info'):
        toast = ToastNotification(message, toast_type, parent=self)
        self._active_toasts.append(toast)

        start_y = self.height() - 20 - toast.sizeHint().height()
        
        for t in reversed(self._active_toasts[:-1]):
            if t.isVisible():
                start_y -= t.height() + 10
                
        target_pos = QPoint(self.width() - toast.width() - 20, start_y)
        
        toast.destroyed.connect(lambda: self._active_toasts.remove(toast) if toast in self._active_toasts else None)
        toast.show_toast(target_pos)

    def _center_on_screen(self):
        screen = QApplication.primaryScreen()
        if screen:
            screen_geo = screen.availableGeometry()
            x = (screen_geo.width() - self.width()) // 2 + screen_geo.x()
            y = (screen_geo.height() - self.height()) // 2 + screen_geo.y()
            self.move(x, y)

    def _build_ui(self):
        central = QWidget()
        self.setCentralWidget(central)
        main_layout = QHBoxLayout(central)
        main_layout.setContentsMargins(0, 0, 0, 0)
        main_layout.setSpacing(0)
        sidebar = QFrame()
        sidebar.setObjectName("sidebar")
        sidebar_layout = QVBoxLayout(sidebar)
        sidebar_layout.setContentsMargins(0, 32, 0, 24)
        sidebar_layout.setSpacing(8)
        logo_label = QLabel()
        logo_pix = QPixmap(get_resource_path("logo.png"))
        if not logo_pix.isNull(): logo_label.setPixmap(logo_pix.scaled(80, 80, Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation))
        logo_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        sidebar_layout.addWidget(logo_label)
        title_label = QLabel("MEDIAFLOW")
        title_label.setObjectName("titleLabel")
        title_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        subtitle_label = QLabel("Multimedia Manager")
        subtitle_label.setObjectName("subtitleLabel")
        subtitle_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        sidebar_layout.addWidget(title_label)
        sidebar_layout.addWidget(subtitle_label)
        sidebar_layout.addSpacing(40)
        self.btn_nav_videos = QPushButton("Videos")
        self.btn_nav_videos.setObjectName("navButton")
        self.btn_nav_videos.setProperty("active", True)
        self.btn_nav_videos.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_nav_videos.clicked.connect(lambda: self._switch_page(0))
        self.btn_nav_videos.setIconSize(QSize(18, 18))
        self.btn_nav_images = QPushButton("Images")
        self.btn_nav_images.setObjectName("navButton")
        self.btn_nav_images.setProperty("active", False)
        self.btn_nav_images.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_nav_images.clicked.connect(lambda: self._switch_page(1))
        self.btn_nav_images.setIconSize(QSize(18, 18))
        self.btn_nav_audio = QPushButton("Audio")
        self.btn_nav_audio.setObjectName("navButton")
        self.btn_nav_audio.setProperty("active", False)
        self.btn_nav_audio.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_nav_audio.clicked.connect(lambda: self._switch_page(2))
        self.btn_nav_audio.setIconSize(QSize(18, 18))
        self.btn_nav_pdfs = QPushButton("PDFs")
        self.btn_nav_pdfs.setObjectName("navButton")
        self.btn_nav_pdfs.setProperty("active", False)
        self.btn_nav_pdfs.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_nav_pdfs.clicked.connect(lambda: self._switch_page(3))
        self.btn_nav_pdfs.setIconSize(QSize(18, 18))
        sidebar_layout.addWidget(self.btn_nav_videos)
        sidebar_layout.addWidget(self.btn_nav_images)
        sidebar_layout.addWidget(self.btn_nav_audio)
        sidebar_layout.addWidget(self.btn_nav_pdfs)
        smart_header_widget = QWidget()
        smart_header_layout = QHBoxLayout(smart_header_widget)
        smart_header_layout.setContentsMargins(20, 16, 20, 4)
        lbl_smart_title = QLabel("SMART FOLDERS")
        lbl_smart_title.setObjectName("smartSidebarTitle")
        self.btn_add_smart = QPushButton("")
        self.btn_add_smart.setObjectName("btnAddSmartFolder")
        self.btn_add_smart.setFixedSize(20, 20)
        self.btn_add_smart.setIconSize(QSize(14, 14))
        self.btn_add_smart.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_add_smart.setToolTip("Create a new Smart Folder")
        self.btn_add_smart.clicked.connect(self._create_smart_folder_dialog)
        smart_header_layout.addWidget(lbl_smart_title, 0, Qt.AlignmentFlag.AlignVCenter)
        smart_header_layout.addStretch()
        smart_header_layout.addWidget(self.btn_add_smart, 0, Qt.AlignmentFlag.AlignVCenter)
        self.smart_scroll = QScrollArea()
        self.smart_scroll.setWidgetResizable(True)
        self.smart_scroll.setMinimumHeight(150)
        self.smart_container = QWidget()
        self.smart_container_layout = QVBoxLayout(self.smart_container)
        self.smart_container_layout.setContentsMargins(0, 0, 0, 0)
        self.smart_container_layout.setSpacing(4)
        self.smart_container_layout.addStretch()
        self.smart_scroll.setWidget(self.smart_container)
        self.smart_folders_config = []
        self.smart_folder_nav_items = {}
        self.smart_folder_tabs = {}
        sidebar_layout.addWidget(smart_header_widget)
        sidebar_layout.addWidget(self.smart_scroll, 1)
        sidebar_layout.addSpacing(12)
        main_layout.addWidget(sidebar)
        content_wrapper = QWidget()
        content_layout = QVBoxLayout(content_wrapper)
        content_layout.setContentsMargins(0, 0, 0, 0)
        content_layout.setSpacing(0)
        header_bar = QFrame()
        header_bar.setObjectName("headerBar")
        header_layout = QHBoxLayout(header_bar)
        header_layout.setContentsMargins(24, 16, 24, 16)
        self.page_title = QLabel("Videos")
        self.page_title.setObjectName("pageTitle")
        self.btn_global_mute = QPushButton("")
        self.btn_global_mute.setObjectName("btnGlobalMute")
        self.btn_global_mute.setFixedSize(36, 36)
        self.btn_global_mute.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_global_mute.clicked.connect(self._toggle_global_mute)
        self.btn_global_mute.setIconSize(QSize(20, 20))
        self.btn_help = QPushButton("?")
        self.btn_help.setObjectName("btnHelp")
        self.btn_help.setFixedSize(36, 36)
        self.btn_help.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_help.setToolTip("About MediaFlow & Help")
        self.btn_help.clicked.connect(self._show_help_dialog)
        self.btn_settings = QPushButton("")
        self.btn_settings.setObjectName("btnSettingsToggle")
        self.btn_settings.setFixedSize(36, 36)
        self.btn_settings.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_settings.clicked.connect(self._toggle_settings)
        self.btn_settings.setIconSize(QSize(20, 20))
        header_layout.addWidget(self.page_title)
        header_layout.addSpacing(20)
        self.progress_bar = QProgressBar()
        self.progress_bar.setVisible(False)
        self.progress_bar.setTextVisible(True)
        self.progress_bar.setMinimumWidth(250)
        self.progress_bar.setMaximumWidth(400)
        header_layout.addWidget(self.progress_bar)
        header_layout.addStretch()
        header_layout.addWidget(self.btn_global_mute)
        header_layout.addSpacing(8)
        header_layout.addWidget(self.btn_help)
        header_layout.addSpacing(8)
        header_layout.addWidget(self.btn_settings)
        content_layout.addWidget(header_bar)
        self.stacked_widget = QStackedWidget()
        content_layout.addWidget(self.stacked_widget, 1)
        self.video_tab = MediaTab('video')
        self.image_tab = MediaTab('image')
        self.audio_tab = MediaTab('audio')
        self.pdf_tab = MediaTab('pdf')
        self.stacked_widget.addWidget(self.video_tab)
        self.stacked_widget.addWidget(self.image_tab)
        self.stacked_widget.addWidget(self.audio_tab)
        self.stacked_widget.addWidget(self.pdf_tab)
        main_layout.addWidget(content_wrapper, 1)
        self.settings_panel = QFrame()
        self.settings_panel.setObjectName("settingsPanel")
        self.settings_panel.setMinimumWidth(0)
        self.settings_panel.setMaximumWidth(0)
        outer_layout = QVBoxLayout(self.settings_panel)
        outer_layout.setContentsMargins(16, 24, 16, 24)
        outer_layout.setSpacing(16)
        settings_header = QHBoxLayout()
        settings_title = QLabel("⚙️  Settings & Folders")
        settings_title.setStyleSheet("font-size: 16px; font-weight: 600; color: #a78bfa;")
        self.btn_close_settings = QPushButton("")
        self.btn_close_settings.setObjectName("btnCloseSettings")
        self.btn_close_settings.setFixedSize(28, 28)
        self.btn_close_settings.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_close_settings.clicked.connect(self._toggle_settings)
        self.btn_close_settings.setIconSize(QSize(18, 18))
        settings_header.addWidget(settings_title)
        settings_header.addStretch()
        settings_header.addWidget(self.btn_close_settings)
        outer_layout.addLayout(settings_header)
        scroll_area = QScrollArea()
        scroll_area.setObjectName("settingsScrollArea")
        scroll_area.setWidgetResizable(True)
        scroll_widget = QWidget()
        settings_layout = QVBoxLayout(scroll_widget)
        settings_layout.setContentsMargins(0, 0, 0, 0)
        settings_layout.setSpacing(16)
        
        # Appearance
        appearance_sec = QGroupBox("🎨  Appearance")
        appearance_sec_layout = QVBoxLayout(appearance_sec)
        theme_row = QHBoxLayout()
        theme_lbl = QLabel("Theme:")
        self.theme_combo = QComboBox()
        self.theme_combo.addItems(["System (Auto)", "Dark Mode", "Light Mode"])
        self.theme_combo.currentTextChanged.connect(self._on_theme_changed)
        theme_row.addWidget(theme_lbl)
        theme_row.addWidget(self.theme_combo, 1)
        appearance_sec_layout.addLayout(theme_row)

        # UI size (accessibility) — scales all stylesheet font sizes
        size_row = QHBoxLayout()
        size_lbl = QLabel("UI Size:")
        size_lbl.setToolTip("Scales text across the whole app (Compact / Normal / Large)")
        self.ui_size_combo = QComboBox()
        self.ui_size_combo.addItems(["Compact", "Normal", "Large"])
        self._ui_size_syncing = False
        self.ui_size_combo.currentTextChanged.connect(self._on_ui_size_changed)
        size_row.addWidget(size_lbl)
        size_row.addWidget(self.ui_size_combo, 1)
        appearance_sec_layout.addLayout(size_row)

        # Reduced motion — skips slide/fade animations (toasts, settings panel)
        self.reduced_motion_checkbox = QCheckBox("Reduce animations")
        self.reduced_motion_checkbox.setToolTip("Disables slide/fade animations for toasts and the settings panel")
        self.reduced_motion_checkbox.toggled.connect(self._on_reduced_motion_changed)
        appearance_sec_layout.addWidget(self.reduced_motion_checkbox)

        # Thumbnail size — applies to every tab's table + grid
        thumb_row = QHBoxLayout()
        thumb_lbl = QLabel("Thumbnails:")
        self.thumb_size_slider = QSlider(Qt.Orientation.Horizontal)
        self.thumb_size_slider.setRange(90, 200)
        self.thumb_size_slider.setValue(int(getattr(self, 'thumb_size', 130)))
        self.thumb_size_slider.setToolTip("Preview thumbnail size in list and grid views")
        self.thumb_size_value_lbl = QLabel(f"{self.thumb_size_slider.value()}px")
        self.thumb_size_value_lbl.setMinimumWidth(38)
        def _thumb_lbl(v): self.thumb_size_value_lbl.setText(f"{v}px")
        self.thumb_size_slider.valueChanged.connect(_thumb_lbl)
        self.thumb_size_slider.sliderReleased.connect(self._on_thumb_size_changed)
        self.thumb_size_slider.valueChanged.connect(self._on_thumb_size_live)
        thumb_row.addWidget(thumb_lbl)
        thumb_row.addWidget(self.thumb_size_slider, 1)
        thumb_row.addWidget(self.thumb_size_value_lbl)
        appearance_sec_layout.addLayout(thumb_row)

        settings_layout.addWidget(appearance_sec)

        # Custom Naming Template
        naming_sec = QGroupBox("🏷️  Custom Naming Template")
        naming_layout = QVBoxLayout(naming_sec)
        naming_layout.setSpacing(10)

        # Delimiter input row
        sep_row = QHBoxLayout()
        sep_lbl = QLabel("Separator:")
        sep_lbl.setToolTip("Separator/delimiter in between words (e.g. space, hyphen, underscore)")
        self.separator_input = QLineEdit()
        self.separator_input.setPlaceholderText("e.g. space, _ or -")
        self.separator_input.setText(self.naming_separator)
        self.separator_input.textChanged.connect(self._on_naming_template_changed)
        sep_row.addWidget(sep_lbl)
        sep_row.addWidget(self.separator_input, 1)
        naming_layout.addLayout(sep_row)

        # Drag-and-drop / checkable field list row
        list_lbl = QLabel("Fields (Check to include, Drag to reorder):")
        list_lbl.setStyleSheet("font-size: 11px; font-weight: 500;")
        naming_layout.addWidget(list_lbl)

        self.template_list = NamingTemplateListWidget(self)
        self.template_list.setFixedHeight(180)
        self.template_list.setDragDropMode(QAbstractItemView.DragDropMode.InternalMove)
        
        # Populate QListWidget initially (signals blocked to avoid saving default state immediately)
        self.template_list.blockSignals(True)
        self.template_list.model().blockSignals(True)
        for f_name in self.naming_all_fields_ordered:
            item = QListWidgetItem(f_name)
            item.setFlags(item.flags() | Qt.ItemFlag.ItemIsUserCheckable | Qt.ItemFlag.ItemIsDragEnabled)
            config_key = FIELD_MAP.get(f_name)
            is_checked = config_key in self.naming_fields
            item.setCheckState(Qt.CheckState.Checked if is_checked else Qt.CheckState.Unchecked)
            self.template_list.addItem(item)
        self.template_list.model().blockSignals(False)
        self.template_list.blockSignals(False)
        
        # NOTE: only itemChanged is connected — one user action previously fired
        # this handler 2-3x through redundant view+model signals (each run did
        # a full fsync save + refreshed every preview row in every tab).
        # Reorders are handled explicitly by NamingTemplateListWidget.dropEvent.
        self.template_list.itemChanged.connect(self._on_naming_template_changed)
        naming_layout.addWidget(self.template_list)

        # Preview layout
        self.template_preview_label = QLabel()
        self.template_preview_label.setStyleSheet("font-size: 11px; color: #a78bfa; font-weight: 500;")
        naming_layout.addWidget(self.template_preview_label)

        # Keep extension checkbox
        self.keep_extension_checkbox = QCheckBox("Keep File Extension")
        self.keep_extension_checkbox.setChecked(self.naming_keep_extension)
        self.keep_extension_checkbox.stateChanged.connect(self._on_naming_template_changed)
        naming_layout.addWidget(self.keep_extension_checkbox)

        settings_layout.addWidget(naming_sec)


        apps_sec = QGroupBox("🚀  Default Applications")
        apps_sec_layout = QVBoxLayout(apps_sec)
        apps_sec_layout.setSpacing(10)
        vp_label = QLabel("Video Player")
        vp_label.setProperty("heading", "true")
        apps_sec_layout.addWidget(vp_label)
        vp_row = QHBoxLayout()
        self.video_player_label = QLabel("System Default")
        self.video_player_label.setObjectName("appPathLabel")
        self.video_player_label.setWordWrap(True)
        self.btn_native_vp = QPushButton("Native")
        self.btn_native_vp.setObjectName("btnSettingsAdd")
        self.btn_native_vp.setFixedWidth(80)
        self.btn_native_vp.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_native_vp.clicked.connect(self._toggle_native_video_player)


        self.btn_browse_vp = QPushButton("Browse…")
        self.btn_browse_vp.setObjectName("btnSettingsAdd")
        self.btn_browse_vp.setFixedWidth(90)
        self.btn_browse_vp.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_browse_vp.clicked.connect(self._browse_video_player)
        self.btn_browse_vp.setIconSize(QSize(16, 16))
        self.btn_clear_vp = QPushButton("")
        self.btn_clear_vp.setObjectName("btnClearVP")
        self.btn_clear_vp.setFixedSize(28, 28)
        self.btn_clear_vp.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_clear_vp.setToolTip("Reset to system default")
        self.btn_clear_vp.clicked.connect(self._clear_video_player)
        self.btn_clear_vp.setIconSize(QSize(18, 18))
        vp_row.addWidget(self.video_player_label, 1)
        vp_row.addWidget(self.btn_native_vp)
        vp_row.addWidget(self.btn_browse_vp)
        vp_row.addWidget(self.btn_clear_vp)
        apps_sec_layout.addLayout(vp_row)
        io_label = QLabel("Photo Viewer")
        io_label.setProperty("heading", "true")
        apps_sec_layout.addWidget(io_label)
        io_row = QHBoxLayout()
        self.image_opener_label = QLabel("System Default")
        self.image_opener_label.setObjectName("appPathLabel")
        self.image_opener_label.setWordWrap(True)
        self.btn_native_io = QPushButton("Native")
        self.btn_native_io.setObjectName("btnSettingsAdd")
        self.btn_native_io.setFixedWidth(80)
        self.btn_native_io.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_native_io.clicked.connect(self._toggle_native_image_opener)
        self.btn_browse_io = QPushButton("Browse…")
        self.btn_browse_io.setObjectName("btnSettingsAdd")
        self.btn_browse_io.setFixedWidth(90)
        self.btn_browse_io.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_browse_io.clicked.connect(self._browse_image_opener)
        self.btn_browse_io.setIconSize(QSize(16, 16))
        self.btn_clear_io = QPushButton("")
        self.btn_clear_io.setObjectName("btnClearIO")
        self.btn_clear_io.setFixedSize(28, 28)
        self.btn_clear_io.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_clear_io.setToolTip("Reset to system default")
        self.btn_clear_io.clicked.connect(self._clear_image_opener)
        self.btn_clear_io.setIconSize(QSize(18, 18))
        io_row.addWidget(self.image_opener_label, 1)
        io_row.addWidget(self.btn_native_io)
        io_row.addWidget(self.btn_browse_io)
        io_row.addWidget(self.btn_clear_io)
        apps_sec_layout.addLayout(io_row)
        ap_label = QLabel("Audio Player")
        ap_label.setProperty("heading", "true")
        apps_sec_layout.addWidget(ap_label)
        ap_row = QHBoxLayout()
        self.audio_player_label = QLabel("System Default")
        self.audio_player_label.setObjectName("appPathLabel")
        self.audio_player_label.setWordWrap(True)
        self.btn_native_ap = QPushButton("Native")
        self.btn_native_ap.setObjectName("btnSettingsAdd")
        self.btn_native_ap.setFixedWidth(80)
        self.btn_native_ap.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_native_ap.clicked.connect(self._toggle_native_audio_player)
        self.btn_browse_ap = QPushButton("Browse…")
        self.btn_browse_ap.setObjectName("btnSettingsAdd")
        self.btn_browse_ap.setFixedWidth(90)
        self.btn_browse_ap.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_browse_ap.clicked.connect(self._browse_audio_player)
        self.btn_browse_ap.setIconSize(QSize(16, 16))
        self.btn_clear_ap = QPushButton("")
        self.btn_clear_ap.setObjectName("btnClearAP")
        self.btn_clear_ap.setFixedSize(28, 28)
        self.btn_clear_ap.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_clear_ap.setToolTip("Reset to system default")
        self.btn_clear_ap.clicked.connect(self._clear_audio_player)
        self.btn_clear_ap.setIconSize(QSize(18, 18))
        ap_row.addWidget(self.audio_player_label, 1)
        ap_row.addWidget(self.btn_native_ap)
        ap_row.addWidget(self.btn_browse_ap)
        ap_row.addWidget(self.btn_clear_ap)
        apps_sec_layout.addLayout(ap_row)
        pdf_label_app = QLabel("PDF Reader")
        pdf_label_app.setProperty("heading", "true")
        apps_sec_layout.addWidget(pdf_label_app)
        po_row = QHBoxLayout()
        self.pdf_opener_label = QLabel("System Default")
        self.pdf_opener_label.setObjectName("appPathLabel")
        self.pdf_opener_label.setWordWrap(True)
        self.btn_browse_po = QPushButton("Browse…")
        self.btn_browse_po.setObjectName("btnSettingsAdd")
        self.btn_browse_po.setFixedWidth(90)
        self.btn_browse_po.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_browse_po.clicked.connect(self._browse_pdf_opener)
        self.btn_browse_po.setIconSize(QSize(16, 16))
        self.btn_clear_po = QPushButton("")
        self.btn_clear_po.setObjectName("btnClearPO")
        self.btn_clear_po.setFixedSize(28, 28)
        self.btn_clear_po.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_clear_po.setToolTip("Reset to system default")
        self.btn_clear_po.clicked.connect(self._clear_pdf_opener)
        self.btn_clear_po.setIconSize(QSize(18, 18))
        po_row.addWidget(self.pdf_opener_label, 1)
        po_row.addWidget(self.btn_browse_po)
        po_row.addWidget(self.btn_clear_po)
        apps_sec_layout.addLayout(po_row)
        settings_layout.addWidget(apps_sec)
        ff_sec = QGroupBox("🔍  Deep Metadata (FFprobe)")
        ff_sec_layout = QVBoxLayout(ff_sec)
        ff_sec_layout.setSpacing(10)
        ff_desc = QLabel("Required for video codecs, audio tracks, and HDR detection.")
        ff_desc.setWordWrap(True)
        ff_sec_layout.addWidget(ff_desc)
        ffprobe_heading = QLabel("FFprobe Path")
        ffprobe_heading.setProperty("heading", "true")
        ff_sec_layout.addWidget(ffprobe_heading)
        ff_row = QHBoxLayout()
        self.ffprobe_path_label = QLabel("System PATH (Default)")
        self.ffprobe_path_label.setObjectName("appPathLabel")
        self.ffprobe_path_label.setWordWrap(True)
        self.btn_browse_ff = QPushButton("Browse…")
        self.btn_browse_ff.setObjectName("btnSettingsAdd")
        self.btn_browse_ff.setFixedWidth(90)
        self.btn_browse_ff.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_browse_ff.clicked.connect(self._browse_ffprobe_path)
        self.btn_browse_ff.setIconSize(QSize(16, 16))
        self.btn_clear_ff = QPushButton("")
        self.btn_clear_ff.setObjectName("btnClearFF")
        self.btn_clear_ff.setFixedSize(28, 28)
        self.btn_clear_ff.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_clear_ff.setToolTip("Reset to system PATH")
        self.btn_clear_ff.clicked.connect(self._clear_ffprobe_path)
        self.btn_clear_ff.setIconSize(QSize(18, 18))
        ff_row.addWidget(self.ffprobe_path_label, 1)
        ff_row.addWidget(self.btn_browse_ff)
        ff_row.addWidget(self.btn_clear_ff)
        ff_sec_layout.addLayout(ff_row)
        settings_layout.addWidget(ff_sec)
        videos_sec = QGroupBox("🎬  Videos Directories")
        videos_sec_layout = QVBoxLayout(videos_sec)
        self.videos_list_widget = QListWidget()
        self.btn_add_video_folder = QPushButton("Add Folder")
        self.btn_add_video_folder.setObjectName("btnSettingsAdd")
        self.btn_add_video_folder.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_add_video_folder.clicked.connect(self._add_video_folder)
        self.btn_add_video_folder.setIconSize(QSize(16, 16))
        self.btn_remove_video_folder = QPushButton("Remove Selected")
        self.btn_remove_video_folder.setObjectName("btnSettingsRemove")
        self.btn_remove_video_folder.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_remove_video_folder.clicked.connect(self._remove_video_folder)
        self.btn_remove_video_folder.setIconSize(QSize(16, 16))
        self.videos_list_widget.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)
        videos_sec_layout.addWidget(self.videos_list_widget)
        
        video_btn_layout = QHBoxLayout()
        video_btn_layout.addWidget(self.btn_add_video_folder)
        video_btn_layout.addWidget(self.btn_remove_video_folder)
        
        self.btn_clear_video_folders = QPushButton("Clear All")
        self.btn_clear_video_folders.setObjectName("btnSettingsRemove")
        self.btn_clear_video_folders.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_clear_video_folders.clicked.connect(self._clear_video_folders)
        video_btn_layout.addWidget(self.btn_clear_video_folders)
        
        videos_sec_layout.addLayout(video_btn_layout)
        settings_layout.addWidget(videos_sec)
        images_sec = QGroupBox("🖼️  Images Directories")
        images_sec_layout = QVBoxLayout(images_sec)
        self.images_list_widget = QListWidget()
        self.btn_add_image_folder = QPushButton("Add Folder")
        self.btn_add_image_folder.setObjectName("btnSettingsAdd")
        self.btn_add_image_folder.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_add_image_folder.clicked.connect(self._add_image_folder)
        self.btn_add_image_folder.setIconSize(QSize(16, 16))
        self.btn_remove_image_folder = QPushButton("Remove Selected")
        self.btn_remove_image_folder.setObjectName("btnSettingsRemove")
        self.btn_remove_image_folder.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_remove_image_folder.clicked.connect(self._remove_image_folder)
        self.btn_remove_image_folder.setIconSize(QSize(16, 16))
        self.images_list_widget.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)
        images_sec_layout.addWidget(self.images_list_widget)
        
        image_btn_layout = QHBoxLayout()
        image_btn_layout.addWidget(self.btn_add_image_folder)
        image_btn_layout.addWidget(self.btn_remove_image_folder)
        
        self.btn_clear_image_folders = QPushButton("Clear All")
        self.btn_clear_image_folders.setObjectName("btnSettingsRemove")
        self.btn_clear_image_folders.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_clear_image_folders.clicked.connect(self._clear_image_folders)
        image_btn_layout.addWidget(self.btn_clear_image_folders)
        
        images_sec_layout.addLayout(image_btn_layout)
        settings_layout.addWidget(images_sec)
        audio_sec = QGroupBox("🎵  Audio Directories")
        audio_sec_layout = QVBoxLayout(audio_sec)
        self.audio_list_widget = QListWidget()
        self.btn_add_audio_folder = QPushButton("Add Folder")
        self.btn_add_audio_folder.setObjectName("btnSettingsAdd")
        self.btn_add_audio_folder.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_add_audio_folder.clicked.connect(self._add_audio_folder)
        self.btn_add_audio_folder.setIconSize(QSize(16, 16))
        self.btn_remove_audio_folder = QPushButton("Remove Selected")
        self.btn_remove_audio_folder.setObjectName("btnSettingsRemove")
        self.btn_remove_audio_folder.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_remove_audio_folder.clicked.connect(self._remove_audio_folder)
        self.btn_remove_audio_folder.setIconSize(QSize(16, 16))
        self.audio_list_widget.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)
        audio_sec_layout.addWidget(self.audio_list_widget)
        
        audio_btn_layout = QHBoxLayout()
        audio_btn_layout.addWidget(self.btn_add_audio_folder)
        audio_btn_layout.addWidget(self.btn_remove_audio_folder)
        
        self.btn_clear_audio_folders = QPushButton("Clear All")
        self.btn_clear_audio_folders.setObjectName("btnSettingsRemove")
        self.btn_clear_audio_folders.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_clear_audio_folders.clicked.connect(self._clear_audio_folders)
        audio_btn_layout.addWidget(self.btn_clear_audio_folders)
        
        audio_sec_layout.addLayout(audio_btn_layout)
        settings_layout.addWidget(audio_sec)

        pdf_sec = QGroupBox("📄  PDFs Directories")
        pdf_sec_layout = QVBoxLayout(pdf_sec)
        self.pdf_list_widget = QListWidget()
        self.btn_add_pdf_folder = QPushButton("Add Folder")
        self.btn_add_pdf_folder.setObjectName("btnSettingsAdd")
        self.btn_add_pdf_folder.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_add_pdf_folder.clicked.connect(self._add_pdf_folder)
        self.btn_add_pdf_folder.setIconSize(QSize(16, 16))
        self.btn_remove_pdf_folder = QPushButton("Remove Selected")
        self.btn_remove_pdf_folder.setObjectName("btnSettingsRemove")
        self.btn_remove_pdf_folder.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_remove_pdf_folder.clicked.connect(self._remove_pdf_folder)
        self.btn_remove_pdf_folder.setIconSize(QSize(16, 16))
        self.pdf_list_widget.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)
        pdf_sec_layout.addWidget(self.pdf_list_widget)
        
        pdf_btn_layout = QHBoxLayout()
        pdf_btn_layout.addWidget(self.btn_add_pdf_folder)
        pdf_btn_layout.addWidget(self.btn_remove_pdf_folder)
        
        self.btn_clear_pdf_folders = QPushButton("Clear All")
        self.btn_clear_pdf_folders.setObjectName("btnSettingsRemove")
        self.btn_clear_pdf_folders.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_clear_pdf_folders.clicked.connect(self._clear_pdf_folders)
        pdf_btn_layout.addWidget(self.btn_clear_pdf_folders)
        
        pdf_sec_layout.addLayout(pdf_btn_layout)
        settings_layout.addWidget(pdf_sec)

        # 'Open With' Applications Section
        open_with_sec = QGroupBox("🌐  'Open With' Applications")
        open_with_sec_layout = QVBoxLayout(open_with_sec)
        open_with_sec_layout.setSpacing(10)
        open_with_desc = QLabel("Configure custom applications to show in the 'Open with...' right-click menu.")
        open_with_desc.setWordWrap(True)
        open_with_sec_layout.addWidget(open_with_desc)
        
        self.btn_configure_open_with = QPushButton("Configure Applications...")
        self.btn_configure_open_with.setObjectName("btnSettingsAdd")
        self.btn_configure_open_with.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_configure_open_with.clicked.connect(self._manage_open_with_apps)
        open_with_sec_layout.addWidget(self.btn_configure_open_with)
        settings_layout.addWidget(open_with_sec)

        settings_layout.addStretch()
        scroll_area.setWidget(scroll_widget)
        outer_layout.addWidget(scroll_area, 1)
        main_layout.addWidget(self.settings_panel)
        self._update_template_preview()

    def _manage_open_with_apps(self):
        dialog = ConfigureOpenWithDialog(self.open_with_apps, self)
        if dialog.exec() == QDialog.DialogCode.Accepted:
            self.open_with_apps = dialog.get_apps()
            self._save_state()

    def _show_help_dialog(self):
        dialog = AboutDialog(self)
        dialog.exec()

    def _on_theme_changed(self, text):
        ThemeManager.apply_theme(self, text)
        self._save_state()

    UI_SCALES = {"Compact": 0.85, "Normal": 1.0, "Large": 1.2}

    def _on_ui_size_changed(self, text):
        if getattr(self, '_ui_size_syncing', False): return
        self.ui_scale = self.UI_SCALES.get(text, 1.0)
        ThemeManager.apply_theme(self, self.theme_combo.currentText())
        self._save_state()

    def _on_reduced_motion_changed(self, checked: bool):
        self.reduced_motion = bool(checked)
        self._save_state()

    # Thumbnail size — live label updates while dragging; layout reflow on release
    def _on_thumb_size_live(self, value: int):
        self.thumb_size = int(value)

    def _on_thumb_size_changed(self):
        size = int(getattr(self, 'thumb_size', 130))
        for tab in [self.video_tab, self.image_tab, self.audio_tab, self.pdf_tab] + list(getattr(self, 'smart_folder_tabs', {}).values()):
            tab.apply_thumbnail_size(size)
        self._save_state()

    def open_folders_from_args(self, dirs):
        """C2: route command-line / second-instance folders to matching tabs.

        Picks the tab by sampling file extensions inside each directory
        (falls back to Videos), appends it to that tab's sources and scans.
        """
        first_page = None
        for d in dirs:
            if not os.path.isdir(d):
                continue
            d = os.path.normpath(d)
            exts = set()
            try:
                # Sample up to 300 files (filter first, slice after) for reliable type guess in mixed dirs
                all_names = os.listdir(d)
                file_names = [n for n in all_names if os.path.isfile(os.path.join(d, n))][:300]
                for name in file_names:
                    exts.add(os.path.splitext(name)[1].lower())
            except OSError:
                continue
            if exts and (exts & IMAGE_EXTENSIONS) and not (exts & VIDEO_EXTENSIONS):
                tab, page = self.image_tab, 1
            elif exts and (exts & AUDIO_EXTENSIONS) and not (exts & VIDEO_EXTENSIONS):
                tab, page = self.audio_tab, 2
            elif exts and (exts & PDF_EXTENSIONS) and not (exts & VIDEO_EXTENSIONS):
                tab, page = self.pdf_tab, 3
            else:
                tab, page = self.video_tab, 0

            list_widget = {0: self.videos_list_widget, 1: self.images_list_widget,
                           2: self.audio_list_widget, 3: self.pdf_list_widget}[page]
            existing_items = [list_widget.item(i).text() for i in range(list_widget.count())]
            if d not in existing_items:
                list_widget.addItem(d)
            current = [list_widget.item(i).text() for i in range(list_widget.count())]
            try:
                tab.update_directories(current)  # triggers a scan internally
            except Exception as e:
                logger.warning("Could not scan CLI folder %s: %s", d, e)
            if first_page is None:
                first_page = page
        if first_page is not None:
            self._switch_page(first_page)

    SHORTCUTS_HELP = [
        ("Ctrl+O", "Add source folder"),
        ("Ctrl+R / F5", "Reload files"),
        ("Ctrl+F", "Focus search filter"),
        ("Ctrl+E", "Export visible rows to CSV"),
        ("Ctrl+Z / Ctrl+Y", "Undo / redo rename (sidecars follow)"),
        ("Delete", "Send selected files to Recycle Bin"),
        ("Ctrl+A", "Select all visible rows"),
        ("Ctrl+P", "Toggle preview panel"),
        ("Ctrl+T", "Quick Trim selected video"),
        ("Ctrl+Shift+C", "Compare two selected files"),
        ("Ctrl+Shift+D", "Find exact duplicates"),
        ("Ctrl+I", "Detailed file info"),
        ("Enter", "Open / play focused row"),
        ("Up / Down", "Move row selection"),
        ("F1", "This cheat sheet"),
    ]

    def _show_shortcut_cheatsheet(self):
        """D1: F1 keyboard shortcut reference."""
        is_dark = getattr(self, 'current_theme', 'dark') == 'dark'
        bg = "#1e1b4b" if is_dark else "#ffffff"
        fg = "#e5e7eb" if is_dark else "#1f2937"
        key_fg = "#c4b5fd" if is_dark else "#4338ca"
        rows_html = "".join(
            f"<tr><td style='padding:4px 18px 4px 0;color:{key_fg};white-space:nowrap;'>"
            f"<b>{k}</b></td><td style='padding:4px 0;color:{fg};'>{d}</td></tr>"
            for k, d in self.SHORTCUTS_HELP)
        dlg = QDialog(self)
        dlg.setWindowTitle("MediaFlow — Keyboard Shortcuts")
        dlg.setMinimumWidth(430)
        lay = QVBoxLayout(dlg)
        lbl = QLabel(f"<table>{rows_html}</table>")
        lbl.setTextFormat(Qt.TextFormat.RichText)
        lay.addWidget(lbl)
        btn = QPushButton("Close")
        btn.setObjectName("btnSelectFolder")
        btn.clicked.connect(dlg.accept)
        h = QHBoxLayout(); h.addStretch(); h.addWidget(btn); h.addStretch()
        lay.addLayout(h)
        dlg.setStyleSheet(f"QDialog {{ background: {bg}; }}")
        dlg.exec()

    def _switch_page(self, index: int):
        self.stacked_widget.setCurrentIndex(index)
        if index == 0: self.page_title.setText("Videos")
        elif index == 1: self.page_title.setText("Images")
        elif index == 2: self.page_title.setText("Audio")
        elif index == 3: self.page_title.setText("PDFs")
        self.btn_nav_videos.setProperty("active", index == 0)
        self.btn_nav_images.setProperty("active", index == 1)
        self.btn_nav_audio.setProperty("active", index == 2)
        self.btn_nav_pdfs.setProperty("active", index == 3)
        self.btn_nav_videos.style().unpolish(self.btn_nav_videos)
        self.btn_nav_videos.style().polish(self.btn_nav_videos)
        self.btn_nav_images.style().unpolish(self.btn_nav_images)
        self.btn_nav_images.style().polish(self.btn_nav_images)
        self.btn_nav_audio.style().unpolish(self.btn_nav_audio)
        self.btn_nav_audio.style().polish(self.btn_nav_audio)
        self.btn_nav_pdfs.style().unpolish(self.btn_nav_pdfs)
        self.btn_nav_pdfs.style().polish(self.btn_nav_pdfs)
        if hasattr(self, 'smart_folder_nav_items'):
            for item in self.smart_folder_nav_items.values(): item.set_active(False)

    def _create_smart_folder_dialog(self):
        dialog = CreateSmartFolderDialog(parent=self)
        if dialog.exec() == QDialog.DialogCode.Accepted:
            name, media_type, query = dialog.get_values()
            self.add_smart_folder(name, media_type, query)

    def create_smart_folder_from_query(self, media_type: str, query: str):
        dialog = CreateSmartFolderDialog(media_type=media_type, query=query, parent=self)
        if dialog.exec() == QDialog.DialogCode.Accepted:
            name, new_type, new_query = dialog.get_values()
            self.add_smart_folder(name, new_type, new_query)

    BUILTIN_PAGE_TITLES = ("videos", "images", "audio", "pdfs")

    def add_smart_folder(self, name: str, media_type: str, query: str):
        # Case-insensitive dedupe against existing smart folders AND the
        # built-in page titles (Videos/Images/Audio/PDFs) — duplicate page
        # titles were previously allowed for built-ins.
        if name.strip().lower() in self.BUILTIN_PAGE_TITLES:
            QMessageBox.warning(self, "Reserved Name", f"'{name}' is a built-in page. Please choose another name."); return
        if any(f['name'].lower() == name.lower() for f in self.smart_folders_config):
            QMessageBox.warning(self, "Duplicate Folder", f"A Smart Folder named '{name}' already exists."); return
        config = {'name': name, 'type': media_type, 'query': query}
        self.smart_folders_config.append(config)
        self._save_state()
        smart_tab = MediaTab(media_type, smart_query=query, is_smart_folder=True)
        self.stacked_widget.addWidget(smart_tab)
        self.smart_folder_tabs[name] = smart_tab
        nav_item = SmartFolderNavItem(name, parent=self)
        nav_item.clicked.connect(self.switch_to_smart_folder)
        nav_item.delete_clicked.connect(self.delete_smart_folder)
        idx = self.smart_container_layout.count() - 1
        self.smart_container_layout.insertWidget(idx, nav_item)
        self.smart_folder_nav_items[name] = nav_item
        self.switch_to_smart_folder(name)

    def delete_smart_folder(self, name: str):
        reply = QMessageBox.question(self, "Delete Smart Folder", f"Are you sure you want to delete the Smart Folder '{name}'?", QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No, QMessageBox.StandardButton.No)
        if reply != QMessageBox.StandardButton.Yes: return
        if name in self.smart_folder_nav_items:
            nav_item = self.smart_folder_nav_items.pop(name)
            self.smart_container_layout.removeWidget(nav_item)
            nav_item.deleteLater()
        if name in self.smart_folder_tabs:
            smart_tab = self.smart_folder_tabs.pop(name)
            self.stacked_widget.removeWidget(smart_tab)
            smart_tab.deleteLater()
        # Case-insensitive filter to match the case-insensitive dedupe used at
        # creation time (previously exact-case, so 'Videos' vs 'videos' drifted)
        self.smart_folders_config = [f for f in self.smart_folders_config if f['name'].lower() != name.lower()]
        self._save_state()
        self._switch_page(0)

    def switch_to_smart_folder(self, name: str):
        if name not in self.smart_folder_tabs: return
        smart_tab = self.smart_folder_tabs[name]
        idx = self.stacked_widget.indexOf(smart_tab)
        if idx >= 0:
            self.stacked_widget.setCurrentIndex(idx)
            self.page_title.setText(name)
            self.btn_nav_videos.setProperty("active", False)
            self.btn_nav_images.setProperty("active", False)
            self.btn_nav_audio.setProperty("active", False)
            self.btn_nav_pdfs.setProperty("active", False)
            self.btn_nav_videos.style().unpolish(self.btn_nav_videos)
            self.btn_nav_videos.style().polish(self.btn_nav_videos)
            self.btn_nav_images.style().unpolish(self.btn_nav_images)
            self.btn_nav_images.style().polish(self.btn_nav_images)
            self.btn_nav_audio.style().unpolish(self.btn_nav_audio)
            self.btn_nav_audio.style().polish(self.btn_nav_audio)
            self.btn_nav_pdfs.style().unpolish(self.btn_nav_pdfs)
            self.btn_nav_pdfs.style().polish(self.btn_nav_pdfs)
            for n, item in self.smart_folder_nav_items.items(): item.set_active(n == name)
            self.refresh_smart_folder_tab(smart_tab)

    def refresh_smart_folder_tab(self, smart_tab: MediaTab):
        smart_tab._on_clear()
        sources = []
        if smart_tab.media_type in ['video', 'all'] and hasattr(self, 'video_tab'): sources.extend(self.video_tab.media_infos)
        if smart_tab.media_type in ['image', 'all'] and hasattr(self, 'image_tab'): sources.extend(self.image_tab.media_infos)
        if smart_tab.media_type in ['audio', 'all'] and hasattr(self, 'audio_tab'): sources.extend(self.audio_tab.media_infos)
        if smart_tab.media_type in ['pdf', 'all'] and hasattr(self, 'pdf_tab'): sources.extend(self.pdf_tab.media_infos)
        seen = set()
        unique_sources = []
        for info in sources:
            if info.filepath not in seen: seen.add(info.filepath); unique_sources.append(info)
        matching_infos = [info for info in unique_sources if matches_query(info, smart_tab.smart_query)]
        smart_tab.table.setSortingEnabled(False)
        for info in matching_infos: smart_tab._on_file_found(info)
        smart_tab.table.setSortingEnabled(True)
        smart_tab._update_stats()

    def _setup_shortcuts(self):
        shortcut_open = QAction("Add Folder", self)
        shortcut_open.setShortcut(QKeySequence("Ctrl+O"))
        shortcut_open.triggered.connect(self._on_shortcut_open_folder)
        self.addAction(shortcut_open)
        # Helper: safely call a method on the current widget (was: lambdas that
        # assumed currentWidget() was always a MediaTab, raising AttributeError
        # during teardown or for future non-MediaTab widgets).
        def _safe_call(method_name, *args):
            w = self.stacked_widget.currentWidget()
            if w is None: return
            if '.' in method_name:
                parts = method_name.split('.')
                obj = w
                for p in parts[:-1]:
                    obj = getattr(obj, p, None)
                    if obj is None: return
                fn = getattr(obj, parts[-1], None)
            else:
                fn = getattr(w, method_name, None)
            if callable(fn):
                fn(*args)
        # Gate keyboard shortcuts on the corresponding button state — otherwise
        # Ctrl+Z/Y/Delete fire even when the UI disabled them (e.g. after a
        # list clear, where stale history could rename old-session files).
        def _gated_call(method_name, button_attr, *args):
            w = self.stacked_widget.currentWidget()
            btn = getattr(w, button_attr, None) if w is not None else None
            if btn is not None and not btn.isEnabled():
                return
            _safe_call(method_name, *args)
        shortcut_reload = QAction("Reload Files", self)
        shortcut_reload.setShortcut(QKeySequence("Ctrl+R"))
        shortcut_reload.triggered.connect(lambda: _safe_call('_on_load_files'))
        self.addAction(shortcut_reload)
        shortcut_undo = QAction("Undo Rename", self)
        shortcut_undo.setShortcut(QKeySequence("Ctrl+Z"))
        shortcut_undo.triggered.connect(lambda: _gated_call('_on_undo_rename', 'btn_undo'))
        self.addAction(shortcut_undo)
        shortcut_redo = QAction("Redo Rename", self)
        shortcut_redo.setShortcut(QKeySequence("Ctrl+Y"))
        shortcut_redo.triggered.connect(lambda: _gated_call('_on_redo_rename', 'btn_redo'))
        self.addAction(shortcut_redo)
        shortcut_search = QAction("Focus Search", self)
        shortcut_search.setShortcut(QKeySequence("Ctrl+F"))
        shortcut_search.triggered.connect(lambda: _safe_call('_focus_search'))
        self.addAction(shortcut_search)
        shortcut_delete = QAction("Delete Selected", self)
        shortcut_delete.setShortcut(QKeySequence("Delete"))
        shortcut_delete.triggered.connect(lambda: _gated_call('_on_delete_selected', 'btn_delete'))
        self.addAction(shortcut_delete)
        shortcut_refresh = QAction("Refresh", self)
        shortcut_refresh.setShortcut(QKeySequence("F5"))
        shortcut_refresh.triggered.connect(lambda: _safe_call('_on_load_files'))
        self.addAction(shortcut_refresh)
        
        shortcut_dupes = QAction("Find Duplicates", self)
        shortcut_dupes.setShortcut(QKeySequence("Ctrl+Shift+D"))
        # FIX: was '_on_find_duplicates' (nonexistent — silently dead shortcut)
        shortcut_dupes.triggered.connect(lambda: _safe_call('_find_exact_duplicates'))
        self.addAction(shortcut_dupes)

        shortcut_info = QAction("File Info", self)
        shortcut_info.setShortcut(QKeySequence("Ctrl+I"))
        # FIX: was '_show_file_info_dialog' (nonexistent — silently dead shortcut)
        shortcut_info.triggered.connect(lambda: _safe_call('_show_file_info_dialog'))
        self.addAction(shortcut_info)

        shortcut_preview = QAction("Toggle Preview", self)
        shortcut_preview.setShortcut(QKeySequence("Ctrl+P"))
        shortcut_preview.triggered.connect(lambda: _safe_call('btn_toggle_preview.click'))
        self.addAction(shortcut_preview)

        shortcut_compare = QAction("Compare Selected", self)
        shortcut_compare.setShortcut(QKeySequence("Ctrl+Shift+C"))
        shortcut_compare.triggered.connect(lambda: _safe_call('_on_compare_selected'))
        self.addAction(shortcut_compare)

        shortcut_trim = QAction("Quick Trim", self)
        shortcut_trim.setShortcut(QKeySequence("Ctrl+T"))
        shortcut_trim.triggered.connect(lambda: _safe_call('_on_quick_trim'))
        self.addAction(shortcut_trim)

        # A3: export current view
        shortcut_export = QAction("Export CSV", self)
        shortcut_export.setShortcut(QKeySequence("Ctrl+E"))
        shortcut_export.triggered.connect(lambda: _safe_call('_export_list_csv'))
        self.addAction(shortcut_export)

        # D1: F1 cheat sheet
        shortcut_help = QAction("Keyboard Shortcuts", self)
        shortcut_help.setShortcut(QKeySequence("F1"))
        shortcut_help.triggered.connect(self._show_shortcut_cheatsheet)
        self.addAction(shortcut_help)
    def _update_native_button_text(self):
        if self.video_tab.default_player == "native":
            self.btn_native_vp.setText("System")
        else:
            self.btn_native_vp.setText("Native")
            
        if self.image_tab.default_player == "native":
            self.btn_native_io.setText("System")
        else:
            self.btn_native_io.setText("Native")
            
        if self.audio_tab.default_player == "native":
            self.btn_native_ap.setText("System")
        else:
            self.btn_native_ap.setText("Native")
            
        # PDF has no native player; only browse/clear available

    def _toggle_native_video_player(self):
        if self.video_tab.default_player == "native":
            self._clear_video_player()
        else:
            self._set_native_video_player()

    def _browse_video_player(self):
        path, _ = QFileDialog.getOpenFileName(self, "Select Video Player Application", os.environ.get('PROGRAMFILES', 'C:\\'), "Applications (*.exe);;All Files (*)")
        if path:
            path = os.path.normpath(path)
            app_name = os.path.splitext(os.path.basename(path))[0]
            self.video_player_label.setText(f"{app_name}\n{path}")
            self.video_tab.default_player = path
            self._update_native_button_text()
            self._save_state()

    def _clear_video_player(self):
        self.video_player_label.setText("System Default")
        self.video_tab.default_player = ""
        self._update_native_button_text()
        self._save_state()

    def _set_native_video_player(self):
        self.video_player_label.setText("Native Player")
        self.video_tab.default_player = "native"
        self._update_native_button_text()
        self._save_state()


    def _toggle_native_image_opener(self):
        if self.image_tab.default_player == "native":
            self._clear_image_opener()
        else:
            self._set_native_image_opener()

    def _set_native_image_opener(self):
        self.image_opener_label.setText("Native Viewer")
        self.image_tab.default_player = "native"
        self._update_native_button_text()
        self._save_state()

    def _browse_image_opener(self):
        path, _ = QFileDialog.getOpenFileName(self, "Select Photo Viewer Application", os.environ.get('PROGRAMFILES', 'C:\\'), "Applications (*.exe);;All Files (*)")
        if path:
            path = os.path.normpath(path)
            app_name = os.path.splitext(os.path.basename(path))[0]
            self.image_opener_label.setText(f"{app_name}\n{path}")
            self.image_tab.default_player = path
            self._update_native_button_text()
            self._save_state()

    def _clear_image_opener(self):
        self.image_opener_label.setText("System Default")
        self.image_tab.default_player = ""
        self._update_native_button_text()
        self._save_state()


    def _toggle_native_audio_player(self):
        if self.audio_tab.default_player == "native":
            self._clear_audio_player()
        else:
            self._set_native_audio_player()

    def _set_native_audio_player(self):
        self.audio_player_label.setText("Native Player")
        self.audio_tab.default_player = "native"
        self._update_native_button_text()
        self._save_state()

    def _browse_audio_player(self):
        path, _ = QFileDialog.getOpenFileName(self, "Select Audio Player Application", os.environ.get('PROGRAMFILES', 'C:\\'), "Applications (*.exe);;All Files (*)")
        if path:
            path = os.path.normpath(path)
            app_name = os.path.splitext(os.path.basename(path))[0]
            self.audio_player_label.setText(f"{app_name}\n{path}")
            self.audio_tab.default_player = path
            self._update_native_button_text()
            self._save_state()

    def _clear_audio_player(self):
        self.audio_player_label.setText("System Default")
        self.audio_tab.default_player = ""
        self._update_native_button_text()
        self._save_state()




    def _browse_pdf_opener(self):
        path, _ = QFileDialog.getOpenFileName(self, "Select PDF Reader Application", os.environ.get('PROGRAMFILES', 'C:\\'), "Applications (*.exe);;All Files (*)")
        if path:
            path = os.path.normpath(path)
            app_name = os.path.splitext(os.path.basename(path))[0]
            self.pdf_opener_label.setText(f"{app_name}\n{path}")
            self.pdf_tab.default_player = path
            self._update_native_button_text()
            self._save_state()

    def _clear_pdf_opener(self):
        self.pdf_opener_label.setText("System Default")
        self.pdf_tab.default_player = ""
        self._update_native_button_text()
        self._save_state()

    def _on_naming_template_changed(self):
        # Attribute sync stays synchronous (cheap, and close-time saves read
        # these values), but the expensive parts — fsync disk write and the
        # O(all rows × all tabs) preview refresh — are debounced so a drag or
        # keystroke doesn't hammer the disk and UI.
        all_ordered = []
        checked_fields = []
        for i in range(self.template_list.count()):
            item = self.template_list.item(i)
            text = item.text()
            all_ordered.append(text)
            if item.checkState() == Qt.CheckState.Checked:
                config_key = FIELD_MAP.get(text)
                if config_key is not None:
                    checked_fields.append(config_key)
                else:
                    logger.warning("Skipping unknown naming field in template editor: %s", text)
        self.naming_all_fields_ordered = all_ordered
        self.naming_fields = checked_fields
        self.naming_separator = self.separator_input.text()
        self.naming_keep_extension = self.keep_extension_checkbox.isChecked()
        self._update_template_preview()
        self._debounced_save_state()
        if not hasattr(self, '_preview_refresh_timer'):
            self._preview_refresh_timer = QTimer(self)
            self._preview_refresh_timer.setSingleShot(True)
            self._preview_refresh_timer.setInterval(300)
            self._preview_refresh_timer.timeout.connect(self._refresh_all_tab_previews)
        self._preview_refresh_timer.start()

    def _update_template_preview(self):
        preview_parts = []
        for i in range(self.template_list.count()):
            item = self.template_list.item(i)
            if item.checkState() == Qt.CheckState.Checked:
                preview_parts.append(f"[{item.text()}]")
        if preview_parts:
            formula = self.naming_separator.join(preview_parts)
            self.template_preview_label.setText(f"Formula Preview: {formula}")
        else:
            self.template_preview_label.setText("Formula Preview: (no fields checked)")

    def _refresh_all_tab_previews(self):
        tabs = [self.video_tab, self.image_tab, self.audio_tab, self.pdf_tab]
        if hasattr(self, 'smart_folder_tabs'):
            for smart_tab in self.smart_folder_tabs.values():
                tabs.append(smart_tab)
        for tab in tabs:
            if hasattr(tab, 'table'):
                for row in range(tab.table.rowCount()):
                    tab._update_row_preview(row)

    def _save_state(self):
        # Narrow try/except with logging — was `except Exception: pass` which
        # silently swallowed disk-full, permission, and serialization errors.
        try:
            os.makedirs(CONFIG_DIR, exist_ok=True)
            video_folders = [self.videos_list_widget.item(i).text() for i in range(self.videos_list_widget.count())]
            image_folders = [self.images_list_widget.item(i).text() for i in range(self.images_list_widget.count())]
            audio_folders = [self.audio_list_widget.item(i).text() for i in range(self.audio_list_widget.count())]
            pdf_folders = [self.pdf_list_widget.item(i).text() for i in range(self.pdf_list_widget.count())]
            is_maximized = self.isMaximized()
            if is_maximized:
                norm_geo = self.normalGeometry()
                if norm_geo.width() > 100 and norm_geo.height() > 100: geo = {'x': norm_geo.x(), 'y': norm_geo.y(), 'width': norm_geo.width(), 'height': norm_geo.height()}
                else: geo = self._normal_geometry if hasattr(self, '_normal_geometry') else {'x': self.x(), 'y': self.y(), 'width': max(self.minimumWidth(), self.width()), 'height': max(self.minimumHeight(), self.height())}
            else: geo = {'x': self.x(), 'y': self.y(), 'width': self.width(), 'height': self.height()}
            state = {
                'geometry': geo, 'maximized': is_maximized,
                'video_folders': video_folders, 'image_folders': image_folders, 'audio_folders': audio_folders, 'pdf_folders': pdf_folders,
                'default_video_player': self.video_tab.default_player, 'default_image_opener': self.image_tab.default_player, 'default_audio_player': self.audio_tab.default_player, 'default_pdf_opener': self.pdf_tab.default_player,
                'ffprobe_path': getattr(self, 'ffprobe_path', ''),
                'video_tab': self.video_tab.get_state_dict(), 'image_tab': self.image_tab.get_state_dict(), 'audio_tab': self.audio_tab.get_state_dict(), 'pdf_tab': self.pdf_tab.get_state_dict(),
                'smart_folders': getattr(self, 'smart_folders_config', []),
                'theme': self.theme_combo.currentText(),
                # FIX: global mute was never persisted — every launch reset it
                'global_mute': bool(getattr(self, 'global_mute', False)),
                'ui_scale': float(getattr(self, 'ui_scale', 1.0)),
                'reduced_motion': bool(getattr(self, 'reduced_motion', False)),
                'thumb_size': int(getattr(self, 'thumb_size', 130)),
                'naming_separator': self.naming_separator,
                'naming_fields': self.naming_fields,
                'naming_all_fields_ordered': self.naming_all_fields_ordered,
                'naming_keep_extension': self.naming_keep_extension,
                'open_with_apps': getattr(self, 'open_with_apps', [])
            }
            # Atomic write: temp file + fsync + os.replace
            tmp_path = CONFIG_FILE + '.tmp'
            with open(tmp_path, 'w', encoding='utf-8') as f:
                json.dump(state, f, indent=2, ensure_ascii=False)
                f.flush()
                os.fsync(f.fileno())
            os.replace(tmp_path, CONFIG_FILE)
        except (OSError, ValueError, TypeError) as e:
            logger.warning("Failed to save MediaFlow state: %s", e)

    def _debounced_save_state(self):
        """Save state at most once per 1.5s — prevents disk thrash on rapid edits."""
        if not hasattr(self, '_save_state_timer'):
            self._save_state_timer = QTimer(self)
            self._save_state_timer.setSingleShot(True)
            self._save_state_timer.setInterval(1500)
            self._save_state_timer.timeout.connect(self._save_state)
        self._save_state_timer.start()

    def _load_state(self):
        """Load persisted state with PER-SECTION isolation.

        A malformed value in one section must not abort the rest of the load.
        Data-bearing sections (folders/tabs/naming/smart folders) set
        _load_failed on failure so closeEvent skips saving — otherwise a
        half-loaded session would overwrite a recoverable config on disk
        with near-empty state.
        """
        self._load_failed = False
        if not os.path.exists(CONFIG_FILE):
            ThemeManager.apply_theme(self, "System (Auto)")
            return
        try:
            with open(CONFIG_FILE, 'r', encoding='utf-8') as f: state = json.load(f)
            if not isinstance(state, dict):
                raise TypeError("config root is not a JSON object")
        except json.JSONDecodeError as e:
            logger.warning("Corrupt config file (%s); starting fresh: %s", CONFIG_FILE, e)
            self._load_failed = True
            ThemeManager.apply_theme(self, "System (Auto)")
            return
        except OSError as e:
            logger.warning("Could not read config %s; starting fresh: %s", CONFIG_FILE, e)
            self._load_failed = True
            ThemeManager.apply_theme(self, "System (Auto)")
            return

        def run_section(label, fn, destructive=True):
            try:
                fn()
            except Exception as e:
                logger.exception("Failed to load '%s' section from config: %s", label, e)
                if destructive:
                    # Don't risk replacing on-disk state with a partial load
                    self._load_failed = True

        def _str_list(val):
            if isinstance(val, list): return [v for v in val if isinstance(v, str) and v]
            if isinstance(val, str) and val: return [val]
            return []

        # ── Accessibility & comfort (non-destructive; loads BEFORE theme so
        # apply_theme sees the saved ui_scale) ──
        def _a11y():
            s = state.get('ui_scale', 1.0)
            try:
                s = float(s)
            except (TypeError, ValueError):
                s = 1.0
            self.ui_scale = s if 0.5 <= s <= 2.0 else 1.0
            self.reduced_motion = bool(state.get('reduced_motion', False))
            ts = state.get('thumb_size', 130)
            try:
                ts = int(ts)
            except (TypeError, ValueError):
                ts = 130
            self.thumb_size = ts if 90 <= ts <= 200 else 130

            # Settings widgets are built by now — sync them silently
            self._ui_size_syncing = True
            try:
                scale_to_text = {v: k for k, v in self.UI_SCALES.items()}
                self.ui_size_combo.setCurrentText(scale_to_text.get(self.ui_scale, "Normal"))
            finally:
                self._ui_size_syncing = False
            self.reduced_motion_checkbox.blockSignals(True)
            self.reduced_motion_checkbox.setChecked(self.reduced_motion)
            self.reduced_motion_checkbox.blockSignals(False)
            self.thumb_size_slider.blockSignals(True)
            self.thumb_size_slider.setValue(int(self.thumb_size))
            self.thumb_size_slider.blockSignals(False)
            self.thumb_size_value_lbl.setText(f"{int(self.thumb_size)}px")
        run_section('accessibility', _a11y, destructive=False)

        # ── Theme (non-destructive) ──
        def _theme():
            theme = state.get('theme', 'System (Auto)')
            # Validate against combo items — setCurrentText() is a silent no-op
            # for unknown values but apply_theme() still maps them, desyncing
            # the UI from the applied theme.
            items = [self.theme_combo.itemText(i) for i in range(self.theme_combo.count())]
            if theme not in items:
                logger.warning("Unknown saved theme %r; using System (Auto)", theme)
                theme = 'System (Auto)'
            self.theme_combo.blockSignals(True)
            self.theme_combo.setCurrentText(theme)
            self.theme_combo.blockSignals(False)
            ThemeManager.apply_theme(self, theme)
        run_section('theme', _theme, destructive=False)

        # ── Custom Naming Template ──
        def _naming():
            sep = state.get('naming_separator', ' ')
            self.naming_separator = sep if isinstance(sep, str) else ' '
            fields = state.get('naming_fields', list(DEFAULT_NAMING_FIELDS))
            self.naming_fields = [f for f in fields if f in FIELD_MAP.values()] if isinstance(fields, list) else list(DEFAULT_NAMING_FIELDS)
            ordered = state.get('naming_all_fields_ordered', None)
            if not isinstance(ordered, list):
                ordered = list(DEFAULT_NAMING_FIELDS_ORDERED)
            # Reconcile against FIELD_MAP: keep known fields in their saved
            # order, drop unknown leftovers, and append fields added by newer
            # versions so they actually appear for existing configs.
            reconciled, seen = [], set()
            for f_name in ordered + list(DEFAULT_NAMING_FIELDS_ORDERED):
                if isinstance(f_name, str) and f_name in FIELD_MAP and f_name not in seen:
                    reconciled.append(f_name); seen.add(f_name)
            dropped = [f for f in ordered if isinstance(f, str) and f not in FIELD_MAP]
            if dropped:
                logger.warning("Dropping unknown naming fields from config: %s", dropped)
            self.naming_all_fields_ordered = reconciled
            self.naming_keep_extension = bool(state.get('naming_keep_extension', True))
            apps = state.get('open_with_apps', [])
            self.open_with_apps = apps if isinstance(apps, list) else []

            # Sync Custom Naming Template settings UI widgets
            self.separator_input.blockSignals(True)
            self.separator_input.setText(self.naming_separator)
            self.separator_input.blockSignals(False)

            self.keep_extension_checkbox.blockSignals(True)
            self.keep_extension_checkbox.setChecked(self.naming_keep_extension)
            self.keep_extension_checkbox.blockSignals(False)

            self.template_list.blockSignals(True)
            self.template_list.model().blockSignals(True)
            self.template_list.clear()
            for f_name in self.naming_all_fields_ordered:
                item = QListWidgetItem(f_name)
                item.setFlags(item.flags() | Qt.ItemFlag.ItemIsUserCheckable | Qt.ItemFlag.ItemIsDragEnabled)
                config_key = FIELD_MAP[f_name]
                is_checked = config_key in self.naming_fields
                item.setCheckState(Qt.CheckState.Checked if is_checked else Qt.CheckState.Unchecked)
                self.template_list.addItem(item)
            self.template_list.model().blockSignals(False)
            self.template_list.blockSignals(False)

            self._update_template_preview()
        run_section('naming template', _naming)

        # ── Global mute (non-destructive) ──
        def _mute():
            if bool(state.get('global_mute', False)) and not getattr(self, 'global_mute', False):
                self._toggle_global_mute()
        run_section('global mute', _mute, destructive=False)

        # ── Geometry (non-destructive) ──
        def _geometry():
            geo = state.get('geometry', {})
            has_geo = False
            if isinstance(geo, dict):
                try:
                    x, y = int(geo.get('x', 0)), int(geo.get('y', 0))
                    w, h = int(geo.get('width', 0)), int(geo.get('height', 0))
                except (TypeError, ValueError):
                    logger.warning("Malformed geometry in config; using default")
                else:
                    if w > 100 and h > 100:
                        self.setGeometry(x, y, w, h)
                        self._normal_geometry = {'x': x, 'y': y, 'width': w, 'height': h}
                        has_geo = True
            if state.get('maximized', False): self.showMaximized()
            elif not has_geo: self._center_on_screen()
        run_section('geometry', _geometry, destructive=False)

        # ── Source folder lists + per-tab directories ──
        video_folders = image_folders = audio_folders = pdf_folders = []

        def _folders():
            nonlocal video_folders, image_folders, audio_folders, pdf_folders
            pairs = [
                ('video_folders', self.videos_list_widget, self.video_tab),
                ('image_folders', self.images_list_widget, self.image_tab),
                ('audio_folders', self.audio_list_widget, self.audio_tab),
                ('pdf_folders', self.pdf_list_widget, self.pdf_tab),
            ]
            for key, widget, tab in pairs:
                folders = _str_list(state.get(key, []))
                widget.clear()
                widget.addItems(folders)   # addItems(str) would insert every CHARACTER as an item
                tab.set_directories(folders)
                if key == 'video_folders': video_folders = folders
                elif key == 'image_folders': image_folders = folders
                elif key == 'audio_folders': audio_folders = folders
                elif key == 'pdf_folders': pdf_folders = folders
        run_section('source folders', _folders)

        # ── Default external players (non-destructive) ──
        def _players():
            vp = state.get('default_video_player', '')
            if vp == "native":
                self.video_tab.default_player = "native"
                self.video_player_label.setText("Native Player")
            elif isinstance(vp, str) and vp and os.path.exists(vp):
                self.video_tab.default_player = vp
                app_name = os.path.splitext(os.path.basename(vp))[0]
                self.video_player_label.setText(f"{app_name}\n{vp}")
            io = state.get('default_image_opener', '')
            if io == "native":
                self.image_tab.default_player = "native"
                self.image_opener_label.setText("Native Viewer")
            elif isinstance(io, str) and io and os.path.exists(io):
                self.image_tab.default_player = io
                app_name = os.path.splitext(os.path.basename(io))[0]
                self.image_opener_label.setText(f"{app_name}\n{io}")
            ap = state.get('default_audio_player', '')
            if ap == "native":
                self.audio_tab.default_player = "native"
                self.audio_player_label.setText("Native Player")
            elif isinstance(ap, str) and ap and os.path.exists(ap):
                self.audio_tab.default_player = ap
                app_name = os.path.splitext(os.path.basename(ap))[0]
                self.audio_player_label.setText(f"{app_name}\n{ap}")
            po = state.get('default_pdf_opener', '')
            if po != "native" and isinstance(po, str) and po and os.path.exists(po):
                self.pdf_tab.default_player = po
                app_name = os.path.splitext(os.path.basename(po))[0]
                self.pdf_opener_label.setText(f"{app_name}\n{po}")
            self._update_native_button_text()
        run_section('default players', _players, destructive=False)

        # ── FFprobe path (#25: only accept existing files) ──
        def _ffprobe():
            fp = state.get('ffprobe_path', '')
            if isinstance(fp, str) and fp and os.path.exists(fp):
                self.ffprobe_path = fp
                app_name = os.path.splitext(os.path.basename(fp))[0]
                self.ffprobe_path_label.setText(f"{app_name}\n{fp}")
            else:
                if fp:
                    logger.warning("Ignoring stored ffprobe path that no longer exists: %s", fp)
                self.ffprobe_path = ''
        run_section('ffprobe path', _ffprobe, destructive=False)

        # ── Per-tab file metadata (artist/rating/tags/columns/history) ──
        def _tabs():
            for key, tab in (('video_tab', self.video_tab), ('image_tab', self.image_tab),
                             ('audio_tab', self.audio_tab), ('pdf_tab', self.pdf_tab)):
                raw = state.get(key)
                if isinstance(raw, dict):
                    tab.load_state_dict(raw)
        run_section('tab state', _tabs)

        # ── Kick off initial scans ──
        try:
            if video_folders: self.video_tab._start_scan(video_folders)
            if image_folders: self.image_tab._start_scan(image_folders)
            if audio_folders: self.audio_tab._start_scan(audio_folders)
            if pdf_folders: self.pdf_tab._start_scan(pdf_folders)
        except Exception as e:
            logger.exception("Failed to start initial scans: %s", e)
            self._load_failed = True

        # ── Smart folders ──
        def _smart():
            smart_folders = state.get('smart_folders', [])
            if not isinstance(smart_folders, list): return
            for sf in smart_folders:
                try:
                    if not isinstance(sf, dict):
                        raise TypeError("entry is not an object")
                    name = sf['name']; media_type = sf['type']; query = sf['query']
                    if not isinstance(name, str) or not name.strip():
                        raise TypeError("'name' must be a non-empty string")
                    if media_type not in ('video', 'image', 'audio', 'pdf', 'all'):
                        raise ValueError(f"unknown media type {media_type!r}")
                    if not isinstance(query, str): query = str(query)
                except (KeyError, TypeError, ValueError) as se:
                    # Broadened from KeyError-only: non-dict entries / non-string
                    # names previously escaped and aborted the whole load.
                    logger.warning("Skipping malformed smart folder entry (%s): %s", se, sf)
                    continue
                if any(isinstance(f, dict) and f['name'].lower() == name.lower() for f in self.smart_folders_config): continue
                config = {'name': name, 'type': media_type, 'query': query}
                self.smart_folders_config.append(config)
                smart_tab = MediaTab(media_type, smart_query=query, is_smart_folder=True)
                self.stacked_widget.addWidget(smart_tab)
                self.smart_folder_tabs[name] = smart_tab
                nav_item = SmartFolderNavItem(name, parent=self)
                nav_item.clicked.connect(self.switch_to_smart_folder)
                nav_item.delete_clicked.connect(self.delete_smart_folder)
                idx = self.smart_container_layout.count() - 1
                self.smart_container_layout.insertWidget(idx, nav_item)
                self.smart_folder_nav_items[name] = nav_item
        run_section('smart folders', _smart)

        # Apply persisted thumbnail size to every tab (built with the default)
        def _apply_thumbs():
            tabs_ = [self.video_tab, self.image_tab, self.audio_tab, self.pdf_tab]
            for st_ in getattr(self, 'smart_folder_tabs', {}).values():
                tabs_.append(st_)
            for t_ in tabs_:
                if int(getattr(t_, 'thumb_size', 130)) != int(getattr(self, 'thumb_size', 130)):
                    t_.apply_thumbnail_size(int(self.thumb_size))
        run_section('thumbnail size', _apply_thumbs, destructive=False)

    def resizeEvent(self, event):
        if not self.isMaximized() and not self.isFullScreen():
            self._normal_geometry = {'x': self.x(), 'y': self.y(), 'width': self.width(), 'height': self.height()}
        super().resizeEvent(event)
        if hasattr(self, 'hover_overlay') and self.hover_overlay:
            self.hover_overlay.adjust_layout()

    def moveEvent(self, event):
        if not self.isMaximized() and not self.isFullScreen():
            self._normal_geometry = {'x': self.x(), 'y': self.y(), 'width': self.width(), 'height': self.height()}
        super().moveEvent(event)

    def closeEvent(self, event):
        # Stop any pending debounced save so it can't fire during teardown
        if hasattr(self, '_save_state_timer'):
            self._save_state_timer.stop()
        # FIX: never overwrite a config we failed to load — a half-initialized
        # session would replace recoverable on-disk state with near-empty data.
        if getattr(self, '_load_failed', False):
            logger.warning("Skipping state save on close: config failed to load earlier; preserving original file.")
        else:
            self._save_state()
        super().closeEvent(event)

    def _toggle_global_mute(self):
        self.global_mute = not self.global_mute
        is_dark = (self.current_theme == "dark")
        self.btn_global_mute.setIcon(get_vector_icon('mute' if self.global_mute else 'unmute', is_dark))
        self.btn_global_mute.setText("")
        tabs = []
        if hasattr(self, 'video_tab'): tabs.append(self.video_tab)
        if hasattr(self, 'image_tab'): tabs.append(self.image_tab)
        if hasattr(self, 'audio_tab'): tabs.append(self.audio_tab)
        if hasattr(self, 'pdf_tab'): tabs.append(self.pdf_tab)
        # CRITICAL: smart folder tabs are full MediaTab instances with their own
        # audio_output — must be muted too or audio plays at full volume after
        # switching to a smart folder post-mute.
        if hasattr(self, 'smart_folder_tabs'):
            tabs.extend(self.smart_folder_tabs.values())
        for tab in tabs:
            if hasattr(tab, 'audio_output') and tab.audio_output: tab.audio_output.setMuted(self.global_mute)
            if hasattr(tab, 'btn_mute') and tab.btn_mute:
                tab.btn_mute.setIcon(get_vector_icon('mute' if self.global_mute else 'unmute', is_dark))
                tab.btn_mute.setText("")
        if hasattr(self, 'hover_overlay') and self.hover_overlay and self.hover_overlay.isVisible():
            self.hover_overlay.audio_output.setMuted(self.global_mute)

    def _browse_ffprobe_path(self):
        path, _ = QFileDialog.getOpenFileName(self, "Select ffprobe Executable", os.environ.get('PROGRAMFILES', 'C:\\'), "Executables (ffprobe.exe);;All Files (*)")
        if path:
            path = os.path.normpath(path)
            app_name = os.path.splitext(os.path.basename(path))[0]
            self.ffprobe_path_label.setText(f"{app_name}\n{path}")
            self.ffprobe_path = path
            self._save_state()

    def _clear_ffprobe_path(self):
        self.ffprobe_path_label.setText("System PATH (Default)")
        self.ffprobe_path = ""
        self._save_state()

    def _toggle_settings(self):
        self._settings_visible = not self._settings_visible
        target_width = 400 if self._settings_visible else 0
        if getattr(self, 'reduced_motion', False):
            # Reduced motion: jump instantly instead of animating
            self.settings_panel.setMinimumWidth(target_width)
            self.settings_panel.setMaximumWidth(target_width)
            return
        if hasattr(self, 'settings_animation') and self.settings_animation.state() == QPropertyAnimation.State.Running: self.settings_animation.stop()
        if hasattr(self, 'settings_animation_max') and self.settings_animation_max.state() == QPropertyAnimation.State.Running: self.settings_animation_max.stop()
        self.settings_animation = QPropertyAnimation(self.settings_panel, b"minimumWidth")
        self.settings_animation.setDuration(250)
        self.settings_animation.setStartValue(self.settings_panel.width())
        self.settings_animation.setEndValue(target_width)
        self.settings_animation.setEasingCurve(QEasingCurve.Type.InOutQuad)
        self.settings_animation_max = QPropertyAnimation(self.settings_panel, b"maximumWidth")
        self.settings_animation_max.setDuration(250)
        self.settings_animation_max.setStartValue(self.settings_panel.width())
        self.settings_animation_max.setEndValue(target_width)
        self.settings_animation_max.setEasingCurve(QEasingCurve.Type.InOutQuad)
        self.settings_animation.start()
        self.settings_animation_max.start()

    def _add_video_folder(self):
        folder = QFileDialog.getExistingDirectory(self, "Select Video Folder")
        if folder:
            folder = os.path.normpath(folder)
            items = [self.videos_list_widget.item(i).text() for i in range(self.videos_list_widget.count())]
            if folder not in items:
                self.videos_list_widget.addItem(folder)
                self._update_video_directories()

    def _remove_video_folder(self):
        selected = self.videos_list_widget.selectedItems()
        if not selected: return
        for item in selected: self.videos_list_widget.takeItem(self.videos_list_widget.row(item))
        self._update_video_directories()

    def _clear_video_folders(self):
        self.videos_list_widget.clear()
        self._update_video_directories()

    def _update_video_directories(self):
        folders = [self.videos_list_widget.item(i).text() for i in range(self.videos_list_widget.count())]
        self.video_tab.update_directories(folders)
        self._save_state()

    def _add_image_folder(self):
        folder = QFileDialog.getExistingDirectory(self, "Select Image Folder")
        if folder:
            folder = os.path.normpath(folder)
            items = [self.images_list_widget.item(i).text() for i in range(self.images_list_widget.count())]
            if folder not in items:
                self.images_list_widget.addItem(folder)
                self._update_image_directories()

    def _remove_image_folder(self):
        selected = self.images_list_widget.selectedItems()
        if not selected: return
        for item in selected: self.images_list_widget.takeItem(self.images_list_widget.row(item))
        self._update_image_directories()

    def _clear_image_folders(self):
        self.images_list_widget.clear()
        self._update_image_directories()

    def _update_image_directories(self):
        folders = [self.images_list_widget.item(i).text() for i in range(self.images_list_widget.count())]
        self.image_tab.update_directories(folders)
        self._save_state()

    def _add_audio_folder(self):
        folder = QFileDialog.getExistingDirectory(self, "Select Audio Folder")
        if folder:
            folder = os.path.normpath(folder)
            items = [self.audio_list_widget.item(i).text() for i in range(self.audio_list_widget.count())]
            if folder not in items:
                self.audio_list_widget.addItem(folder)
                self._update_audio_directories()

    def _remove_audio_folder(self):
        selected = self.audio_list_widget.selectedItems()
        if not selected: return
        for item in selected: self.audio_list_widget.takeItem(self.audio_list_widget.row(item))
        self._update_audio_directories()

    def _clear_audio_folders(self):
        self.audio_list_widget.clear()
        self._update_audio_directories()

    def _update_audio_directories(self):
        folders = [self.audio_list_widget.item(i).text() for i in range(self.audio_list_widget.count())]
        self.audio_tab.update_directories(folders)
        self._save_state()

    def _add_pdf_folder(self):
        folder = QFileDialog.getExistingDirectory(self, "Select PDF Folder")
        if folder:
            folder = os.path.normpath(folder)
            items = [self.pdf_list_widget.item(i).text() for i in range(self.pdf_list_widget.count())]
            if folder not in items:
                self.pdf_list_widget.addItem(folder)
                self._update_pdf_directories()

    def _remove_pdf_folder(self):
        selected = self.pdf_list_widget.selectedItems()
        if not selected: return
        for item in selected: self.pdf_list_widget.takeItem(self.pdf_list_widget.row(item))
        self._update_pdf_directories()

    def _clear_pdf_folders(self):
        self.pdf_list_widget.clear()
        self._update_pdf_directories()

    def _update_pdf_directories(self):
        folders = [self.pdf_list_widget.item(i).text() for i in range(self.pdf_list_widget.count())]
        self.pdf_tab.update_directories(folders)
        self._save_state()

    def _on_shortcut_open_folder(self):
        idx = self.stacked_widget.currentIndex()
        if idx == 0: self._add_video_folder()
        elif idx == 1: self._add_image_folder()
        elif idx == 2: self._add_audio_folder()
        elif idx == 3: self._add_pdf_folder()

    def dragEnterEvent(self, event):
        if event.mimeData().hasUrls(): event.acceptProposedAction()
        else: super().dragEnterEvent(event)

    def dropEvent(self, event):
        urls = event.mimeData().urls()
        if not urls: return
        active_tab = self.stacked_widget.currentWidget()
        if not active_tab: return
        directories = []; files = []
        for url in urls:
            path = os.path.normpath(url.toLocalFile())
            if os.path.isdir(path): directories.append(path)
            elif os.path.isfile(path): files.append(path)
        if directories:
            idx = self.stacked_widget.currentIndex()
            if idx == 0: list_widget = self.videos_list_widget; update_func = self._update_video_directories
            elif idx == 1: list_widget = self.images_list_widget; update_func = self._update_image_directories
            elif idx == 2: list_widget = self.audio_list_widget; update_func = self._update_audio_directories
            elif idx == 3: list_widget = self.pdf_list_widget; update_func = self._update_pdf_directories
            # Use a set for O(1) membership tests AND update it inside the loop
            # so dropping the same folder twice in one event doesn't add duplicates.
            existing = set(list_widget.item(i).text() for i in range(list_widget.count()))
            added_any = False
            for d in directories:
                if d not in existing:
                    list_widget.addItem(d)
                    existing.add(d)
                    added_any = True
            if added_any: update_func()
        if files:
            allowed_exts = set()
            if active_tab.media_type == 'video': allowed_exts = VIDEO_EXTENSIONS
            elif active_tab.media_type == 'image': allowed_exts = IMAGE_EXTENSIONS
            elif active_tab.media_type == 'audio': allowed_exts = AUDIO_EXTENSIONS
            elif active_tab.media_type == 'pdf': allowed_exts = PDF_EXTENSIONS
            else:
                # 'all' / smart folders: accept the full supported union plus
                # extensionless files (was empty set → drops silently ignored)
                allowed_exts = get_extensions_for_type(active_tab.media_type)
            valid_files = [f for f in files
                           if os.path.splitext(f)[1].lower() in allowed_exts or not os.path.splitext(f)[1]]
            if valid_files:
                was_sorting = active_tab.table.isSortingEnabled()
                active_tab.table.setSortingEnabled(False)
                try:
                    for filepath in valid_files:
                        if filepath in [v.filepath for v in active_tab.media_infos]: continue
                        info = MediaInfo(filepath, active_tab.media_type)
                        active_tab._on_file_found(info)
                finally:
                    active_tab.table.setSortingEnabled(was_sorting)
                total = len(active_tab.media_infos)
                active_tab.btn_process.setEnabled(total > 0)
                active_tab.btn_relocate.setEnabled(total > 0)
                active_tab.btn_find_dupes.setEnabled(total > 0)
                active_tab.btn_clear.setVisible(total > 0)
                active_tab._update_stats()

AUDIT_LOG_FILE = os.path.join(CONFIG_DIR, "rename_audit.csv")

def append_rename_audit(entries):
    """C3: append-only audit trail of every rename/move (old → new).

    CSV rows: timestamp, operation, old_path, new_path. Best-effort — failures
    are logged and never interrupt renames. Portable mode keeps this beside
    the exe automatically via CONFIG_DIR.
    """
    if not entries:
        return
    try:
        os.makedirs(CONFIG_DIR, exist_ok=True)
        import csv as _csv
        ts = datetime.now().isoformat(timespec="seconds")
        # Append atomically: check emptiness via file size after opening (avoids TOCTOU)
        with open(AUDIT_LOG_FILE, 'a', encoding='utf-8', newline='') as f:
            wr = _csv.writer(f)
            try:
                needs_header = f.tell() == 0
            except OSError:
                needs_header = not os.path.exists(AUDIT_LOG_FILE) or os.path.getsize(AUDIT_LOG_FILE) == 0
            if needs_header:
                wr.writerow(["timestamp", "operation", "old_path", "new_path"])
            # First entry is the main file; rest are sidecars — header written once, no TOCTOU
            first_old = entries[0][0] if entries else None
            for old_p, new_p in entries:
                op = "sidecar" if old_p != first_old else "rename"
                wr.writerow([ts, op, old_p, new_p])
    except OSError as e:
        logger.warning("rename audit log write failed: %s", e)

def main():
    if sys.platform == 'win32':
        try:
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("antigravity.mediaflow.app.1")
        except Exception:
            pass

    app = QApplication(sys.argv)
    app.setApplicationName("MediaFlow")
    app.setOrganizationName("MediaFlow")

    # ── C1: Single instance ──
    # A second launch just focuses the running window (and hands over any
    # folders passed on its command line). QLocalServer also cleans up stale
    # locks after a crash.
    _sock = QLocalSocket()
    _sock.connectToServer("MediaFlowSingleInstance")
    if _sock.waitForConnected(300):
        hint_dirs = [a for a in sys.argv[1:] if os.path.isdir(a)]
        try:
            _sock.write(("open\t" + "\n".join(hint_dirs)).encode("utf-8"))
            _sock.flush()
            _sock.waitForBytesWritten(300)
        except Exception:
            pass
        _sock.disconnectFromServer()
        print("MediaFlow is already running \u2014 focusing the existing window.")
        return
    QLocalServer.removeServer("MediaFlowSingleInstance")  # stale lock from crash
    _instance_server = QLocalServer()
    if not _instance_server.listen("MediaFlowSingleInstance"):
        logger.warning("Single-instance server unavailable (%s); continuing standalone.",
                       _instance_server.errorString())

    # Set application-wide window icon (shows on top-left title bar and in the taskbar)
    logo_path = get_resource_path("logo.png")
    if os.path.exists(logo_path):
        app.setWindowIcon(QIcon(logo_path))

    font = QFont(BASE_FONT_FAMILY, 10)
    app.setFont(font)
    
    palette = QPalette()
    palette.setColor(QPalette.ColorRole.Window, QColor("#0f0c29"))
    palette.setColor(QPalette.ColorRole.WindowText, QColor("#e0e0e0"))
    app.setPalette(palette)

    window = MediaFlowWindow()

    def _second_instance_connected():
        conn = _instance_server.nextPendingConnection()
        if conn is None:
            return
        # Wait briefly for the payload — readAll() alone can race the sender
        if not conn.bytesAvailable():
            conn.waitForReadyRead(300)
        data = bytes(conn.readAll()).decode("utf-8", "replace")
        conn.disconnectFromServer()
        window.setWindowState(window.windowState() & ~Qt.WindowState.WindowMinimized | Qt.WindowState.WindowActive)
        window.raise_()
        window.activateWindow()
        if data.startswith("open\t"):
            dirs = [d for d in data.split("\t", 1)[1].split("\n") if d]
            if dirs:
                QTimer.singleShot(0, lambda: window.open_folders_from_args(dirs))

    _instance_server.newConnection.connect(_second_instance_connected)

    window.show()

    # ── C2: launch folders from the command line ──
    cli_dirs = [os.path.abspath(a) for a in sys.argv[1:] if os.path.isdir(a)]
    if cli_dirs:
        QTimer.singleShot(0, lambda: window.open_folders_from_args(cli_dirs))

    sys.exit(app.exec())

if __name__ == "__main__":
    main()