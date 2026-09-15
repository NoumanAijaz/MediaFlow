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
import weakref
from datetime import datetime
import numpy as np
import cv2

# ─── Module-level setup ────────────────────────────────────────────────────────
__version__ = "2.4.0"
logger = logging.getLogger(__name__)
if not logger.handlers:
    logging.basicConfig(level=logging.INFO, format="[MediaFlow] %(levelname)s: %(message)s")

def _global_excepthook(exc_type, exc_value, exc_traceback):
    if issubclass(exc_type, KeyboardInterrupt):
        sys.__excepthook__(exc_type, exc_value, exc_traceback)
        return
    logger.critical("Unhandled top-level exception:", exc_info=(exc_type, exc_value, exc_traceback))

sys.excepthook = _global_excepthook

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

# ─── Nebula design tokens ────────────────────────────────────────────────────
# Single source of truth for the futuristic skin. Same hues as before, but
# deeper backgrounds, higher-contrast text and an electric cyan "live" accent.
class Nebula:
    BG0 = "#07060F"      # window abyss (dark)
    BG1 = "#0B0918"      # sidebar / layer 1 (dark)
    BG2 = "#15122B"      # glass panel base (dark)
    ACCENT = "#8B5CF6"   # violet — primary actions
    ACCENT2 = "#22D3EE"  # electric cyan — active/live states (watch, focus, selection stripe)
    TEXT = "#ECECF4"     # primary text (dark) — better contrast than the old #e0e0e0
    TEXT_DIM = "#8E8AA8"
    ACCENT_L = "#6D28D9"   # violet (light theme)
    ACCENT2_L = "#0891B2"  # cyan (light theme)
    TEXT_L = "#0F172A"
    TEXT_DIM_L = "#64748B"


def apply_glow(widget, color=None, radius=20, alpha=110):
    """Attach a soft neon glow to a widget (QGraphicsDropShadowEffect).

    Pass color=None to remove. Kept subtle on purpose — glow marks ACTIVE or
    PRIMARY things only; everything glowing means nothing glows.
    """
    if widget is None:
        return None
    if color is None:
        try:
            widget.setGraphicsEffect(None)
        except (RuntimeError, TypeError, AttributeError):
            pass
        return None
    try:
        eff = QGraphicsDropShadowEffect(widget)
        eff.setBlurRadius(max(0, radius))
        eff.setOffset(0, 0)
        c = QColor(color)
        if not c.isValid():
            return None
        c.setAlpha(max(0, min(255, int(alpha))))
        eff.setColor(c)
        widget.setGraphicsEffect(eff)
        return eff
    except (RuntimeError, TypeError, AttributeError):
        return None


def _safe_int(val, default=0):
    """int() that tolerates ffprobe's 'N/A' / None / float strings / missing values."""
    try:
        return int(float(val))
    except (TypeError, ValueError, OverflowError):
        return default


def _safe_float(val, default=0.0):
    try:
        v = float(val)
    except (TypeError, ValueError, OverflowError):
        return default
    return v if math.isfinite(v) else default


def _mono_font(point=9, bold=True):
    """Monospace font for data columns (duration/size/dates) so digits align."""
    f = QFont()
    f.setFamilies(["Consolas", "Cascadia Mono", "JetBrains Mono", "DejaVu Sans Mono", "monospace"])
    f.setPointSize(point)
    f.setBold(bold)
    return f

from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout, QGridLayout,
    QPushButton, QLabel, QFileDialog, QTableWidget, QTableWidgetItem,
    QHeaderView, QComboBox, QLineEdit, QMessageBox, QProgressBar, QProgressDialog,
    QFrame, QAbstractItemView, QMenu, QCheckBox, QDialog, QDialogButtonBox, QRadioButton,
    QFormLayout, QGroupBox, QStackedWidget, QListWidget, QListWidgetItem,
    QStyledItemDelegate, QSlider, QScrollArea, QStyle, QSpinBox, QDoubleSpinBox,
    QSplitter, QSizePolicy, QInputDialog, QTableWidgetSelectionRange, QDateEdit,
    QGraphicsDropShadowEffect, QStyleOptionSlider, QToolBar, QTreeWidget, QTreeWidgetItem
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
    mt = (media_type or '').lower()
    if mt == 'video': return set(VIDEO_EXTENSIONS)
    elif mt == 'audio': return set(AUDIO_EXTENSIONS)
    elif mt == 'image': return set(IMAGE_EXTENSIONS)
    elif mt == 'pdf': return set(PDF_EXTENSIONS)
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
        target = os.path.join(base, "MediaFlowData")
        try:
            os.makedirs(target, exist_ok=True)
            test_file = os.path.join(target, ".__write_test__")
            with open(test_file, "w") as f:
                f.write("1")
            os.remove(test_file)
            return target
        except (PermissionError, OSError):
            pass
    appdata = os.environ.get('APPDATA')
    if sys.platform == "win32" and appdata:
        return os.path.join(appdata, 'MediaFlow')
    # Linux/macOS fallback — XDG or HOME
    xdg = os.environ.get('XDG_CONFIG_HOME')
    if xdg and os.path.isabs(xdg):
        return os.path.join(xdg, 'MediaFlow')
    return os.path.join(os.path.expanduser('~'), '.config', 'MediaFlow')

CONFIG_DIR = _resolve_config_dir()
CONFIG_FILE = os.path.join(CONFIG_DIR, 'config.json')

def get_resource_path(relative_path):
    """Get absolute path to resource, works for dev and for PyInstaller"""
    try:
        base_path = sys._MEIPASS
        if not isinstance(base_path, str) or not base_path:
            raise AttributeError
    except AttributeError:
        base_path = os.path.dirname(os.path.abspath(__file__))
    return os.path.join(base_path, relative_path)

CACHE_LOCK = threading.Lock()

def update_metadata_cache(entries_to_add: dict, paths_to_delete: list = None, not_before_ts: float = None):
    """Atomically update the metadata cache using os.replace() safely across threads.

    not_before_ts: optional snapshot time. Cache entries whose '_updated' stamp
    is newer than this are preserved even if listed in paths_to_delete — an
    orphaned/older scanner must not delete entries a newer scan just wrote.
    """
    import tempfile
    with CACHE_LOCK:
        cache_path = os.path.join(CONFIG_DIR, 'scan_cache.json')
        try:
            os.makedirs(CONFIG_DIR, exist_ok=True)
            if entries_to_add is not None and not isinstance(entries_to_add, dict):
                logger.warning("update_metadata_cache: entries_to_add is not a dict; ignoring.")
                entries_to_add = None
            for _ in range(5):
                try:
                    current_cache = {}
                    if os.path.exists(cache_path):
                        try:
                            with open(cache_path, 'r', encoding='utf-8') as f:
                                current_cache = json.load(f)
                        except (json.JSONDecodeError, UnicodeDecodeError):
                            logger.warning("Corrupted scan cache detected at %s; resetting cache.", cache_path)
                            current_cache = {}
                    if not isinstance(current_cache, dict):
                        logger.warning("Scan cache at %s is not a dict; resetting cache.", cache_path)
                        current_cache = {}
                    if entries_to_add:
                        # Stamp entries with the write time so a later purge from a
                        # stale scanner can distinguish fresh entries from stale ones.
                        _now = time.time()
                        stamped_entries = {}
                        for _k, _v in entries_to_add.items():
                            if isinstance(_v, dict):
                                stamped_entries[_k] = {**_v, '_updated': _now}
                            else:
                                stamped_entries[_k] = _v
                        current_cache.update(stamped_entries)
                    if paths_to_delete:
                        for p in paths_to_delete:
                            if not_before_ts is not None:
                                entry = current_cache.get(p)
                                if isinstance(entry, dict):
                                    try:
                                        if float(entry.get('_updated', 0) or 0) > not_before_ts:
                                            continue  # refreshed by a newer scan — keep it
                                    except (TypeError, ValueError):
                                        pass
                            current_cache.pop(p, None)
                    # Unique temp name: a fixed '.tmp' races across processes.
                    fd, temp_path = tempfile.mkstemp(dir=CONFIG_DIR, prefix='scan_cache.', suffix='.tmp')
                    try:
                        with os.fdopen(fd, 'w', encoding='utf-8') as f:
                            json.dump(current_cache, f, ensure_ascii=False, indent=2)
                            f.flush()
                            os.fsync(f.fileno())
                        os.replace(temp_path, cache_path)  # atomic on both Windows and POSIX
                    except BaseException:
                        try:
                            os.remove(temp_path)
                        except OSError:
                            pass
                        raise
                    break
                except (TypeError, ValueError) as e:
                    # Deterministic serialization errors won't heal on retry.
                    logger.warning("Cache write failed (not retrying): %s", e)
                    break
                except Exception as e:
                    logger.warning("Cache write attempt failed: %s", e)
                    time.sleep(0.05)
        except Exception as e:
            logger.warning("update_metadata_cache failed: %s", e)

def get_resolution_tag(width: int, height: int) -> str:
    try:
        width = int(width)
        height = int(height)
    except (TypeError, ValueError):
        return ""
    if width <= 0 or height <= 0: return ""
    lesser = min(width, height)
    if lesser >= 2160: return "4K"
    elif lesser >= 1440: return "2K"
    elif lesser >= 1080: return "1K"
    else: return "K"

def format_duration_compact(total_seconds: float) -> str:
    total_seconds = int(round(_safe_float(total_seconds, 0.0)))
    if total_seconds < 0: total_seconds = 0
    hours = total_seconds // 3600
    minutes = (total_seconds % 3600) // 60
    seconds = total_seconds % 60
    if hours > 0: return f"{hours}{minutes:02d}{seconds:02d}"
    else: return f"{minutes}{seconds:02d}"

def format_duration(total_seconds: float) -> str:
    total_seconds = int(round(_safe_float(total_seconds, 0.0)))
    if total_seconds < 0: total_seconds = 0
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
    size_bytes = _safe_float(size_bytes, 0)
    if size_bytes <= 0: return "0 B"
    for unit in ['B', 'KB', 'MB', 'GB', 'TB']:
        if abs(size_bytes) < 1024.0:
            return f"{size_bytes:.1f} {unit}"
        size_bytes /= 1024.0
    return f"{size_bytes:.1f} PB"

def parse_naming_format(filename: str, media_type: str = None) -> tuple[str | None, str | None]:
    if not isinstance(filename, str):
        return None, None
    filename = filename.strip()
    if not filename:
        return None, None
    # Match video: Artist Duration Resolution [Rating] (including 'K' for sub-1080p)
    match = re.match(r"^(.+?)\s+(\d+)\s+(4K|2K|1K|K)(?:\s+(\d+|—))?(?:\..+)?$", filename, re.IGNORECASE)
    if match:
        artist = match.group(1).strip()
        rating = match.group(4)
        return artist, (None if rating == "—" else rating)
    
    # Match image: Artist Resolution [Rating] (including 'K' for sub-1080p)
    match_img = re.match(r"^(.+?)\s+(4K|2K|1K|K)(?:\s+(\d+|—))?(?:\..+)?$", filename, re.IGNORECASE)
    if match_img:
        artist = match_img.group(1).strip()
        rating = match_img.group(3)
        return artist, (None if rating == "—" else rating)
        
    # Match audio: Artist Duration [Rating] (rating is optional).
    # NOTE: only apply this bare-integer pattern to audio files — for other
    # media types it wrongly swallows trailing numbers (e.g. the year in
    # "Beach Trip 2021.mp4" gets parsed as a duration and then dropped from
    # {name} during renames).
    if media_type is None or media_type == 'audio':
        match_aud = re.match(r"^(.+?)\s+(\d+)(?:\s+(\d+|—))?(?:\..+)?$", filename, re.IGNORECASE)
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
    except Exception as e:
        logger.debug("calculate_file_hash failed for %s: %s", filepath, e)
        return None

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
                    try:
                        with _CV_LOCK:
                            cap.release()
                    except Exception:
                        try:
                            cap.release()
                        except Exception:
                            pass
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
    except Exception as e:
        logger.debug("hamming_distance failed for %s/%s: %s", h1, h2, e)
        return 999

def matches_query(info: 'MediaInfo', query_str: str, preview_name: str = "") -> bool:
    if not query_str: return True
    # posix=False on Windows so backslashes in paths (name:C:\foo) survive splitting
    try: terms = shlex.split(query_str.strip(), posix=(os.name != 'nt'))
    except Exception: terms = query_str.strip().split()
    
    # Prefer user-edited values stored on the info object; fall back to parsing
    # the raw filename only when no edited/parsed values exist yet.
    parsed_artist = getattr(info, 'parsed_artist', None) or ""
    parsed_rating = getattr(info, 'parsed_rating', None) or ""
    if not parsed_artist and not parsed_rating:
        parsed_artist, parsed_rating = parse_naming_format(getattr(info, 'filename', '') or "", getattr(info, 'media_type', None))
    artist = (parsed_artist or "").lower().strip()
    rating = (parsed_rating or "").lower().strip()
    filename = (getattr(info, 'filename', '') or "").lower()
    
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
                tags = [t.lower().strip() for t in (getattr(info, 'tags', []) or [])]
                if ',' in val:
                    query_tags = [x.strip() for x in val.split(',')]
                    if not any(qt in tags for qt in query_tags): return False
                else:
                    if val not in tags: return False
            elif key in ['name', 'artist']:
                # Check both parsed artist name and raw filename
                if not val or (val not in artist and val not in filename): return False
            elif key in ['res', 'resolution']:
                res_tag = (getattr(info, 'resolution_tag', '') or '').lower()
                res_dims = f"{getattr(info, 'width', 0)}x{getattr(info, 'height', 0)}".lower()
                res_dims_alt = f"{getattr(info, 'width', 0)}×{getattr(info, 'height', 0)}".lower()
                if val not in res_tag and val not in res_dims and val not in res_dims_alt: return False
            elif key == 'type':
                norm_val = {'videos': 'video', 'images': 'image', 'pdfs': 'pdf', 'audios': 'audio'}.get(val, val)
                if norm_val != (getattr(info, 'media_type', '') or '').lower(): return False
            elif key in ['ext', 'extension']:
                ext_val = val if val.startswith('.') else f".{val}"
                if (getattr(info, 'extension', '') or '').lower() != ext_val.lower(): return False
            else:
                val_sub = f"{key}:{val}"
                tags = [t.lower().strip() for t in (getattr(info, 'tags', []) or [])]
                if not (val_sub in filename or val_sub in artist or val_sub in rating or (preview_name and val_sub in preview_name.lower()) or any(val_sub in t for t in tags)): return False
        else:
            val = term_clean.lower()
            tags = [t.lower().strip() for t in (getattr(info, 'tags', []) or [])]
            if not (val in filename or val in artist or val in rating or (preview_name and val in preview_name.lower()) or any(val in t for t in tags)): return False
    return True

_WIN_RESERVED_NAMES = {
    'CON', 'PRN', 'AUX', 'NUL',
    'COM1', 'COM2', 'COM3', 'COM4', 'COM5', 'COM6', 'COM7', 'COM8', 'COM9',
    'LPT1', 'LPT2', 'LPT3', 'LPT4', 'LPT5', 'LPT6', 'LPT7', 'LPT8', 'LPT9'
}

def sanitize_folder_name(name: str) -> str:
    """Remove illegal characters and reserved device names for folder names across OS."""
    if not isinstance(name, str) or not name:
        return "Unknown"
    # Remove control chars (0-31) and Windows illegal characters: \ / : * ? " < > |
    clean = re.sub(r'[\x00-\x1f\\/*?:"<>|]', "", name).strip()
    # Reserved device names break Windows even from non-Windows hosts (USB
    # drives) and even with an extension (CON.txt), so always guard the stem.
    clean = clean.rstrip(". ")
    if clean.split('.')[0].upper() in _WIN_RESERVED_NAMES:
        clean = f"{clean}_folder"
    if len(clean) > 100:
        clean = clean[:100].rstrip(". ")
    return clean or "Unknown"

def _strip_path_traversal(value: str) -> str:
    """Remove path separators and '..' components from a substituted path segment."""
    if not value:
        return ""
    if not isinstance(value, str):
        value = str(value)
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
    if tags is None:
        tags = getattr(info, 'tags', []) or []
    else:
        tags = [t for t in tags if isinstance(t, str) and t]
    if not isinstance(template, str):
        return ""
    parsed_artist, parsed_rating = parse_naming_format(getattr(info, 'filename', '') or "", getattr(info, 'media_type', None))
    user_artist = getattr(info, 'parsed_artist', None)
    user_rating = getattr(info, 'parsed_rating', None)

    # Fallback: user edit -> parsed filename -> tags -> default
    artist = user_artist or parsed_artist or (tags[0] if tags else "Unknown Artist")
    rating = user_rating or parsed_rating or "Unrated"

    dt = get_media_datetime(info)
    date_str = dt.strftime("%Y-%m-%d") if dt else "Unknown Date"
    year_str = dt.strftime("%Y") if dt else "Unknown Year"
    ym_str = dt.strftime("%Y%m") if dt else "Unknown YM"

    ext = (getattr(info, 'extension', '') or '').replace('.', '')
    stem = os.path.splitext(os.path.basename(getattr(info, 'filename', '') or ''))[0]
    # Map variables to data; apply extra traversal-stripping to user-controlled fields
    replacements = {
        'type': _strip_path_traversal(getattr(info, 'media_type', '') or 'unknown'),
        'ext': _strip_path_traversal(ext),
        'name': _strip_path_traversal(sanitize_folder_name(artist)),
        'filename': _strip_path_traversal(sanitize_folder_name(stem or "Unknown")),
        'rating': _strip_path_traversal(sanitize_folder_name(rating)),
        'resolution': _strip_path_traversal(getattr(info, 'resolution_tag', '') or "Unknown"),
        'tag': _strip_path_traversal(sanitize_folder_name(tags[0]) if tags else "Untagged"),
        'tags': _strip_path_traversal(sanitize_folder_name(", ".join(tags)) if tags else "Untagged"),
        'date': _strip_path_traversal(date_str),
        'year': _strip_path_traversal(year_str),
        'ym': _strip_path_traversal(ym_str)
    }

    result = template
    for key, val in replacements.items():
        pattern = re.compile(re.escape('{' + key + '}'), re.IGNORECASE)
        result = pattern.sub(val, result)

    return result

def get_ffprobe_command(custom_path=None) -> str | None:
    if custom_path and os.path.isfile(custom_path): return custom_path
    sh_path = shutil.which("ffprobe")
    return sh_path

def _resolve_ffmpeg_from_ffprobe_hint(ffprobe_hint: str | None) -> str | None:
    """Resolve an ffmpeg binary from a stored ffprobe path or directory.

    The settings UI stores the ffprobe *file* path (or its directory); the
    trim exporter needs the ffmpeg *sibling* next to it.
    """
    if not ffprobe_hint or not isinstance(ffprobe_hint, str):
        return None
    base_dir = ffprobe_hint if os.path.isdir(ffprobe_hint) else os.path.dirname(ffprobe_hint)
    if not base_dir:
        return None
    cand = os.path.join(base_dir, "ffmpeg.exe" if sys.platform == "win32" else "ffmpeg")
    return cand if os.path.isfile(cand) else None

def get_ffmpeg_command(custom_path=None) -> str | None:
    if custom_path:
        if os.path.isdir(custom_path):
            resolved = _resolve_ffmpeg_from_ffprobe_hint(custom_path)
            if resolved: return resolved
        elif os.path.isfile(custom_path):
            name = os.path.basename(custom_path).lower()
            if name in ("ffmpeg", "ffmpeg.exe"):
                return custom_path
            resolved = _resolve_ffmpeg_from_ffprobe_hint(custom_path)
            if resolved: return resolved
    sh_path = shutil.which("ffmpeg")
    if sh_path: return sh_path
    ffprobe_cmd = get_ffprobe_command()
    if ffprobe_cmd and os.path.dirname(ffprobe_cmd):
        ffmpeg_sibling = os.path.join(os.path.dirname(ffprobe_cmd), "ffmpeg.exe" if sys.platform == "win32" else "ffmpeg")
        if os.path.isfile(ffmpeg_sibling):
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
        # errors='replace': a single stray non-UTF-8 tag byte must not discard
        # the entire metadata payload via UnicodeDecodeError.
        result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, encoding='utf-8', errors='replace', startupinfo=startupinfo, timeout=10)
        if result.returncode == 0 and result.stdout:
            return parse_ffprobe_json(json.loads(result.stdout))
    except Exception as e:
        logger.debug("get_file_deep_metadata failed for %s: %s", filepath, e)
    return None

def parse_ffprobe_json(data: dict) -> dict:
    parsed = {'format': '', 'size_bytes': 0, 'duration_seconds': 0.0, 'bitrate_kbps': 0, 'video': None, 'audio': None, 'hdr_type': 'SDR'}
    if not isinstance(data, dict):
        return parsed
    fmt = data.get('format', {}) or {}
    if not isinstance(fmt, dict):
        fmt = {}
    parsed['format'] = fmt.get('format_long_name', fmt.get('format_name', 'Unknown')) or 'Unknown'
    parsed['size_bytes'] = _safe_int(fmt.get('size', 0))
    parsed['duration_seconds'] = _safe_float(fmt.get('duration', 0.0))
    parsed['bitrate_kbps'] = _safe_int(fmt.get('bit_rate', 0)) // 1000
    for stream in (data.get('streams') or []):
        if not isinstance(stream, dict):
            continue
        codec_type = stream.get('codec_type')
        if codec_type == 'video' and not parsed['video']:
            v_info = {'codec': (stream.get('codec_name') or '').upper(), 'profile': stream.get('profile') or '', 'width': _safe_int(stream.get('width', 0)), 'height': _safe_int(stream.get('height', 0)), 'fps': 0.0, 'bitrate_kbps': 0, 'pix_fmt': stream.get('pix_fmt') or ''}
            fps_str = str(stream.get('r_frame_rate') or stream.get('avg_frame_rate') or '')
            if '/' in fps_str:
                try:
                    parts = fps_str.split('/')
                    if len(parts) == 2:
                        num, den = float(parts[0]), float(parts[1])
                        if den > 0: v_info['fps'] = round(num / den, 2)
                except (ValueError, ZeroDivisionError): pass
            elif fps_str:
                try:
                    val = float(fps_str)
                    if val > 0: v_info['fps'] = round(val, 2)
                except ValueError: pass
            v_info['bitrate_kbps'] = _safe_int(stream.get('bit_rate', 0)) // 1000
            parsed['video'] = v_info
            for sd in (stream.get('side_data_list') or []):
                if not isinstance(sd, dict):
                    continue
                sd_type = sd.get('side_data_type', '') or ''
                if 'dovi' in sd_type.lower() or 'dolby vision' in sd_type.lower() or sd.get('dovi_profile') is not None:
                    parsed['hdr_type'] = 'Dolby Vision'; break
            if parsed['hdr_type'] == 'SDR':
                color_transfer = stream.get('color_transfer', '')
                if color_transfer == 'smpte2084':
                    codec_tag = stream.get('codec_tag_string', '')
                    parsed['hdr_type'] = 'Dolby Vision' if codec_tag in ['dvh1', 'dvhe'] else 'HDR10'
                elif color_transfer == 'arib-std-b67': parsed['hdr_type'] = 'HLG'
        elif codec_type == 'audio' and not parsed['audio']:
            reported_layout = stream.get('channel_layout') or ''
            a_info = {'codec': (stream.get('codec_name') or '').upper(), 'sample_rate_hz': _safe_int(stream.get('sample_rate', 0)), 'channels': _safe_int(stream.get('channels', 0)), 'channel_layout': reported_layout, 'bitrate_kbps': 0}
            a_info['bitrate_kbps'] = _safe_int(stream.get('bit_rate', 0)) // 1000
            ch = a_info['channels']
            if reported_layout:
                # Prefer ffprobe's reported layout; annotate only unusual channel counts.
                a_info['channel_layout'] = reported_layout if ch in (1, 2, 6, 8) else (f"{reported_layout} ({ch} ch)" if ch > 0 else reported_layout)
            elif ch == 1: a_info['channel_layout'] = 'Mono'
            elif ch == 2: a_info['channel_layout'] = 'Stereo'
            elif ch == 6: a_info['channel_layout'] = '5.1 Surround'
            elif ch == 8: a_info['channel_layout'] = '7.1 Surround'
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
        if width <= 0 or height <= 0: return None
        if media_type == 'audio':
            img = QImage(width, height, QImage.Format.Format_ARGB32_Premultiplied)
            img.fill(QColor("#1e1b4b"))
            with QPainter(img) as painter:
                painter.setRenderHint(QPainter.RenderHint.Antialiasing)
                painter.setFont(QFont(BASE_FONT_FAMILY, 14, QFont.Weight.Bold))
                painter.setPen(QColor("#a78bfa"))
                painter.drawText(QRect(0, 0, width, height), Qt.AlignmentFlag.AlignCenter, "AUDIO")
            return img
        if media_type == 'pdf':
            img = QImage(width, height, QImage.Format.Format_ARGB32_Premultiplied)
            img.fill(QColor("#1e1b4b"))
            with QPainter(img) as painter:
                painter.setRenderHint(QPainter.RenderHint.Antialiasing)
                painter.setFont(QFont(BASE_FONT_FAMILY, 14, QFont.Weight.Bold))
                painter.setPen(QColor("#f87171"))
                painter.drawText(QRect(0, 0, width, height), Qt.AlignmentFlag.AlignCenter, "PDF")
            return img
        if media_type == 'video':
            cap = None
            try:
                # Lock granularity: hold _CV_LOCK around each individual cv2 C++
                # call (as calculate_perceptual_hash does) instead of across the
                # whole open+seek+decode sequence. Holding it across decode
                # serialized all scan workers behind one file and stalled any
                # GUI-thread cv2 calls for seconds at a time.
                with _CV_LOCK:
                    cap = cv2.VideoCapture(filepath)
                if not cap.isOpened(): return None
                with _CV_LOCK:
                    total_frames = cap.get(cv2.CAP_PROP_FRAME_COUNT)
                # Some playable files (bad index, .ts captures) report
                # FRAME_COUNT <= 0 or NaN — fall through to frame 0 instead
                # of giving up on the thumbnail.
                if math.isfinite(total_frames) and total_frames > 0:
                    target_frame = int(total_frames * 0.1)
                else:
                    target_frame = 0
                with _CV_LOCK:
                    cap.set(cv2.CAP_PROP_POS_FRAMES, target_frame)
                    ret, frame = cap.read()
                if not ret or frame is None:
                    with _CV_LOCK:
                        cap.set(cv2.CAP_PROP_POS_FRAMES, 0)
                        ret, frame = cap.read()
            finally:
                if cap is not None:
                    try:
                        with _CV_LOCK:
                            cap.release()
                    except Exception:
                        try:
                            cap.release()
                        except Exception:
                            pass
        else:
            with _CV_LOCK:
                frame = cv2.imdecode(np.fromfile(filepath, dtype=np.uint8), cv2.IMREAD_COLOR)
            ret = frame is not None
        if not ret or frame is None: return None
        with _CV_LOCK:
            frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
        h, w = frame.shape[:2]
        if h <= 0 or w <= 0: return None
        aspect = w / h
        if aspect <= 0: return None
        if width / height > aspect:
            new_h = height
            new_w = max(1, int(height * aspect))
        else:
            new_w = width
            new_h = max(1, int(width / aspect))
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
    filepath = os.path.abspath(filepath)
    base = os.path.splitext(filepath)[0]
    parent = os.path.dirname(filepath) or "."
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
        # Accept exact stem, language markers (.en / -de / _pt-br), or descriptive tags (.forced, .default, .sdh, .cc),
        # including stacked combinations common in Plex/Jellyfin libraries (movie.en.forced.srt).
        if mid == "" or re.fullmatch(r"(?:[\.\-_ ][a-zA-Z0-9_\-]+)+", mid):
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
                    if b[0] != 0xFF: return None  # desynced — not a valid marker stream
                    marker = b[1]
                    # 0xFF fill bytes precede some markers — skip them so the
                    # parser stays in sync (e.g. "FF FF E1" padding sequences).
                    while marker == 0xFF:
                        nxt = f.read(1)
                        if not nxt: return None
                        marker = nxt[0]
                    # Standalone markers (SOI/TEM/RSTn) have no length/payload — must not consume bytes
                    if marker in (0xD8, 0x01) or 0xD0 <= marker <= 0xD7:
                        continue
                    if marker == 0xD9: return None  # EOI — no Exif found
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
                # EXIF IFDs live near the start; never slurp a whole (possibly
                # hundreds-of-MB) TIFF into RAM.
                tiff_data = f.read(1024 * 1024)
            if not tiff_data or len(tiff_data) < 16:
                return None

            endian = "little" if tiff_data[:2] == b"II" else "big"
            ifd0 = int.from_bytes(tiff_data[4:8], endian)

            def rd(off, n): return tiff_data[off:off + n]

            def walk_ifd(ifd_off, want, depth=0):
                vals = {}
                if depth > 4:  # hostile/cyclic SubIFD pointer — bail instead of recursing
                    return vals
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
                            vals.update(walk_ifd(sub, want, depth + 1))
                return vals

            got = walk_ifd(ifd0, {0x9003, 0x9004, 0x0132})
            raw = got.get(0x9003) or got.get(0x9004) or got.get(0x0132)
            if raw:
                return datetime.strptime(raw.strip()[:19], "%Y:%m:%d %H:%M:%S")
    except Exception as e:
        logger.debug("_exif_datetime_original failed for %s: %s", filepath, e)
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
            # NOTE: never prepend \\?\ here — SHFileOperationW does not support
            # extended-length paths and would delete long paths PERMANENTLY
            # (FOF_ALLOWUNDO ignored) while reporting success. Prefer send2trash
            # (handles long paths correctly); if unavailable, attempt the shell
            # API on the original path — a visible failure is safer than a
            # silent permanent delete.
            if len(path) > 240:
                try:
                    from send2trash import send2trash as _send2trash
                    _send2trash(path)
                    return not os.path.exists(path)
                except ImportError:
                    logger.warning("Path longer than 240 chars and send2trash not installed; recycling may fail: %s", path)
                except Exception as e:
                    logger.warning("send2trash failed for %s: %s", path, e)
                    return False
            # SHFileOperationW requires a DOUBLE-null-terminated string;
            # create_unicode_buffer already appends one terminator, so add one.
            p_from_buf = create_unicode_buffer(path + "\0")
            fileop = SHFILEOPSTRUCTW()
            fileop.hwnd = None
            fileop.wFunc = 3  # FO_DELETE
            fileop.pFrom = cast(p_from_buf, LPCWSTR)
            fileop.pTo = None
            fileop.fFlags = 0x0040 | 0x0010 | 0x0004  # ALLOWUNDO | NOCONFIRMATION | SILENT
            fileop.fAnyOperationsAborted = 0
            fileop.hNameMappings = None
            fileop.lpszProgressTitle = None
            ok = windll.shell32.SHFileOperationW(byref(fileop)) == 0
            # Return code 0 with the abort flag set means nothing was deleted.
            if ok and bool(fileop.fAnyOperationsAborted):
                return False
            return ok and not os.path.exists(path)
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

_ICON_COLOR_OVERRIDE = None  # per-theme accent for vector icons (set by apply_theme)


def set_icon_accent(color_hex):
    """Point vector icons at the active theme's accent color (None = default violet)."""
    global _ICON_COLOR_OVERRIDE
    _ICON_COLOR_OVERRIDE = color_hex


def get_vector_icon(name: str, is_dark: bool, color_override: str = None) -> QIcon:
    # Cache icons to avoid rebuilding 6 sizes x ~20 icons on every theme toggle
    cache_key = (name, is_dark, _ICON_COLOR_OVERRIDE, color_override)
    if cache_key in _ICON_CACHE:
        return _ICON_CACHE[cache_key]
    icon = _build_vector_icon(name, is_dark, color_override)
    _ICON_CACHE[cache_key] = icon
    return icon


def _build_vector_icon(name: str, is_dark: bool, color_override: str = None) -> QIcon:
    accent = color_override or _ICON_COLOR_OVERRIDE
    if color_override:
        color_hex = color_override
    elif name in ['delete', 'clear', 'mute', 'stop', 'close', 'btnSettingsRemove']:
        color_hex = '#f87171' if is_dark else '#dc2626'
    elif name in ['process', 'play', 'pause', 'valid', 'check']:
        color_hex = '#34d399' if is_dark else '#059669'
    elif name in ['warning']:
        color_hex = '#fbbf24' if is_dark else '#d97706'
    elif name in ['video', 'image', 'audio', 'star', 'save', 'plus', 'pdf', 'relocate',
                  'stats', 'watch', 'filter', 'duplicate', 'tag', 'columns', 'presets',
                  'scissors', 'trim', 'info', 'prev', 'next', 'shuffle']:
        color_hex = accent or ('#a78bfa' if is_dark else '#6366f1')
    else:
        color_hex = accent or ('#c4b5fd' if is_dark else '#4338ca')

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
        elif name == 'prev':
            painter.setBrush(QBrush(color))
            painter.drawRoundedRect(QRectF(5, 5, 2.5, 14), 1, 1)
            path = QPainterPath()
            path.moveTo(18, 5)
            path.lineTo(8, 12)
            path.lineTo(18, 19)
            path.closeSubpath()
            painter.drawPath(path)
        elif name == 'next':
            painter.setBrush(QBrush(color))
            path = QPainterPath()
            path.moveTo(6, 5)
            path.lineTo(16, 12)
            path.lineTo(6, 19)
            path.closeSubpath()
            painter.drawPath(path)
            painter.drawRoundedRect(QRectF(16.5, 5, 2.5, 14), 1, 1)
        elif name == 'shuffle':
            pen_shuf = QPen(color, 2.0, Qt.PenStyle.SolidLine, Qt.PenCapStyle.RoundCap, Qt.PenJoinStyle.RoundJoin)
            painter.setPen(pen_shuf)
            painter.setBrush(Qt.BrushStyle.NoBrush)
            painter.drawLine(QPointF(4, 7), QPointF(9, 7))
            painter.drawLine(QPointF(9, 7), QPointF(15, 17))
            painter.drawLine(QPointF(15, 17), QPointF(20, 17))
            painter.drawLine(QPointF(17, 14), QPointF(20, 17))
            painter.drawLine(QPointF(17, 20), QPointF(20, 17))
            painter.drawLine(QPointF(4, 17), QPointF(9, 17))
            painter.drawLine(QPointF(9, 17), QPointF(15, 7))
            painter.drawLine(QPointF(15, 7), QPointF(20, 7))
            painter.drawLine(QPointF(17, 4), QPointF(20, 7))
            painter.drawLine(QPointF(17, 10), QPointF(20, 7))
        elif name == 'tag':
            path = QPainterPath()
            path.moveTo(4, 11)
            path.lineTo(4, 5)
            path.lineTo(10, 5)
            path.lineTo(19, 14)
            path.lineTo(13, 20)
            path.closeSubpath()
            fill_color = QColor(color)
            fill_color.setAlpha(60)
            painter.setBrush(QBrush(fill_color))
            painter.drawPath(path)
            painter.setBrush(Qt.BrushStyle.NoBrush)
            painter.drawEllipse(QPointF(7.5, 8.5), 1.5, 1.5)
        elif name == 'stats':
            fill_color = QColor(color)
            fill_color.setAlpha(70)
            painter.setBrush(QBrush(fill_color))
            painter.drawRoundedRect(QRectF(4, 13, 4, 7), 1, 1)
            painter.drawRoundedRect(QRectF(10, 8, 4, 12), 1, 1)
            painter.drawRoundedRect(QRectF(16, 4, 4, 16), 1, 1)
        elif name == 'watch':
            painter.drawEllipse(QRectF(3.5, 3.5, 17, 17))
            fill_color = QColor(color)
            fill_color.setAlpha(35)
            painter.setBrush(QBrush(fill_color))
            painter.drawEllipse(QRectF(7, 7, 10, 10))
            painter.setBrush(Qt.BrushStyle.NoBrush)
            painter.drawLine(QPointF(12, 12), QPointF(12, 6.5))
            painter.drawLine(QPointF(12, 12), QPointF(15.5, 12))
            painter.drawEllipse(QPointF(12, 12), 1.5, 1.5)
        elif name in ['scissors', 'trim']:
            painter.drawEllipse(QRectF(4, 5, 5, 5))
            painter.drawEllipse(QRectF(4, 14, 5, 5))
            painter.drawLine(QPointF(8.5, 8.5), QPointF(20, 17))
            painter.drawLine(QPointF(8.5, 15.5), QPointF(20, 7))
        elif name == 'duplicate':
            painter.drawRoundedRect(QRectF(7, 3, 13, 13), 2, 2)
            fill_color = QColor(color)
            fill_color.setAlpha(60)
            painter.setBrush(QBrush(fill_color))
            painter.drawRoundedRect(QRectF(4, 7, 13, 13), 2, 2)
        elif name == 'filter':
            path = QPainterPath()
            path.moveTo(3, 4)
            path.lineTo(21, 4)
            path.lineTo(13.5, 13)
            path.lineTo(13.5, 19)
            path.lineTo(10.5, 20.5)
            path.lineTo(10.5, 13)
            path.closeSubpath()
            fill_color = QColor(color)
            fill_color.setAlpha(60)
            painter.setBrush(QBrush(fill_color))
            painter.drawPath(path)
        elif name == 'columns':
            painter.drawRoundedRect(QRectF(3, 4, 18, 16), 2, 2)
            painter.drawLine(QPointF(9, 4), QPointF(9, 20))
            painter.drawLine(QPointF(15, 4), QPointF(15, 20))
        elif name == 'presets':
            painter.drawLine(QPointF(4, 7), QPointF(20, 7))
            painter.drawLine(QPointF(4, 12), QPointF(20, 12))
            painter.drawLine(QPointF(4, 17), QPointF(20, 17))
            fill_color = QColor(color)
            painter.setBrush(QBrush(fill_color))
            painter.drawEllipse(QPointF(8, 7), 2, 2)
            painter.drawEllipse(QPointF(16, 12), 2, 2)
            painter.drawEllipse(QPointF(10, 17), 2, 2)
        elif name == 'info':
            painter.drawEllipse(QRectF(4, 4, 16, 16))
            fill_color = QColor(color)
            painter.setBrush(QBrush(fill_color))
            painter.drawEllipse(QPointF(12, 8.5), 1.2, 1.2)
            painter.setBrush(Qt.BrushStyle.NoBrush)
            painter.drawLine(QPointF(12, 11), QPointF(12, 16))
            painter.drawLine(QPointF(10.5, 11), QPointF(12, 11))
            painter.drawLine(QPointF(10.5, 16), QPointF(13.5, 16))
        elif name in ['check', 'valid']:
            path = QPainterPath()
            path.moveTo(4, 12)
            path.lineTo(9.5, 17.5)
            path.lineTo(20, 6.5)
            painter.drawPath(path)
        elif name == 'warning':
            path = QPainterPath()
            path.moveTo(12, 4)
            path.lineTo(21, 19.5)
            path.lineTo(3, 19.5)
            path.closeSubpath()
            fill_color = QColor(color)
            fill_color.setAlpha(45)
            painter.setBrush(QBrush(fill_color))
            painter.drawPath(path)
            painter.setBrush(Qt.BrushStyle.NoBrush)
            painter.drawLine(QPointF(12, 9), QPointF(12, 14))
            painter.drawEllipse(QPointF(12, 16.5), 0.8, 0.8)

        painter.end()
        icon.addPixmap(pixmap)
    return icon

class EditableCellLineEdit(QLineEdit):
    """Table cell text editor: stays in clean read-only mode with a standard
    arrow cursor when idle/hovered. Enters active editing mode only on an
    explicit click or keyboard Tab navigation.

    Prevents focus-follows-mouse / sloppy focus or synthetic focus events
    from hovering over the cell widget and stealing focus or triggering
    accidental row selections in the parent QTableWidget.
    """

    def __init__(self, placeholder: str = "", parent=None):
        super().__init__(parent)
        self.setPlaceholderText(placeholder)
        self.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.setReadOnly(True)
        self.setCursor(Qt.CursorShape.ArrowCursor)
        self._editing_active = False
        self.installEventFilter(self)

    def eventFilter(self, watched, ev):
        if watched is self and ev.type() == QEvent.Type.FocusIn:
            if not self._editing_active:
                # Consume any FocusIn event that was not triggered by an explicit edit activation.
                # This stops QAbstractItemView from seeing FocusIn and selecting the table row on hover.
                return True
        return super().eventFilter(watched, ev)

    def _enclosing_table(self):
        p = self.parent()
        while p is not None:
            if isinstance(p, QTableWidget):
                return p
            p = p.parent()
        return None

    def _start_editing(self):
        self._editing_active = True
        self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        self.setReadOnly(False)
        self.setCursor(Qt.CursorShape.IBeamCursor)
        self.setFocus(Qt.FocusReason.MouseFocusReason)

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            table = self._enclosing_table()
            if table is not None:
                pos = table.viewport().mapFromGlobal(self.mapToGlobal(self.rect().center()))
                idx = table.indexAt(pos)
                if idx.isValid():
                    table.setCurrentCell(idx.row(), idx.column())
            self._start_editing()
        super().mousePressEvent(event)

    def focusInEvent(self, event):
        if not self._editing_active:
            self.clearFocus()
            self.setFocusPolicy(Qt.FocusPolicy.NoFocus)
            event.ignore()
            return
        super().focusInEvent(event)

    def focusOutEvent(self, event):
        if event.reason() == Qt.FocusReason.PopupFocusReason:
            # Context menu opened (copy/paste) — don't exit edit mode
            super().focusOutEvent(event)
            return
        if self._editing_active:
            self._editing_active = False
            self.editingFinished.emit()
        # Set read-only BEFORE super().focusOutEvent(): while the widget is
        # still editable at focus-out, QLineEdit emits its own native
        # editingFinished — producing a double emission (duplicate saves).
        self.setReadOnly(True)
        super().focusOutEvent(event)
        self.setCursor(Qt.CursorShape.ArrowCursor)
        self.deselect()
        self.setFocusPolicy(Qt.FocusPolicy.NoFocus)

    def _handle_tab_navigation(self, forward: bool) -> bool:
        table = self._enclosing_table()
        if table is None:
            return False
        pos = table.viewport().mapFromGlobal(self.mapToGlobal(self.rect().center()))
        idx = table.indexAt(pos)
        if not idx.isValid():
            return False
        row, col = idx.row(), idx.column()
        p = table.parent()
        owner = None
        while p is not None:
            if hasattr(p, 'COL_ARTIST') and hasattr(p, 'COL_TAGS'):
                owner = p
                break
            p = p.parent()
        col_artist = getattr(owner, 'COL_ARTIST', 6)
        col_tags = getattr(owner, 'COL_TAGS', 8)

        if forward:
            if col == col_artist:
                target_row, target_col = row, col_tags
            else:
                target_row, target_col = row + 1, col_artist
        else:
            if col == col_tags:
                target_row, target_col = row, col_artist
            else:
                target_row, target_col = row - 1, col_tags

        if 0 <= target_row < table.rowCount():
            if owner is not None and hasattr(owner, '_ensure_widgets_for_row'):
                owner._ensure_widgets_for_row(target_row)
            target_widget = table.cellWidget(target_row, target_col)
            if isinstance(target_widget, EditableCellLineEdit):
                if self._editing_active:
                    self.editingFinished.emit()
                self._editing_active = False
                self.setReadOnly(True)
                self.setCursor(Qt.CursorShape.ArrowCursor)
                self.deselect()
                self.clearFocus()
                self.setFocusPolicy(Qt.FocusPolicy.NoFocus)

                table.setCurrentCell(target_row, target_col)
                target_widget._start_editing()
                target_widget.selectAll()
                return True
        return False

    def keyPressEvent(self, event):
        if event.key() in (Qt.Key.Key_Return, Qt.Key.Key_Enter):
            if self._editing_active:
                self.editingFinished.emit()
            self._editing_active = False
            self.setReadOnly(True)
            self.setCursor(Qt.CursorShape.ArrowCursor)
            self.deselect()
            self.clearFocus()
            self.setFocusPolicy(Qt.FocusPolicy.NoFocus)
            event.accept()
            return
        elif event.key() == Qt.Key.Key_Escape:
            self._editing_active = False
            self.setReadOnly(True)
            self.setCursor(Qt.CursorShape.ArrowCursor)
            self.deselect()
            self.clearFocus()
            self.setFocusPolicy(Qt.FocusPolicy.NoFocus)
            event.accept()
            return
        elif event.key() == Qt.Key.Key_Tab:
            forward = not bool(event.modifiers() & Qt.KeyboardModifier.ShiftModifier)
            if self._handle_tab_navigation(forward=forward):
                event.accept()
                return
        elif event.key() == Qt.Key.Key_Backtab:
            if self._handle_tab_navigation(forward=False):
                event.accept()
                return
        super().keyPressEvent(event)

class EditableCellComboBox(QComboBox):
    """Table cell combobox (e.g. Rating): stays in clean read-only/no-focus mode
    when idle or hovered. Activates and focuses only on an explicit mouse click.

    Prevents hover/pointer drift or synthetic FocusIn events from triggering
    accidental row selections in the parent QTableWidget, and ignores wheel
    events to prevent inadvertent value changes while scrolling the table.
    """

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.installEventFilter(self)
        self._clicking = False

    def _is_popup_open(self) -> bool:
        try:
            v = self.view()
            return bool(v is not None and v.isVisible())
        except (RuntimeError, AttributeError):
            return False

    def eventFilter(self, watched, ev):
        if watched is self and ev.type() == QEvent.Type.FocusIn:
            # Drop FocusIn unless triggered by an active user click or open popup
            if not self._clicking and not self._is_popup_open():
                return True
        return super().eventFilter(watched, ev)

    def _enclosing_table(self):
        p = self.parent()
        while p is not None:
            if isinstance(p, QTableWidget):
                return p
            p = p.parent()
        return None

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self._clicking = True
            self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
            table = self._enclosing_table()
            if table is not None:
                pos = table.viewport().mapFromGlobal(self.mapToGlobal(self.rect().center()))
                idx = table.indexAt(pos)
                if idx.isValid():
                    table.setCurrentCell(idx.row(), idx.column())
            try:
                super().mousePressEvent(event)
            finally:
                self._clicking = False
        else:
            super().mousePressEvent(event)

    def focusInEvent(self, event):
        if not self._clicking and not self._is_popup_open():
            self.clearFocus()
            self.setFocusPolicy(Qt.FocusPolicy.NoFocus)
            event.ignore()
            return
        super().focusInEvent(event)

    def focusOutEvent(self, event):
        super().focusOutEvent(event)
        if not self._is_popup_open():
            self.setFocusPolicy(Qt.FocusPolicy.NoFocus)

    def hidePopup(self):
        super().hidePopup()
        self.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.clearFocus()

    def wheelEvent(self, event):
        # Prevent wheel from accidentally altering rating while scrolling the table
        event.ignore()

class NoTextDelegate(QStyledItemDelegate):
    def paint(self, painter, option, index):
        painter.save()
        # H4 FIX: QStyledItemDelegate inherits QObject not QWidget;
        # use self.parent().window() instead of self.window()
        is_dark = True
        top_win = getattr(self.parent(), 'window', lambda: None)()
        if top_win and hasattr(top_win, 'current_theme'):
            is_dark = (top_win.current_theme == 'dark')

        
        # Draw background selection/hover only
        if option.state & QStyle.StateFlag.State_Selected:
            bg_color = QColor(99, 102, 241, 64) if is_dark else QColor(99, 102, 241, 45)
            painter.fillRect(option.rect, bg_color)
            # Nebula: cyan edge stripe marks the active row ONLY on column 0
            if index.column() == 0:
                stripe = QColor(Nebula.ACCENT2) if is_dark else QColor(Nebula.ACCENT2_L)
                painter.fillRect(option.rect.x(), option.rect.y(), 3, option.rect.height(), stripe)
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
            # Nebula: cyan edge stripe marks the active row ONLY on column 0
            if index.column() == 0:
                stripe = QColor(Nebula.ACCENT2) if is_dark else QColor(Nebula.ACCENT2_L)
                painter.fillRect(opt.rect.x(), opt.rect.y(), 3, opt.rect.height(), stripe)
        elif opt.state & QStyle.StateFlag.State_MouseOver:
            bg_color = QColor(255, 255, 255, 12) if is_dark else QColor(0, 0, 0, 10)
            painter.fillRect(opt.rect, bg_color)
            
        raw_text = opt.text
        if not raw_text or raw_text == "—":
            super().paint(painter, option, index)
            painter.restore()
            return
            
        text = raw_text.lstrip("✓⚠✕⚠️ ").strip()
        badge_bg = QColor(255, 255, 255, 15)
        badge_fg = QColor("#9ca3af") if is_dark else QColor("#4b5563")
        
        if "Valid" in raw_text:
            badge_bg = QColor(16, 185, 129, 30) if is_dark else QColor(16, 185, 129, 25)
            badge_fg = QColor("#34d399") if is_dark else QColor("#059669")
        elif "Unsupported" in raw_text or "Error" in raw_text:
            badge_bg = QColor(239, 68, 68, 30) if is_dark else QColor(239, 68, 68, 25)
            badge_fg = QColor("#f87171") if is_dark else QColor("#dc2626")
        elif "Renamed" in raw_text:
            badge_bg = QColor(99, 102, 241, 30) if is_dark else QColor(99, 102, 241, 25)
            badge_fg = QColor("#c4b5fd") if is_dark else QColor("#4338ca")
        elif "Dup" in raw_text:
            badge_bg = QColor(245, 158, 11, 30) if is_dark else QColor(245, 158, 11, 25)
            badge_fg = QColor("#facc15") if is_dark else QColor("#d97706")
            
        badge_height = 22
        y_offset = (opt.rect.height() - badge_height) // 2
        
        badge_font = QFont(BASE_FONT_FAMILY, 9, QFont.Weight.DemiBold)
        painter.setFont(badge_font)
        fm = painter.fontMetrics()
        text_w = fm.horizontalAdvance(text)
        badge_width = min(opt.rect.width() - 8, max(64, text_w + 24))
        x_offset = opt.rect.x() + (opt.rect.width() - badge_width) // 2
        badge_rect = QRect(x_offset, opt.rect.y() + y_offset, badge_width, badge_height)
        
        painter.setBrush(badge_bg)
        painter.setPen(Qt.PenStyle.NoPen)
        painter.drawRoundedRect(QRectF(badge_rect), 5, 5)

        # Nebula: 5px status dot
        painter.setPen(Qt.PenStyle.NoPen)
        painter.setBrush(badge_fg)
        painter.drawEllipse(QRectF(badge_rect.x() + 8, badge_rect.center().y() - 2.5, 5.0, 5.0))
        painter.setPen(badge_fg)
        text_rect = QRect(badge_rect.x() + 18, badge_rect.y(), badge_rect.width() - 20, badge_rect.height())
        painter.drawText(text_rect, Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter, text)
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
        def split_alphanumeric(t): return [(0, int(c)) if c.isdigit() else (1, c.lower()) for c in re.split(r'(\d+)', t) if c]
        return split_alphanumeric(self.text()) < split_alphanumeric(other.text())

# ─── Theme Manager ──────────────────────────────────────────────────────────────

DARK_STYLESHEET = """
QMainWindow { background: #07060F; }
QWidget { color: #ECECF4; font-family: 'Segoe UI', 'Inter', sans-serif; }
#sidebar { background: #0B0918; border-right: 1px solid #1E1A3A; min-width: 230px; max-width: 230px; }
#titleLabel { font-size: 20px; font-weight: 800; color: #ffffff; letter-spacing: 2px; margin-top: 10px; }
#subtitleLabel { font-size: 10px; font-weight: 600; color: #a78bfa; letter-spacing: 1.5px; text-transform: uppercase; margin-top: 2px; }
#smartSidebarTitle { font-size: 11px; font-weight: 700; color: #7c7c9a; letter-spacing: 1.5px; text-transform: uppercase; margin-left: 12px; }
#navButton { background: transparent; color: #9ca3af; text-align: left; padding: 12px 24px; font-size: 13px; font-weight: 600; letter-spacing: 0.5px; border-radius: 8px; margin: 4px 16px; border: 1px solid transparent; }
#navButton:hover { background: rgba(139, 92, 246, 0.08); color: #c4b5fd; border: 1px solid rgba(139, 92, 246, 0.15); }
#navButton[active="true"] { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #6D28D9, stop:1 #8B5CF6); color: #ffffff; border: 1px solid rgba(124, 58, 237, 0.3); border-left: 3px solid #22D3EE; font-weight: 700; }
#controlPanel { background: #121027; border: 1px solid #29234A; border-radius: 16px; padding: 14px 18px; }
#filterPanel { background: #0F0D20; border: 1px solid #29234A; border-radius: 12px; padding: 10px 16px; margin-bottom: 8px; }
#advancedFilterPanel { background: #0F0D20; border: 1px solid #29234A; border-radius: 12px; padding: 10px 16px; margin-bottom: 8px; }
#statsPanel { background: #121027; border: 1px solid #29234A; border-left: 4px solid #8B5CF6; border-radius: 8px; padding: 0px; }
#statValue { font-size: 18px; font-weight: 800; color: #ffffff; margin: 0; padding: 0; }
#statLabel { font-size: 9px; color: #a78bfa; text-transform: uppercase; letter-spacing: 1px; font-weight: bold; margin: 0; padding: 0; }
QPushButton { border: none; border-radius: 8px; padding: 8px 18px; font-size: 12px; font-weight: 600; letter-spacing: 0.4px; }
#btnSelectFolder { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #6366f1, stop:1 #8b5cf6); color: white; min-width: 180px; }
/* Compact padding for control-panel action buttons */
#btnLoadFiles, #btnStopLoading, #btnClearAll, #btnWatch, #btnViewMode, #btnTogglePreview, #btnToggleStats, #btnBatchEdit, #btnBatchTag, #btnFindDuplicates, #btnDelete, #btnProcessAll, #btnUndo, #btnRedo, #btnRelocate { padding-left: 12px; padding-right: 12px; }

#btnSelectFolder:hover { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #4f46e5, stop:1 #7c3aed); }
#btnSelectFolder:pressed { background: #4338ca; }
#btnSelectFolder:disabled { background: rgba(255, 255, 255, 0.05); color: rgba(255, 255, 255, 0.2); }
#btnProcessAll { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #10b981, stop:1 #06d6a0); color: white; min-width: 130px; font-size: 13px; font-weight: 700; padding: 10px 22px; }
#btnProcessAll:hover { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #059669, stop:1 #10b981); }
#btnProcessAll:pressed { background: #047857; }
#btnProcessAll:disabled { background: rgba(255, 255, 255, 0.05); color: rgba(255, 255, 255, 0.2); }
#btnClearAll, #btnDelete, #btnStopLoading { background: rgba(255, 255, 255, 0.03); color: #c4b5fd; border: 1px solid rgba(239, 68, 68, 0.25); min-width: 95px; }
#btnClearAll:hover, #btnDelete:hover, #btnStopLoading:hover { background: rgba(239, 68, 68, 0.2); color: #ffffff; border: 1px solid #ef4444; }
#btnClearAll:pressed, #btnDelete:pressed, #btnStopLoading:pressed { background: #b91c1c; color: #ffffff; }
#btnClearAll:disabled, #btnDelete:disabled, #btnStopLoading:disabled { background: transparent; color: rgba(255, 255, 255, 0.15); border: 1px solid rgba(255, 255, 255, 0.05); }
#btnWatch { background: rgba(255, 255, 255, 0.05); color: #c4b5fd; border: 1px solid rgba(167, 139, 250, 0.2); min-width: 90px; }
#btnWatch:checked { background: rgba(16, 185, 129, 0.2); color: #34d399; border: 1px solid rgba(16, 185, 129, 0.5); }
#btnLoadFiles, #btnBatchEdit, #btnBatchTag, #btnFindDuplicates, #btnRelocate, #btnUndo, #btnRedo { background: rgba(255, 255, 255, 0.045); color: #ECECF4; border: 1px solid rgba(139, 92, 246, 0.25); min-width: 100px; }
#btnLoadFiles:hover, #btnBatchEdit:hover, #btnBatchTag:hover, #btnFindDuplicates:hover, #btnRelocate:hover, #btnUndo:hover, #btnRedo:hover { background: rgba(139, 92, 246, 0.15); color: #ffffff; border: 1px solid #8b5cf6; }
#btnLoadFiles:pressed, #btnBatchEdit:pressed, #btnBatchTag:pressed, #btnFindDuplicates:pressed, #btnRelocate:pressed, #btnUndo:pressed, #btnRedo:pressed { background: rgba(139, 92, 246, 0.3); }
#btnLoadFiles:disabled, #btnBatchEdit:disabled, #btnBatchTag:disabled, #btnFindDuplicates:disabled, #btnRelocate:disabled, #btnUndo:disabled, #btnRedo:disabled { background: transparent; color: rgba(255, 255, 255, 0.15); border: 1px solid rgba(255, 255, 255, 0.05); }
#btnViewMode, #btnTogglePreview, #btnToggleStats { background: rgba(167, 139, 250, 0.12); color: #c4b5fd; border: 1px solid rgba(167, 139, 250, 0.25); min-width: 90px; padding: 6px 12px; font-size: 11px; border-radius: 6px; }
#btnViewMode:hover, #btnTogglePreview:hover, #btnToggleStats:hover { background: rgba(167, 139, 250, 0.22); color: #ffffff; }
#btnViewMode:pressed, #btnTogglePreview:pressed, #btnToggleStats:pressed { background: rgba(139, 92, 246, 0.35); }
#btnViewMode:checked, #btnTogglePreview:checked, #btnToggleStats:checked { background: rgba(99, 102, 241, 0.4); color: #ffffff; border: 1px solid rgba(99, 102, 241, 0.6); }
#btnViewMode:disabled, #btnTogglePreview:disabled, #btnToggleStats:disabled { background: transparent; color: rgba(255, 255, 255, 0.05); }
#previewPanel, #statsSidePanel { background: #121027; border: 1px solid #29234A; border-radius: 12px; }
#sidePanelStack { background: transparent; border: none; }
#sidebarDivider { background-color: #1E1A3A; height: 1px; max-height: 1px; margin: 8px 0; }
#sidebarToolHeader { font-size: 10px; font-weight: 700; color: #8E8AA8; letter-spacing: 1.2px; text-transform: uppercase; padding: 2px 4px 4px 4px; }
#sidebarToolButton { background: transparent; color: #9ca3af; text-align: left; padding: 5px 8px; font-size: 11px; font-weight: 500; border-radius: 6px; border: 1px solid transparent; min-height: 26px; }
#sidebarToolButton:hover { background: rgba(139, 92, 246, 0.12); color: #c4b5fd; border: 1px solid rgba(139, 92, 246, 0.25); }
#sidebarToolButton:pressed { background: rgba(139, 92, 246, 0.25); color: #ffffff; }
#inspectorActionButton, #inspectorActionsFrame QPushButton { background: transparent; color: #9ca3af; text-align: center; padding: 6px 10px; font-size: 11px; font-weight: 500; border-radius: 6px; border: 1px solid transparent; min-height: 28px; }
#inspectorActionButton:hover, #inspectorActionsFrame QPushButton:hover { background: rgba(139, 92, 246, 0.14); color: #c4b5fd; border: 1px solid rgba(139, 92, 246, 0.28); }
#inspectorActionButton:pressed, #inspectorActionsFrame QPushButton:pressed { background: rgba(139, 92, 246, 0.25); color: #ffffff; }
#vDivider { background-color: rgba(139, 92, 246, 0.25); width: 1px; max-width: 1px; margin: 4px 6px; }
.filter-chip { background: rgba(139, 92, 246, 0.15); color: #c4b5fd; border: 1px solid rgba(139, 92, 246, 0.35); border-radius: 12px; padding: 3px 10px; font-size: 11px; font-weight: 600; }
.filter-chip:hover { background: rgba(139, 92, 246, 0.28); color: #ffffff; border: 1px solid #8b5cf6; }
#filterResultCount { color: #a78bfa; font-size: 11px; font-weight: 600; padding: 0 4px; }
QTableWidget { background: rgba(16, 13, 34, 0.72); border: 1px solid rgba(139, 92, 246, 0.18); border-radius: 14px; gridline-color: rgba(139, 92, 246, 0.07); selection-background-color: rgba(99, 102, 241, 0.25); font-size: 12px; outline: none; }
QTableWidget::item { padding: 6px 10px; border-bottom: 1px solid rgba(139, 92, 246, 0.06); }
QTableWidget::item:selected { background: rgba(99, 102, 241, 0.18); }
QTableWidget::item:hover { background: rgba(34, 211, 238, 0.05); }
QHeaderView::section { background: #0F0D20; color: #8E8AA8; font-weight: 700; font-size: 11px; text-transform: uppercase; letter-spacing: 0.6px; padding: 10px 12px; border: none; border-bottom: 2px solid rgba(139, 92, 246, 0.35); border-right: 1px solid rgba(139, 92, 246, 0.08); }

QScrollBar:vertical { background: transparent; width: 8px; margin: 4px 2px; }
QScrollBar::handle:vertical { background: rgba(167, 139, 250, 0.35); border-radius: 4px; min-height: 30px; }
QScrollBar::handle:vertical:hover { background: rgba(167, 139, 250, 0.55); }
QScrollBar:horizontal { background: transparent; height: 8px; margin: 2px 4px; }
QScrollBar::handle:horizontal { background: rgba(167, 139, 250, 0.35); border-radius: 4px; min-width: 30px; }
QScrollBar::handle:horizontal:hover { background: rgba(167, 139, 250, 0.55); }
QLineEdit { background: rgba(34, 30, 68, 0.8); border: 1px solid rgba(139, 92, 246, 0.28); border-radius: 6px; padding: 4px 8px; color: #ECECF4; font-size: 12px; }
QLineEdit:focus { border: 1px solid #22D3EE; background: rgba(42, 37, 84, 0.9); }
EditableCellLineEdit { background: transparent; border: 1px solid transparent; border-radius: 6px; padding: 4px 8px; color: #ECECF4; font-size: 12px; }
EditableCellLineEdit:hover { background: rgba(255, 255, 255, 0.04); border: 1px dashed rgba(139, 92, 246, 0.35); }
EditableCellLineEdit:focus { background: rgba(42, 37, 84, 0.9); border: 1px solid #22D3EE; color: #ffffff; }
QComboBox { background: rgba(34, 30, 68, 0.8); border: 1px solid rgba(139, 92, 246, 0.28); border-radius: 6px; padding: 4px 8px; color: #ECECF4; font-size: 12px; min-width: 55px; }
#searchComboBox { background: rgba(34, 30, 68, 0.8); border: 1px solid rgba(139, 92, 246, 0.28); border-radius: 6px; }
#searchComboBox QLineEdit { background: transparent; border: none; padding: 4px 8px; color: #ECECF4; font-size: 12px; }
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
#settingsPanel { background: #121027; border: 1px solid #29234A; border-radius: 12px; }
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

/* ── Nebula additions (dark) ── */
QSpinBox:focus, QDoubleSpinBox:focus, QDateEdit:focus { border: 1px solid #22D3EE; }
QComboBox:focus { border: 1px solid #22D3EE; }
#emptyTitle { font-size: 24px; font-weight: 800; color: #ECECF4; letter-spacing: 0.5px; }
#emptySub { color: #8E8AA8; font-size: 13px; }
#emptySteps { color: #6E6A8C; font-size: 12px; }
"""

LIGHT_STYLESHEET = """
QMainWindow { background: #f8fafc; }
QWidget { color: #0f172a; font-family: 'Segoe UI', 'Inter', sans-serif; }
#sidebar { background: #ffffff; border-right: 1px solid #e2e8f0; min-width: 230px; max-width: 230px; }
#titleLabel { font-size: 20px; font-weight: 800; color: #0f172a; letter-spacing: 2px; margin-top: 10px; }
#subtitleLabel { font-size: 10px; font-weight: 700; color: #6366f1; letter-spacing: 1.5px; text-transform: uppercase; margin-top: 2px; }
#smartSidebarTitle { font-size: 11px; font-weight: 700; color: #64748b; letter-spacing: 1.5px; text-transform: uppercase; margin-left: 12px; }
#navButton { background: transparent; color: #475569; text-align: left; padding: 12px 24px; font-size: 13px; font-weight: 600; letter-spacing: 0.5px; border-radius: 8px; margin: 4px 16px; border: 1px solid transparent; }
#navButton:hover { background: #f1f5f9; color: #0f172a; border: 1px solid #cbd5e1; }
#navButton[active="true"] { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #EDE9FE, stop:1 #E0E7FF); color: #4338CA; border: 1px solid #C7D2FE; border-left: 3px solid #0891B2; font-weight: 700; }
#controlPanel { background: #ffffff; border: 1px solid #E5E9F0; border-radius: 16px; padding: 14px 18px; }
#filterPanel { background: #f8fafc; border: 1px solid #E5E9F0; border-radius: 12px; padding: 10px 16px; margin-bottom: 8px; }
#advancedFilterPanel { background: #f8fafc; border: 1px solid #E5E9F0; border-radius: 12px; padding: 10px 16px; margin-bottom: 8px; }
#statsPanel { background: #ffffff; border: 1px solid #E5E9F0; border-left: 4px solid #6366f1; border-radius: 8px; padding: 0px; }
#statValue { font-size: 18px; font-weight: 800; color: #0f172a; margin: 0; padding: 0; }
#statLabel { font-size: 9px; color: #6366f1; text-transform: uppercase; letter-spacing: 1px; font-weight: bold; margin: 0; padding: 0; }
QPushButton { border: none; border-radius: 8px; padding: 8px 18px; font-size: 12px; font-weight: 600; letter-spacing: 0.4px; }
#btnSelectFolder { background: #6366f1; color: white; min-width: 180px; }
/* Compact padding for control-panel action buttons */
#btnLoadFiles, #btnStopLoading, #btnClearAll, #btnWatch, #btnViewMode, #btnTogglePreview, #btnToggleStats, #btnBatchEdit, #btnBatchTag, #btnFindDuplicates, #btnDelete, #btnProcessAll, #btnUndo, #btnRedo, #btnRelocate { padding-left: 12px; padding-right: 12px; }

#btnSelectFolder:hover { background: #4f46e5; }
#btnSelectFolder:pressed { background: #3730a3; }
#btnSelectFolder:disabled { background: #cbd5e1; color: #94a3b8; }
#btnProcessAll { background: #10b981; color: white; min-width: 130px; font-size: 13px; font-weight: 700; padding: 10px 22px; }
#btnProcessAll:hover { background: #059669; }
#btnProcessAll:pressed { background: #047857; }
#btnProcessAll:disabled { background: #e2e8f0; color: #94a3b8; }
#btnClearAll, #btnDelete, #btnStopLoading { background: #ffffff; color: #64748b; border: 1px solid #fca5a5; min-width: 95px; }
#btnClearAll:hover, #btnDelete:hover, #btnStopLoading:hover { background: #fee2e2; color: #dc2626; border: 1px solid #ef4444; }
#btnClearAll:pressed, #btnDelete:pressed, #btnStopLoading:pressed { background: #ef4444; color: #ffffff; }
#btnClearAll:disabled, #btnDelete:disabled, #btnStopLoading:disabled { background: #f8fafc; color: #cbd5e1; border: 1px solid #e2e8f0; }
#btnWatch { background: #ffffff; color: #475569; border: 1px solid #cbd5e1; min-width: 90px; }
#btnWatch:checked { background: #ecfdf5; color: #059669; border: 1px solid #6ee7b7; }
#btnLoadFiles, #btnBatchEdit, #btnBatchTag, #btnFindDuplicates, #btnRelocate, #btnUndo, #btnRedo { background: #ffffff; color: #334155; border: 1px solid #cbd5e1; min-width: 100px; }
#btnLoadFiles:hover, #btnBatchEdit:hover, #btnBatchTag:hover, #btnFindDuplicates:hover, #btnRelocate:hover, #btnUndo:hover, #btnRedo:hover { background: #f1f5f9; color: #0f172a; border: 1px solid #6366f1; }
#btnLoadFiles:pressed, #btnBatchEdit:pressed, #btnBatchTag:pressed, #btnFindDuplicates:pressed, #btnRelocate:pressed, #btnUndo:pressed, #btnRedo:pressed { background: #e2e8f0; }
#btnLoadFiles:disabled, #btnBatchEdit:disabled, #btnBatchTag:disabled, #btnFindDuplicates:disabled, #btnRelocate:disabled, #btnUndo:disabled, #btnRedo:disabled { background: #f8fafc; color: #94a3b8; border: 1px solid #e2e8f0; }
#btnViewMode, #btnTogglePreview, #btnToggleStats { background: #f1f5f9; color: #475569; border: 1px solid #cbd5e1; min-width: 90px; padding: 6px 12px; font-size: 11px; border-radius: 6px; }
#btnViewMode:hover, #btnTogglePreview:hover, #btnToggleStats:hover { background: #e2e8f0; color: #0f172a; }
#btnViewMode:pressed, #btnTogglePreview:pressed, #btnToggleStats:pressed { background: #cbd5e1; }
#btnViewMode:checked, #btnTogglePreview:checked, #btnToggleStats:checked { background: #e0e7ff; color: #4338ca; border: 1px solid #c7d2fe; }
#previewPanel, #statsSidePanel { background: #ffffff; border: 1px solid #e2e8f0; border-radius: 12px; }
#sidePanelStack { background: transparent; border: none; }
#sidebarDivider { background-color: #e2e8f0; height: 1px; max-height: 1px; margin: 8px 0; }
#sidebarToolHeader { font-size: 10px; font-weight: 700; color: #64748b; letter-spacing: 1.2px; text-transform: uppercase; padding: 2px 4px 4px 4px; }
#sidebarToolButton { background: transparent; color: #475569; text-align: left; padding: 5px 8px; font-size: 11px; font-weight: 500; border-radius: 6px; border: 1px solid transparent; min-height: 26px; }
#sidebarToolButton:hover { background: #f1f5f9; color: #0f172a; border: 1px solid #cbd5e1; }
#sidebarToolButton:pressed { background: #e2e8f0; color: #0f172a; }
#inspectorActionButton, #inspectorActionsFrame QPushButton { background: transparent; color: #475569; text-align: center; padding: 6px 10px; font-size: 11px; font-weight: 500; border-radius: 6px; border: 1px solid transparent; min-height: 28px; }
#inspectorActionButton:hover, #inspectorActionsFrame QPushButton:hover { background: #f1f5f9; color: #0f172a; border: 1px solid #cbd5e1; }
#inspectorActionButton:pressed, #inspectorActionsFrame QPushButton:pressed { background: #e2e8f0; color: #0f172a; }
#vDivider { background-color: #cbd5e1; width: 1px; max-width: 1px; margin: 4px 6px; }
.filter-chip { background: #e0e7ff; color: #4338ca; border: 1px solid #c7d2fe; border-radius: 12px; padding: 3px 10px; font-size: 11px; font-weight: 600; }
.filter-chip:hover { background: #c7d2fe; color: #3730a3; border: 1px solid #818cf8; }
#filterResultCount { color: #4338ca; font-size: 11px; font-weight: 600; padding: 0 4px; }
QTableWidget { background: #ffffff; border: 1px solid #e2e8f0; border-radius: 14px; gridline-color: #f1f5f9; selection-background-color: #e0e7ff; font-size: 12px; outline: none; }
QTableWidget::item { padding: 6px 10px; border-bottom: 1px solid #f1f5f9; }
QTableWidget::item:selected { background: #e0e7ff; color: #0f172a; }
QHeaderView::section { background: #f8fafc; color: #475569; font-weight: 700; font-size: 11px; text-transform: uppercase; letter-spacing: 0.6px; padding: 10px 12px; border: none; border-bottom: 2px solid #cbd5e1; border-right: 1px solid #e2e8f0; }

QScrollBar:vertical { background: transparent; width: 8px; margin: 4px 2px; }
QScrollBar::handle:vertical { background: #cbd5e1; border-radius: 4px; min-height: 30px; }
QScrollBar::handle:vertical:hover { background: #94a3b8; }
QScrollBar:horizontal { background: transparent; height: 8px; margin: 2px 4px; }
QScrollBar::handle:horizontal { background: #cbd5e1; border-radius: 4px; min-width: 30px; }
QScrollBar::handle:horizontal:hover { background: #94a3b8; }
QLineEdit { background: #ffffff; border: 1px solid #cbd5e1; border-radius: 6px; padding: 4px 8px; color: #0f172a; font-size: 12px; }
QLineEdit:focus { border: 1px solid #6366f1; }
EditableCellLineEdit { background: transparent; border: 1px solid transparent; border-radius: 6px; padding: 4px 8px; color: #0f172a; font-size: 12px; }
EditableCellLineEdit:hover { background: rgba(0, 0, 0, 0.03); border: 1px dashed rgba(99, 102, 241, 0.35); }
EditableCellLineEdit:focus { background: #ffffff; border: 1px solid #6366f1; color: #0f172a; }
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
#settingsPanel { background: #ffffff; border: 1px solid #e2e8f0; border-radius: 12px; }
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

/* ── Nebula additions (light) ── */
QTableWidget::item:hover { background: rgba(2, 132, 199, 0.05); }
QLineEdit:focus, QComboBox:focus, QSpinBox:focus, QDoubleSpinBox:focus, QDateEdit:focus { border: 1px solid #0891B2; }
#emptyTitle { font-size: 24px; font-weight: 800; color: #0F172A; letter-spacing: 0.5px; }
#emptySub { color: #64748B; font-size: 13px; }
#emptySteps { color: #94A3B8; font-size: 12px; }
"""

# Nebula: honor the cross-platform base font instead of hardcoding Segoe UI
# (macOS/Linux fell back arbitrarily; this routes both themes through
# BASE_FONT_FAMILY resolved at startup).
_NEBULA_FAM = f"'{BASE_FONT_FAMILY}', 'Inter', sans-serif"
DARK_STYLESHEET = DARK_STYLESHEET.replace("'Segoe UI', 'Inter', sans-serif", _NEBULA_FAM)
LIGHT_STYLESHEET = LIGHT_STYLESHEET.replace("'Segoe UI', 'Inter', sans-serif", _NEBULA_FAM)

def _remap_css(css: str, mapping: dict) -> str:
    # Single-pass, case-insensitive token replacement. Keys are sorted longest-
    # first so each token in the CSS is matched and replaced exactly once —
    # sequential iteration would allow text introduced by an earlier replacement
    # to match a later key (cascade corruption).
    if not mapping:
        return css
    lookup = {k.lower(): v for k, v in mapping.items()}
    pattern = re.compile(
        "|".join(re.escape(k) for k in sorted(mapping, key=len, reverse=True)),
        re.IGNORECASE
    )
    return pattern.sub(lambda m: lookup[m.group(0).lower()], css)

# ─── Color Accent Mapping Dictionaries ──────────────────────────────────────

# Dark mode accent maps (remap DARK_STYLESHEET base violet & cyan tokens)
_DARK_DEEP_SPACE_MAP = {
    '#8b5cf6': '#22d3ee', '#a78bfa': '#67e8f9', '#c4b5fd': '#a5f3fc',
    '#6366f1': '#0891b2', '#6d28d9': '#0e7490', '#4f46e5': '#0e7490',
    '#7c3aed': '#06b6d4', '#4338ca': '#155e75', '#3730a3': '#164e63',
    '#07060f': '#020617', '#0b0918': '#050b1a', '#1e1a3a': '#13233f',
    '#1e1b4b': '#0b1b33', '#0f0d20': '#050d1c', '#6e6a8c': '#5c6f8c',
    '139, 92, 246': '34, 211, 238', '167, 139, 250': '103, 232, 249',
    '99, 102, 241': '8, 145, 178', '124, 58, 237': '6, 182, 212',
    '21, 18, 43': '8, 20, 40', '16, 13, 34': '6, 14, 30',
    '34, 30, 68': '12, 26, 48', '42, 37, 84': '16, 34, 60',
    '30, 27, 75': '8, 18, 36', '15, 12, 41': '5, 12, 26',
    '45, 40, 90': '12, 24, 46',
}

_DARK_ORANGE_MAP = {
    '#8b5cf6': '#f59e0b', '#a78bfa': '#fbbf24', '#c4b5fd': '#fde68a',
    '#6366f1': '#d97706', '#6d28d9': '#b45309', '#4f46e5': '#b45309',
    '#7c3aed': '#d97706', '#4338ca': '#92400e', '#3730a3': '#78350f',
    '#22d3ee': '#fb923c',
    '139, 92, 246': '245, 158, 11', '167, 139, 250': '251, 191, 36',
    '99, 102, 241': '217, 119, 6', '124, 58, 237': '217, 119, 6',
    '34, 211, 238': '251, 146, 60',
}

_DARK_RED_MAP = {
    '#8b5cf6': '#ef4444', '#a78bfa': '#f87171', '#c4b5fd': '#fecaca',
    '#6366f1': '#dc2626', '#6d28d9': '#b91c1c', '#4f46e5': '#b91c1c',
    '#7c3aed': '#dc2626', '#4338ca': '#991b1b', '#3730a3': '#7f1d1d',
    '#22d3ee': '#f43f5e',
    '139, 92, 246': '239, 68, 68', '167, 139, 250': '248, 113, 113',
    '99, 102, 241': '220, 38, 38', '124, 58, 237': '220, 38, 38',
    '34, 211, 238': '244, 63, 94',
}

_DARK_BLUE_MAP = {
    '#8b5cf6': '#3b82f6', '#a78bfa': '#60a5fa', '#c4b5fd': '#bfdbfe',
    '#6366f1': '#2563eb', '#6d28d9': '#1d4ed8', '#4f46e5': '#1d4ed8',
    '#7c3aed': '#2563eb', '#4338ca': '#1e40af', '#3730a3': '#1e3a8a',
    '#22d3ee': '#38bdf8',
    '139, 92, 246': '59, 130, 246', '167, 139, 250': '96, 165, 250',
    '99, 102, 241': '37, 99, 235', '124, 58, 237': '37, 99, 235',
    '34, 211, 238': '56, 189, 248',
}

_DARK_EMERALD_MAP = {
    '#8b5cf6': '#10b981', '#a78bfa': '#34d399', '#c4b5fd': '#a7f3d0',
    '#6366f1': '#059669', '#6d28d9': '#047857', '#4f46e5': '#047857',
    '#7c3aed': '#059669', '#4338ca': '#065f46', '#3730a3': '#064e3b',
    '#22d3ee': '#2dd4bf', '#6e6a8c': '#6b8a7c',
    '#07060f': '#03110d', '#0b0918': '#061511', '#1e1a3a': '#14332a',
    '#1e1b4b': '#0c2119', '#0f0d20': '#06130e',
    '139, 92, 246': '16, 185, 129', '167, 139, 250': '52, 211, 153',
    '99, 102, 241': '5, 150, 105', '124, 58, 237': '5, 150, 105',
    '34, 211, 238': '45, 212, 191',
    '21, 18, 43': '6, 24, 20', '16, 13, 34': '5, 18, 15',
    '34, 30, 68': '10, 30, 25', '42, 37, 84': '12, 36, 30',
    '30, 27, 75': '6, 22, 18', '15, 12, 41': '4, 15, 12',
    '45, 40, 90': '10, 28, 23',
}

# Light mode accent maps (remap LIGHT_STYLESHEET base indigo tokens)
_LIGHT_DEEP_SPACE_MAP = {
    '#6366f1': '#0891b2', '#4f46e5': '#0e7490', '#4338ca': '#155e75', '#3730a3': '#164e63',
    '#7e22ce': '#0e7490', '#6b21a8': '#155e75', '#0891b2': '#0891b2',
    '#ede9fe': '#e0f2fe', '#e0e7ff': '#ccfbf1', '#c7d2fe': '#a5f3fc',
    '#e9d5ff': '#a5f3fc', '#f3e8ff': '#e0f2fe', '#d8b4fe': '#67e8f9',
    '99, 102, 241': '8, 145, 178', '2, 132, 199': '8, 145, 178',
}

_LIGHT_ORANGE_MAP = {
    '#6366f1': '#d97706', '#4f46e5': '#b45309', '#4338ca': '#92400e', '#3730a3': '#78350f',
    '#7e22ce': '#b45309', '#6b21a8': '#92400e', '#0891b2': '#ea580c',
    '#ede9fe': '#fef3c7', '#e0e7ff': '#ffedd5', '#c7d2fe': '#fed7aa',
    '#e9d5ff': '#fed7aa', '#f3e8ff': '#fef3c7', '#d8b4fe': '#fcd34d',
    '99, 102, 241': '217, 119, 6', '2, 132, 199': '234, 88, 12',
}

_LIGHT_RED_MAP = {
    '#6366f1': '#dc2626', '#4f46e5': '#b91c1c', '#4338ca': '#991b1b', '#3730a3': '#7f1d1d',
    '#7e22ce': '#b91c1c', '#6b21a8': '#991b1b', '#0891b2': '#e11d48',
    '#ede9fe': '#ffe4e6', '#e0e7ff': '#fee2e2', '#c7d2fe': '#fecaca',
    '#e9d5ff': '#fecaca', '#f3e8ff': '#ffe4e6', '#d8b4fe': '#fda4af',
    '99, 102, 241': '220, 38, 38', '2, 132, 199': '225, 29, 72',
}

_LIGHT_BLUE_MAP = {
    '#6366f1': '#2563eb', '#4f46e5': '#1d4ed8', '#4338ca': '#1e40af', '#3730a3': '#1e3a8a',
    '#7e22ce': '#1d4ed8', '#6b21a8': '#1e40af', '#0891b2': '#0284c7',
    '#ede9fe': '#e0f2fe', '#e0e7ff': '#dbeafe', '#c7d2fe': '#bfdbfe',
    '#e9d5ff': '#bfdbfe', '#f3e8ff': '#e0f2fe', '#d8b4fe': '#93c5fd',
    '99, 102, 241': '37, 99, 235', '2, 132, 199': '2, 132, 199',
}

_LIGHT_EMERALD_MAP = {
    '#6366f1': '#059669', '#4f46e5': '#047857', '#4338ca': '#065f46', '#3730a3': '#064e3b',
    '#7e22ce': '#047857', '#6b21a8': '#065f46', '#0891b2': '#0d9488',
    '#ede9fe': '#ecfdf5', '#e0e7ff': '#d1fae5', '#c7d2fe': '#a7f3d0',
    '#e9d5ff': '#a7f3d0', '#f3e8ff': '#ecfdf5', '#d8b4fe': '#6ee7b7',
    '99, 102, 241': '5, 150, 105', '2, 132, 199': '13, 148, 136',
}

def _theme_palette(spec: dict) -> QPalette:
    """Build a QPalette from a role-name → hex dict."""
    roles = {
        'window': QPalette.ColorRole.Window, 'window_text': QPalette.ColorRole.WindowText,
        'base': QPalette.ColorRole.Base, 'alt': QPalette.ColorRole.AlternateBase,
        'tip_base': QPalette.ColorRole.ToolTipBase, 'tip_text': QPalette.ColorRole.ToolTipText,
        'text': QPalette.ColorRole.Text, 'button': QPalette.ColorRole.Button,
        'button_text': QPalette.ColorRole.ButtonText, 'bright': QPalette.ColorRole.BrightText,
        'highlight': QPalette.ColorRole.Highlight, 'highlight_text': QPalette.ColorRole.HighlightedText,
        'link': QPalette.ColorRole.Link,
    }
    pal = QPalette()
    for key, role in roles.items():
        if key in spec:
            pal.setColor(role, QColor(spec[key]))
    return pal

THEME_BASES = {
    'dark': {
        'dark': True,
        'css': DARK_STYLESHEET,
        'palette': {
            'window': '#07060F', 'window_text': '#ECECF4', 'base': '#07060F',
            'alt': '#15122B', 'tip_base': '#15122B', 'tip_text': '#ECECF4',
            'text': '#ECECF4', 'button': '#15122B', 'button_text': '#ECECF4',
            'bright': '#a78bfa', 'highlight': '#6366f1',
            'highlight_text': '#ffffff', 'link': '#22D3EE'
        }
    },
    'light': {
        'dark': False,
        'css': LIGHT_STYLESHEET,
        'palette': {
            'window': '#f8fafc', 'window_text': '#0f172a', 'base': '#ffffff',
            'alt': '#f1f5f9', 'tip_base': '#ffffff', 'tip_text': '#0f172a',
            'text': '#0f172a', 'button': '#ffffff', 'button_text': '#0f172a',
            'bright': '#dc2626', 'highlight': '#6366f1',
            'highlight_text': '#ffffff', 'link': '#2563eb'
        }
    }
}

ACCENTS = {
    "Deep Space": {
        'dark': {
            'accent': '#22D3EE', 'accent2': '#818CF8',
            'icon_dark': '#67e8f9', 'icon_light': '#0891b2',
            'remap': _DARK_DEEP_SPACE_MAP,
            'palette_highlight': '#0891B2', 'palette_bright': '#67E8F9',
        },
        'light': {
            'accent': '#0891B2', 'accent2': '#0284C7',
            'icon_dark': '#67e8f9', 'icon_light': '#0891b2',
            'remap': _LIGHT_DEEP_SPACE_MAP,
            'palette_highlight': '#0891B2', 'palette_bright': '#0891B2',
        }
    },
    "Orange": {
        'dark': {
            'accent': '#F59E0B', 'accent2': '#FB923C',
            'icon_dark': '#FBBF24', 'icon_light': '#D97706',
            'remap': _DARK_ORANGE_MAP,
            'palette_highlight': '#D97706', 'palette_bright': '#FBBF24',
        },
        'light': {
            'accent': '#D97706', 'accent2': '#EA580C',
            'icon_dark': '#FBBF24', 'icon_light': '#D97706',
            'remap': _LIGHT_ORANGE_MAP,
            'palette_highlight': '#D97706', 'palette_bright': '#D97706',
        }
    },
    "Red": {
        'dark': {
            'accent': '#EF4444', 'accent2': '#F43F5E',
            'icon_dark': '#F87171', 'icon_light': '#DC2626',
            'remap': _DARK_RED_MAP,
            'palette_highlight': '#DC2626', 'palette_bright': '#F87171',
        },
        'light': {
            'accent': '#DC2626', 'accent2': '#E11D48',
            'icon_dark': '#F87171', 'icon_light': '#DC2626',
            'remap': _LIGHT_RED_MAP,
            'palette_highlight': '#DC2626', 'palette_bright': '#DC2626',
        }
    },
    "Blue": {
        'dark': {
            'accent': '#3B82F6', 'accent2': '#38BDF8',
            'icon_dark': '#60A5FA', 'icon_light': '#2563EB',
            'remap': _DARK_BLUE_MAP,
            'palette_highlight': '#2563EB', 'palette_bright': '#60A5FA',
        },
        'light': {
            'accent': '#2563EB', 'accent2': '#0284C7',
            'icon_dark': '#60A5FA', 'icon_light': '#2563EB',
            'remap': _LIGHT_BLUE_MAP,
            'palette_highlight': '#2563EB', 'palette_bright': '#2563EB',
        }
    },
    "Violet": {
        'dark': {
            'accent': Nebula.ACCENT, 'accent2': Nebula.ACCENT2,
            'icon_dark': '#a78bfa', 'icon_light': '#6366f1',
            'remap': {},
            'palette_highlight': '#6366f1', 'palette_bright': '#a78bfa',
        },
        'light': {
            'accent': Nebula.ACCENT_L, 'accent2': Nebula.ACCENT2_L,
            'icon_dark': '#a78bfa', 'icon_light': '#6366f1',
            'remap': {},
            'palette_highlight': '#6366f1', 'palette_bright': '#6366f1',
        }
    },
    "Emerald": {
        'dark': {
            'accent': '#10B981', 'accent2': '#2DD4BF',
            'icon_dark': '#34D399', 'icon_light': '#059669',
            'remap': _DARK_EMERALD_MAP,
            'palette_highlight': '#059669', 'palette_bright': '#34D399',
        },
        'light': {
            'accent': '#059669', 'accent2': '#0D9488',
            'icon_dark': '#34D399', 'icon_light': '#059669',
            'remap': _LIGHT_EMERALD_MAP,
            'palette_highlight': '#059669', 'palette_bright': '#059669',
        }
    },
}

# Legacy alias dictionary for backwards compatibility
THEMES = {
    "Dark Mode": {'dark': True, 'accent': ACCENTS['Deep Space']['dark']['accent'], 'accent2': ACCENTS['Deep Space']['dark']['accent2']},
    "Light Mode": {'dark': False, 'accent': ACCENTS['Deep Space']['light']['accent'], 'accent2': ACCENTS['Deep Space']['light']['accent2']},
    "Deep Space": {'dark': True, 'accent': ACCENTS['Deep Space']['dark']['accent'], 'accent2': ACCENTS['Deep Space']['dark']['accent2']},
    "Aurora": {'dark': True, 'accent': ACCENTS['Emerald']['dark']['accent'], 'accent2': ACCENTS['Emerald']['dark']['accent2']},
    "Glass Morph": {'dark': False, 'accent': ACCENTS['Deep Space']['light']['accent'], 'accent2': ACCENTS['Deep Space']['light']['accent2']},
}

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
    def apply_theme(window, theme_choice="System (Auto)", accent_choice=None, ui_scale=None):
        app = QApplication.instance()
        
        # 1. Resolve mode
        if theme_choice == "System (Auto)":
            family = ThemeManager.get_system_theme()
            mode_name = "System (Auto)"
        elif str(theme_choice).lower() in ("light", "light mode"):
            family = "light"
            mode_name = "Light"
        elif str(theme_choice).lower() in ("dark", "dark mode"):
            family = "dark"
            mode_name = "Dark"
        elif theme_choice == "Deep Space" or theme_choice == "Aurora":
            family = "dark"
            mode_name = "Dark"
            if accent_choice is None:
                accent_choice = "Deep Space" if theme_choice == "Deep Space" else "Emerald"
        elif theme_choice == "Glass Morph":
            family = "light"
            mode_name = "Light"
            if accent_choice is None:
                accent_choice = "Deep Space"
        else:
            family = ThemeManager.get_system_theme()
            mode_name = "System (Auto)"

        # 2. Resolve accent
        if accent_choice is None:
            accent_choice = getattr(window, 'current_accent', 'Deep Space')
        if accent_choice not in ACCENTS:
            accent_choice = 'Deep Space'

        base = THEME_BASES[family]
        accent_data = ACCENTS[accent_choice][family]
        is_dark = base['dark']

        window.current_theme = 'dark' if is_dark else 'light'
        window.current_theme_mode = mode_name
        window.current_accent = accent_choice
        window.current_theme_name = f"{'Dark' if is_dark else 'Light'} ({accent_choice})"
        window.theme_accent = accent_data['accent']
        window.theme_accent2 = accent_data['accent2']

        # 3. Generate stylesheet
        css = base['css']
        if accent_data.get('remap'):
            css = _remap_css(css, accent_data['remap'])

        scale = ui_scale if ui_scale is not None else float(getattr(window, 'ui_scale', 1.0) or 1.0)
        app.setStyleSheet(scale_stylesheet(css, scale))

        # 4. Set Palette
        pal_spec = dict(base['palette'])
        pal_spec['highlight'] = accent_data['palette_highlight']
        pal_spec['bright'] = accent_data['palette_bright']
        app.setPalette(_theme_palette(pal_spec))

        # 5. Set vector icon color override
        set_icon_accent(accent_data['icon_dark'] if is_dark else accent_data['icon_light'])

        # 6. Regenerate Vector Icons dynamically
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
            window.btn_global_mute.setIcon(get_vector_icon('mute' if getattr(window, 'global_mute', False) else 'unmute', is_dark))
        if hasattr(window, 'btn_settings') and window.btn_settings:
            window.btn_settings.setIcon(get_vector_icon('settings', is_dark))
        if hasattr(window, '_refresh_tools_bar_icons'):
            window._refresh_tools_bar_icons(is_dark)
            
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
                tab.btn_find_dupes.setIcon(get_vector_icon('duplicate', is_dark))
            if hasattr(tab, 'btn_batch_edit') and tab.btn_batch_edit:
                tab.btn_batch_edit.setIcon(get_vector_icon('edit', is_dark))
            if hasattr(tab, 'btn_batch_tag') and tab.btn_batch_tag:
                tab.btn_batch_tag.setIcon(get_vector_icon('tag', is_dark))
            if hasattr(tab, 'btn_relocate') and tab.btn_relocate:
                tab.btn_relocate.setIcon(get_vector_icon('relocate', is_dark))
            if hasattr(tab, 'btn_delete') and tab.btn_delete:
                tab.btn_delete.setIcon(get_vector_icon('delete', is_dark))
            if hasattr(tab, 'btn_process') and tab.btn_process:
                tab.btn_process.setIcon(get_vector_icon('process', is_dark))
            if hasattr(tab, 'btn_watch') and tab.btn_watch:
                tab.btn_watch.setIcon(get_vector_icon('watch', is_dark))
            if hasattr(tab, 'btn_toggle_stats') and tab.btn_toggle_stats:
                tab.btn_toggle_stats.setIcon(get_vector_icon('stats', is_dark))
            if hasattr(tab, 'btn_advanced_filter') and tab.btn_advanced_filter:
                tab.btn_advanced_filter.setIcon(get_vector_icon('filter', is_dark))
            if hasattr(tab, 'btn_save_search') and tab.btn_save_search:
                tab.btn_save_search.setIcon(get_vector_icon('plus', is_dark))
            if hasattr(tab, 'btn_play') and tab.btn_play:
                tab.btn_play.setIcon(get_vector_icon('pause' if tab.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState else 'play', is_dark))
            if hasattr(tab, 'btn_mute') and tab.btn_mute:
                tab.btn_mute.setIcon(get_vector_icon('mute' if tab.audio_output.isMuted() else 'unmute', is_dark))
            if hasattr(tab, 'btn_close_preview') and tab.btn_close_preview:
                tab.btn_close_preview.setIcon(get_vector_icon('close', is_dark))
            if hasattr(tab, 'btn_close_stats') and tab.btn_close_stats:
                tab.btn_close_stats.setIcon(get_vector_icon('close', is_dark))
            if hasattr(tab, 'insp_btn_info') and tab.insp_btn_info:
                tab.insp_btn_info.setIcon(get_vector_icon('info', is_dark))
            if hasattr(tab, 'insp_btn_folder') and tab.insp_btn_folder:
                tab.insp_btn_folder.setIcon(get_vector_icon('folder', is_dark))
            if hasattr(tab, 'insp_btn_trim') and tab.insp_btn_trim:
                tab.insp_btn_trim.setIcon(get_vector_icon('scissors', is_dark))
            if hasattr(tab, 'insp_btn_play') and tab.insp_btn_play:
                tab.insp_btn_play.setIcon(get_vector_icon('play', is_dark))
            if hasattr(tab, '_update_theme_styling'):
                tab._update_theme_styling(is_dark)

                
        if hasattr(window, 'btn_close_settings') and window.btn_close_settings:
            window.btn_close_settings.setIcon(get_vector_icon('close', is_dark))
        if hasattr(window, '_update_settings_shadow_color'):
            window._update_settings_shadow_color()
            
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
        
        ThemeManager._update_inline_styles(window, is_dark, accent_data)
        if hasattr(window, 'hover_overlay') and window.hover_overlay:
            window.hover_overlay.update_theme()
        
        window.ensurePolished()

    @staticmethod
    def _update_inline_styles(window, is_dark, accent_data=None):
        base_grid = """
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
        
        base_menu = """
            QMenu { background-color: #1e1b4b; color: #e0e0e0; border: 1px solid rgba(99, 102, 241, 0.4); border-radius: 8px; padding: 4px; }
            QMenu::item { padding: 6px 20px; border-radius: 4px; }
            QMenu::item:selected { background-color: rgba(99, 102, 241, 0.4); color: #ffffff; }
        """ if is_dark else """
            QMenu { background-color: #ffffff; color: #0f172a; border: 1px solid #e2e8f0; border-radius: 8px; padding: 4px; }
            QMenu::item { padding: 6px 20px; border-radius: 4px; }
            QMenu::item:selected { background-color: #e0e7ff; color: #0f172a; }
        """

        remap = accent_data.get('remap', {}) if accent_data else {}
        grid_style = _remap_css(base_grid, remap) if remap else base_grid
        menu_style = _remap_css(base_menu, remap) if remap else base_menu

        tabs = [getattr(window, t, None) for t in ('video_tab', 'image_tab', 'audio_tab', 'pdf_tab')]
        tabs = [t for t in tabs if t is not None] + list(getattr(window, 'smart_folder_tabs', {}).values())
        for tab in tabs:
            if hasattr(tab, 'grid_view'): tab.grid_view.setStyleSheet(grid_style)
            if hasattr(tab, 'dupe_menu'): tab.dupe_menu.setStyleSheet(menu_style)
            if hasattr(tab, 'header_menu'): tab.header_menu.setStyleSheet(menu_style)
            if hasattr(tab, 'empty_state') and tab.empty_state:
                tab.empty_state.update_theme(is_dark)
            if hasattr(tab, 'btn_process') and tab.btn_process:
                apply_glow(tab.btn_process, getattr(window, 'theme_accent', None) or Nebula.ACCENT, 20, 100)
            if hasattr(tab, 'btn_watch') and tab.btn_watch:
                if getattr(tab, '_watch_enabled', False):
                    apply_glow(tab.btn_watch, getattr(window, 'theme_accent2', None) or Nebula.ACCENT2, 16, 140)
                else:
                    apply_glow(tab.btn_watch, None)
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
            elif self.extension in IMAGE_EXTENSIONS: self.media_type = 'image'
            else:
                self.media_type = 'unknown'
                self.is_valid = False
                self.error_message = "Unsupported media format"
        if cached_data:
            self.width = cached_data.get('width', 0) or 0
            self.height = cached_data.get('height', 0) or 0
            self.duration_seconds = cached_data.get('duration_seconds', 0.0) or 0.0
            self.duration_formatted = cached_data.get('duration_formatted', "") or ""
            self.resolution_tag = cached_data.get('resolution_tag', "") or ""
            self.duration_compact = cached_data.get('duration_compact', "") or ""
            self.is_valid = cached_data.get('is_valid', False)
            self.error_message = cached_data.get('error_message', "") or ""
            self.size_bytes = cached_data.get('size_bytes', 0) or 0
            self.size_formatted = cached_data.get('size_formatted', "—") or "—"
            self.tags = cached_data.get('tags', []) or []
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
            if self.media_type == 'unknown':
                self.error_message = "Unsupported media format"
                return
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
            except Exception as e:
                logger.debug("stat failed for %s: %s", filepath, e)
            self._extract_metadata()

    def _extract_metadata(self):
        try:
            if self.media_type == 'video':
                cap = None
                video_ok = False
                try:
                    with _CV_LOCK:
                        cap = cv2.VideoCapture(self.filepath)
                        if cap.isOpened():
                            self.width = int(cap.get(cv2.CAP_PROP_FRAME_WIDTH))
                            self.height = int(cap.get(cv2.CAP_PROP_FRAME_HEIGHT))
                            fps = cap.get(cv2.CAP_PROP_FPS)
                            frame_count = cap.get(cv2.CAP_PROP_FRAME_COUNT)
                            if fps > 0 and frame_count > 0:
                                self.duration_seconds = frame_count / fps
                                video_ok = True
                            elif self.width > 0 and self.height > 0:
                                video_ok = True
                finally:
                    if cap is not None:
                        try:
                            with _CV_LOCK:
                                cap.release()
                        except Exception:
                            try:
                                cap.release()
                            except Exception:
                                pass
                # ffprobe fills gaps OpenCV can't: missing duration (VFR webm/mkv/ts
                # report fps=0 or frame_count=0 despite valid dimensions) or dims.
                if not video_ok or self.duration_seconds <= 0:
                    try:
                        deep = get_file_deep_metadata(self.filepath)
                        if deep:
                            if deep.get('duration_seconds', 0) > 0 and self.duration_seconds <= 0:
                                self.duration_seconds = deep['duration_seconds']
                            if deep.get('video'):
                                if self.width <= 0:
                                    self.width = deep['video'].get('width', 0)
                                if self.height <= 0:
                                    self.height = deep['video'].get('height', 0)
                            if self.width > 0 and self.height > 0:
                                video_ok = True
                    except Exception as e:
                        logger.debug("ffprobe video fallback failed for %s: %s", self.filepath, e)
                if not video_ok and not (self.width > 0 and self.height > 0):
                    self.error_message = "Cannot open video file"
                    return
                if self.duration_seconds > 0:
                    self.duration_compact = format_duration_compact(self.duration_seconds)
                    total_sec = int(round(self.duration_seconds))
                    h = total_sec // 3600; m = (total_sec % 3600) // 60; s = total_sec % 60
                    if h > 0: self.duration_formatted = f"{h}h {m:02d}m {s:02d}s"
                    else: self.duration_formatted = f"{m}m {s:02d}s"
                else:
                    self.duration_compact = ""
                    self.duration_formatted = "—"
            elif self.media_type == 'audio':
                self.width = 0; self.height = 0; self.resolution_tag = ""
                duration_ok = False
                # NOTE: no cv2.VideoCapture attempt here — OpenCV's FFmpeg backend
                # cannot demux audio-only files, so this open always failed and
                # merely burned a lock-acquire + open per audio file across all
                # scan workers. The wave/ffprobe/mutagen fallbacks below cover it.
                if not duration_ok and self.extension == '.wav':
                    try:
                        import wave
                        with wave.open(self.filepath, 'rb') as f:
                            frames = f.getnframes(); rate = f.getframerate()
                            if rate > 0 and frames > 0: self.duration_seconds = frames / float(rate); duration_ok = True
                    except Exception as e:
                        logger.debug("wave fallback failed for %s: %s", self.filepath, e)
                # Try ffprobe for audio duration (more accurate than file-size heuristics)
                if not duration_ok:
                    try:
                        deep = get_file_deep_metadata(self.filepath)
                        if deep and deep.get('duration_seconds', 0) > 0:
                            self.duration_seconds = deep['duration_seconds']; duration_ok = True
                    except Exception as e:
                        logger.debug("ffprobe audio duration fallback failed for %s: %s", self.filepath, e)
                # Try mutagen for MP3/FLAC/OGG/M4A as a fallback
                if not duration_ok:
                    try:
                        import mutagen
                        mfile = mutagen.File(self.filepath, easy=True)
                        if mfile is not None and hasattr(mfile, 'info'):
                            length = getattr(mfile.info, 'length', None)
                            if length is not None and float(length) > 0:
                                self.duration_seconds = float(length); duration_ok = True
                    except ImportError:
                        pass  # mutagen not installed
                    except Exception as e:
                        logger.debug("mutagen fallback failed for %s: %s", self.filepath, e)
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
                if not os.path.isfile(self.filepath) or self.size_bytes <= 0:
                    self.error_message = "PDF file missing or empty"
                    return
            elif self.media_type == 'image':
                reader = QImageReader(self.filepath)
                sz = reader.size() if reader.canRead() else None
                if sz is not None and sz.isValid() and sz.width() > 0 and sz.height() > 0:
                    self.width = sz.width()
                    self.height = sz.height()
                else:
                    # OpenCV fallback for WebP/TIFF/unsupported Qt formats
                    with _CV_LOCK:
                        img = cv2.imdecode(np.fromfile(self.filepath, dtype=np.uint8), cv2.IMREAD_COLOR)
                    if img is None:
                        self.error_message = "Cannot open image file"
                        return
                    self.height, self.width = img.shape[:2]
                self.duration_seconds = 0.0; self.duration_compact = ""; self.duration_formatted = "—"
            else:
                self.is_valid = False
                self.error_message = "Unsupported media format"
                return
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
        try:
            paths_with_stats = []
            self.status_update.emit("Scanning directories…")
            if self.media_type == 'video': valid_exts = VIDEO_EXTENSIONS
            elif self.media_type == 'audio': valid_exts = AUDIO_EXTENSIONS
            elif self.media_type == 'image': valid_exts = IMAGE_EXTENSIONS
            elif self.media_type == 'pdf': valid_exts = PDF_EXTENSIONS
            else: valid_exts = VIDEO_EXTENSIONS | AUDIO_EXTENSIONS | IMAGE_EXTENSIONS | PDF_EXTENSIONS
            
            seen_norm_paths = set()
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
                            elif entry.is_file(follow_symlinks=True):
                                if entry.name.startswith('.'):
                                    continue  # dotfiles (.DS_Store, .gitignore) are never media
                                ext = os.path.splitext(entry.name)[1].lower()
                                # Include files without extensions as requested
                                if ext in valid_exts or ext == '':
                                    full_path = os.path.normpath(entry.path)
                                    norm_key = os.path.normcase(full_path)
                                    if norm_key not in seen_norm_paths:
                                        if not self._should_exclude(full_path):
                                            try:
                                                st = entry.stat(follow_symlinks=True)
                                                paths_with_stats.append((full_path, st.st_size, st.st_mtime))
                                                seen_norm_paths.add(norm_key)
                                            except Exception as e:
                                                logger.warning("stat failed for %s: %s", full_path, e)
                    except Exception as e:
                        logger.warning("scandir failed for %s: %s", current_dir, e)

            total = len(paths_with_stats)
            self.status_update.emit(f"Found {total} files. Reading metadata…")

            cache_path = os.path.join(CONFIG_DIR, 'scan_cache.json')
            cache = {}
            try:
                # Read under CACHE_LOCK: update_metadata_cache os.replace()s the
                # file from other threads; on Windows an open handle without
                # FILE_SHARE_DELETE makes that replace fail after retries.
                with CACHE_LOCK:
                    loaded = {}
                    if os.path.exists(cache_path):
                        with open(cache_path, 'r', encoding='utf-8') as f:
                            loaded = json.load(f)
                    cache = loaded if isinstance(loaded, dict) else {}
            except Exception as e:
                logger.warning("scan_cache.json load failed (%s): %s — starting with empty cache", cache_path, e)

            new_entries = {}
            from concurrent.futures import ThreadPoolExecutor, as_completed

            # Use a safe worker pool for CPU/IO operations
            num_workers = min(8, os.cpu_count() or 4)
            # Snapshot taken before processing: update_metadata_cache will refuse
            # to purge entries stamped after this time (written by a newer scan
            # that may have started while this orphaned thread was still running).
            scan_started = time.time()
            # Not used as a context manager: on the interrupt path we must NOT
            # block in __exit__'s shutdown(wait=True) after requesting a cancel.
            executor = ThreadPoolExecutor(max_workers=num_workers)
            try:
                futures = {executor.submit(self._process_scan_item, item, cache, self.force_full, self.media_type): idx for idx, item in enumerate(paths_with_stats)}
                for idx, future in enumerate(as_completed(futures)):
                    if self.isInterruptionRequested():
                        if new_entries:
                            update_metadata_cache(new_entries)
                        # Consistent with all other early-exit paths (0 = did not
                        # finish; the handler treats any value as "scan over").
                        self.scan_complete.emit(0)
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
            finally:
                executor.shutdown(wait=False, cancel_futures=True)

            # Cross-platform case-normalized cache cleanup.
            # Two guards prevent wrongful purges from the shared global cache:
            #   1. Extension filter — this scan only validated files of ONE media
            #      type, so it may only purge cache entries of that type. Without
            #      this, scanning Videos over a folder that also holds audio/
            #      images wiped their cache entries, forcing full re-extraction
            #      on every visit to the other tabs.
            #   2. Timestamp filter (not_before_ts) — entries a NEWER scan wrote
            #      after this run started are preserved.
            norm_dirs = [os.path.normcase(os.path.normpath(d)).rstrip(os.sep) + os.sep for d in self.directories]
            deleted_paths = []
            for cached_path in cache:
                cached_norm = os.path.normcase(os.path.normpath(cached_path))
                cached_norm_dir = cached_norm + os.sep if not cached_norm.endswith(os.sep) else cached_norm
                is_under_scanned = any(cached_norm_dir.startswith(nd) for nd in norm_dirs)
                if not is_under_scanned or cached_norm in seen_norm_paths:
                    continue
                cached_ext = os.path.splitext(cached_path)[1].lower()
                if cached_ext not in valid_exts and cached_ext != '':
                    continue  # belongs to another media type's scan
                if self._should_exclude(cached_path):
                    continue  # excluded files are invisible to this scan, keep their cache
                deleted_paths.append(cached_path)

            if new_entries or deleted_paths:
                update_metadata_cache(new_entries, deleted_paths, not_before_ts=scan_started)

            self.scan_complete.emit(total)
        except Exception as e:
            logger.error("ScannerThread.run crashed: %s", e)
            self.scan_complete.emit(0)

# ─── Dialogs ────────────────────────────────────────────────────────────────────

class AboutDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("About MediaFlow")
        self.setMinimumSize(600, 500)
        self._build_ui()

    def _build_ui(self):
        is_dark = getattr(self.parent(), 'current_theme', 'dark') == 'dark' if self.parent() else True
        body_color = "#e0e0e0" if is_dark else "#0f172a"
        box_text_color = "#e5e7eb" if is_dark else "#334155"

        layout = QVBoxLayout(self)
        layout.setContentsMargins(24, 24, 24, 24)
        layout.setSpacing(16)
        
        # Logo + Title Header
        header = QHBoxLayout()
        logo_label = QLabel()
        logo_pixmap = QPixmap(get_resource_path("logo.png"))
        if not logo_pixmap.isNull():
            logo_label.setPixmap(logo_pixmap.scaled(54, 54, Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation))
        header.addWidget(logo_label)
        
        title_vbox = QVBoxLayout()
        title_vbox.setSpacing(2)
        app_title = QLabel("MediaFlow")
        app_title.setStyleSheet("font-size: 22px; font-weight: 800; color: #a78bfa; letter-spacing: 0.5px;")
        meta_color = '#9ca3af' if is_dark else '#64748b'
        app_sub = QLabel(f"Version {globals().get('__version__', '2.4.0')}  •  High-Performance Media Asset Organizer")
        app_sub.setStyleSheet(f"font-size: 12px; color: {meta_color}; font-weight: 500;")
        title_vbox.addWidget(app_title)
        title_vbox.addWidget(app_sub)
        header.addLayout(title_vbox)
        header.addStretch()
        layout.addLayout(header)
        
        # Scroll area for the rich info sections
        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        scroll.setStyleSheet("background: transparent;")
        
        content = QWidget()
        content.setStyleSheet("background: transparent;")
        content_layout = QVBoxLayout(content)
        content_layout.setContentsMargins(0, 0, 8, 0)
        content_layout.setSpacing(14)
        
        # About text block
        about_lbl = QLabel(
            "<b>MediaFlow</b> is a premium desktop utility designed to organize and rename your video, "
            "image, and audio libraries using dynamic, custom-defined naming templates. It provides "
            "real-time previews, instant directory scanning with an optimized metadata cache, "
            "a native player, and advanced multithreaded operations."
        )
        about_lbl.setWordWrap(True)
        about_lbl.setStyleSheet(f"font-size: 13px; line-height: 1.5; color: {body_color};")
        content_layout.addWidget(about_lbl)
        
        # Divider line
        divider = QFrame()
        divider.setFrameShape(QFrame.Shape.HLine)
        divider.setFrameShadow(QFrame.Shadow.Sunken)
        divider.setStyleSheet("background-color: rgba(167, 139, 250, 0.15); height: 1px; border: none;")
        content_layout.addWidget(divider)
        
        # Media Decoding Warning Box
        codec_group = QGroupBox("Media Decoding & Codec Support Warning")
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
        explanation_lbl.setStyleSheet(f"font-size: 12.5px; line-height: 1.4; color: {box_text_color}; font-weight: normal;")
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
        resolution_lbl.setStyleSheet(f"font-size: 12.5px; line-height: 1.4; color: {box_text_color}; font-weight: normal;")
        codec_layout.addWidget(resolution_lbl)
        
        content_layout.addWidget(codec_group)
        
        # FFprobe Metadata Configuration Box
        ff_group = QGroupBox("Deep Metadata & FFprobe Requirement")
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
        ff_explanation_lbl.setStyleSheet(f"font-size: 12.5px; line-height: 1.4; color: {box_text_color}; font-weight: normal;")
        ff_layout.addWidget(ff_explanation_lbl)
        
        ff_config_lbl = QLabel(
            "<b>How to install and configure FFprobe:</b><br><br>"
            "1. <b>Download FFmpeg/FFprobe:</b> Download the FFmpeg package from the official website (ffmpeg.org) or install it via your package manager (e.g. run <code>winget install Gnu.FFmpeg</code> in Windows Terminal).<br><br>"
            "2. <b>Add to System PATH:</b> Extract the files and add the bin folder to your Windows System Environment Variables (PATH) to let MediaFlow detect it automatically.<br><br>"
            "3. <b>Configure Custom Path in Settings:</b> Alternatively, open MediaFlow settings, scroll to the 'Deep Metadata (FFprobe)' section, and click Browse to select your <code>ffprobe.exe</code> binary manually."
        )
        ff_config_lbl.setWordWrap(True)
        ff_config_lbl.setStyleSheet(f"font-size: 12.5px; line-height: 1.4; color: {box_text_color}; font-weight: normal;")
        ff_layout.addWidget(ff_config_lbl)
        
        content_layout.addWidget(ff_group)
        content_layout.addStretch()
        
        scroll.setWidget(content)
        layout.addWidget(scroll, 1)
        
        # Close Button
        btn_close = QPushButton("Close")
        btn_close.setObjectName("btnCommon")
        btn_close.setFixedHeight(36)
        btn_close.clicked.connect(self.accept)
        layout.addWidget(btn_close)


class ConfigureOpenWithDialog(QDialog):
    def __init__(self, current_apps: list = None, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Configure Open With Applications")
        self.setMinimumSize(500, 350)
        self.apps = list(current_apps or [])
        self._build_ui()

    def _build_ui(self):
        layout = QVBoxLayout(self)
        layout.setSpacing(10)
        
        self.table = QTableWidget(0, 2)
        self.table.setHorizontalHeaderLabels(["Name", "Executable Path"])
        self.table.horizontalHeader().setStretchLastSection(True)
        self.table.setSelectionBehavior(QTableWidget.SelectionBehavior.SelectRows)
        self.table.setEditTriggers(QTableWidget.EditTrigger.NoEditTriggers)
        layout.addWidget(self.table)
        
        btn_layout = QHBoxLayout()
        btn_add = QPushButton("Add...")
        btn_add.clicked.connect(self._on_add)
        btn_layout.addWidget(btn_add)
        
        btn_remove = QPushButton("Remove")
        btn_remove.clicked.connect(self._on_remove)
        btn_layout.addWidget(btn_remove)
        
        btn_layout.addStretch()
        layout.addLayout(btn_layout)
        
        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok | QDialogButtonBox.StandardButton.Cancel)
        buttons.accepted.connect(self.accept)
        buttons.rejected.connect(self.reject)
        layout.addWidget(buttons)
        
        self._populate_table()

    def _populate_table(self):
        self.table.setRowCount(len(self.apps))
        for r, app in enumerate(self.apps):
            self.table.setItem(r, 0, QTableWidgetItem(app.get('name', '')))
            self.table.setItem(r, 1, QTableWidgetItem(app.get('path', '')))

    def _on_add(self):
        if sys.platform == "win32":
            start_dir = "C:\\Program Files"
            file_filter = "Executable Files (*.exe);;All Files (*.*)"
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
        if self.apply_rating.isChecked():
            rating = self.rating_combo.currentText()  # Returns "—" or "1".."10"
        else:
            rating = None  # None indicates do not modify rating
        return artist, rating

class SmartRelocateDialog(QDialog):
    def __init__(self, selected_infos: list, all_infos: list, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Smart Relocate Files")
        self.setMinimumSize(600, 450)
        self.media_infos = all_infos
        self.selected_infos = list(selected_infos)
        
        layout = QVBoxLayout(self)
        
        # 1. Source Selection
        source_group = QGroupBox("1. What to Move?")
        source_layout = QVBoxLayout(source_group)
        self.radio_selected = QRadioButton(f"Move Selected Files ({len(self.selected_infos)} files)")
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
        help_lbl = QLabel("Use variables: <b>{type}</b>, <b>{name}</b> (= artist), <b>{filename}</b> (= file stem), <b>{rating}</b>, <b>{resolution}</b>, <b>{tag}</b>, <b>{tags}</b>")
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
        is_dark = getattr(self.parent(), 'current_theme', 'dark') == 'dark' if self.parent() else True
        btn_row = QHBoxLayout()
        self.btn_preview = QPushButton("Update Preview")
        self.btn_preview.setIcon(get_vector_icon('sync', is_dark))
        self.btn_preview.clicked.connect(self._generate_preview)
        self.btn_execute = QPushButton("Execute Move")
        self.btn_execute.setIcon(get_vector_icon('process', is_dark))
        self.btn_execute.clicked.connect(self.accept)
        btn_cancel = QPushButton("Cancel")
        btn_cancel.clicked.connect(self.reject)
        
        btn_row.addWidget(self.btn_preview)
        btn_row.addStretch()
        btn_row.addWidget(btn_cancel)
        btn_row.addWidget(self.btn_execute)
        layout.addLayout(btn_row)
        
        # Fallback to user home if no candidate files exist (was "" which produced
        # relative paths that could land in CWD — e.g. System32 when elevated)
        first = self.selected_infos[0] if self.selected_infos else (self.media_infos[0] if self.media_infos else None)
        if first:
            base_dir = os.path.dirname(first.filepath)
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
            tags = getattr(info, 'tags', []) or []
            dest_dir = parse_destination_template(self.template_input.text(), info, tags)
            # Mirror execute-time anchoring so the preview shows the real path
            if not os.path.isabs(dest_dir):
                dest_dir = os.path.join(os.path.dirname(info.filepath), dest_dir)
            final_path = os.path.join(dest_dir, info.filename)
            self.preview_list.addItem(f"{info.filename}  ->  {final_path}")
            
        if len(target_infos) > 10:
            self.preview_list.addItem(f"... and {len(target_infos) - 10} more files.")

    def _get_target_infos(self) -> list:
        if self.radio_selected.isChecked():
            # FIX: resolve infos by OBJECT (row indices drifted from media_infos
            # order after sorting/removals — the dialog used to move the WRONG files)
            return list(self.selected_infos)
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
        track_w = max(1, self.width() - 32)  # guard: below 32px width drew handles off-widget
        if self._max <= self._min: return 16
        ratio = (val - self._min) / (self._max - self._min)
        return int(round(16 + ratio * track_w))

    def _x_to_val(self, x: int) -> int:
        track_w = self.width() - 32
        if track_w <= 0: return self._min
        ratio = max(0.0, min(1.0, (x - 16) / track_w))
        return int(round(self._min + ratio * (self._max - self._min)))

    def paintEvent(self, event):
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        w = self.width()
        h = self.height()
        track_y = h // 2 - 4
        track_h = 8

        main_win = self.window()
        is_dark = getattr(main_win, 'current_theme', 'dark') == 'dark' if main_win else True
        accent = getattr(main_win, 'theme_accent', None) or (Nebula.ACCENT if is_dark else Nebula.ACCENT_L)
        accent2 = getattr(main_win, 'theme_accent2', None) or (Nebula.ACCENT2 if is_dark else Nebula.ACCENT2_L)

        # Background track
        painter.setPen(Qt.PenStyle.NoPen)
        painter.setBrush(QColor("#1e1b4b") if is_dark else QColor("#e2e8f0"))
        painter.drawRoundedRect(16, track_y, w - 32, track_h, 4, 4)

        # Highlighted selected range
        in_x = self._val_to_x(self._in_pos)
        out_x = self._val_to_x(self._out_pos)
        if out_x > in_x:
            grad = QLinearGradient(in_x, 0, out_x, 0)
            grad.setColorAt(0, QColor(accent))
            grad.setColorAt(1, QColor(accent2))
            painter.setBrush(grad)
            painter.drawRoundedRect(in_x, track_y, out_x - in_x, track_h, 4, 4)

        # Current playback position marker
        cur_x = self._val_to_x(self._cur_pos)
        painter.setPen(QPen(QColor("#fbbf24" if is_dark else "#d97706"), 2))
        painter.drawLine(cur_x, 4, cur_x, h - 4)

        # IN handle (Left flag/knob)
        handle_border = QColor("#ffffff" if is_dark else "#0f172a")
        painter.setPen(QPen(handle_border, 1.5))
        painter.setBrush(QColor(accent2))
        in_poly = QPolygon([
            QPoint(in_x - 10, h // 2 - 12),
            QPoint(in_x, h // 2 - 12),
            QPoint(in_x, h // 2 + 12),
            QPoint(in_x - 10, h // 2 + 12),
            QPoint(in_x - 5, h // 2)
        ])
        painter.drawPolygon(in_poly)

        # OUT handle (Right flag/knob)
        painter.setPen(QPen(handle_border, 1.5))
        painter.setBrush(QColor(accent))
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
            if abs(in_x - out_x) <= 4:
                # When handles are collapsed together, select handle based on mouse position
                if x >= out_x:
                    self._dragging_handle = 'out'
                else:
                    self._dragging_handle = 'in'
            elif abs(x - in_x) <= 12:
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

    def __init__(self, filepath: str, in_sec: float, out_sec: float, output_path: str, custom_ffmpeg: str = None, cut_mode: str = 'precise', parent=None):
        super().__init__(parent)
        self.filepath = filepath
        self.in_sec = in_sec
        self.out_sec = out_sec
        self.output_path = output_path
        self.custom_ffmpeg = custom_ffmpeg
        self.cut_mode = cut_mode if cut_mode in ('precise', 'fast') else 'precise'
        self._proc = None
        self._cancelled = False

    def cancel(self):
        self._cancelled = True
        p = self._proc
        if p is not None:
            try:
                p.terminate()
                p.kill()
            except Exception:
                pass

    def run(self):
        ffmpeg_cmd = get_ffmpeg_command(self.custom_ffmpeg)
        if not ffmpeg_cmd:
            self.trim_finished.emit(False, "", "FFmpeg executable not found. Please ensure FFmpeg is installed.")
            return

        if not (math.isfinite(self.in_sec) and math.isfinite(self.out_sec)) or self.out_sec <= self.in_sec or self.in_sec < 0:
            self.trim_finished.emit(False, "", "Invalid trim range.")
            return
        out_abs = os.path.abspath(self.output_path)
        out_dir = os.path.dirname(out_abs)
        if not os.path.isdir(out_dir):
            self.trim_finished.emit(False, "", f"Output folder does not exist:\n{out_dir}")
            return
        if os.path.basename(out_abs).startswith('-'):
            # A leading dash would be parsed as an ffmpeg flag.
            self.trim_finished.emit(False, "", "Output filename must not start with '-'.")
            return
        src = os.path.abspath(self.filepath)
        if self.cut_mode == 'fast':
            # Stream copy: instant, but cuts snap to the nearest keyframe
            cmd = [
                ffmpeg_cmd,
                "-y",
                "-ss", f"{self.in_sec:.3f}",
                "-to", f"{self.out_sec:.3f}",
                "-i", src,
                "-c", "copy",
                "-avoid_negative_ts", "make_zero",
                os.path.abspath(self.output_path)
            ]
        else:
            # Precise (default): fast input-side seek + veryfast re-encode —
            # the clip starts exactly on the previewed IN point instead of the
            # preceding keyframe. Re-encode audio to AAC to guarantee A/V sync.
            cmd = [
                ffmpeg_cmd,
                "-y",
                "-ss", f"{self.in_sec:.3f}",
                "-to", f"{self.out_sec:.3f}",
                "-i", src,
                "-c:v", "libx264", "-preset", "veryfast", "-crf", "20",
                "-c:a", "aac", "-b:a", "192k",
                "-avoid_negative_ts", "make_zero",
                os.path.abspath(self.output_path)
            ]

        startupinfo = None
        if sys.platform == "win32":
            startupinfo = subprocess.STARTUPINFO()
            startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW

        try:
            # No fixed timeout: precise mode re-encodes, so long clips on slow
            # disks legitimately take more than 2 minutes — a hard 120s timeout
            # turned every large export into a deterministic "export failed".
            self._proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, encoding='utf-8', errors='replace', startupinfo=startupinfo)
            stdout, stderr = self._proc.communicate()
            if self._cancelled:
                self.trim_finished.emit(False, "", "Trim export was cancelled.")
                return
            if self._proc.returncode == 0 and os.path.exists(self.output_path) and os.path.getsize(self.output_path) > 0:
                self.trim_finished.emit(True, self.output_path, "")
            else:
                err = stderr or "FFmpeg failed with unknown error."
                self.trim_finished.emit(False, "", err)
        except Exception as e:
            if not self._cancelled:
                self.trim_finished.emit(False, "", str(e))
        finally:
            self._proc = None


class QuickTrimDialog(QDialog):
    def __init__(self, filepath: str, parent_tab=None, parent=None):
        super().__init__(parent)
        self.filepath = filepath
        self.parent_tab = parent_tab
        self.duration_ms = 0
        self.in_ms = 0
        self.out_ms = 0
        self._playing_selection = False
        
        self.setWindowTitle(f"Quick Trim — {os.path.basename(filepath)}")
        self.resize(780, 580)

        is_dark = getattr(self.parent_tab.window(), 'current_theme', 'dark') == 'dark' if (self.parent_tab and self.parent_tab.window()) else True

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
        
        self.btn_play = QPushButton("")
        self.btn_play.setIcon(get_vector_icon('play', is_dark))
        self.btn_play.setFixedSize(32, 32)
        self.btn_play.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_play.clicked.connect(self._toggle_playback)
        controls_layout.addWidget(self.btn_play)

        self.time_label = QLabel("00:00.000 / 00:00.000")
        self.time_label.setStyleSheet("font-family: monospace; font-size: 11px; color: #a78bfa;")
        controls_layout.addWidget(self.time_label)

        controls_layout.addStretch()

        self.btn_play_selection = QPushButton("Play Selection")
        self.btn_play_selection.setIcon(get_vector_icon('play', is_dark))
        self.btn_play_selection.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_play_selection.clicked.connect(self._play_selection)
        controls_layout.addWidget(self.btn_play_selection)

        self.btn_mute = QPushButton("")
        self.btn_mute.setIcon(get_vector_icon('unmute', is_dark))
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
        btn_set_in_cur = QPushButton("Set to Current")
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
        btn_set_out_cur = QPushButton("Set to Current")
        btn_set_out_cur.clicked.connect(self._set_out_to_current)

        points_layout.addWidget(btn_out_minus5, 1, 2)
        points_layout.addWidget(btn_out_minus1, 1, 3)
        points_layout.addWidget(btn_out_plus1, 1, 4)
        points_layout.addWidget(btn_out_plus5, 1, 5)
        points_layout.addWidget(btn_set_out_cur, 1, 6)

        # Trimmed duration label
        self.trim_dur_label = QLabel("Clip Duration: 00:00.000")
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

        # Cut mode — frame-exact by default, stream copy for instant results
        mode_row = QHBoxLayout()
        mode_lbl = QLabel("Cut Mode:")
        self.cut_mode_combo = QComboBox()
        self.cut_mode_combo.addItem("Precise — frame-exact (re-encode)")
        self.cut_mode_combo.addItem("Fast — instant (keyframe copy)")
        self.cut_mode_combo.setToolTip(
            "Precise re-encodes the clip so it starts exactly on your IN point (a few seconds).\n"
            "Fast copies streams without re-encoding (instant) but the cut snaps to the nearest keyframe."
        )
        mode_row.addWidget(mode_lbl)
        mode_row.addWidget(self.cut_mode_combo, 1)
        layout.addLayout(mode_row)

        # Action buttons
        btn_box = QHBoxLayout()
        btn_box.addStretch()
        self.btn_cancel = QPushButton("Cancel")
        self.btn_cancel.clicked.connect(self.reject)
        btn_box.addWidget(self.btn_cancel)

        self.btn_export = QPushButton("Export Trimmed Clip")
        self.btn_export.setObjectName("btnProcessAll")
        self.btn_export.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_export.setIcon(get_vector_icon('scissors', is_dark))
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
            s = s.strip().replace(',', '.')
            if not s or '-' in s: return None
            parts = s.split(':')
            if len(parts) == 3:
                hrs_s, mins_s, secs_s = parts
                if not hrs_s.isdigit() or not mins_s.isdigit(): return None
                hrs, mins = int(hrs_s), int(mins_s)
                secs, ms = self._parse_secs_ms(secs_s)
                if secs is None or mins >= 60: return None
                return (hrs * 3600 + mins * 60 + secs) * 1000 + ms
            elif len(parts) == 2:
                mins_s, secs_s = parts
                if not mins_s.isdigit(): return None
                mins = int(mins_s)
                secs, ms = self._parse_secs_ms(secs_s)
                if secs is None or mins >= 60: return None
                return (mins * 60 + secs) * 1000 + ms
            elif len(parts) == 1:
                secs, ms = self._parse_secs_ms(parts[0])
                if secs is None: return None
                return secs * 1000 + ms
        except Exception as e:
            logger.debug("_str_to_ms parse failed for '%s': %s", s, e)
        return None

    @staticmethod
    def _parse_secs_ms(secs_s: str) -> tuple[int | None, int]:
        """Parse 'SS[.mmm]' — exactly zero or one dot, digits only, secs < 60."""
        if secs_s.count('.') > 1:
            return None, 0
        secs_parts = secs_s.split('.')
        if not secs_parts[0].isdigit():
            return None, 0
        secs = int(secs_parts[0])
        if secs >= 60:
            return None, 0
        ms = 0
        if len(secs_parts) > 1:
            if not secs_parts[1].isdigit():
                return None, 0
            ms = int(secs_parts[1].ljust(3, '0')[:3])
        return secs, ms

    def _on_duration_changed(self, dur: int):
        if dur > 0:
            first_duration = self.duration_ms <= 0
            self.duration_ms = dur
            self.range_slider.set_range(0, dur)
            if first_duration:
                # Only default the OUT point on the FIRST real duration —
                # late duration updates must not wipe the user's trim selection.
                self.out_ms = dur
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
        self.trim_dur_label.setText(f"Clip Duration: {self._ms_to_str(clip_ms)}")

    def _toggle_playback(self):
        if self.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState:
            self.player.pause()
            self._playing_selection = False
        else:
            self.player.play()

    def _on_playback_state_changed(self, state):
        is_dark = getattr(self.parent_tab.window(), 'current_theme', 'dark') == 'dark' if (self.parent_tab and self.parent_tab.window()) else True
        self.btn_play.setIcon(get_vector_icon('pause' if state == QMediaPlayer.PlaybackState.PlayingState else 'play', is_dark))

    def _play_selection(self):
        self._playing_selection = True
        self.player.setPosition(self.in_ms)
        self.player.play()

    def _toggle_mute(self):
        is_muted = self.audio_output.isMuted()
        self.audio_output.setMuted(not is_muted)
        is_dark = getattr(self.parent_tab.window(), 'current_theme', 'dark') == 'dark' if (self.parent_tab and self.parent_tab.window()) else True
        self.btn_mute.setIcon(get_vector_icon('mute' if not is_muted else 'unmute', is_dark))

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

    def _cut_mode(self) -> str:
        return 'fast' if self.cut_mode_combo.currentIndex() == 1 else 'precise'

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
        self.btn_export.setText("Trimming clip...")

        # FIX (crash): the worker used to be parented to this dialog — closing
        # the dialog mid-export destroyed a running QThread (hard abort). It is
        # now unparented and parked on the main window until it finishes.
        main_win = self.window()
        # Settings stores the ffprobe FILE path as `ffprobe_path` (there is no
        # `custom_ffprobe_path` attr — the old lookup always yielded None and,
        # worse, would have executed ffprobe AS ffmpeg). Resolve the sibling.
        ffprobe_stored = getattr(main_win, 'ffprobe_path', '') or None
        custom_ff = _resolve_ffmpeg_from_ffprobe_hint(ffprobe_stored)
        worker = TrimExportWorker(self.filepath, in_sec, out_sec, output_path, custom_ffmpeg=custom_ff, cut_mode=self._cut_mode())
        worker.trim_finished.connect(self._on_export_finished)
        worker.finished.connect(worker.deleteLater)
        self._park_trim_worker(worker)
        self.worker = worker
        worker.start()

    def _on_export_finished(self, success: bool, output_path: str, err: str):
        if getattr(self, '_suppress_export_result', False):
            self._suppress_export_result = False
            return
        self.btn_export.setEnabled(True)
        self.btn_export.setText("Export Trimmed Clip")
        
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

    def _park_trim_worker(self, worker):
        """Keep running export workers alive on the main window (not this dialog)
        so closing the dialog can't destroy a running QThread."""
        main_win = self.window()
        if main_win is None:
            return
        pool = getattr(main_win, '_orphaned_trim_workers', None)
        if pool is None:
            pool = []
            main_win._orphaned_trim_workers = pool
        try:
            pruned = []
            for w in pool:
                try:
                    if w.isRunning():
                        pruned.append(w)
                except RuntimeError:
                    continue  # deleted C++ worker — drop it, keep the others
            pool[:] = pruned
        except Exception:
            pass
        pool.append(worker)

    def _release_player(self):
        """Release media sources so the file handle isn't locked after close.

        done() (accept/reject) does NOT trigger closeEvent on QDialog, so both
        paths must clean up — otherwise QMediaPlayer keeps the source open.
        """
        self.player.stop()
        self.player.setSource(QUrl())
        try:
            self.player.setVideoOutput(None)
            self.player.setAudioOutput(None)
        except (TypeError, RuntimeError):
            pass

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
        
        top = parent.window() if parent else self.window()
        is_dark = (getattr(top, 'current_theme', 'dark') == 'dark') if top else True
        self.update_theme(is_dark)

    def set_active(self, active: bool):
        self.active = active
        self.btn_nav.setProperty("active", active)
        self.btn_nav.style().unpolish(self.btn_nav)
        self.btn_nav.style().polish(self.btn_nav)

    def update_theme(self, is_dark):
        w = self.window()
        accent = getattr(w, 'theme_accent', None) or ('#a78bfa' if is_dark else '#4338ca')
        accent2 = getattr(w, 'theme_accent2', None) or ('#7c3aed' if is_dark else '#6366f1')
        if is_dark:
            self.btn_nav.setStyleSheet(f"""
                QPushButton {{ background: transparent; color: #9ca3af; text-align: left; padding: 10px 12px; font-size: 13px; font-weight: 600; border-radius: 6px; border: none; }}
                QPushButton:hover {{ background: rgba(167, 139, 250, 0.1); color: #e0e0e0; }}
                QPushButton[active="true"] {{ background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 {accent}, stop:1 {accent2}); color: #ffffff; }}
            """)
            self.btn_delete.setStyleSheet("""
                QPushButton { background: transparent; color: #ef4444; font-size: 11px; font-weight: bold; border: none; border-radius: 10px; padding: 0; }
                QPushButton:hover { background: rgba(239, 68, 68, 0.2); color: #f87171; }
            """)
        else:
            self.btn_nav.setStyleSheet(f"""
                QPushButton {{ background: transparent; color: #475569; text-align: left; padding: 10px 12px; font-size: 13px; font-weight: 600; border-radius: 6px; border: none; }}
                QPushButton:hover {{ background: #f1f5f9; color: #0f172a; }}
                QPushButton[active="true"] {{ background: #e0e7ff; color: {accent}; font-weight: bold; }}
            """)
            self.btn_delete.setStyleSheet("""
                QPushButton { background: transparent; color: #dc2626; font-size: 11px; font-weight: bold; border: none; border-radius: 10px; padding: 0; }
                QPushButton:hover { background: #fee2e2; color: #ef4444; }
            """)
        self.btn_nav.setIcon(get_vector_icon('star', is_dark))
        self.btn_delete.setIcon(get_vector_icon('close', is_dark))
        for btn in (self.btn_nav, self.btn_delete):
            btn.style().unpolish(btn)
            btn.style().polish(btn)
        self.btn_nav.style().polish(self.btn_nav)

class DeepMetadataWorker(QThread):
    """Background worker for ffprobe — prevents UI freezes up to 10s."""
    metadata_ready = pyqtSignal(object)  # dict or None ('dict or None' was a truthy-expression bug)

    def __init__(self, filepath: str, ffprobe_path: str = None, parent=None):
        super().__init__(parent)
        self.filepath = filepath
        self.ffprobe_path = ffprobe_path
        self._proc = None
        self._cancelled = False

    def cancel(self):
        self._cancelled = True
        p = self._proc
        if p is not None:
            try:
                p.kill()
            except Exception:
                pass

    def run(self):
        ffprobe_cmd = get_ffprobe_command(self.ffprobe_path)
        if not ffprobe_cmd or self._cancelled:
            if not self._cancelled:
                self.metadata_ready.emit(None)
            return
        cmd = [ffprobe_cmd, "-v", "error", "-show_format", "-show_streams", "-of", "json", os.path.abspath(self.filepath)]
        startupinfo = None
        if sys.platform == "win32":
            startupinfo = subprocess.STARTUPINFO()
            startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
        try:
            self._proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, encoding='utf-8', errors='replace', startupinfo=startupinfo)
            stdout, stderr = self._proc.communicate(timeout=10)
            if not self._cancelled and self._proc.returncode == 0 and stdout:
                meta = parse_ffprobe_json(json.loads(stdout))
                self.metadata_ready.emit(meta)
            elif not self._cancelled:
                self.metadata_ready.emit(None)
        except Exception as e:
            if not self._cancelled:
                logger.warning("DeepMetadataWorker failed for %s: %s", self.filepath, e)
                self.metadata_ready.emit(None)
        finally:
            self._proc = None


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
        
        main_win = parent.window() if parent else self.window()
        is_dark = getattr(main_win, 'current_theme', 'dark') == 'dark' if main_win else True
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
        sep.setStyleSheet("background: rgba(167, 139, 250, 0.3); border: none; height: 1px;")
        layout.addWidget(sep)
        if not get_ffprobe_command(custom_ffprobe_path):
            warning_banner = QFrame()
            warning_banner.setStyleSheet(f"QFrame {{ background: rgba(239, 68, 68, 0.15); border: 1px solid rgba(239, 68, 68, 0.3); border-radius: 8px; padding: 8px; }}")
            warn_layout = QVBoxLayout(warning_banner)
            warn_title = QLabel("Deep Metadata Unavailable")
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
        self._is_closed = False
        # Start background worker (was: blocking call up to 10s on UI thread)
        # Park on the main window so dialog close cannot destroy a running QThread
        self._worker = DeepMetadataWorker(filepath, custom_ffprobe_path, parent=None)
        main_win = parent.window() if parent else (QApplication.activeWindow() or None)
        if main_win is self and parent:
            main_win = parent
        self._pool = None
        if main_win is not None:
            self._pool = getattr(main_win, '_orphaned_metadata_workers', None)
            if self._pool is None:
                self._pool = []
                main_win._orphaned_metadata_workers = self._pool
            self._pool.append(self._worker)
            def _cleanup_worker(w=self._worker, p=self._pool):
                try:
                    p.remove(w)
                except (ValueError, RuntimeError):
                    pass
            self._worker.finished.connect(_cleanup_worker)
        self._worker.metadata_ready.connect(self._on_metadata_ready)
        self._worker.finished.connect(self._worker.deleteLater)
        self._worker.start()

    def closeEvent(self, event):
        self._is_closed = True
        w = getattr(self, '_worker', None)
        if w is not None:
            w.cancel()
        super().closeEvent(event)

    def done(self, result):
        self._is_closed = True
        w = getattr(self, '_worker', None)
        if w is not None:
            w.cancel()
        super().done(result)

    def _on_metadata_ready(self, meta):
        if getattr(self, '_is_closed', False):
            return
        # Remove loading placeholder
        try:
            self._loading_label.setParent(None)
            self._loading_label.deleteLater()
        except RuntimeError:
            return
        accent_color, text_color, sub_text_color = self._theme
        filepath = self.filepath
        if meta:
            gen_group = QGroupBox("General Info")
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
                v_group = QGroupBox("Video Stream")
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
                a_group = QGroupBox("Audio Stream")
                a_layout = QFormLayout(a_group)
                a_layout.addRow(self._make_label("Codec:", sub_text_color), self._make_value(a['codec'], text_color))
                a_layout.addRow(self._make_label("Channels:", sub_text_color), self._make_value(a['channel_layout'], text_color))
                if a['sample_rate_hz'] > 0: a_layout.addRow(self._make_label("Sample Rate:", sub_text_color), self._make_value(f"{a['sample_rate_hz'] / 1000:.1f} kHz", text_color))
                if a['bitrate_kbps'] > 0: a_layout.addRow(self._make_label("Bitrate:", sub_text_color), self._make_value(f"{a['bitrate_kbps']} kbps", text_color))
                self.scroll_layout.addWidget(a_group)
        else:
            fallback_group = QGroupBox("General Info (Basic)")
            fallback_layout = QFormLayout(fallback_group)
            try:
                sb = os.path.getsize(filepath)
                if sb >= 1024**3: size_str = f"{sb/(1024**3):.2f} GB"
                elif sb >= 1024**2: size_str = f"{sb/(1024**2):.1f} MB"
                elif sb >= 1024: size_str = f"{sb/1024:.0f} KB"
                else: size_str = f"{sb} B"
                fallback_layout.addRow(self._make_label("Size:", sub_text_color), self._make_value(size_str, text_color))
            except Exception as e:
                logger.debug("DetailedInfo fallback size failed for %s: %s", filepath, e)
            ext = os.path.splitext(filepath)[1].lower()
            if ext in VIDEO_EXTENSIONS:
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
                except Exception as e:
                    logger.debug("DetailedInfo cv2 fallback failed for %s: %s", filepath, e)
                finally:
                    if cap is not None:
                        try:
                            with _CV_LOCK:
                                cap.release()
                        except Exception:
                            try:
                                cap.release()
                            except Exception:
                                pass
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
    """Click-to-jump slider that ALSO supports drag-seeking.

    QSlider only arms its internal drag state (sliderDown / pressed control)
    inside its base mousePressEvent — swallowing the press without calling
    super() previously meant valueChanged-gated seek handlers never fired on
    click, and dragging did nothing at all. We track the drag ourselves and
    mirror the sliderDown state so both click and drag seek correctly while
    still avoiding the base class's page-step double-seek on press.
    """
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._seek_dragging = False

    def _value_at(self, x: float) -> int:
        # Compute from the style's groove/handle rects so margins, orientation,
        # and RTL are honored.
        opt = QStyleOptionSlider()
        self.initStyleOption(opt)
        groove = self.style().subControlRect(QStyle.ComplexControl.CC_Slider, opt, QStyle.SubControl.SC_SliderGroove, self)
        handle = self.style().subControlRect(QStyle.ComplexControl.CC_Slider, opt, QStyle.SubControl.SC_SliderHandle, self)
        span = max(1, groove.width() - handle.width())
        pos = int(x - groove.x() - handle.width() / 2)
        return QStyle.sliderValueFromPosition(self.minimum(), self.maximum(), pos, span, self.invertedAppearance())

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton and self.orientation() == Qt.Orientation.Horizontal:
            self._seek_dragging = True
            # Arm sliderDown BEFORE setValue so valueChanged handlers that gate
            # on isSliderDown() (e.g. the audio player) fire for click-to-seek.
            self.setSliderDown(True)
            self.setValue(self._value_at(event.position().x()))
            event.accept()
            return
        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if self._seek_dragging and self.orientation() == Qt.Orientation.Horizontal:
            self.setValue(self._value_at(event.position().x()))
            event.accept()
            return
        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        if self._seek_dragging and event.button() == Qt.MouseButton.LeftButton:
            self._seek_dragging = False
            self.setSliderDown(False)
            event.accept()
            return
        super().mouseReleaseEvent(event)

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
        # Re-clamp height after the width clamp — on short/narrow windows the
        # old order recomputed h from the clamped w and overflowed the parent.
        if h > p_height // 2:
            w = max(480, min((p_height // 2) * 16 // 9, 854))
            h = min((w * 9) // 16, max(1, p_height // 2))
        
        x = (p_width - w) // 2
        y = (p_height - h) // 2
        self.container.setGeometry(x, y, w, h)

    def eventFilter(self, watched, event):
        if event.type() == QEvent.Type.MouseButtonPress:
            if event.button() in (Qt.MouseButton.LeftButton, Qt.MouseButton.RightButton):
                sw = getattr(self.parent_window, 'stacked_widget', None)
                active_tab = sw.currentWidget() if sw else None
                if active_tab and hasattr(active_tab, '_dismissed_info'):
                    active_tab._dismissed_info = self.info
                self.hide_preview()
                return True
        return super().eventFilter(watched, event)

    def mousePressEvent(self, event):
        if event.button() in (Qt.MouseButton.LeftButton, Qt.MouseButton.RightButton):
            sw = getattr(self.parent_window, 'stacked_widget', None)
            active_tab = sw.currentWidget() if sw else None
            if active_tab and hasattr(active_tab, '_dismissed_info'):
                active_tab._dismissed_info = self.info
            self.hide_preview()

    def show_preview(self, info, target_global_rect):
        self.segment_timer.stop()  # FIX: Stop running segment timer before loading new media
        # Pause background player if playing
        sw = getattr(self.parent_window, 'stacked_widget', None)
        active_tab = sw.currentWidget() if sw else None
        player = getattr(active_tab, 'player', None)
        if player is not None:
            try:
                if player.playbackState() == QMediaPlayer.PlaybackState.PlayingState:
                    player.pause()
            except (RuntimeError, AttributeError):
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
        if hasattr(self, 'mouse_check_timer'):
            self.mouse_check_timer.stop()
        self.player.stop()
        self.player.setSource(QUrl())
        self.has_started = False
        self.info = None
        self.hide()

    def closeEvent(self, event):
        self.hide_preview()
        try:
            self.player.setVideoOutput(None)
        except Exception:
            pass
        super().closeEvent(event)

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
            icon_name = 'check'
            bg_color = "#34d399" if is_dark else "#059669"
        elif toast_type == 'warning':
            icon_name = 'warning'
            bg_color = "#fbbf24" if is_dark else "#d97706"
        elif toast_type == 'error':
            icon_name = 'clear'
            bg_color = "#f87171" if is_dark else "#dc2626"
        else: # info
            icon_name = 'info'
            bg_color = "#60a5fa" if is_dark else "#3b82f6"

        layout = QHBoxLayout(self)
        layout.setContentsMargins(15, 10, 15, 10)
        layout.setSpacing(10)

        icon_label = QLabel()
        icon_pixmap = get_vector_icon(icon_name, is_dark, color_override="#ffffff").pixmap(20, 20)
        icon_label.setPixmap(icon_pixmap)
        icon_label.setStyleSheet("background: transparent;")
        
        msg_label = QLabel(message)
        msg_label.setWordWrap(True)
        msg_label.setStyleSheet("color: white; font-weight: bold; background: transparent;")

        layout.addWidget(icon_label)
        layout.addWidget(msg_label, 1)

        self.setFixedWidth(320)
        self.setStyleSheet(f"""
            ToastNotification {{
                background-color: {bg_color};
                border-radius: 12px;
                border: 1px solid rgba(255, 255, 255, 0.22);
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
        
        self._orig_pixmap = QPixmap(filepath)
        central = QWidget(self)
        self.setCentralWidget(central)
        layout = QVBoxLayout(central)
        layout.setContentsMargins(10, 10, 10, 10)
        
        self.label = QLabel(central)
        self.label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        layout.addWidget(self.label, 1)
        self._update_scaled_image()
        
        if is_dark:
            self.setStyleSheet("QMainWindow { background-color: #0f0c29; } QLabel { color: #f3f4f6; }")
        else:
            self.setStyleSheet("QMainWindow { background-color: #f1f5f9; } QLabel { color: #1e293b; }")

    def resizeEvent(self, event):
        super().resizeEvent(event)
        self._update_scaled_image()

    def _update_scaled_image(self):
        if hasattr(self, '_orig_pixmap') and not self._orig_pixmap.isNull():
            target_size = self.label.size()
            if target_size.width() > 10 and target_size.height() > 10:
                self.label.setPixmap(self._orig_pixmap.scaled(
                    target_size, Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation))
        else:
            self.label.setText("Failed to load image.")

    def keyPressEvent(self, event):
        if event.key() == Qt.Key.Key_Escape:
            self.close()
        else:
            super().keyPressEvent(event)

    def contextMenuEvent(self, event):
        menu = QMenu(self)
        is_dark = getattr(self.parent(), 'current_theme', 'dark') == 'dark' if self.parent() else True
        act_folder = menu.addAction(get_vector_icon('folder', is_dark), "Open Containing Folder")
        act_folder.triggered.connect(self._open_containing_folder)
        menu.exec(event.globalPos())

    def _open_containing_folder(self):
        if hasattr(self, 'filepath') and self.filepath:
            norm_file = os.path.normpath(os.path.abspath(self.filepath))
            norm_folder = os.path.dirname(norm_file)
            if sys.platform == "win32":
                if os.path.isfile(norm_file):
                    try:
                        subprocess.Popen(f'explorer.exe /select,"{norm_file}"', shell=False)
                        return
                    except Exception:
                        pass
                if os.path.isdir(norm_folder):
                    try:
                        os.startfile(norm_folder)
                        return
                    except Exception:
                        subprocess.Popen(f'explorer.exe "{norm_folder}"', shell=False)
            elif sys.platform == "darwin":
                if os.path.isfile(norm_file):
                    subprocess.Popen(["open", "-R", norm_file])
                elif os.path.isdir(norm_folder):
                    subprocess.Popen(["open", norm_folder])
            else:
                if os.path.isdir(norm_folder):
                    subprocess.Popen(["xdg-open", norm_folder])

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
        
        self.slider = ClickToSeekSlider(Qt.Orientation.Horizontal, self)
        self.slider.setRange(0, 1000)
        self.slider.setCursor(Qt.CursorShape.PointingHandCursor)
        # Single seek path: sliderMoved AND valueChanged+isSliderDown both fired
        # per drag pixel (2x setPosition). valueChanged alone covers both.
        self.slider.valueChanged.connect(self._on_slider_value_changed)
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
        self.player.playbackStateChanged.connect(lambda state: self._update_play_button_text())
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
        if not self.slider.isSliderDown():
            duration = self.player.duration()
            if duration > 0:
                val = int((position / duration) * 1000)
                self.slider.blockSignals(True)
                self.slider.setValue(val)
                self.slider.blockSignals(False)

    def _set_position(self, value):
        duration = self.player.duration()
        if duration > 0:
            pos = int((value / 1000) * duration)
            self.player.setPosition(pos)

    def _on_slider_value_changed(self, value):
        if self.slider.isSliderDown():
            self._set_position(value)

    def keyPressEvent(self, event):
        if event.key() == Qt.Key.Key_Space:
            self._toggle_playback()
        elif event.key() == Qt.Key.Key_M:
            self._toggle_mute()
        elif event.key() == Qt.Key.Key_Left:
            new_pos = max(0, self.player.position() - 5000)
            self.player.setPosition(new_pos)
        elif event.key() == Qt.Key.Key_Right:
            dur = self.player.duration()
            new_pos = min(dur, self.player.position() + 5000) if dur > 0 else self.player.position() + 5000
            self.player.setPosition(new_pos)
        elif event.key() == Qt.Key.Key_Up:
            vol = min(1.0, self.audio_output.volume() + 0.05)
            self.audio_output.setVolume(vol)
        elif event.key() == Qt.Key.Key_Down:
            vol = max(0.0, self.audio_output.volume() - 0.05)
            self.audio_output.setVolume(vol)
        elif event.key() == Qt.Key.Key_Escape:
            self.close()
        else:
            super().keyPressEvent(event)

    def contextMenuEvent(self, event):
        menu = QMenu(self)
        is_dark = getattr(self.parent(), 'current_theme', 'dark') == 'dark' if self.parent() else True
        act_folder = menu.addAction(get_vector_icon('folder', is_dark), "Open Containing Folder")
        act_folder.triggered.connect(self._open_containing_folder)
        menu.exec(event.globalPos())

    def _open_containing_folder(self):
        if hasattr(self, 'filepath') and self.filepath:
            norm_file = os.path.normpath(os.path.abspath(self.filepath))
            norm_folder = os.path.dirname(norm_file)
            if sys.platform == "win32":
                if os.path.isfile(norm_file):
                    try:
                        subprocess.Popen(f'explorer.exe /select,"{norm_file}"', shell=False)
                        return
                    except Exception:
                        pass
                if os.path.isdir(norm_folder):
                    try:
                        os.startfile(norm_folder)
                        return
                    except Exception:
                        subprocess.Popen(f'explorer.exe "{norm_folder}"', shell=False)
            elif sys.platform == "darwin":
                if os.path.isfile(norm_file):
                    subprocess.Popen(["open", "-R", norm_file])
                elif os.path.isdir(norm_folder):
                    subprocess.Popen(["open", norm_folder])
            else:
                if os.path.isdir(norm_folder):
                    subprocess.Popen(["xdg-open", norm_folder])

    def closeEvent(self, event):
        self.player.stop()
        self.player.setSource(QUrl())
        try:
            self.player.setAudioOutput(None)
        except (TypeError, RuntimeError):
            pass
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
        
        self.btn_random_mode = QPushButton(self.controls_widget)
        self.btn_random_mode.setFixedSize(30, 30)
        self.btn_random_mode.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_random_mode.clicked.connect(self.launch_random_discovery_player)
        self.btn_random_mode.setIcon(get_vector_icon('shuffle', is_dark))
        self.btn_random_mode.setToolTip("Random Discovery Player (R)")
        self.btn_random_mode.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        buttons_layout.addWidget(self.btn_random_mode)

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
        pos_sec = max(0, int(position)) // 1000
        dur_sec = max(0, int(duration)) // 1000
        pos_str = f"{pos_sec // 60:02d}:{pos_sec % 60:02d}"
        dur_str = f"{dur_sec // 60:02d}:{dur_sec % 60:02d}"
        self.time_label.setText(f"{pos_str} / {dur_str}")

    def _on_slider_moved(self, value):
        duration = self.player.duration()
        if duration > 0:
            pos = int(value * duration / 1000)
            self.player.setPosition(pos)


    def contextMenuEvent(self, event):
        is_dark = getattr(self.parent_window, 'current_theme', 'dark') == 'dark' if self.parent_window else True
        menu = QMenu(self)
        act_shuffle = menu.addAction(get_vector_icon('shuffle', is_dark), "🎲 Random Discovery Player (R)")
        act_shuffle.triggered.connect(self.launch_random_discovery_player)
        menu.addSeparator()
        act_play = menu.addAction(get_vector_icon('play', is_dark), "Play / Pause (Space)")
        act_play.triggered.connect(self._toggle_playback)
        act_mute = menu.addAction(get_vector_icon('mute', is_dark), "Mute / Unmute (M)")
        act_mute.triggered.connect(self._toggle_mute)
        act_fs = menu.addAction(get_vector_icon('preview', is_dark), "Toggle Fullscreen (F)")
        act_fs.triggered.connect(self.toggle_fullscreen)
        menu.addSeparator()
        act_folder = menu.addAction(get_vector_icon('folder', is_dark), "Open Containing Folder")
        act_folder.triggered.connect(self._open_containing_folder)
        menu.exec(event.globalPos())

    def _open_containing_folder(self):
        if hasattr(self, 'filepath') and self.filepath:
            norm_file = os.path.normpath(os.path.abspath(self.filepath))
            norm_folder = os.path.dirname(norm_file)
            if sys.platform == "win32":
                if os.path.isfile(norm_file):
                    try:
                        subprocess.Popen(f'explorer.exe /select,"{norm_file}"', shell=False)
                        return
                    except Exception:
                        pass
                if os.path.isdir(norm_folder):
                    try:
                        os.startfile(norm_folder)
                        return
                    except Exception:
                        subprocess.Popen(f'explorer.exe "{norm_folder}"', shell=False)
            elif sys.platform == "darwin":
                if os.path.isfile(norm_file):
                    subprocess.Popen(["open", "-R", norm_file])
                elif os.path.isdir(norm_folder):
                    subprocess.Popen(["open", norm_folder])
            else:
                if os.path.isdir(norm_folder):
                    subprocess.Popen(["xdg-open", norm_folder])

    def launch_random_discovery_player(self):
        self.player.pause()
        parent_win = self.parent_window
        candidate_pool = []
        if parent_win and hasattr(parent_win, 'video_tab') and parent_win.video_tab:
            for info in getattr(parent_win.video_tab, 'media_infos', []):
                if getattr(info, 'media_type', '') == 'video' and os.path.exists(info.filepath):
                    candidate_pool.append(info.filepath)
        if not candidate_pool:
            folder = os.path.dirname(self.filepath)
            if os.path.isdir(folder):
                try:
                    for entry in os.scandir(folder):
                        if entry.is_file() and os.path.splitext(entry.name)[1].lower() in VIDEO_EXTENSIONS:
                            candidate_pool.append(entry.path)
                except Exception:
                    pass
        if not candidate_pool:
            candidate_pool = [self.filepath]
        self.close()
        shuffle_win = RandomShufflePlayerWindow(candidate_pool, initial_file=self.filepath, parent=parent_win)
        if parent_win:
            if not hasattr(parent_win, '_native_players'):
                parent_win._native_players = []
            prune_native_players(parent_win)
            parent_win._native_players.append(shuffle_win)
        shuffle_win.show()

    def keyPressEvent(self, event):
        if event.key() == Qt.Key.Key_R:
            self.launch_random_discovery_player()
            return
        elif event.key() == Qt.Key.Key_Space:
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
        try:
            self.player.setVideoOutput(None)
            self.player.setAudioOutput(None)
        except (TypeError, RuntimeError):
            pass
        super().closeEvent(event)


class RandomShufflePlayerWindow(QMainWindow):
    """Hidden Discovery Video Player.
    
    Plays random videos from random timestamps with:
    - Interactive seek slider with time display
    - Previous and Next buttons navigating with a full history stack
    - Jump Time button to re-roll timestamp on the currently playing video
    - Distinctive futuristic HUD overlay (Cyberpunk/Nebula styled)
    - Full keyboard navigation and auto-hiding controls
    """
    def __init__(self, video_pool: list[str], initial_file: str = None, parent=None):
        super().__init__(parent)
        self.parent_window = parent
        self.setWindowFlags(Qt.WindowType.Window)
        self.setAttribute(Qt.WidgetAttribute.WA_DeleteOnClose)
        self.resize(980, 560)
        
        # Deduplicate pool
        seen = set()
        self.video_pool = []
        for v in (video_pool or []):
            if isinstance(v, str) and os.path.isfile(v):
                norm = os.path.normcase(os.path.normpath(v))
                if norm not in seen:
                    seen.add(norm)
                    self.video_pool.append(v)
        if not self.video_pool and initial_file and os.path.isfile(initial_file):
            self.video_pool = [initial_file]
            
        # History list: [{'filepath': str, 'start_pos_ms': int, 'saved_pos_ms': int, 'duration_ms': int, 'title': str}]
        self.history = []
        self.history_index = -1
        self.pending_random_seek = False
        self.pending_seek_target_ms = None
        self._current_filepath = ""

        # Controls auto-hide timer
        self.controls_timer = QTimer(self)
        self.controls_timer.setSingleShot(True)
        self.controls_timer.timeout.connect(self._hide_controls_if_idle)
        
        self._build_ui()
        self._setup_player()
        
        # Start initial playback
        if initial_file and os.path.isfile(initial_file):
            self._load_video_clip(initial_file, pick_random_time=True, record_new_history=True)
        else:
            self.play_random_next(force_new=True)

    def _build_ui(self):
        is_dark = getattr(self.parent_window, 'current_theme', 'dark') == 'dark' if self.parent_window else True
        self.setWindowTitle("MediaFlow — 🎲 Random Discovery Stream")
        
        central = QWidget(self)
        central.setStyleSheet("background: #07060f;" if is_dark else "background: #0f172a;")
        self.setCentralWidget(central)
        
        layout = QVBoxLayout(central)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)
        
        # ─── Top HUD Header Bar ───
        self.header_bar = QWidget(central)
        self.header_bar.setFixedHeight(44)
        self.header_bar.setStyleSheet(
            "background: rgba(11, 9, 24, 0.92); border-bottom: 1px solid rgba(34, 211, 238, 0.3);" if is_dark else
            "background: rgba(248, 250, 252, 0.95); border-bottom: 1px solid #cbd5e1;"
        )
        header_layout = QHBoxLayout(self.header_bar)
        header_layout.setContentsMargins(14, 0, 14, 0)
        header_layout.setSpacing(10)
        
        # Pill Badge
        badge = QLabel("🎲 RANDOM STREAM", self.header_bar)
        badge.setStyleSheet(
            "background: rgba(34, 211, 238, 0.15); color: #22d3ee; border: 1px solid rgba(34, 211, 238, 0.5); "
            "border-radius: 6px; padding: 3px 8px; font-weight: bold; font-size: 10px; letter-spacing: 1px;"
        )
        header_layout.addWidget(badge)
        
        # Title Label
        self.title_label = QLabel("Loading...", self.header_bar)
        self.title_label.setStyleSheet(
            "color: #ececf4; font-weight: bold; font-size: 13px;" if is_dark else
            "color: #0f172a; font-weight: bold; font-size: 13px;"
        )
        self.title_label.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Preferred)
        header_layout.addWidget(self.title_label, 1)
        
        # Metadata Pill
        self.meta_label = QLabel("", self.header_bar)
        self.meta_label.setStyleSheet("color: #a78bfa; font-size: 11px; font-weight: 600;" if is_dark else "color: #6366f1; font-size: 11px; font-weight: 600;")
        header_layout.addWidget(self.meta_label)
        
        # History Counter
        self.history_label = QLabel("Track 1 / 1", self.header_bar)
        self.history_label.setFont(_mono_font(9, bold=True))
        self.history_label.setStyleSheet("color: #22d3ee; padding: 2px 6px; background: rgba(34, 211, 238, 0.1); border-radius: 4px;")
        header_layout.addWidget(self.history_label)
        
        layout.addWidget(self.header_bar)
        
        # ─── Video Display Widget ───
        self.video_widget = DoubleClickVideoWidget(central)
        self.video_widget.double_clicked.connect(self.toggle_fullscreen)
        self.video_widget.mouse_moved.connect(self.show_controls_temporarily)
        layout.addWidget(self.video_widget, 1)
        
        # ─── Bottom HUD Controls ───
        self.controls_widget = QWidget(central)
        self.controls_widget.setFixedHeight(76)
        self.controls_widget.setStyleSheet(
            "background: qlineargradient(x1:0, y1:0, x2:0, y2:1, stop:0 rgba(17, 14, 38, 0.96), stop:1 rgba(7, 6, 15, 0.98)); "
            "border-top: 1px solid rgba(139, 92, 246, 0.35);" if is_dark else
            "background: rgba(248, 250, 252, 0.98); border-top: 1px solid #cbd5e1;"
        )
        controls_layout = QVBoxLayout(self.controls_widget)
        controls_layout.setContentsMargins(16, 6, 16, 8)
        controls_layout.setSpacing(6)
        
        # Row 1: Seek Slider + Time display
        seek_row = QHBoxLayout()
        seek_row.setContentsMargins(0, 0, 0, 0)
        seek_row.setSpacing(12)
        
        self.seek_slider = ClickToSeekSlider(Qt.Orientation.Horizontal, self.controls_widget)
        self.seek_slider.setRange(0, 1000)
        self.seek_slider.setCursor(Qt.CursorShape.PointingHandCursor)
        self.seek_slider.setFixedHeight(14)
        self.seek_slider.setStyleSheet("""
            QSlider::groove:horizontal {
                height: 6px;
                background: rgba(139, 92, 246, 0.25);
                border-radius: 3px;
            }
            QSlider::sub-page:horizontal {
                background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #8b5cf6, stop:1 #22d3ee);
                border-radius: 3px;
            }
            QSlider::handle:horizontal {
                background: #22d3ee;
                border: 2px solid #ffffff;
                width: 14px;
                margin-top: -4px;
                margin-bottom: -4px;
                border-radius: 7px;
            }
            QSlider::handle:horizontal:hover {
                background: #67e8f9;
                border: 2px solid #22d3ee;
            }
        """)
        seek_row.addWidget(self.seek_slider, 1)
        
        self.time_label = QLabel("00:00 / 00:00", self.controls_widget)
        self.time_label.setFont(_mono_font(9, bold=True))
        self.time_label.setFixedWidth(115)
        self.time_label.setAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
        self.time_label.setStyleSheet("color: #ececf4;" if is_dark else "color: #0f172a;")
        seek_row.addWidget(self.time_label)
        controls_layout.addLayout(seek_row)
        
        # Row 2: Control Buttons
        btn_row = QHBoxLayout()
        btn_row.setContentsMargins(0, 0, 0, 0)
        btn_row.setSpacing(10)
        
        # Prev Button
        self.btn_prev = QPushButton(self.controls_widget)
        self.btn_prev.setFixedSize(34, 30)
        self.btn_prev.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_prev.setIcon(get_vector_icon('prev', is_dark))
        self.btn_prev.setToolTip("Previous in History (P / Left)")
        self.btn_prev.clicked.connect(self.play_history_prev)
        self.btn_prev.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        btn_row.addWidget(self.btn_prev)
        
        # Play / Pause
        self.btn_play = QPushButton(self.controls_widget)
        self.btn_play.setFixedSize(36, 30)
        self.btn_play.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_play.setIcon(get_vector_icon('play', is_dark))
        self.btn_play.setToolTip("Play / Pause (Space)")
        self.btn_play.clicked.connect(self._toggle_playback)
        self.btn_play.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        apply_glow(self.btn_play, "#22d3ee", radius=14, alpha=100)
        btn_row.addWidget(self.btn_play)
        
        # Next Button
        self.btn_next = QPushButton(self.controls_widget)
        self.btn_next.setFixedSize(34, 30)
        self.btn_next.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_next.setIcon(get_vector_icon('next', is_dark))
        self.btn_next.setToolTip("Next Random Video & Timestamp (N / Right)")
        self.btn_next.clicked.connect(lambda: self.play_random_next(force_new=False))
        self.btn_next.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        btn_row.addWidget(self.btn_next)
        
        # Jump Time button
        self.btn_jump_time = QPushButton(" 🎲 Jump Time", self.controls_widget)
        self.btn_jump_time.setFixedHeight(30)
        self.btn_jump_time.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_jump_time.setIcon(get_vector_icon('shuffle', is_dark))
        self.btn_jump_time.setToolTip("Jump to a new random timestamp in this video (J / R)")
        self.btn_jump_time.clicked.connect(self.jump_random_time_current)
        self.btn_jump_time.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.btn_jump_time.setStyleSheet(
            "QPushButton { background: rgba(34, 211, 238, 0.12); color: #22d3ee; border: 1px solid rgba(34, 211, 238, 0.4); "
            "border-radius: 6px; font-weight: 600; padding: 0 10px; } "
            "QPushButton:hover { background: rgba(34, 211, 238, 0.25); border-color: #22d3ee; }"
        )
        btn_row.addWidget(self.btn_jump_time)
        
        # Shuffle New Video button
        self.btn_force_shuffle = QPushButton(" 🔀 New Video", self.controls_widget)
        self.btn_force_shuffle.setFixedHeight(30)
        self.btn_force_shuffle.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_force_shuffle.setIcon(get_vector_icon('sync', is_dark))
        self.btn_force_shuffle.setToolTip("Always pick a new random video from pool (Shift+N)")
        self.btn_force_shuffle.clicked.connect(lambda: self.play_random_next(force_new=True))
        self.btn_force_shuffle.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        self.btn_force_shuffle.setStyleSheet(
            "QPushButton { background: rgba(139, 92, 246, 0.15); color: #c4b5fd; border: 1px solid rgba(139, 92, 246, 0.4); "
            "border-radius: 6px; font-weight: 600; padding: 0 10px; } "
            "QPushButton:hover { background: rgba(139, 92, 246, 0.28); border-color: #a78bfa; }"
        )
        btn_row.addWidget(self.btn_force_shuffle)
        
        # Audio controls
        btn_row.addSpacing(10)
        self.btn_mute = QPushButton(self.controls_widget)
        self.btn_mute.setFixedSize(30, 30)
        self.btn_mute.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_mute.clicked.connect(self._toggle_mute)
        self.btn_mute.setIcon(get_vector_icon('unmute', is_dark))
        self.btn_mute.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        btn_row.addWidget(self.btn_mute)
        
        self.volume_slider = QSlider(Qt.Orientation.Horizontal, self.controls_widget)
        self.volume_slider.setRange(0, 100)
        self.volume_slider.setValue(70)
        self.volume_slider.setFixedWidth(85)
        self.volume_slider.setCursor(Qt.CursorShape.PointingHandCursor)
        self.volume_slider.valueChanged.connect(self._on_volume_changed)
        self.volume_slider.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        btn_row.addWidget(self.volume_slider)
        
        btn_row.addStretch()
        
        # Pool size counter
        self.pool_label = QLabel(f"Pool: {len(self.video_pool)} videos", self.controls_widget)
        self.pool_label.setStyleSheet("color: #8e8aa8; font-size: 11px;")
        btn_row.addWidget(self.pool_label)
        
        # Fullscreen button
        self.btn_fullscreen = QPushButton(self.controls_widget)
        self.btn_fullscreen.setFixedSize(30, 30)
        self.btn_fullscreen.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_fullscreen.clicked.connect(self.toggle_fullscreen)
        self.btn_fullscreen.setIcon(get_vector_icon('preview', is_dark))
        self.btn_fullscreen.setToolTip("Toggle Fullscreen (F)")
        self.btn_fullscreen.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        btn_row.addWidget(self.btn_fullscreen)
        
        controls_layout.addLayout(btn_row)
        layout.addWidget(self.controls_widget)
        
        # Mouse tracking & event filters for auto-hiding
        self._enable_mouse_tracking_recursive(central)
        self.setMouseTracking(True)
        central.installEventFilter(self)
        for child in central.findChildren(QWidget):
            child.installEventFilter(self)

    def _setup_player(self):
        is_dark = getattr(self.parent_window, 'current_theme', 'dark') == 'dark' if self.parent_window else True
        self.player = QMediaPlayer(self)
        self.audio_output = QAudioOutput(self)
        self.player.setAudioOutput(self.audio_output)
        self.player.setVideoOutput(self.video_widget)
        
        self.player.positionChanged.connect(self._on_player_position_changed)
        self.player.durationChanged.connect(self._on_player_duration_changed)
        self.player.playbackStateChanged.connect(self._on_player_state_changed)
        self.player.mediaStatusChanged.connect(self._on_media_status_changed)
        self.seek_slider.valueChanged.connect(self._on_slider_moved)
        
        global_mute = getattr(self.parent_window, 'global_mute', False) if self.parent_window else False
        self.audio_output.setMuted(global_mute)
        self.audio_output.setVolume(0.7)
        self.btn_mute.setIcon(get_vector_icon('mute' if global_mute else 'unmute', is_dark))

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
                self.volume_slider.setValue(min(100, self.volume_slider.value() + 5))
            elif delta < 0:
                self.volume_slider.setValue(max(0, self.volume_slider.value() - 5))
            self.show_controls_temporarily()
            return True
        return super().eventFilter(watched, event)

    def show_controls_temporarily(self):
        self.setCursor(Qt.CursorShape.ArrowCursor)
        self.controls_widget.show()
        self.header_bar.show()
        if self.isFullScreen():
            self.controls_timer.start(2500)

    def _hide_controls_if_idle(self):
        if self.isFullScreen():
            self.controls_widget.hide()
            self.header_bar.hide()
            self.setCursor(Qt.CursorShape.BlankCursor)

    def toggle_fullscreen(self):
        if self.isFullScreen():
            self.showNormal()
            self.controls_widget.show()
            self.header_bar.show()
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
        if self.pending_random_seek and duration > 0:
            self.pending_random_seek = False
            target_pos = self._calc_random_time(duration)
            self.player.setPosition(target_pos)
            if 0 <= self.history_index < len(self.history):
                self.history[self.history_index]['start_pos_ms'] = target_pos
                self.history[self.history_index]['saved_pos_ms'] = target_pos
                self.history[self.history_index]['duration_ms'] = duration
        elif self.pending_seek_target_ms is not None and duration > 0:
            target = min(duration - 500, max(0, self.pending_seek_target_ms))
            self.pending_seek_target_ms = None
            self.player.setPosition(target)

    def _on_media_status_changed(self, status):
        if status in (QMediaPlayer.MediaStatus.LoadedMedia, QMediaPlayer.MediaStatus.BufferedMedia):
            dur = self.player.duration()
            if self.pending_random_seek and dur > 0:
                self.pending_random_seek = False
                target_pos = self._calc_random_time(dur)
                self.player.setPosition(target_pos)
                if 0 <= self.history_index < len(self.history):
                    self.history[self.history_index]['start_pos_ms'] = target_pos
                    self.history[self.history_index]['saved_pos_ms'] = target_pos
                    self.history[self.history_index]['duration_ms'] = dur
            elif self.pending_seek_target_ms is not None and dur > 0:
                target = min(dur - 500, max(0, self.pending_seek_target_ms))
                self.pending_seek_target_ms = None
                self.player.setPosition(target)

    def _update_time_label(self, position, duration):
        pos_sec = max(0, int(position)) // 1000
        dur_sec = max(0, int(duration)) // 1000
        pos_str = f"{pos_sec // 60:02d}:{pos_sec % 60:02d}"
        dur_str = f"{dur_sec // 60:02d}:{dur_sec % 60:02d}"
        self.time_label.setText(f"{pos_str} / {dur_str}")

    def _on_slider_moved(self, value):
        duration = self.player.duration()
        if duration > 0:
            pos = int(value * duration / 1000)
            self.player.setPosition(pos)

    def _calc_random_time(self, duration_ms: int) -> int:
        if duration_ms > 12000:
            min_pos = int(duration_ms * 0.05)
            max_pos = int(duration_ms * 0.85)
            return random.randint(min_pos, max_pos)
        elif duration_ms > 3000:
            return random.randint(500, duration_ms - 1000)
        return 0

    def _load_video_clip(self, filepath: str, target_time_ms: int = None, pick_random_time: bool = False, record_new_history: bool = True):
        self._current_filepath = filepath
        self.title_label.setText(os.path.basename(filepath))
        self.setWindowTitle(f"MediaFlow — 🎲 {os.path.basename(filepath)}")
        
        # Check if duration is known beforehand from parent tab MediaInfo
        known_duration_ms = 0
        if self.parent_window and hasattr(self.parent_window, 'video_tab') and self.parent_window.video_tab:
            for info in getattr(self.parent_window.video_tab, 'media_infos', []):
                if getattr(info, 'filepath', '') == filepath:
                    if getattr(info, 'duration_seconds', 0) > 0:
                        known_duration_ms = int(info.duration_seconds * 1000)
                    res = getattr(info, 'resolution_tag', '')
                    dims = f"{getattr(info, 'width', 0)}x{getattr(info, 'height', 0)}" if getattr(info, 'width', 0) > 0 else ""
                    self.meta_label.setText(f"[{res} {dims}]" if res or dims else "")
                    break

        if target_time_ms is not None:
            self.pending_seek_target_ms = target_time_ms
            self.pending_random_seek = False
            start_pos = target_time_ms
        elif pick_random_time:
            if known_duration_ms > 0:
                start_pos = self._calc_random_time(known_duration_ms)
                self.pending_seek_target_ms = start_pos
                self.pending_random_seek = False
            else:
                self.pending_random_seek = True
                self.pending_seek_target_ms = None
                start_pos = 0
        else:
            self.pending_seek_target_ms = None
            self.pending_random_seek = False
            start_pos = 0

        if record_new_history:
            entry = {
                'filepath': filepath,
                'start_pos_ms': start_pos,
                'saved_pos_ms': start_pos,
                'duration_ms': known_duration_ms,
                'title': os.path.basename(filepath)
            }
            # Truncate future history if branched
            if self.history_index < len(self.history) - 1:
                self.history = self.history[:self.history_index + 1]
            self.history.append(entry)
            self.history_index = len(self.history) - 1

        self._update_history_ui()
        
        self.player.setSource(QUrl.fromLocalFile(filepath))
        self.player.play()
        if start_pos > 0:
            QTimer.singleShot(150, lambda: self._apply_initial_seek(start_pos))

    def _apply_initial_seek(self, target_ms: int):
        if self.player and self.player.playbackState() != QMediaPlayer.PlaybackState.StoppedState:
            dur = self.player.duration()
            if dur > 0:
                self.player.setPosition(min(dur - 500, max(0, target_ms)))

    def _update_history_ui(self):
        total = len(self.history)
        current = self.history_index + 1 if total > 0 else 0
        self.history_label.setText(f"Track {current} / {total}")
        self.btn_prev.setEnabled(self.history_index > 0)

    def play_random_next(self, force_new: bool = False):
        if 0 <= self.history_index < len(self.history):
            self.history[self.history_index]['saved_pos_ms'] = self.player.position()

        if not force_new and self.history_index < len(self.history) - 1:
            # Advance in existing history forward
            self.history_index += 1
            entry = self.history[self.history_index]
            self._load_video_clip(entry['filepath'], target_time_ms=entry['saved_pos_ms'], pick_random_time=False, record_new_history=False)
            return

        # Pick new random video from pool
        if not self.video_pool:
            return
        
        if len(self.video_pool) > 1:
            choices = [v for v in self.video_pool if v != self._current_filepath]
            chosen = random.choice(choices if choices else self.video_pool)
        else:
            chosen = self.video_pool[0]

        self._load_video_clip(chosen, pick_random_time=True, record_new_history=True)

    def play_history_prev(self):
        if self.history_index <= 0:
            return
        if 0 <= self.history_index < len(self.history):
            self.history[self.history_index]['saved_pos_ms'] = self.player.position()
        
        self.history_index -= 1
        entry = self.history[self.history_index]
        self._load_video_clip(entry['filepath'], target_time_ms=entry['saved_pos_ms'], pick_random_time=False, record_new_history=False)

    def jump_random_time_current(self):
        if not self._current_filepath:
            return
        dur = self.player.duration()
        if dur > 0:
            new_pos = self._calc_random_time(dur)
            self.player.setPosition(new_pos)
            if 0 <= self.history_index < len(self.history):
                self.history[self.history_index]['saved_pos_ms'] = new_pos

    def keyPressEvent(self, event):
        key = event.key()
        if key == Qt.Key.Key_Space:
            self._toggle_playback()
            self.show_controls_temporarily()
        elif key in (Qt.Key.Key_N, Qt.Key.Key_Right):
            if event.modifiers() & Qt.KeyboardModifier.ControlModifier:
                new_pos = min(self.player.duration(), self.player.position() + 10000)
                self.player.setPosition(new_pos)
            else:
                self.play_random_next(force_new=bool(event.modifiers() & Qt.KeyboardModifier.ShiftModifier))
            self.show_controls_temporarily()
        elif key in (Qt.Key.Key_P, Qt.Key.Key_Left):
            if event.modifiers() & Qt.KeyboardModifier.ControlModifier:
                new_pos = max(0, self.player.position() - 10000)
                self.player.setPosition(new_pos)
            else:
                self.play_history_prev()
            self.show_controls_temporarily()
        elif key in (Qt.Key.Key_J, Qt.Key.Key_R):
            self.jump_random_time_current()
            self.show_controls_temporarily()
        elif key == Qt.Key.Key_F:
            self.toggle_fullscreen()
        elif key == Qt.Key.Key_Escape:
            if self.isFullScreen():
                self.toggle_fullscreen()
        elif key == Qt.Key.Key_M:
            self._toggle_mute()
            self.show_controls_temporarily()
        elif key == Qt.Key.Key_Up:
            self.volume_slider.setValue(min(100, self.volume_slider.value() + 5))
            self.show_controls_temporarily()
        elif key == Qt.Key.Key_Down:
            self.volume_slider.setValue(max(0, self.volume_slider.value() - 5))
            self.show_controls_temporarily()
        elif key == Qt.Key.Key_BracketLeft:
            new_pos = max(0, self.player.position() - 5000)
            self.player.setPosition(new_pos)
            self.show_controls_temporarily()
        elif key == Qt.Key.Key_BracketRight:
            new_pos = min(self.player.duration(), self.player.position() + 5000)
            self.player.setPosition(new_pos)
            self.show_controls_temporarily()
        else:
            super().keyPressEvent(event)

    def contextMenuEvent(self, event):
        is_dark = getattr(self.parent_window, 'current_theme', 'dark') == 'dark' if self.parent_window else True
        menu = QMenu(self)
        act_next = menu.addAction(get_vector_icon('next', is_dark), "Next Random Video (N)")
        act_next.triggered.connect(lambda: self.play_random_next(force_new=False))
        act_prev = menu.addAction(get_vector_icon('prev', is_dark), "Previous Video in History (P)")
        act_prev.setEnabled(self.history_index > 0)
        act_prev.triggered.connect(self.play_history_prev)
        act_jump = menu.addAction(get_vector_icon('shuffle', is_dark), "Jump to Random Timestamp (J / R)")
        act_jump.triggered.connect(self.jump_random_time_current)
        menu.addSeparator()
        act_play = menu.addAction(get_vector_icon('play', is_dark), "Play / Pause (Space)")
        act_play.triggered.connect(self._toggle_playback)
        act_mute = menu.addAction(get_vector_icon('mute', is_dark), "Mute / Unmute (M)")
        act_mute.triggered.connect(self._toggle_mute)
        act_fs = menu.addAction(get_vector_icon('preview', is_dark), "Toggle Fullscreen (F)")
        act_fs.triggered.connect(self.toggle_fullscreen)
        menu.addSeparator()
        act_folder = menu.addAction(get_vector_icon('folder', is_dark), "Open Containing Folder")
        act_folder.triggered.connect(self._open_containing_folder)
        menu.exec(event.globalPos())

    def _open_containing_folder(self):
        if hasattr(self, '_current_filepath') and self._current_filepath:
            norm_file = os.path.normpath(os.path.abspath(self._current_filepath))
            norm_folder = os.path.dirname(norm_file)
            if sys.platform == "win32":
                if os.path.isfile(norm_file):
                    try:
                        subprocess.Popen(f'explorer.exe /select,"{norm_file}"', shell=False)
                        return
                    except Exception:
                        pass
                if os.path.isdir(norm_folder):
                    try:
                        os.startfile(norm_folder)
                        return
                    except Exception:
                        subprocess.Popen(f'explorer.exe "{norm_folder}"', shell=False)
            elif sys.platform == "darwin":
                if os.path.isfile(norm_file):
                    subprocess.Popen(["open", "-R", norm_file])
                elif os.path.isdir(norm_folder):
                    subprocess.Popen(["open", norm_folder])
            else:
                if os.path.isdir(norm_folder):
                    subprocess.Popen(["xdg-open", norm_folder])

    def closeEvent(self, event):
        self.controls_timer.stop()
        self.player.stop()
        self.player.setSource(QUrl())
        try:
            self.player.setVideoOutput(None)
            self.player.setAudioOutput(None)
        except (TypeError, RuntimeError):
            pass
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
        # Use true application top-level window (MainWindow)
        main_win = parent_window.window() if parent_window else self.window()
        is_dark = getattr(main_win, 'current_theme', 'dark') == 'dark' if main_win else True
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
        
        global_mute = getattr(main_win, 'global_mute', False) if main_win else False
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
        main_win = self.parent_window.window() if self.parent_window else self.window()
        is_dark = getattr(main_win, 'current_theme', 'dark') == 'dark' if main_win else True
        self.btn_mute.setIcon(get_vector_icon('mute' if not is_muted else 'unmute', is_dark))

    def _on_volume_changed(self, value):
        self.audio_output.setVolume(value / 100.0)
        if value > 0 and self.audio_output.isMuted():
            self._toggle_mute()

    def _on_player_state_changed(self, state):
        main_win = self.parent_window.window() if self.parent_window else self.window()
        is_dark = getattr(main_win, 'current_theme', 'dark') == 'dark' if main_win else True
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
        pos_sec = max(0, int(position)) // 1000
        dur_sec = max(0, int(duration)) // 1000
        pos_str = f"{pos_sec // 60:02d}:{pos_sec % 60:02d}"
        dur_str = f"{dur_sec // 60:02d}:{dur_sec % 60:02d}"
        self.time_label.setText(f"{pos_str} / {dur_str}")

    def _on_slider_moved(self, value):
        duration = self.player.duration()
        if duration > 0:
            pos = int(value * duration / 1000)
            self.player.setPosition(pos)

    def cleanup(self):
        """Release player resources (mirrors _ComparisonPane.cleanup)."""
        try:
            self.player.stop()
        except (TypeError, RuntimeError):
            pass
        try:
            self.player.setSource(QUrl())
        except (TypeError, RuntimeError):
            pass
        try:
            self.player.setVideoOutput(None)
            self.player.setAudioOutput(None)
        except (TypeError, RuntimeError):
            pass


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
            try:
                sp.cleanup()
            except (TypeError, RuntimeError):
                pass
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

        is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark' if self.window() else True
        self.is_dark = is_dark
        btn_delete = QPushButton("Delete File")
        btn_delete.setObjectName("btnDelete")
        btn_delete.setIcon(get_vector_icon('delete', is_dark))
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
            self.seek_slider.valueChanged.connect(self._on_seek)  # FIX: sliderMoved never fires for click-to-seek
            slider_row.addWidget(self.seek_slider, 1)

            self.time_label = QLabel("00:00 / 00:00")
            self.time_label.setStyleSheet("font-family: monospace; font-size: 10px; color: #a78bfa;")
            slider_row.addWidget(self.time_label)
            ctrls.addLayout(slider_row)

            btns_row = QHBoxLayout()
            self.btn_play = QPushButton()
            self.btn_play.setIcon(get_vector_icon('play', is_dark))
            self.btn_play.setIconSize(QSize(14, 14))
            self.btn_play.setFixedSize(28, 28)
            self.btn_play.setCursor(Qt.CursorShape.PointingHandCursor)
            self.btn_play.clicked.connect(self._toggle_playback)
            btns_row.addWidget(self.btn_play)

            self.btn_mute = QPushButton()
            self.btn_mute.setIcon(get_vector_icon('unmute', is_dark))
            self.btn_mute.setIconSize(QSize(14, 14))
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
            icon_lbl = QLabel()
            icon_lbl.setAlignment(Qt.AlignmentFlag.AlignCenter)
            media_icon_name = 'audio' if info.media_type == 'audio' else ('pdf' if info.media_type == 'pdf' else 'image')
            icon_lbl.setPixmap(get_vector_icon(media_icon_name, is_dark).pixmap(48, 48))
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
        # Audio panes create their player above with no source yet — load it
        # here. Video panes already loaded + paused on their first frame, so
        # re-setting the source would be redundant. Image/PDF panes have NO
        # player at all: the old unguarded block raised AttributeError here
        # (crash on "Compare" for any two images).
        if self.player is not None and info.media_type != 'video':
            try:
                self.player.stop()
                self.player.setSource(QUrl())
                self.player.setSource(QUrl.fromLocalFile(info.filepath))
            except (TypeError, RuntimeError):
                pass

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
        _, parsed_rating = parse_naming_format(info.filename, getattr(info, 'media_type', None))
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
        is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark' if self.window() else True
        diff_style = "color: #fbbf24; font-weight: bold; background: rgba(245, 158, 11, 0.15); border-radius: 4px; padding: 1px 4px;"
        same_color = "#e0e0e0" if is_dark else "#0f172a"
        same_style = f"color: {same_color}; font-weight: normal; background: transparent; padding: 1px 4px;"

        # Resolution
        my_res = (self.info.width, self.info.height)
        other_res = (other_info.width, other_info.height)
        self.lbl_res.setStyleSheet(diff_style if my_res != other_res and (my_res[0] or other_res[0]) else same_style)

        # Size
        self.lbl_size.setStyleSheet(diff_style if self.info.size_bytes != other_info.size_bytes else same_style)

        # Duration (safe float handling for image/PDF/NoneType duration)
        dur1_val = getattr(self.info, 'duration_seconds', 0) or 0.0
        dur2_val = getattr(other_info, 'duration_seconds', 0) or 0.0
        dur1 = round(float(dur1_val), 1)
        dur2 = round(float(dur2_val), 1)
        self.lbl_dur.setStyleSheet(diff_style if dur1 != dur2 and (dur1 > 0 or dur2 > 0) else same_style)

        # Rating (parsed from filename convention)
        _, r1 = parse_naming_format(self.info.filename, getattr(self.info, 'media_type', None))
        _, r2 = parse_naming_format(other_info.filename, getattr(other_info, 'media_type', None))
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
        is_dark = getattr(self, 'is_dark', True)
        self.btn_mute.setIcon(get_vector_icon('mute' if not is_muted else 'unmute', is_dark))

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
            self.seek_slider.blockSignals(True)
            self.seek_slider.setValue(int((pos / dur) * 1000))
            self.seek_slider.blockSignals(False)
        if self.time_label:
            self.time_label.setText(f"{self._format_ms(pos)} / {self._format_ms(dur)}")

    def _on_duration_changed(self, dur):
        pos = self.player.position() if self.player else 0
        if self.time_label:
            self.time_label.setText(f"{self._format_ms(pos)} / {self._format_ms(dur)}")

    def _on_playback_state_changed(self, state):
        if self.btn_play:
            is_dark = getattr(self, 'is_dark', True)
            self.btn_play.setIcon(get_vector_icon('pause' if state == QMediaPlayer.PlaybackState.PlayingState else 'play', is_dark))

    def _format_ms(self, ms: int) -> str:
        s = max(0, ms // 1000)
        return f"{s // 60:02d}:{s % 60:02d}"

    def cleanup(self):
        if self.player:
            self.player.stop()
            self.player.setSource(QUrl())
            try:
                self.player.setVideoOutput(None)
                self.player.setAudioOutput(None)
            except (TypeError, RuntimeError):
                pass


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
        is_dark = getattr(self.parent_tab.window(), 'current_theme', 'dark') == 'dark' if (self.parent_tab and self.parent_tab.window()) else True
        top_bar = QHBoxLayout()
        top_bar.setSpacing(10)

        self.btn_sync = QPushButton("Synced Playback")
        self.btn_sync.setObjectName("btnWatch")
        self.btn_sync.setIcon(get_vector_icon('sync', is_dark))
        self.btn_sync.setCheckable(True)
        is_both_videos = (info_left.media_type == 'video' and info_right.media_type == 'video')
        self.btn_sync.setChecked(is_both_videos)
        self.btn_sync.setEnabled(is_both_videos)
        top_bar.addWidget(self.btn_sync)

        self.btn_swap = QPushButton("Swap Sides")
        self.btn_swap.setIcon(get_vector_icon('sync', is_dark))
        self.btn_swap.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_swap.clicked.connect(self._swap_sides)
        top_bar.addWidget(self.btn_swap)

        top_bar.addStretch()

        btn_keep_both = QPushButton("Keep Both (Close)")
        btn_keep_both.setIcon(get_vector_icon('check', is_dark))
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
        current_sizes = self.splitter.sizes()

        self.pane_left.cleanup()
        self.pane_right.cleanup()

        self.info_left, self.info_right = self.info_right, self.info_left
        self.setWindowTitle(f"MediaFlow — Comparison: {self.info_left.filename} vs {self.info_right.filename}")

        # Unparent old panes immediately from splitter before deleteLater
        old_left = self.pane_left
        old_right = self.pane_right
        old_left.setParent(None)
        old_right.setParent(None)
        old_left.deleteLater()
        old_right.deleteLater()

        self.pane_left = _ComparisonPane(self.info_left, "Left File", is_left=True, parent_window=self)
        self.pane_right = _ComparisonPane(self.info_right, "Right File", is_left=False, parent_window=self)

        self.pane_left.delete_requested.connect(self._delete_file)
        self.pane_right.delete_requested.connect(self._delete_file)

        self.splitter.addWidget(self.pane_left)
        self.splitter.addWidget(self.pane_right)
        self.splitter.setSizes(current_sizes if sum(current_sizes) > 0 else [600, 600])

        self.pane_left.highlight_diffs(self.info_right)
        self.pane_right.highlight_diffs(self.info_left)

    def _restore_pane_after_failed_delete(self, pane, info: MediaInfo):
        """Re-attach media outputs detached by cleanup() so the pane is usable again."""
        if pane is None or pane.player is None:
            return
        try:
            if pane.video_widget is not None:
                pane.player.setVideoOutput(pane.video_widget)
            if pane.audio_output is not None:
                pane.player.setAudioOutput(pane.audio_output)
            pane.player.setSource(QUrl.fromLocalFile(info.filepath))
        except (TypeError, RuntimeError):
            pass

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

        # Cleanup players first to release file locks
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
            # Restore playback if deletion failed: cleanup() detached the
            # video/audio outputs — re-attach them, not just the source, or the
            # panes stay black for the rest of the window's life.
            self._restore_pane_after_failed_delete(self.pane_left, self.info_left)
            self._restore_pane_after_failed_delete(self.pane_right, self.info_right)
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
    def __init__(self, row: int, info, label, thumb_width: int, thumb_height: int):
        super().__init__()
        self.row = row
        self.info = info
        self.label = label
        self.tw_ = thumb_width
        self.th_ = thumb_height
        self.signals = _ThumbnailWorkerSignals()
        # Auto-delete so the runnable is cleaned up after run() finishes
        self.setAutoDelete(True)

    @pyqtSlot()
    def run(self):
        try:
            image = generate_thumbnail(self.info.filepath, self.info.media_type, width=self.tw_, height=self.th_)
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
        # Generation of the tab's table when this worker was queued; results
        # from a previous generation (after Clear/reload) are dropped by the
        # handler instead of resurrecting rows into the fresh table.
        self.watch_generation = 0

    @pyqtSlot()
    def run(self):
        info = None
        try:
            info = MediaInfo(self.filepath, self.media_type)
            if info is not None:
                info.watch_generation = self.watch_generation
        except Exception as e:
            logger.warning("Watch metadata extraction failed for %s: %s", self.filepath, e)
        try:
            self.signals.ready.emit(info)
        except RuntimeError:
            pass

class SkeletonThumbLabel(QLabel):
    """Thumbnail placeholder with a subtle shimmer sweep while loading.

    Falls back to a static block under reduced-motion; renders normally
    once a real pixmap is set (timer self-stops).

    All pending cells share ONE class-level timer. Previously every pending
    cell ran its own 20 Hz QTimer + full paintEvent — during bulk scans that
    meant hundreds of concurrent timers and repaints scaling with library size.
    """

    _shimmer_refs = {}   # id(label) -> weakref, labels currently animating
    _shimmer_timer = None

    def __init__(self, parent=None):
        super().__init__(parent)
        self._phase = 0.0

    @classmethod
    def _ensure_shimmer_timer(cls):
        if cls._shimmer_timer is None:
            cls._shimmer_timer = QTimer()
            cls._shimmer_timer.setInterval(50)
            cls._shimmer_timer.timeout.connect(cls._advance_all)
        return cls._shimmer_timer

    @classmethod
    def _advance_all(cls):
        dead = []
        for key, ref in list(cls._shimmer_refs.items()):
            w = ref()
            if w is None:
                dead.append(key)
                continue
            try:
                w._advance()
            except RuntimeError:
                # C++ object already deleted (grid cleared mid-animation)
                dead.append(key)
        for key in dead:
            cls._shimmer_refs.pop(key, None)
        if not cls._shimmer_refs and cls._shimmer_timer is not None:
            cls._shimmer_timer.stop()

    def _register_shimmer(self):
        cls = SkeletonThumbLabel
        existing = cls._shimmer_refs.get(id(self))
        if existing is not None and existing() is not None:
            return  # already animating
        cls._shimmer_refs[id(self)] = weakref.ref(self)
        cls._ensure_shimmer_timer().start()

    def _unregister_shimmer(self):
        SkeletonThumbLabel._shimmer_refs.pop(id(self), None)

    def _advance(self):
        pm = self.pixmap()
        if (pm is not None and not pm.isNull()) or bool(self.text()):
            self._unregister_shimmer()
            return
        self._phase = (self._phase + 0.045) % 1.0
        self.update()

    def stop_shimmer(self, fallback_text: str = None):
        self._unregister_shimmer()
        if fallback_text is not None:
            self.setText(fallback_text)
        self.update()

    def start_shimmer(self):
        w = self.window()
        reduced = bool(getattr(w, 'reduced_motion', False)) if w is not None else False
        if reduced:
            # Accessibility: static placeholder, no animation
            if not self.text():
                self.setText(self.property("emoji") or "…")
            return
        self._register_shimmer()

    def paintEvent(self, event):
        pm = self.pixmap()
        if pm is not None and not pm.isNull():
            super().paintEvent(event)
            return
        if self.text():
            super().paintEvent(event)
            return
        w = self.window()
        is_dark = True
        if w is not None and hasattr(w, 'current_theme'):
            is_dark = (w.current_theme == 'dark')
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        rect = QRectF(self.rect().adjusted(1, 1, -1, -1))
        painter.setPen(Qt.PenStyle.NoPen)
        base = QColor("#1A1734") if is_dark else QColor("#E7E9F2")
        painter.setBrush(base)
        painter.drawRoundedRect(rect, 8, 8)
        # Moving highlight sweep
        sweep_w = max(40.0, rect.width() * 0.35)
        x = rect.left() - sweep_w + self._phase * (rect.width() + 2 * sweep_w)
        grad = QLinearGradient(x, 0.0, x + sweep_w, 0.0)
        _acc = getattr(w, 'theme_accent', None)
        if _acc:
            hi = QColor(_acc)
            hi.setAlpha(42 if is_dark else 30)
        else:
            hi = QColor(139, 92, 246, 42) if is_dark else QColor(99, 102, 241, 30)
        grad.setColorAt(0.0, QColor(0, 0, 0, 0))
        grad.setColorAt(0.5, hi)
        grad.setColorAt(1.0, QColor(0, 0, 0, 0))
        painter.setBrush(QBrush(grad))
        painter.drawRoundedRect(rect, 8, 8)
        painter.end()


class EmptyStateWidget(QWidget):
    """Beginner-friendly empty state: what to do next + one glowing CTA.

    Shown as view-stack page 2 whenever a tab has no rows.
    """

    ADD_METHODS = {'video': '_add_video_folder', 'image': '_add_image_folder',
                   'audio': '_add_audio_folder', 'pdf': '_add_pdf_folder',
                   'all': '_on_shortcut_open_folder'}

    def __init__(self, media_type: str, parent=None):
        super().__init__(parent)
        self.media_type = media_type
        lay = QVBoxLayout(self)
        lay.setAlignment(Qt.AlignmentFlag.AlignCenter)
        lay.setSpacing(10)

        self.icon_lbl = QLabel()
        self.icon_lbl.setAlignment(Qt.AlignmentFlag.AlignCenter)
        icon = get_vector_icon('folder', True)
        self.icon_lbl.setPixmap(icon.pixmap(128, 128))
        lay.addWidget(self.icon_lbl)
        lay.addSpacing(8)

        self.title_lbl = QLabel("Your library is empty")
        self.title_lbl.setObjectName("emptyTitle")
        self.title_lbl.setAlignment(Qt.AlignmentFlag.AlignCenter)
        lay.addWidget(self.title_lbl)

        self.sub_lbl = QLabel("Drop a folder anywhere in the window, or click below to add one.")
        self.sub_lbl.setObjectName("emptySub")
        self.sub_lbl.setAlignment(Qt.AlignmentFlag.AlignCenter)
        lay.addWidget(self.sub_lbl)

        self.cta_btn = QPushButton("＋  Add Folder")
        self.cta_btn.setObjectName("btnSelectFolder")
        self.cta_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        self.cta_btn.setFixedHeight(44)
        self.cta_btn.setMinimumWidth(200)
        method = self.ADD_METHODS.get(media_type, '_add_video_folder')
        self.cta_btn.clicked.connect(lambda: self._trigger(method))
        lay.addWidget(self.cta_btn, 0, Qt.AlignmentFlag.AlignCenter)
        lay.addSpacing(6)

        self.steps_lbl = QLabel("1. Add folder    →    2. Edit Name / Rating    →    3. Process All   (Ctrl+Z undoes everything)")
        self.steps_lbl.setObjectName("emptySteps")
        self.steps_lbl.setAlignment(Qt.AlignmentFlag.AlignCenter)
        lay.addWidget(self.steps_lbl)

    def _trigger(self, method_name: str):
        w = self.window()
        if w is not None:
            fn = getattr(w, method_name, None) or getattr(w, '_add_video_folder', None)
            if callable(fn):
                fn()

    def update_theme(self, is_dark: bool):
        w = self.window()
        accent = getattr(w, 'theme_accent', None) if w is not None else None
        if not accent:
            accent = Nebula.ACCENT if is_dark else Nebula.ACCENT_L
        apply_glow(self.cta_btn, accent, 26, 90)
        if hasattr(self, 'icon_lbl') and self.icon_lbl:
            icon = get_vector_icon('folder', is_dark)
            self.icon_lbl.setPixmap(icon.pixmap(128, 128))


def _make_toolbar_divider() -> QFrame:
    sep = QFrame()
    sep.setFrameShape(QFrame.Shape.VLine)
    sep.setFrameShadow(QFrame.Shadow.Plain)
    sep.setObjectName("vDivider")
    sep.setFixedWidth(1)
    sep.setFixedHeight(22)
    return sep


# ═══ FEATURE SUITE (v2.5) Dialogs & Helpers ═══

DEFAULT_PRESET_NAME = "Default"

_DASH_PALETTE = ["#a78bfa", "#34d399", "#60a5fa", "#fbbf24",
                 "#f472b6", "#22d3ee", "#f87171", "#a3e635"]


def _norm_key(path: str) -> str:
    """Canonical identity for folder/profile keys (case-insensitive on Windows)."""
    return os.path.normcase(os.path.normpath(path))


class _BarChartWidget(QWidget):
    """Minimal horizontal bar chart painted with QPainter — no QtCharts dependency.

    Theme-aware: pulls is_dark from the attached window on every paint so a
    live theme switch re-renders correctly without extra plumbing.
    """

    def __init__(self, title: str, parent=None):
        super().__init__(parent)
        self._title = title
        self._rows = []  # (label, value, value_text, color)
        self.setMinimumHeight(56)

    def set_data(self, rows):
        cleaned = []
        for label, value, text, color in rows:
            try:
                v = float(value)
            except (TypeError, ValueError):
                continue
            if v > 0:
                cleaned.append((str(label), v, str(text), color))
        cleaned.sort(key=lambda r: r[1], reverse=True)
        self._rows = cleaned
        self.setMinimumHeight(40 + 30 * max(1, len(cleaned)))
        self.update()

    def paintEvent(self, event):
        is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark'
        fg = "#e5e7eb" if is_dark else "#1f2937"
        sub_fg = "#9ca3af" if is_dark else "#64748b"
        track = QColor(255, 255, 255, 22) if is_dark else QColor(15, 23, 42, 14)
        p = QPainter(self)
        try:
            p.setRenderHint(QPainter.RenderHint.Antialiasing)
            rect = self.rect()
            margin = 8
            y = rect.top() + 4
            p.setFont(QFont(BASE_FONT_FAMILY, 10, QFont.Weight.Bold))
            p.setPen(QColor(fg))
            p.drawText(QRect(rect.left() + margin, y, rect.width() - 2 * margin, 18),
                       Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter, self._title)
            y += 26
            if not self._rows:
                p.setFont(QFont(BASE_FONT_FAMILY, 9))
                p.setPen(QColor(sub_fg))
                p.drawText(QRect(rect.left() + margin, y, rect.width() - 2 * margin, 18),
                           Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter, "(no data)")
                return
            fm = p.fontMetrics()
            label_w = 110
            value_w = 85
            bar_left = rect.left() + margin + label_w + 8
            bar_right = rect.right() - margin - value_w - 10
            bar_w = max(10, bar_right - bar_left)
            max_v = self._rows[0][1] or 1.0
            p.setFont(QFont(BASE_FONT_FAMILY, 9))
            for label, value, text, color in self._rows:
                if y + 22 > rect.bottom():
                    break
                p.setPen(QColor(sub_fg))
                elided = fm.elidedText(label, Qt.TextElideMode.ElideRight, label_w)
                p.drawText(QRect(rect.left() + margin, y, label_w, 20),
                           Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter, elided)
                p.setPen(Qt.PenStyle.NoPen)
                p.setBrush(track)
                p.drawRoundedRect(QRectF(bar_left, y + 4, bar_w, 12), 6, 6)
                frac = max(0.04, min(1.0, value / max_v)) if max_v > 0 else 0.04
                p.setBrush(QColor(color))
                p.drawRoundedRect(QRectF(bar_left, y + 4, max(8, bar_w * frac), 12), 6, 6)
                p.setPen(QColor(fg))
                p.drawText(QRect(rect.right() - margin - value_w, y, value_w, 20),
                           Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter, text)
                y += 30
        finally:
            p.end()


class LibraryDashboardDialog(QDialog):
    """Aggregated statistics for every library tab: stat cards + bar charts.

    Read-only and cheap: no hashing, no disk IO beyond what MediaInfo already
    holds — safe to open at any time, even mid-scan.
    """

    def __init__(self, main_win, parent=None):
        super().__init__(parent or main_win)
        self.main_win = main_win
        is_dark = getattr(main_win, 'current_theme', 'dark') == 'dark'
        self.setWindowTitle("Library Dashboard")
        self.setMinimumSize(700, 540)
        self.resize(780, 620)
        root = QVBoxLayout(self)
        root.setContentsMargins(18, 18, 18, 14)
        root.setSpacing(12)

        title = QLabel("Library Dashboard")
        title.setStyleSheet(f"font-size: 16px; font-weight: bold; color: {'#a78bfa' if is_dark else '#4338ca'};")
        root.addWidget(title)

        scroll = QScrollArea()
        scroll.setWidgetResizable(True)
        scroll.setFrameShape(QFrame.Shape.NoFrame)
        content = QWidget()
        content.setStyleSheet("background: transparent;")
        self._content_lay = QVBoxLayout(content)
        self._content_lay.setContentsMargins(2, 2, 2, 2)
        self._content_lay.setSpacing(14)
        scroll.setWidget(content)
        root.addWidget(scroll, 1)

        stats = self._collect()
        total_files = sum(s[1] for s in stats)
        if total_files == 0:
            empty = QLabel("No media loaded yet — add a folder and scan first, then reopen the dashboard.")
            empty.setStyleSheet(f"color: {'#9ca3af' if is_dark else '#64748b'};")
            self._content_lay.addWidget(empty)
        self._build_cards(stats, is_dark)
        self._build_charts(stats, is_dark)
        self._content_lay.addStretch()

        btn_row = QHBoxLayout()
        btn_row.addStretch()
        close_btn = QPushButton("Close")
        close_btn.clicked.connect(self.accept)
        btn_row.addWidget(close_btn)
        root.addLayout(btn_row)

    def _iter_tabs(self):
        pairs = []
        for name, attr in (("Videos", "video_tab"), ("Images", "image_tab"),
                           ("Audio", "audio_tab"), ("PDFs", "pdf_tab")):
            tab = getattr(self.main_win, attr, None)
            if tab is not None and hasattr(tab, 'media_infos'):
                pairs.append((name, tab))
        for name, smart in (getattr(self.main_win, 'smart_folder_tabs', {}) or {}).items():
            if smart is not None and hasattr(smart, 'media_infos'):
                pairs.append((f"Smart: {name}", smart))
        return pairs

    def _collect(self):
        """Per-tab aggregates: (name, files, valid, size_bytes, ready_to_rename, session_renames)."""
        stats = []
        for name, tab in self._iter_tabs():
            infos = list(getattr(tab, 'media_infos', []) or [])
            valid = [i for i in infos if getattr(i, 'is_valid', False)]
            size = sum(int(getattr(i, 'size_bytes', 0) or 0) for i in valid)
            ready = 0
            table = getattr(tab, 'table', None)
            if table is not None and hasattr(tab, 'COL_PREVIEW'):
                for r in range(table.rowCount()):
                    if table.isRowHidden(r):
                        continue
                    it = table.item(r, tab.COL_PREVIEW)
                    if it is not None and it.text().strip() not in ("", "—"):
                        ready += 1
            renames = len(list(getattr(tab, '_rename_history', []) or []))
            stats.append((name, len(infos), len(valid), size, ready, renames))
        return stats

    def _stat_card(self, caption, value_text, is_dark, accent):
        card = QFrame()
        card.setStyleSheet(
            "QFrame { background: %s; border: 1px solid %s; border-radius: 10px; }"
            % ("rgba(255,255,255,0.04)" if is_dark else "rgba(255,255,255,0.70)",
               "rgba(167,139,250,0.25)" if is_dark else "rgba(67,56,202,0.15)")
        )
        lay = QVBoxLayout(card)
        lay.setContentsMargins(12, 10, 12, 10)
        lay.setSpacing(2)
        val = QLabel(str(value_text))
        val.setStyleSheet(f"font-size: 18px; font-weight: bold; color: {accent}; border: none; background: transparent;")
        cap = QLabel(caption)
        cap.setStyleSheet(f"font-size: 11px; color: {'#9ca3af' if is_dark else '#64748b'}; border: none; background: transparent;")
        lay.addWidget(val)
        lay.addWidget(cap)
        return card

    def _build_cards(self, stats, is_dark):
        total_files = sum(s[1] for s in stats)
        total_valid = sum(s[2] for s in stats)
        total_size = sum(s[3] for s in stats)
        total_ready = sum(s[4] for s in stats)
        total_renames = sum(s[5] for s in stats)
        valid_pct = f"{(100.0 * total_valid / total_files):.0f}%" if total_files else "—"
        row = QHBoxLayout()
        row.setSpacing(10)
        cards = [
            ("Total Files", f"{total_files}", "#a78bfa"),
            ("Valid", valid_pct, "#34d399"),
            ("Total Size", format_size(total_size) if total_size else "0 B", "#60a5fa"),
            ("Ready to Rename", f"{total_ready}", "#fbbf24"),
            ("Session Renames", f"{total_renames}", "#f472b6"),
        ]
        for caption, value, accent in cards:
            row.addWidget(self._stat_card(caption, value, is_dark, accent))
        self._content_lay.addLayout(row)

    def _build_charts(self, stats, is_dark):
        if stats:
            files_chart = _BarChartWidget("Files by Library")
            files_chart.set_data([
                (name, files, str(files), _DASH_PALETTE[i % len(_DASH_PALETTE)])
                for i, (name, files, _v, _s, _r, _ss) in enumerate(stats)
            ])
            self._content_lay.addWidget(files_chart)

            size_chart = _BarChartWidget("Size by Library")
            size_chart.set_data([
                (name, size, format_size(size), _DASH_PALETTE[i % len(_DASH_PALETTE)])
                for i, (name, _f, _v, size, _r, _ss) in enumerate(stats)
            ])
            self._content_lay.addWidget(size_chart)

        ext_counts = {}
        tag_counts = {}
        for _name, tab in self._iter_tabs():
            for i in list(getattr(tab, 'media_infos', []) or []):
                if not getattr(i, 'is_valid', False):
                    continue
                ext = os.path.splitext(getattr(i, 'filename', '') or '')[1].lower()
                ext_counts[ext or "(none)"] = ext_counts.get(ext or "(none)", 0) + 1
                for t in (getattr(i, 'tags', None) or []):
                    tag_counts[t] = tag_counts.get(t, 0) + 1
        top_exts = sorted(ext_counts.items(), key=lambda kv: kv[1], reverse=True)[:8]
        if top_exts:
            ext_chart = _BarChartWidget("Top File Types")
            ext_chart.set_data([
                (ext, count, str(count), _DASH_PALETTE[idx % len(_DASH_PALETTE)])
                for idx, (ext, count) in enumerate(top_exts)
            ])
            self._content_lay.addWidget(ext_chart)

        top_tags = sorted(tag_counts.items(), key=lambda kv: kv[1], reverse=True)[:12]
        if top_tags:
            tag_line = "   ·   ".join(f"{t} ({c})" for t, c in top_tags)
            lbl = QLabel(f"<b>Top Tags:</b> {tag_line}")
            lbl.setWordWrap(True)
            lbl.setStyleSheet(f"color: {'#9ca3af' if is_dark else '#64748b'}; font-size: 12px;")
            self._content_lay.addWidget(lbl)


# ─── FEATURE: Rename Preset Manager ───────────────────────────────────────────

class RenamePresetManagerDialog(QDialog):
    """Save / apply / manage naming presets.

    A preset captures the full naming formula: checked fields, their display
    order, the separator and the keep-extension switch — everything the
    Custom Naming Template editor controls.
    """

    def __init__(self, main_win, parent=None):
        super().__init__(parent or main_win)
        self.main_win = main_win
        self.setWindowTitle("Rename Presets")
        self.setMinimumSize(640, 470)
        self.resize(700, 510)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(16, 16, 16, 12)
        lay.setSpacing(10)

        hint = QLabel("A preset captures the full naming formula: checked fields, their order, the separator and the keep-extension switch.")
        hint.setWordWrap(True)
        lay.addWidget(hint)

        body = QHBoxLayout()

        left = QVBoxLayout()
        left_lbl = QLabel("Saved Presets")
        left.addWidget(left_lbl)
        self.preset_list = QListWidget()
        self.preset_list.currentRowChanged.connect(self._on_preset_selected)
        left.addWidget(self.preset_list, 1)
        body.addLayout(left, 5)

        right = QVBoxLayout()
        form = QFormLayout()
        self.name_edit = QLineEdit()
        form.addRow("Preset name:", self.name_edit)

        self.fields_list = QListWidget()
        self.fields_list.setFixedHeight(150)
        checked_now = set(getattr(main_win, 'naming_fields', []) or [])
        ordered_now = getattr(main_win, 'naming_all_fields_ordered', None) or list(DEFAULT_NAMING_FIELDS_ORDERED)
        for f_name in ordered_now:
            item = QListWidgetItem(f_name)
            item.setFlags(item.flags() | Qt.ItemFlag.ItemIsUserCheckable)
            key = FIELD_MAP.get(f_name)
            item.setCheckState(Qt.CheckState.Checked if (key is not None and key in checked_now) else Qt.CheckState.Unchecked)
            self.fields_list.addItem(item)
        form.addRow("Fields (checked = used):", self.fields_list)

        self.sep_edit = QLineEdit(str(getattr(main_win, 'naming_separator', ' ') or ' '))
        self.sep_edit.setMaxLength(8)
        form.addRow("Separator:", self.sep_edit)

        self.keep_ext_cb = QCheckBox("Keep original file extension")
        self.keep_ext_cb.setChecked(bool(getattr(main_win, 'naming_keep_extension', True)))
        form.addRow("", self.keep_ext_cb)
        right.addLayout(form)

        btns = QVBoxLayout()
        is_dark = getattr(main_win, 'current_theme', 'dark') == 'dark' if main_win else True
        self.btn_save_new = QPushButton("Save as New Preset")
        self.btn_save_new.setIcon(get_vector_icon('plus', is_dark))
        self.btn_save_new.clicked.connect(self._save_new)
        self.btn_overwrite = QPushButton("Overwrite Selected")
        self.btn_overwrite.setIcon(get_vector_icon('presets', is_dark))
        self.btn_overwrite.clicked.connect(self._overwrite)
        self.btn_apply = QPushButton("Apply to Naming Editor")
        self.btn_apply.setObjectName("btnSelectFolder")
        self.btn_apply.setIcon(get_vector_icon('check', is_dark))
        self.btn_apply.clicked.connect(self._apply)
        self.btn_rename = QPushButton("Rename…")
        self.btn_rename.setIcon(get_vector_icon('edit', is_dark))
        self.btn_rename.clicked.connect(self._rename_preset)
        self.btn_delete = QPushButton("Delete")
        self.btn_delete.setIcon(get_vector_icon('delete', is_dark))
        self.btn_delete.clicked.connect(self._delete)
        for b in (self.btn_save_new, self.btn_overwrite, self.btn_apply, self.btn_rename, self.btn_delete):
            btns.addWidget(b)
        right.addLayout(btns)
        body.addLayout(right, 7)
        lay.addLayout(body, 1)

        close_row = QHBoxLayout()
        close_row.addStretch()
        close_btn = QPushButton("Close")
        close_btn.clicked.connect(self.accept)
        close_row.addWidget(close_btn)
        lay.addLayout(close_row)

        self._load_presets()

    # ── internals ──
    def _load_presets(self):
        self.preset_list.blockSignals(True)
        self.preset_list.clear()
        for name in sorted((getattr(self.main_win, 'rename_presets', {}) or {}).keys()):
            self.preset_list.addItem(QListWidgetItem(name))
        self.preset_list.blockSignals(False)
        if self.preset_list.count():
            self.preset_list.setCurrentRow(0)
        # Load the selected preset into the editor right away so the dialog
        # never shows editor values that don't match the highlighted item.
        self._on_preset_selected(self.preset_list.currentRow())
        self._sync_buttons()

    def _current_name(self):
        it = self.preset_list.currentItem()
        return it.text() if it is not None else None

    def _sync_buttons(self):
        has = self._current_name() is not None
        for b in (self.btn_overwrite, self.btn_apply, self.btn_rename, self.btn_delete):
            b.setEnabled(has)

    def _on_preset_selected(self, _row):
        name = self._current_name()
        preset = (getattr(self.main_win, 'rename_presets', {}) or {}).get(name or '')
        if not preset:
            return
        self.name_edit.setText(name)
        checked = set(preset.get('fields', []) or [])
        for i in range(self.fields_list.count()):
            item = self.fields_list.item(i)
            key = FIELD_MAP.get(item.text())
            if key is not None:
                item.setCheckState(Qt.CheckState.Checked if key in checked else Qt.CheckState.Unchecked)
        self.sep_edit.setText(str(preset.get('separator', ' ') or ' '))
        self.keep_ext_cb.setChecked(bool(preset.get('keep_extension', True)))
        self._sync_buttons()

    def _collect_editor(self):
        fields = []
        for i in range(self.fields_list.count()):
            item = self.fields_list.item(i)
            if item.checkState() == Qt.CheckState.Checked:
                key = FIELD_MAP.get(item.text())
                if key:
                    fields.append(key)
        sep = re.sub(r'[\\/:*?"<>|]', '', self.sep_edit.text())[:8] or ' '
        ordered = [self.fields_list.item(i).text() for i in range(self.fields_list.count())]
        return {'fields': fields, 'all_ordered': ordered, 'separator': sep,
                'keep_extension': self.keep_ext_cb.isChecked()}

    def _persist(self):
        try:
            if hasattr(self.main_win, '_debounced_save_state'):
                self.main_win._debounced_save_state()
        except Exception:
            logger.exception("preset persist failed")

    # ── actions ──
    def _save_new(self):
        raw = self.name_edit.text().strip()
        if not raw:
            QMessageBox.information(self, "Name Required", "Enter a name for the preset first.")
            return
        presets = getattr(self.main_win, 'rename_presets', {})
        final, n = raw, 2
        while final in presets:
            final = f"{raw} {n}"
            n += 1
        presets[final] = self._collect_editor()
        self._persist()
        self._load_presets()
        for i in range(self.preset_list.count()):
            if self.preset_list.item(i).text() == final:
                self.preset_list.setCurrentRow(i)
                break
        if hasattr(self.main_win, 'show_toast'):
            self.main_win.show_toast(f"Preset '{final}' saved.", 'success')

    def _overwrite(self):
        name = self._current_name()
        if not name:
            return
        self.main_win.rename_presets[name] = self._collect_editor()
        self._persist()
        if hasattr(self.main_win, 'show_toast'):
            self.main_win.show_toast(f"Preset '{name}' updated.", 'success')

    def _apply(self):
        name = self._current_name()
        preset = (getattr(self.main_win, 'rename_presets', {}) or {}).get(name or '')
        if not preset:
            return
        try:
            self.main_win._apply_naming_config(
                preset.get('fields', []), preset.get('all_ordered', []),
                preset.get('separator', ' '), preset.get('keep_extension', True))
            if hasattr(self.main_win, 'show_toast'):
                self.main_win.show_toast(f"Preset '{name}' applied to the naming editor.", 'success')
        except Exception:
            logger.exception("apply preset failed")
            QMessageBox.warning(self, "Apply Failed", "Could not apply this preset.")

    def _rename_preset(self):
        name = self._current_name()
        if not name:
            return
        new_name, ok = QInputDialog.getText(self, "Rename Preset", "New name:", text=name)
        if not ok:
            return
        new_name = new_name.strip()
        if not new_name:
            return
        presets = self.main_win.rename_presets
        if new_name != name and new_name in presets:
            QMessageBox.warning(self, "Name Exists", "A preset with that name already exists.")
            return
        presets[new_name] = presets.pop(name)
        self._persist()
        self._load_presets()

    def _delete(self):
        name = self._current_name()
        if not name:
            return
        reply = QMessageBox.question(self, "Delete Preset", f"Delete preset '{name}'?",
                                     QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
                                     QMessageBox.StandardButton.No)
        if reply != QMessageBox.StandardButton.Yes:
            return
        self.main_win.rename_presets.pop(name, None)
        self._persist()
        self._load_presets()


# ─── FEATURE: Preview Changes (rename diff view) ──────────────────────────────

class PreviewChangesDialog(QDialog):
    """Color-coded old → new rename preview for the active tab.

    Nothing is executed here — the dialog mirrors _on_process_all's target
    computation (including the on-disk conflict flag) and lets the user jump
    to a row or hand off to Process All.
    """

    STATUS_META = {
        'ready': ("Ready", "#34d399"),
        'conflict': ("Conflict", "#f87171"),
        'unchanged': ("Unchanged", "#7c7c9a"),
        'incomplete': ("Incomplete", "#fbbf24"),
    }
    FILTERS = ("All rows", "Ready only", "Conflicts only", "Unchanged only", "Incomplete only")

    def __init__(self, tab, parent=None):
        super().__init__(parent or tab.window())
        self.tab = tab
        self.process_requested = False
        media_names = {'video': 'Videos', 'image': 'Images', 'audio': 'Audio', 'pdf': 'PDFs', 'all': 'Smart Folder'}
        tname = media_names.get(getattr(tab, 'media_type', ''), 'Files')
        self.setWindowTitle(f"Preview Changes — {tname}")
        self.setMinimumSize(760, 480)
        self.resize(880, 560)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(16, 16, 16, 12)
        lay.setSpacing(10)

        self.summary_label = QLabel()
        self.summary_label.setWordWrap(True)
        lay.addWidget(self.summary_label)

        filter_row = QHBoxLayout()
        filter_row.addWidget(QLabel("Show:"))
        self.filter_combo = QComboBox()
        self.filter_combo.addItems(list(self.FILTERS))
        self.filter_combo.currentIndexChanged.connect(lambda _i: self._populate())
        filter_row.addWidget(self.filter_combo)
        filter_row.addStretch()
        lay.addLayout(filter_row)

        self.table = QTableWidget(0, 4)
        self.table.setHorizontalHeaderLabels(["Status", "Current Name", "New Name", "Note"])
        self.table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.table.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.table.verticalHeader().setVisible(False)
        self.table.setAlternatingRowColors(True)
        self.table.itemDoubleClicked.connect(self._on_double_click)
        header = self.table.horizontalHeader()
        header.setSectionResizeMode(0, QHeaderView.ResizeMode.ResizeToContents)
        for col in (1, 2, 3):
            header.setSectionResizeMode(col, QHeaderView.ResizeMode.Stretch)
        lay.addWidget(self.table, 1)

        btn_row = QHBoxLayout()
        is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark' if self.window() else True
        self.btn_process = QPushButton("Process All…")
        self.btn_process.setObjectName("btnSelectFolder")
        self.btn_process.setIcon(get_vector_icon('process', is_dark))
        self.btn_process.clicked.connect(self._request_process)
        btn_row.addWidget(self.btn_process)
        btn_row.addStretch()
        close_btn = QPushButton("Close")
        close_btn.clicked.connect(self.accept)
        btn_row.addWidget(close_btn)
        lay.addLayout(btn_row)

        self._rows_cache = []
        try:
            self._rows_cache = tab._collect_rename_preview()
        except Exception:
            logger.exception("rename preview collection failed")
        self._populate()

    def _populate(self):
        want = {'Ready only': {'ready'}, 'Conflicts only': {'conflict'},
                'Unchanged only': {'unchanged'}, 'Incomplete only': {'incomplete'}}.get(self.filter_combo.currentText())
        rows = [r for r in self._rows_cache if (want is None or r['status'] in want)]
        counts = {}
        for r in self._rows_cache:
            counts[r['status']] = counts.get(r['status'], 0) + 1
        self.summary_label.setText(
            f"{counts.get('ready', 0)} ready to rename  ·  {counts.get('conflict', 0)} conflict(s) with files on disk  ·  "
            f"{counts.get('unchanged', 0)} unchanged  ·  {counts.get('incomplete', 0)} incomplete (missing Name/Rating/Date)"
        )
        self.table.setRowCount(0)
        for r in rows:
            row_idx = self.table.rowCount()
            self.table.insertRow(row_idx)
            label, color = self.STATUS_META.get(r['status'], (r['status'], "#888888"))
            s_item = QTableWidgetItem(label)
            s_item.setForeground(QColor(color))
            c_item = QTableWidgetItem(r['current'])
            n_item = QTableWidgetItem(r['final_target'] or r['target'] or "")
            n_item.setForeground(QColor(color))
            note_item = QTableWidgetItem(r.get('note', ''))
            for it in (s_item, c_item, n_item, note_item):
                it.setData(Qt.ItemDataRole.UserRole, r['row'])
            self.table.setItem(row_idx, 0, s_item)
            self.table.setItem(row_idx, 1, c_item)
            self.table.setItem(row_idx, 2, n_item)
            self.table.setItem(row_idx, 3, note_item)
        self.btn_process.setEnabled((counts.get('ready', 0) + counts.get('conflict', 0)) > 0)

    def _on_double_click(self, item):
        row = item.data(Qt.ItemDataRole.UserRole)
        if row is None:
            return
        try:
            if 0 <= int(row) < self.tab.table.rowCount():
                self.tab.table.selectRow(int(row))
                target = self.tab.table.item(int(row), self.tab.COL_FILENAME)
                if target is not None:
                    self.tab.table.scrollToItem(target, QAbstractItemView.ScrollHint.PositionAtCenter)
        except Exception:
            pass

    def _request_process(self):
        self.process_requested = True
        self.accept()


# ─── FEATURE: Duplicate Resolver ──────────────────────────────────────────────

class DuplicateScanWorker(QThread):
    """Background duplicate grouping — keeps the GUI alive for large libraries.

    exact:  group by size → head-hash inside size groups → full-hash confirm
    visual: perceptual hash + single-linkage grouping (Hamming distance ≤ 5)
    Emits groups as lists of entry indexes into the shared entries list.
    """

    progress = pyqtSignal(int, int, str)
    groups_ready = pyqtSignal(list, int)  # groups, skipped count

    def __init__(self, entries, mode, parent=None):
        super().__init__(parent)
        self.entries = entries
        self.mode = mode
        self._cancelled = False

    def cancel(self):
        self._cancelled = True

    def _emit(self, groups, skipped):
        if not self._cancelled:
            self.groups_ready.emit(groups, skipped)

    def run(self):
        groups, skipped = [], 0
        entries = self.entries
        n = len(entries)
        try:
            if self.mode == 'exact':
                self.progress.emit(0, max(1, n), "Grouping by size…")
                size_groups = {}
                for i, e in enumerate(entries):
                    if self._cancelled:
                        return self._emit(groups, skipped)
                    size_groups.setdefault(int(e.get('size', 0)), []).append(i)
                candidates = [g for g in size_groups.values() if len(g) > 1]
                head_map = {}
                done = 0
                total = max(1, sum(len(g) for g in candidates))
                for g in candidates:
                    if self._cancelled:
                        return self._emit(groups, skipped)
                    for i in g:
                        h = calculate_file_hash(entries[i]['path'], head_only=True)
                        if h:
                            head_map.setdefault(h, []).append(i)
                        else:
                            skipped += 1
                        done += 1
                        self.progress.emit(done, total, "Quick scan (head hash)…")
                confirm_groups = [g for g in head_map.values() if len(g) > 1]
                done = 0
                total2 = max(1, sum(len(g) for g in confirm_groups))
                for g in confirm_groups:
                    if self._cancelled:
                        break
                    full_map = {}
                    for i in g:
                        fh = calculate_file_hash(entries[i]['path'], head_only=False)
                        if fh:
                            full_map.setdefault(fh, []).append(i)
                        else:
                            skipped += 1
                        done += 1
                        self.progress.emit(done, total2, "Confirming (full hash)…")
                    for fg in full_map.values():
                        if len(fg) > 1:
                            groups.append(fg)
            else:
                phashes = {}
                for i, e in enumerate(entries):
                    if self._cancelled:
                        break
                    h = calculate_perceptual_hash(e['path'], e.get('media_type', 'image'))
                    if h:
                        phashes[i] = h
                    else:
                        skipped += 1
                    self.progress.emit(i + 1, max(1, n), "Perceptual hashing…")
                ids = list(phashes.keys())
                visited = set()
                for seed in ids:
                    if self._cancelled:
                        break
                    if seed in visited:
                        continue
                    grp = [seed]
                    visited.add(seed)
                    grew = True
                    while grew and not self._cancelled:
                        grew = False
                        for cand in ids:
                            if cand in visited:
                                continue
                            if any(hamming_distance(phashes[m], phashes[cand]) <= 5 for m in grp):
                                grp.append(cand)
                                visited.add(cand)
                                grew = True
                    if len(grp) > 1:
                        groups.append(grp)
        except Exception:
            logger.exception("duplicate scan worker failed")
        self._emit(groups, skipped)


class DuplicateResolverDialog(QDialog):
    """Scan the active tab for duplicate files and batch-recycle the losers.

    Unlike the per-tab 'Find Dupes' highlighter, this dialog proposes which
    copies to keep (newest / largest / …) and recycles the rest through the
    same audited Recycle-Bin path as the Delete action.
    """

    STRATEGIES = ("Keep Newest", "Keep Oldest", "Keep Largest", "Keep Smallest", "Keep First (A–Z)")

    def __init__(self, tab, parent=None):
        super().__init__(parent or tab.window())
        self.tab = tab
        self.main_win = tab.window()
        self.worker = None
        self.groups = []   # list[list[int]] — indexes into self.entries
        self.entries = []  # {'path','size','mtime','info','media_type'}
        self.setWindowTitle("Duplicate Resolver")
        self.setMinimumSize(720, 540)
        self.resize(850, 600)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(16, 16, 16, 12)
        lay.setSpacing(10)

        top = QHBoxLayout()
        top.addWidget(QLabel("Mode:"))
        self.mode_combo = QComboBox()
        self.mode_combo.addItem("Exact content (MD5)", 'exact')
        self.mode_combo.addItem("Visual similarity (images/videos)", 'visual')
        if getattr(tab, 'media_type', '') in ('audio', 'pdf'):
            try:
                self.mode_combo.model().item(1).setEnabled(False)
            except AttributeError:
                pass  # non-standard combo model — visual mode stays selectable but harmless
        top.addWidget(self.mode_combo)
        is_dark = getattr(self.main_win, 'current_theme', 'dark') == 'dark' if self.main_win else True
        self.btn_scan = QPushButton("Start Scan")
        self.btn_scan.setIcon(get_vector_icon('search', is_dark))
        self.btn_scan.clicked.connect(self._start_scan)
        top.addWidget(self.btn_scan)
        top.addStretch()
        lay.addLayout(top)

        self.progress = QProgressBar()
        self.progress.setVisible(False)
        self.progress.setFormat("%v / %m — %p%")
        self.phase_label = QLabel("")
        self.phase_label.setVisible(False)
        lay.addWidget(self.progress)
        lay.addWidget(self.phase_label)

        mid = QHBoxLayout()
        mid.addWidget(QLabel("Keep strategy:"))
        self.strategy_combo = QComboBox()
        self.strategy_combo.addItems(list(self.STRATEGIES))
        mid.addWidget(self.strategy_combo)
        self.btn_autoselect = QPushButton("Auto-Select Duplicates")
        self.btn_autoselect.setIcon(get_vector_icon('check', is_dark))
        self.btn_autoselect.setEnabled(False)
        self.btn_autoselect.clicked.connect(self._auto_select)
        mid.addWidget(self.btn_autoselect)
        mid.addStretch()
        lay.addLayout(mid)

        self.tree = QTreeWidget()
        self.tree.setColumnCount(2)
        self.tree.setHeaderLabels(["File", "Details"])
        self.tree.header().setSectionResizeMode(0, QHeaderView.ResizeMode.Stretch)
        self.tree.header().setSectionResizeMode(1, QHeaderView.ResizeMode.ResizeToContents)
        lay.addWidget(self.tree, 1)

        self.status_label = QLabel("Collecting files from the active tab…")
        self.status_label.setWordWrap(True)
        lay.addWidget(self.status_label)

        btn_row = QHBoxLayout()
        self.btn_recycle = QPushButton("Recycle Checked")
        self.btn_recycle.setIcon(get_vector_icon('delete', is_dark))
        self.btn_recycle.setEnabled(False)
        self.btn_recycle.clicked.connect(self._recycle_checked)
        btn_row.addWidget(self.btn_recycle)
        btn_row.addStretch()
        close_btn = QPushButton("Close")
        close_btn.clicked.connect(self.reject)
        btn_row.addWidget(close_btn)
        lay.addLayout(btn_row)

        for info in list(getattr(tab, 'media_infos', []) or []):
            if not getattr(info, 'is_valid', False):
                continue
            path = info.filepath
            try:
                size = int(getattr(info, 'size_bytes', 0) or 0)
                mtime = os.path.getmtime(path)
            except OSError:
                continue
            self.entries.append({'path': path, 'size': size, 'mtime': mtime, 'info': info,
                                 'media_type': getattr(info, 'media_type', 'video')})
        if not self.entries:
            self.status_label.setText("No valid files in the active tab — load files first.")
            self.btn_scan.setEnabled(False)
        else:
            self.status_label.setText(f"{len(self.entries)} file(s) ready. Start a scan to find duplicate groups.")

    # ── scanning ──
    def closeEvent(self, event):
        if self.worker is not None and self.worker.isRunning():
            self.worker.cancel()
            self.worker.wait(1000)
        super().closeEvent(event)

    def reject(self):
        if self.worker is not None and self.worker.isRunning():
            self.worker.cancel()
            self.worker.wait(1000)
        super().reject()

    def _start_scan(self):
        if self.worker is not None and self.worker.isRunning():
            return
        mode = self.mode_combo.currentData() or 'exact'
        self.btn_scan.setEnabled(False)
        self.mode_combo.setEnabled(False)
        self.progress.setVisible(True)
        self.progress.setValue(0)
        self.progress.setMaximum(1)
        self.phase_label.setVisible(True)
        self.tree.clear()
        self.btn_autoselect.setEnabled(False)
        self.btn_recycle.setEnabled(False)
        self.status_label.setText("Scanning…")
        self.worker = DuplicateScanWorker(self.entries, mode, self)
        self.worker.progress.connect(self._on_progress)
        self.worker.groups_ready.connect(self._on_groups)
        self.worker.finished.connect(self._on_worker_finished)
        self.worker.start()

    def _on_progress(self, done, total, phase):
        self.progress.setMaximum(max(1, int(total)))
        self.progress.setValue(int(done))
        self.phase_label.setText(phase)

    def _on_worker_finished(self):
        self.progress.setVisible(False)
        self.phase_label.setVisible(False)
        self.btn_scan.setEnabled(True)
        self.mode_combo.setEnabled(True)

    # ── results ──
    def _populate_groups(self, groups, note):
        self.tree.clear()
        for gi, grp in enumerate(groups):
            parent = QTreeWidgetItem([f"Group {gi + 1}   ({len(grp)} files)", ""])
            parent.setFlags(parent.flags() & ~Qt.ItemFlag.ItemIsUserCheckable)
            f = parent.font(0)
            f.setBold(True)
            parent.setFont(0, f)
            self.tree.addTopLevelItem(parent)
            for idx in grp:
                e = self.entries[idx]
                details = f"{format_size(e['size'])}  ·  {datetime.fromtimestamp(e['mtime']).strftime('%Y-%m-%d %H:%M')}"
                child = QTreeWidgetItem([os.path.basename(e['path']), details])
                child.setFlags(child.flags() | Qt.ItemFlag.ItemIsUserCheckable)
                child.setCheckState(0, Qt.CheckState.Unchecked)
                child.setData(0, Qt.ItemDataRole.UserRole, int(idx))
                child.setToolTip(0, e['path'])
                parent.addChild(child)
            parent.setExpanded(True)

    def _on_groups(self, groups, skipped):
        self.groups = [list(g) for g in groups]
        note = f" ({skipped} unreadable file(s) skipped)" if skipped else ""
        if not self.groups:
            self.status_label.setText(f"No duplicates found.{note}")
            return
        total = sum(len(g) for g in self.groups)
        self.status_label.setText(
            f"Found {self.group_label(len(self.groups))} with {total} files.{note} "
            f"Pick a keep strategy, Auto-Select, then Recycle Checked.")
        self._populate_groups(self.groups, note)
        self.btn_autoselect.setEnabled(True)
        self.btn_recycle.setEnabled(True)

    def group_label(self, n):
        return f"{n} duplicate group(s)" if n != 1 else "1 duplicate group"

    # ── actions ──
    def _keeper_index(self, grp):
        strategy = self.strategy_combo.currentText()

        def key(i):
            e = self.entries[i]
            if strategy == "Keep Newest":
                return -e['mtime']
            if strategy == "Keep Oldest":
                return e['mtime']
            if strategy == "Keep Largest":
                return -e['size']
            if strategy == "Keep Smallest":
                return e['size']
            return os.path.basename(e['path']).lower()
        return min(grp, key=key)

    def _auto_select(self):
        if not self.groups:
            return
        for gi, grp in enumerate(self.groups):
            keeper = self._keeper_index(grp)
            parent = self.tree.topLevelItem(gi)
            if parent is None:
                continue
            for ci in range(parent.childCount()):
                child = parent.child(ci)
                idx = child.data(0, Qt.ItemDataRole.UserRole)
                is_keeper = (idx == keeper)
                child.setCheckState(0, Qt.CheckState.Unchecked if is_keeper else Qt.CheckState.Checked)
                f = child.font(0)
                f.setBold(is_keeper)
                child.setFont(0, f)

    def _checked_indexes(self):
        out = []
        for gi in range(self.tree.topLevelItemCount()):
            parent = self.tree.topLevelItem(gi)
            for ci in range(parent.childCount()):
                child = parent.child(ci)
                if child.checkState(0) == Qt.CheckState.Checked:
                    idx = child.data(0, Qt.ItemDataRole.UserRole)
                    if idx is not None:
                        out.append(int(idx))
        return out

    def _recycle_checked(self):
        idxs = self._checked_indexes()
        if not idxs:
            QMessageBox.information(self, "Nothing Selected", "Check the duplicates you want to recycle first.")
            return
        reply = QMessageBox.question(
            self, "Recycle Duplicates",
            f"Send {len(idxs)} file(s) to the Recycle Bin?\n\nKeeper files are not touched.",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No)
        if reply != QMessageBox.StandardButton.Yes:
            return
        tab = self.tab
        # Resolve CURRENT rows by info identity — sort-proof (same approach as Find Dupes)
        id_to_row = {}
        for r in range(tab.table.rowCount()):
            ri = tab._get_row_info(r)
            if ri is not None:
                id_to_row[id(ri)] = r
        was_sorting = tab.table.isSortingEnabled()
        tab.table.setSortingEnabled(False)
        tab._updating_table = True
        recycled, failures = 0, []
        recycled_info_ids = set()
        try:
            rows_to_remove = []
            for idx in idxs:
                e = self.entries[idx]
                info = e['info']
                path = getattr(info, 'filepath', None) or e['path']
                sidecars = find_sidecars(path)
                if send_to_recycle_bin(path):
                    trashed = [path]
                    for sc in sidecars:
                        if send_to_recycle_bin(sc):
                            trashed.append(sc)
                        else:
                            failures.append(f"{os.path.basename(sc)}: could not recycle sidecar")
                    append_rename_audit([(p, "(recycle bin)") for p in trashed], op="delete")
                    row = id_to_row.get(id(info), -1)
                    if row >= 0:
                        rows_to_remove.append(row)
                    recycled_info_ids.add(id(info))
                    recycled += 1
                else:
                    failures.append(f"{os.path.basename(path)}: could not recycle")
            for row in sorted(set(rows_to_remove), reverse=True):
                tab._remove_row_from_list(row)
        finally:
            tab._updating_table = False
            tab.table.setSortingEnabled(was_sorting)
        tab._update_stats()
        if recycled:
            if hasattr(self.main_win, 'show_toast'):
                self.main_win.show_toast(
                    f"{recycled} duplicate file(s) sent to the Recycle Bin." +
                    (f" {len(failures)} problem(s)." if failures else ""), 'success' if not failures else 'warning')
        base_msg = f"{recycled} file(s) recycled."
        if failures:
            base_msg += f" {len(failures)} problem(s): " + "; ".join(failures[:5])
        # Prune recycled entries out of the view
        live_ids = {id(v) for v in (getattr(tab, 'media_infos', []) or [])}
        self.groups = [[i for i in grp if id(self.entries[i]['info']) in live_ids] for grp in self.groups]
        self.groups = [g for g in self.groups if len(g) > 1]
        if self.groups:
            self._populate_groups(self.groups, "")
            self.status_label.setText(base_msg + f"  {len(self.groups)} group(s) remain.")
        else:
            self.tree.clear()
            self.btn_autoselect.setEnabled(False)
            self.btn_recycle.setEnabled(False)
            if failures:
                self.status_label.setText(base_msg)
            else:
                self.status_label.setText("All duplicate groups resolved — no groups remain.")


# ─── FEATURE: Tag Editor (embedded tags with write-back) ──────────────────────

class MediaTagEditorDialog(QDialog):
    """Edit embedded tags and write them back to the files.

    Audio (ID3/Vorbis/MP4) via mutagen's easy API; JPEG EXIF (Artist,
    DateTimeOriginal) via piexif. Files without embedded-tag support are
    reported and skipped — the dialog never touches those files.
    """

    AUDIO_FIELDS = ("title", "artist", "album", "albumartist", "genre", "date", "tracknumber")
    LABELS = {
        'title': "Title:", 'artist': "Artist:", 'album': "Album:", 'albumartist': "Album Artist:",
        'genre': "Genre:", 'date': "Year / Date Taken:", 'tracknumber': "Track #:",
    }

    def __init__(self, infos, parent=None):
        super().__init__(parent)
        self.infos = [i for i in infos if getattr(i, 'is_valid', False)]
        single = len(self.infos) == 1
        self.setWindowTitle(f"Tag Editor — {os.path.basename(self.infos[0].filepath)}" if single else "Tag Editor (batch)")
        self.setMinimumWidth(470)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(16, 16, 16, 12)
        lay.setSpacing(10)

        # Classify files by writable kind
        self.audio_paths, self.image_paths, self.skipped = [], [], []
        for i in self.infos:
            path = i.filepath
            ext = os.path.splitext(path)[1].lower()
            if getattr(i, 'media_type', '') == 'audio':
                self.audio_paths.append(path)
            elif getattr(i, 'media_type', '') == 'image' and ext in ('.jpg', '.jpeg'):
                self.image_paths.append(path)
            else:
                self.skipped.append(path)

        writable = len(self.audio_paths) + len(self.image_paths)
        scope = (f"{len(self.infos)} file(s) selected — {writable} writable "
                 f"({len(self.audio_paths)} audio, {len(self.image_paths)} JPEG)")
        if self.skipped:
            scope += f", {len(self.skipped)} without embedded-tag support (skipped)"
        scope_lbl = QLabel(scope)
        scope_lbl.setWordWrap(True)
        lay.addWidget(scope_lbl)

        if len(self.infos) > 1:
            self.apply_all_cb = QCheckBox("Apply to ALL writable files (batch)")
            self.apply_all_cb.setChecked(True)
            lay.addWidget(self.apply_all_cb)
        else:
            self.apply_all_cb = None

        self._edits = {}
        form = QFormLayout()
        for key in self.AUDIO_FIELDS:
            edit = QLineEdit()
            self._edits[key] = edit
            form.addRow(self.LABELS[key], edit)
        lay.addLayout(form)

        self.status_lbl = QLabel("")
        self.status_lbl.setWordWrap(True)
        lay.addWidget(self.status_lbl)

        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Save | QDialogButtonBox.StandardButton.Cancel)
        self.save_btn = buttons.button(QDialogButtonBox.StandardButton.Save)
        is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark' if self.window() else True
        if self.save_btn:
            self.save_btn.setIcon(get_vector_icon('save', is_dark))
        buttons.accepted.connect(self._save_all)
        buttons.rejected.connect(self.reject)
        lay.addWidget(buttons)

        self._load_tags()

    @staticmethod
    def _parse_date_input(text):
        t = (text or "").strip()
        if not t:
            return None
        for f in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%d %H:%M", "%Y-%m-%d", "%Y:%m:%d %H:%M:%S",
                  "%Y:%m:%d", "%Y/%m/%d", "%Y%m%d", "%Y"):
            try:
                return datetime.strptime(t, f)
            except ValueError:
                continue
        return None

    def _load_tags(self):
        if not self.audio_paths and not self.image_paths:
            self.status_lbl.setText("None of the selected files support embedded tag writing.\n"
                                    "Audio needs mutagen and JPEG needs piexif — install with: pip install mutagen piexif")
            self.status_lbl.setStyleSheet("color: #f87171; font-size: 11px;")
            for e in self._edits.values():
                e.setEnabled(False)
            if self.save_btn is not None:
                self.save_btn.setEnabled(False)
            return
        rep = self.audio_paths[0] if self.audio_paths else self.image_paths[0]
        if self.audio_paths:
            try:
                from mutagen import File as MutagenFile
                mfile = MutagenFile(rep, easy=True)
                if mfile is None:
                    raise ValueError("unsupported audio format for tagging")
                for key in self.AUDIO_FIELDS:
                    vals = mfile.get(key, [])
                    self._edits[key].setText(str(vals[0]) if vals else "")
            except ImportError:
                self.status_lbl.setText("mutagen is not installed — run: pip install mutagen")
                self.status_lbl.setStyleSheet("color: #f87171; font-size: 11px;")
                return
            except Exception as ex:
                logger.warning("tag read failed for %s: %s", rep, ex)
        else:
            self._load_image_tags(rep)
        self.status_lbl.setText(f"Loaded from: {os.path.basename(rep)}")
        self.status_lbl.setStyleSheet("color: #9ca3af; font-size: 11px;")

    def _load_image_tags(self, path):
        try:
            import piexif
        except ImportError:
            self.status_lbl.setText("piexif is not installed — run: pip install piexif")
            self.status_lbl.setStyleSheet("color: #f87171; font-size: 11px;")
            return
        try:
            exif = piexif.load(path)
            artist_b = exif.get('0th', {}).get(piexif.ImageIFD.Artist)
            dto = exif.get('Exif', {}).get(piexif.ExifIFD.DateTimeOriginal)
            if artist_b:
                self._edits['artist'].setText(artist_b.decode('utf-8', 'replace').strip())
            if dto:
                raw = dto.decode('utf-8', 'replace').strip()
                dt = self._parse_date_input(raw)
                if dt is not None:
                    self._edits['date'].setText(dt.strftime("%Y-%m-%d"))
        except Exception as ex:
            logger.warning("EXIF read failed for %s: %s", path, ex)

    def _save_audio(self, path, values):
        try:
            from mutagen import File as MutagenFile
        except ImportError as e:
            raise RuntimeError("mutagen is not installed (pip install mutagen)") from e
        mfile = MutagenFile(path, easy=True)
        if mfile is None:
            raise ValueError("unsupported audio format for tagging")
        for key in self.AUDIO_FIELDS:
            val = values.get(key, "")
            if val:
                mfile[key] = [val]
            else:
                mfile.pop(key, None)  # emptied field clears the tag on purpose
        mfile.save()

    def _save_image(self, path, values, dt):
        try:
            import piexif
        except ImportError as e:
            raise RuntimeError("piexif is not installed (pip install piexif)") from e
        artist = values.get('artist', "")
        try:
            exif = piexif.load(path)
        except Exception:
            exif = {"0th": {}, "Exif": {}, "GPS": {}, "1st": {}, "thumbnail": None}
        exif.setdefault('0th', {})
        exif.setdefault('Exif', {})
        if artist:
            exif['0th'][piexif.ImageIFD.Artist] = artist.encode('utf-8')
        else:
            exif['0th'].pop(piexif.ImageIFD.Artist, None)
        if dt is not None:
            exif['Exif'][piexif.ExifIFD.DateTimeOriginal] = dt.strftime("%Y:%m:%d %H:%M:%S").encode('ascii')
        exif_bytes = piexif.dump(exif)
        piexif.insert(exif_bytes, path)

    def _save_all(self):
        values = {k: self._edits[k].text().strip() for k in self.AUDIO_FIELDS}
        dt = self._parse_date_input(values.get('date', ""))
        if self.apply_all_cb is None or self.apply_all_cb.isChecked():
            targets = list(self.audio_paths) + list(self.image_paths)
        else:
            targets = (list(self.audio_paths) + list(self.image_paths))[:1]
        ok, fail = 0, []
        for path in targets:
            try:
                if path in self.audio_paths:
                    self._save_audio(path, values)
                else:
                    self._save_image(path, values, dt)
                ok += 1
            except Exception as ex:
                fail.append(f"{os.path.basename(path)}: {ex}")
        msg = f"Saved tags to {ok} file(s)."
        if fail:
            msg += f"\n\n{len(fail)} failed:\n" + "\n".join(fail[:8])
        self.status_lbl.setText(msg)
        self.status_lbl.setStyleSheet("color: #34d399; font-size: 11px;" if not fail else "color: #fbbf24; font-size: 11px;")
        if ok:
            main_win = self.window()
            if hasattr(main_win, 'show_toast'):
                main_win.show_toast(f"Tags saved to {ok} file(s)." + (f" {len(fail)} failed." if fail else ""),
                                    'success' if not fail else 'warning')


# ─── FEATURE: Folder Profiles + Auto-watch ────────────────────────────────────

class FolderProfilesDialog(QDialog):
    """Bind source folders to naming presets.

    preset only:  adding that folder auto-applies the preset to the naming editor
    auto_rename:  new files discovered (watch mode) are renamed with the preset
                  automatically — no clicks needed
    """

    def __init__(self, main_win, parent=None):
        super().__init__(parent or main_win)
        self.main_win = main_win
        self.setWindowTitle("Folder Profiles & Auto-watch")
        self.setMinimumSize(760, 430)
        self.resize(830, 470)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(16, 16, 16, 12)
        lay.setSpacing(10)

        hint = QLabel("Bind a source folder to a preset: the preset is applied when the folder is added. "
                      "With 'Auto-rename new files' enabled, files discovered in that folder by watch mode are renamed automatically.")
        hint.setWordWrap(True)
        lay.addWidget(hint)

        add_row = QHBoxLayout()
        add_row.addWidget(QLabel("Folder:"))
        self.folder_combo = QComboBox()
        self.folder_combo.setMinimumWidth(320)
        add_row.addWidget(self.folder_combo, 1)
        is_dark = getattr(main_win, 'current_theme', 'dark') == 'dark' if main_win else True
        self.btn_add = QPushButton("Add Profile")
        self.btn_add.setIcon(get_vector_icon('plus', is_dark))
        self.btn_add.clicked.connect(self._add_profile)
        add_row.addWidget(self.btn_add)
        browse_btn = QPushButton("Browse…")
        browse_btn.setIcon(get_vector_icon('folder', is_dark))
        browse_btn.clicked.connect(self._browse)
        add_row.addWidget(browse_btn)
        lay.addLayout(add_row)

        self.table = QTableWidget(0, 3)
        self.table.setHorizontalHeaderLabels(["Folder", "Preset", "Auto-rename new files"])
        self.table.verticalHeader().setVisible(False)
        self.table.verticalHeader().setDefaultSectionSize(36)
        self.table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        header = self.table.horizontalHeader()
        header.setSectionResizeMode(0, QHeaderView.ResizeMode.Stretch)
        header.setSectionResizeMode(1, QHeaderView.ResizeMode.Interactive)
        self.table.setColumnWidth(1, 220)
        header.setMinimumSectionSize(160)
        header.setSectionResizeMode(2, QHeaderView.ResizeMode.ResizeToContents)
        lay.addWidget(self.table, 1)

        self.status_label = QLabel("")
        self.status_label.setWordWrap(True)
        lay.addWidget(self.status_label)

        btn_row = QHBoxLayout()
        self.btn_remove = QPushButton("Remove Selected")
        self.btn_remove.setIcon(get_vector_icon('delete', is_dark))
        self.btn_remove.clicked.connect(self._remove_selected)
        btn_row.addWidget(self.btn_remove)
        btn_row.addStretch()
        save_btn = QPushButton("Save")
        save_btn.setObjectName("btnSelectFolder")
        save_btn.setIcon(get_vector_icon('save', is_dark))
        save_btn.clicked.connect(self.accept)
        btn_row.addWidget(save_btn)
        cancel_btn = QPushButton("Cancel")
        cancel_btn.clicked.connect(self.reject)
        btn_row.addWidget(cancel_btn)
        lay.addLayout(btn_row)

        self._fill_folder_combo()
        self._load_profiles()

    def _known_folders(self):
        folders = []
        for attr in ('video_tab', 'image_tab', 'audio_tab', 'pdf_tab'):
            tab = getattr(self.main_win, attr, None)
            for d in list(getattr(tab, 'directories', []) or []):
                if d and d not in folders:
                    folders.append(d)
        return folders

    def _fill_folder_combo(self):
        self.folder_combo.clear()
        for d in self._known_folders():
            self.folder_combo.addItem(d)

    def _browse(self):
        d = QFileDialog.getExistingDirectory(self, "Select Folder to Profile")
        if d:
            d = os.path.normpath(d)
            pos = self.folder_combo.findText(d)
            if pos < 0:
                self.folder_combo.addItem(d)
                pos = self.folder_combo.count() - 1
            self.folder_combo.setCurrentIndex(pos)

    def _preset_names(self):
        return sorted((getattr(self.main_win, 'rename_presets', {}) or {}).keys())

    def _make_preset_combo(self, selected=None):
        combo = QComboBox()
        combo.setMinimumWidth(180)
        combo.setMinimumHeight(28)
        combo.addItem("(none)", None)
        for name in self._preset_names():
            combo.addItem(name, name)
        if selected:
            pos = combo.findData(selected)
            if pos >= 0:
                combo.setCurrentIndex(pos)
        return combo

    def _make_checkbox_widget(self, checked: bool = False):
        wrap = QWidget()
        lay = QHBoxLayout(wrap)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setAlignment(Qt.AlignmentFlag.AlignCenter)
        cb = QCheckBox()
        cb.setChecked(checked)
        lay.addWidget(cb)
        return wrap

    def _add_profile(self):
        folder = self.folder_combo.currentText().strip()
        if not folder:
            QMessageBox.information(self, "No Folder", "Pick a folder (or Browse) first.")
            return
        key = _norm_key(folder)
        for r in range(self.table.rowCount()):
            if _norm_key(self.table.item(r, 0).text()) == key:
                self.status_label.setText("That folder already has a profile.")
                return
        row = self.table.rowCount()
        self.table.insertRow(row)
        self.table.setItem(row, 0, QTableWidgetItem(folder))
        self.table.setCellWidget(row, 1, self._make_preset_combo())
        self.table.setCellWidget(row, 2, self._make_checkbox_widget(False))

    def _remove_selected(self):
        rows = sorted({i.row() for i in self.table.selectedIndexes()}, reverse=True)
        for r in rows:
            self.table.removeRow(r)

    def _load_profiles(self):
        profiles = getattr(self.main_win, 'folder_profiles', {}) or {}
        for folder_key, prof in profiles.items():
            row = self.table.rowCount()
            self.table.insertRow(row)
            self.table.setItem(row, 0, QTableWidgetItem(str(folder_key)))
            self.table.setCellWidget(row, 1, self._make_preset_combo(prof.get('preset')))
            self.table.setCellWidget(row, 2, self._make_checkbox_widget(bool(prof.get('auto_rename', False))))

    def accept(self):
        profiles = {}
        for r in range(self.table.rowCount()):
            item = self.table.item(r, 0)
            if item is None:
                continue
            folder = item.text().strip()
            if not folder:
                continue
            combo = self.table.cellWidget(r, 1)
            cb_widget = self.table.cellWidget(r, 2)
            cb = cb_widget.findChild(QCheckBox) if cb_widget else None
            if cb is None and isinstance(cb_widget, QCheckBox):
                cb = cb_widget
            preset = combo.currentData() if combo is not None else None
            auto_val = bool(cb.isChecked()) if cb is not None else False
            profiles[_norm_key(folder)] = {'preset': preset, 'auto_rename': auto_val}
        self.main_win.folder_profiles = profiles
        try:
            self.main_win._debounced_save_state()
        except Exception:
            logger.exception("profiles persist failed")
class OverlayContentContainer(QWidget):
    """Hosts view_stack at 100% width and height, and coordinates floating overlay panels."""
    def __init__(self, media_tab, parent=None):
        super().__init__(parent)
        self.media_tab = media_tab
        self.container_layout = QVBoxLayout(self)
        self.container_layout.setContentsMargins(0, 0, 0, 0)
        self.container_layout.setSpacing(0)

    def resizeEvent(self, event):
        super().resizeEvent(event)
        if hasattr(self.media_tab, '_reposition_side_panel'):
            self.media_tab._reposition_side_panel(animate=False)


class OverlayResizeHandle(QWidget):
    """A narrow grip along the left edge of the overlay panel to drag and resize."""
    def __init__(self, media_tab, parent=None):
        super().__init__(parent)
        self.media_tab = media_tab
        self.setCursor(Qt.CursorShape.SizeHorCursor)
        self.setFixedWidth(12)
        self._dragging = False
        self._hovering = False
        self._start_global_x = 0
        self._start_width = 350
        self.setAttribute(Qt.WidgetAttribute.WA_Hover, True)

    def enterEvent(self, event):
        self._hovering = True
        self.update()
        super().enterEvent(event)

    def leaveEvent(self, event):
        self._hovering = False
        self.update()
        super().leaveEvent(event)

    def paintEvent(self, event):
        if self._hovering or self._dragging:
            from PyQt6.QtGui import QPainter, QColor
            painter = QPainter(self)
            painter.setRenderHint(QPainter.RenderHint.Antialiasing)
            is_dark = getattr(self.media_tab.window(), 'current_theme', 'dark') == 'dark' if self.media_tab.window() else True
            color = QColor(167, 139, 250, 160) if is_dark else QColor(99, 102, 241, 140)
            painter.setPen(Qt.PenStyle.NoPen)
            painter.setBrush(color)
            h = min(48, max(24, int(self.height() * 0.15)))
            y = (self.height() - h) // 2
            painter.drawRoundedRect(4, y, 4, h, 2, 2)
            painter.end()

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self._dragging = True
            self._start_global_x = int(event.globalPosition().x())
            self._start_width = getattr(self.media_tab, '_side_panel_width', 350)
            self.update()
            event.accept()
        else:
            super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if self._dragging:
            delta = self._start_global_x - int(event.globalPosition().x())
            c_w = self.media_tab.content_container.width()
            max_w = max(280, int(c_w * 0.70))
            new_w = max(280, min(max_w, self._start_width + delta))
            self.media_tab._side_panel_width = new_w
            self.media_tab._reposition_side_panel(animate=False)
            event.accept()
        else:
            super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        if self._dragging and event.button() == Qt.MouseButton.LeftButton:
            self._dragging = False
            self.update()
            main_win = self.media_tab.window()
            if main_win and hasattr(main_win, '_debounced_save_state'):
                main_win._debounced_save_state()
            event.accept()
        else:
            super().mouseReleaseEvent(event)


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
    COL_DATE_MOD   = 10   # optional — hidden by default, toggle via header menu
    COL_DATE_CREATED = 11 # optional — hidden by default
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
        # Rows the user explicitly removed ("Remove From List") — watch mode
        # must not resurrect them just because the file still exists on disk.
        self._user_removed_paths: set[str] = set()
        # Modal-safety: while a modal dialog / context menu is open, Qt still
        # delivers timer and queued-signal events, and both the watch poll and
        # an active scan can insert/remove rows — invalidating the row indices
        # the dialog was opened with (led to wrong-file edits and deletes).
        self._modal_depth = 0
        self._deferred_found_infos: list = []
        self._watch_was_active_before_modal = False
        # Bumped on every table clear/reload; late-arriving watch metadata from
        # a previous generation is dropped instead of adding duplicate rows.
        self._watch_generation = 0
        
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

        main_win = self.window()
        is_dark = getattr(main_win, 'current_theme', 'dark') == 'dark' if main_win else True

        self.btn_load = QPushButton("Sync Files")
        self.btn_load.setObjectName("btnLoadFiles")
        self.btn_load.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_load.clicked.connect(self._on_load_files)
        self.btn_load.setEnabled(False)
        self.btn_load.setIcon(get_vector_icon('sync', is_dark))
        self.btn_load.setIconSize(QSize(16, 16))

        self.btn_stop = QPushButton("Stop Loading")
        self.btn_stop.setObjectName("btnStopLoading")
        self.btn_stop.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_stop.clicked.connect(self._on_stop_loading)
        self.btn_stop.setVisible(False)
        self.btn_stop.setIcon(get_vector_icon('stop', is_dark))
        self.btn_stop.setIconSize(QSize(16, 16))

        self.btn_clear = QPushButton("Clear List")
        self.btn_clear.setObjectName("btnClearAll")
        self.btn_clear.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_clear.clicked.connect(self._on_clear)
        self.btn_clear.setVisible(False)
        self.btn_clear.setIcon(get_vector_icon('clear', is_dark))
        self.btn_clear.setIconSize(QSize(16, 16))
        
        self.btn_watch = QPushButton("Watch")
        self.btn_watch.setObjectName("btnWatch")
        self.btn_watch.setCheckable(True)
        self.btn_watch.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_watch.setIcon(get_vector_icon('watch', is_dark))
        self.btn_watch.setIconSize(QSize(16, 16))
        self.btn_watch.toggled.connect(self._toggle_watch)
        
        row1_layout.addWidget(self.btn_load)
        row1_layout.addWidget(self.btn_stop)
        row1_layout.addWidget(self.btn_clear)
        row1_layout.addWidget(self.btn_watch)
        row1_layout.addWidget(_make_toolbar_divider())
        row1_layout.addStretch()

        self.btn_view_mode = QPushButton("Grid View")
        self.btn_view_mode.setObjectName("btnViewMode")
        self.btn_view_mode.setCheckable(True)
        self.btn_view_mode.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_view_mode.clicked.connect(self._toggle_view_mode)
        self.btn_view_mode.setIcon(get_vector_icon('grid', is_dark))
        self.btn_view_mode.setIconSize(QSize(16, 16))

        self.btn_toggle_preview = QPushButton("Inspector")
        self.btn_toggle_preview.setObjectName("btnTogglePreview")
        self.btn_toggle_preview.setCheckable(True)
        self.btn_toggle_preview.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_toggle_preview.clicked.connect(self._toggle_preview)
        self.btn_toggle_preview.setIcon(get_vector_icon('preview', is_dark))
        self.btn_toggle_preview.setIconSize(QSize(16, 16))

        self.btn_toggle_stats = QPushButton("Stats")
        self.btn_toggle_stats.setObjectName("btnToggleStats")
        self.btn_toggle_stats.setCheckable(True)
        self.btn_toggle_stats.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_toggle_stats.clicked.connect(self._toggle_stats)
        self.btn_toggle_stats.setIcon(get_vector_icon('stats', is_dark))
        self.btn_toggle_stats.setIconSize(QSize(16, 16))

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
        filter_panel_vbox = QVBoxLayout(filter_panel)
        filter_panel_vbox.setContentsMargins(12, 8, 12, 8)
        filter_panel_vbox.setSpacing(6)

        filter_row1 = QHBoxLayout()
        filter_row1.setContentsMargins(0, 0, 0, 0)
        filter_row1.setSpacing(10)

        self.search_input = QComboBox()
        self.search_input.setObjectName("searchComboBox")
        self.search_input.setEditable(True)
        self.search_input.setInsertPolicy(QComboBox.InsertPolicy.NoInsert)
        search_edit = self.search_input.lineEdit()
        search_edit.setPlaceholderText("Search by filename, name, rating, or tags...")
        search_edit.setClearButtonEnabled(True)
        search_edit.addAction(get_vector_icon('search', is_dark), QLineEdit.ActionPosition.LeadingPosition)
        search_edit.textChanged.connect(self._on_filter_changed)
        search_edit.returnPressed.connect(self._on_search_return_pressed)
        self.search_input.activated.connect(self._on_search_history_activated)
        self.search_input.setMaxVisibleItems(15)
        self.search_input.text = lambda: self.search_input.currentText()
        filter_row1.addWidget(self.search_input, 3)

        if not self.is_smart_folder:
            self.btn_save_search = QPushButton("")
            self.btn_save_search.setObjectName("btnSaveSearch")
            self.btn_save_search.setFixedSize(28, 28)
            self.btn_save_search.setToolTip("Save search filter as Smart Folder")
            self.btn_save_search.setCursor(Qt.CursorShape.PointingHandCursor)
            self.btn_save_search.clicked.connect(self._on_save_search_clicked)
            self.btn_save_search.setIcon(get_vector_icon('plus', is_dark))
            self.btn_save_search.setIconSize(QSize(16, 16))
            filter_row1.addWidget(self.btn_save_search)

        self.exclude_input = QLineEdit()
        self.exclude_input.setObjectName("excludeInput")
        self.exclude_input.setPlaceholderText("Exclude patterns (e.g. *sample*, temp*)...")
        self.exclude_input.setClearButtonEnabled(True)
        self.exclude_input.addAction(get_vector_icon('stop', is_dark), QLineEdit.ActionPosition.LeadingPosition)
        self.exclude_input.textChanged.connect(self._on_exclude_changed)
        filter_row1.addWidget(self.exclude_input, 2)

        self.filter_result_count_label = QLabel("")
        self.filter_result_count_label.setObjectName("filterResultCount")
        self.filter_result_count_label.setVisible(False)
        filter_row1.addWidget(self.filter_result_count_label)

        self.btn_advanced_filter = QPushButton("Filters")
        self.btn_advanced_filter.setObjectName("btnAdvancedFilter")
        self.btn_advanced_filter.setCheckable(True)
        self.btn_advanced_filter.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_advanced_filter.setIcon(get_vector_icon('filter', is_dark))
        self.btn_advanced_filter.setIconSize(QSize(14, 14))
        self.btn_advanced_filter.toggled.connect(lambda checked: self.advanced_filter_panel.setVisible(checked))
        filter_row1.addWidget(self.btn_advanced_filter)

        filter_panel_vbox.addLayout(filter_row1)

        self.filter_chips_container = QWidget()
        self.filter_chips_layout = QHBoxLayout(self.filter_chips_container)
        self.filter_chips_layout.setContentsMargins(0, 2, 0, 0)
        self.filter_chips_layout.setSpacing(6)
        self.filter_chips_container.setVisible(False)
        filter_panel_vbox.addWidget(self.filter_chips_container)

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
        # Optional metadata columns — off until the user enables them
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
        # Re-apply the active filter after ANY user sort: sorting moves row
        # contents while setRowHidden flags / filtered_rows stay attached to
        # row POSITIONS. Without this, "Process All" and batch edits after a
        # sort operated on files the user had filtered out.
        self.table.horizontalHeader().sortIndicatorChanged.connect(self._on_sort_indicator_changed)
        self.table.itemSelectionChanged.connect(self._on_selection_changed)
        self.table.verticalScrollBar().valueChanged.connect(self._load_visible_widgets)
        self.table.verticalScrollBar().rangeChanged.connect(lambda min_val, max_val: self._load_visible_widgets())
        header.sectionClicked.connect(lambda: QTimer.singleShot(50, self._load_visible_widgets))
        self.view_stack = QStackedWidget()
        self.view_stack.addWidget(self.table)
        self.grid_view = QListWidget()
        self.grid_view.setViewMode(QListWidget.ViewMode.IconMode)
        self.grid_view.setResizeMode(QListWidget.ResizeMode.Adjust)
        self.grid_view.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)
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
        # Nebula: page 2 = beginner empty state (title + glowing Add Folder CTA)
        self.empty_state = EmptyStateWidget(self.media_type, self)
        self.view_stack.addWidget(self.empty_state)
        self.view_stack.setCurrentIndex(2)
        self.content_container = OverlayContentContainer(self)
        self.content_container.container_layout.addWidget(self.view_stack)

        self.side_panel = QStackedWidget(self.content_container)
        self.side_panel.setObjectName("sidePanelStack")
        self.side_panel.setMinimumWidth(280)
        self._side_panel_width = 350
        self._panel_anim = None
        self.content_splitter = None

        self._build_preview_pane()
        self._build_stats_panel()
        self.side_panel.addWidget(self.preview_panel)
        self.side_panel.addWidget(self.stats_panel)
        self.side_panel.setVisible(False)

        # Drop shadow for elevated floating card look
        self._panel_shadow = QGraphicsDropShadowEffect(self.side_panel)
        self._panel_shadow.setBlurRadius(26)
        self._panel_shadow.setOffset(-4, 2)
        self._update_shadow_color()
        self.side_panel.setGraphicsEffect(self._panel_shadow)

        # Drag handle on the left edge of the overlay
        self._panel_resize_handle = OverlayResizeHandle(self, self.content_container)
        self._panel_resize_handle.setVisible(False)

        root_layout.addWidget(self.content_container, 1)
        bottom_layout = QVBoxLayout()
        bottom_layout.setContentsMargins(0, 0, 0, 0)
        bottom_layout.setSpacing(8)
        bottom_row1 = QHBoxLayout()
        bottom_row1.setContentsMargins(0, 0, 0, 0)
        bottom_row1.setSpacing(10)
        self.status_label = QLabel("Ready")
        self.status_label.setObjectName("statusLabelReady")
        # Live selection summary ("N selected · size") for quick bulk sanity
        self.sel_stats_label = QLabel("")
        self.sel_stats_label.setObjectName("folderPathLabel")
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
        bottom_row1.addWidget(self.status_label)
        bottom_row1.addStretch()
        bottom_row1.addWidget(self.sel_stats_label)
        bottom_row1.addWidget(self.btn_undo)
        bottom_row1.addWidget(self.btn_redo)
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
        self.btn_batch_tag = QPushButton("Batch Tag")
        self.btn_batch_tag.setObjectName("btnBatchTag")
        self.btn_batch_tag.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_batch_tag.clicked.connect(self._on_batch_tag)
        self.btn_batch_tag.setEnabled(False)
        self.btn_batch_tag.setIconSize(QSize(16, 16))
        self.btn_relocate = QPushButton("Relocate")
        self.btn_relocate.setObjectName("btnRelocate")
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
        self.btn_process = QPushButton("Process All")
        self.btn_process.setObjectName("btnProcessAll")
        self.btn_process.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_process.setEnabled(False)
        self.btn_process.clicked.connect(self._on_process_all)
        self.btn_process.setToolTip("Process all ready files — applies the naming template and renames them")
        self.btn_process.setIconSize(QSize(18, 18))
        self.btn_undo.setIcon(get_vector_icon('undo', is_dark))
        self.btn_redo.setIcon(get_vector_icon('redo', is_dark))
        self.btn_find_dupes.setIcon(get_vector_icon('duplicate', is_dark))
        self.btn_batch_edit.setIcon(get_vector_icon('edit', is_dark))
        self.btn_batch_tag.setIcon(get_vector_icon('tag', is_dark))
        self.btn_relocate.setIcon(get_vector_icon('relocate', is_dark))
        self.btn_delete.setIcon(get_vector_icon('delete', is_dark))
        self.btn_process.setIcon(get_vector_icon('process', is_dark))
        # Cluster 1: File Operations
        bottom_row2.addWidget(self.btn_find_dupes)
        bottom_row2.addWidget(self.btn_batch_edit)
        bottom_row2.addWidget(self.btn_batch_tag)
        bottom_row2.addWidget(self.btn_relocate)
        bottom_row2.addWidget(self.btn_delete)
        bottom_row2.addWidget(_make_toolbar_divider())
        bottom_row2.addStretch()
        # Cluster 2: Primary CTA
        bottom_row2.addWidget(self.btn_process)
        bottom_layout.addLayout(bottom_row1)
        bottom_layout.addLayout(bottom_row2)
        root_layout.addLayout(bottom_layout)

    def _make_stat_card(self, value: str, label: str) -> QFrame:
        card = QFrame()
        card.setObjectName("statsPanel")
        card.setMinimumWidth(125)
        card.setMinimumHeight(48)
        card.setSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.MinimumExpanding)
        layout = QVBoxLayout(card)
        layout.setContentsMargins(12, 5, 12, 5)
        layout.setSpacing(2)
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
            is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark' if self.window() else True
            self.search_input.addItem(get_vector_icon('clear', is_dark), "Clear Search History")
        self.search_input.setEditText(curr)
        self.search_input.blockSignals(False)

    def _on_search_history_activated(self, index: int):
        text = self.search_input.itemText(index)
        if text in ("Clear Search History", "✕ Clear Search History"):
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

    def _on_sort_indicator_changed(self, *args):
        """Keep hidden-state/filtered_rows in sync with the sorted row order."""
        if self._updating_table:
            return
        self._apply_filter()

    def _enter_modal(self):
        """Pause row-mutating background activity while a modal dialog/menu is open."""
        self._modal_depth += 1
        if self._modal_depth == 1:
            self._watch_was_active_before_modal = self._watch_timer.isActive()
            if self._watch_was_active_before_modal:
                self._watch_timer.stop()

    def _exit_modal(self):
        self._modal_depth = max(0, self._modal_depth - 1)
        if self._modal_depth == 0:
            if self._watch_was_active_before_modal:
                self._watch_was_active_before_modal = False
                self._watch_timer.start()
            # Replay scan results that arrived while the modal blocked row updates
            if self._deferred_found_infos:
                deferred, self._deferred_found_infos = self._deferred_found_infos, []
                for info in deferred:
                    self._on_file_found(info)
                self._apply_filter()
                self._update_stats()
                self._load_visible_widgets()

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
                    _gi = self._grid_item(info)
                    if _gi: _gi.setHidden(True)
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
                _gi = self._grid_item(info)
                if _gi: _gi.setHidden(False)
            else:
                self.table.setRowHidden(row, True)
                _gi = self._grid_item(info)
                if _gi: _gi.setHidden(True)
        self._apply_advanced_filters()
        self._update_filter_chips()
        self._update_stats()
        self._load_visible_widgets()

    def _update_filter_chips(self):
        if not hasattr(self, 'filter_chips_layout') or not self.filter_chips_layout:
            return
        while self.filter_chips_layout.count():
            item = self.filter_chips_layout.takeAt(0)
            w = item.widget()
            if w:
                w.deleteLater()

        chips = []
        # Search chip
        stext = self.search_input.currentText().strip() if hasattr(self.search_input, 'currentText') else self.search_input.text().strip()
        if stext:
            def clear_search():
                if hasattr(self.search_input, 'setEditText'):
                    self.search_input.setEditText("")
                elif hasattr(self.search_input, 'clearEditText'):
                    self.search_input.clearEditText()
                elif hasattr(self.search_input, 'clear'):
                    self.search_input.clear()
                self._apply_filter()
            chips.append((f'"{stext}"', clear_search))

        # Exclude chip
        etext = self.exclude_input.text().strip() if hasattr(self, 'exclude_input') and self.exclude_input else ""
        if etext:
            def clear_exclude():
                self.exclude_input.clear()
                self._apply_filter()
            chips.append((f'Exclude: {etext}', clear_exclude))

        # Resolution chip
        if hasattr(self, 'adv_res') and self.adv_res.currentIndex() > 0:
            def clear_res():
                self.adv_res.setCurrentIndex(0)
                self._filter_timer.start()
            chips.append((self.adv_res.currentText(), clear_res))

        # Rating chip
        if hasattr(self, 'adv_rating') and self.adv_rating.currentIndex() > 0:
            def clear_rating():
                self.adv_rating.setCurrentIndex(0)
                self._filter_timer.start()
            chips.append((self.adv_rating.currentText(), clear_rating))

        # Duration chip
        if hasattr(self, 'adv_dur_min') and hasattr(self, 'adv_dur_max'):
            dmin = self.adv_dur_min.value()
            dmax = self.adv_dur_max.value()
            if dmin > 0 or dmax > 0:
                def clear_dur():
                    self.adv_dur_min.setValue(0)
                    self.adv_dur_max.setValue(0)
                    self._filter_timer.start()
                lbl = f"Dur: {dmin}s–{dmax}s" if (dmin and dmax) else (f"Dur ≥ {dmin}s" if dmin else f"Dur ≤ {dmax}s")
                chips.append((lbl, clear_dur))

        # Size chip
        if hasattr(self, 'adv_size_min') and hasattr(self, 'adv_size_max'):
            smin = self.adv_size_min.value()
            smax = self.adv_size_max.value()
            if smin > 0 or smax > 0:
                unit = self.adv_size_unit.currentText() if hasattr(self, 'adv_size_unit') else "MB"
                def clear_sz():
                    self.adv_size_min.setValue(0)
                    self.adv_size_max.setValue(0)
                    self._filter_timer.start()
                lbl = f"Size: {smin}–{smax} {unit}" if (smin and smax) else (f"Size ≥ {smin} {unit}" if smin else f"Size ≤ {smax} {unit}")
                chips.append((lbl, clear_sz))

        # Date chip
        if hasattr(self, 'adv_date_from') and hasattr(self, 'adv_date_to'):
            d_from = self.adv_date_from.date()
            d_to = self.adv_date_to.date()
            if d_from != self.adv_date_from.minimumDate() or d_to != self.adv_date_to.maximumDate():
                def clear_date():
                    self.adv_date_from.setDate(self.adv_date_from.minimumDate())
                    self.adv_date_to.setDate(self.adv_date_to.maximumDate())
                    self._filter_timer.start()
                chips.append((f"{d_from.toString('yyyy-MM-dd')} to {d_to.toString('yyyy-MM-dd')}", clear_date))

        total_rows = self.table.rowCount()
        matching_rows = len(self.filtered_rows) if hasattr(self, 'filtered_rows') else total_rows
        if chips:
            for text, callback in chips:
                chip_btn = QPushButton(f"{text}  ✕")
                chip_btn.setProperty("class", "filter-chip")
                chip_btn.setCursor(Qt.CursorShape.PointingHandCursor)
                chip_btn.setFixedHeight(24)
                chip_btn.clicked.connect(callback)
                self.filter_chips_layout.addWidget(chip_btn)

            if len(chips) > 1:
                clear_all_btn = QPushButton("Clear all")
                clear_all_btn.setProperty("class", "filter-chip")
                clear_all_btn.setStyleSheet("font-weight: 600; color: #a78bfa;")
                clear_all_btn.setCursor(Qt.CursorShape.PointingHandCursor)
                clear_all_btn.setFixedHeight(24)
                def on_clear_all():
                    if hasattr(self.search_input, 'setEditText'): self.search_input.setEditText("")
                    elif hasattr(self.search_input, 'clear'): self.search_input.clear()
                    if hasattr(self, 'exclude_input'): self.exclude_input.clear()
                    if hasattr(self, '_clear_advanced_filters'): self._clear_advanced_filters()
                    self._apply_filter()
                clear_all_btn.clicked.connect(on_clear_all)
                self.filter_chips_layout.addWidget(clear_all_btn)

            self.filter_chips_layout.addStretch()
            self.filter_chips_container.setVisible(True)
            if total_rows > 0:
                self.filter_result_count_label.setText(f"{matching_rows} of {total_rows} matches")
                self.filter_result_count_label.setVisible(True)
            else:
                self.filter_result_count_label.setVisible(False)
        else:
            self.filter_chips_container.setVisible(False)
            if total_rows > 0 and matching_rows < total_rows:
                self.filter_result_count_label.setText(f"{matching_rows} of {total_rows} matches")
                self.filter_result_count_label.setVisible(True)
            else:
                self.filter_result_count_label.setVisible(False)


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
            
            # Resolution — use the SHORTER side so portrait media classifies
            # correctly (a 1080×1920 portrait video is 1080p, not "Below 480p")
            if res_idx > 0:
                w_ = int(getattr(info, 'width', 0) or 0)
                h_ = int(getattr(info, 'height', 0) or 0)
                dims = [d for d in (w_, h_) if d > 0]
                h = min(dims) if dims else 0
                if h > 0:
                    if res_idx == 1 and h < 4320: keep = False # 8K+
                    elif res_idx == 2 and (h < 2160 or h >= 4320): keep = False # 4K
                    elif res_idx == 3 and (h < 1440 or h >= 2160): keep = False # 1440p
                    elif res_idx == 4 and (h < 1080 or h >= 1440): keep = False # 1080p
                    elif res_idx == 5 and (h < 720 or h >= 1080): keep = False # 720p
                    elif res_idx == 6 and (h < 480 or h >= 720): keep = False # 480p
                    elif res_idx == 7 and h >= 480: keep = False # Below 480p

            # Duration
            d = float(getattr(info, 'duration_seconds', 0) or 0.0)
            if keep and dur_max > 0:
                if d < dur_min or d > dur_max: keep = False
            elif keep and dur_min > 0:
                if d < dur_min: keep = False

            # Modified date range (local time, matches os.stat display)
            if keep and date_active:
                m_ts = float(getattr(info, 'mtime', 0) or 0)
                if m_ts > 0:
                    m_date = QDateTime.fromSecsSinceEpoch(int(m_ts)).date()
                    if m_date < date_from or m_date > date_to:
                        keep = False

            # Size
            s = int(getattr(info, 'size_bytes', 0) or 0)
            if keep and sz_max > 0:
                if s < int(sz_min * sz_multiplier) or s > int(sz_max * sz_multiplier): keep = False
            elif keep and sz_min > 0:
                if s < int(sz_min * sz_multiplier): keep = False

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
                _gi = self._grid_item(info)
                if _gi: _gi.setHidden(True)

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
        self._scan_generation = getattr(self, '_scan_generation', 0) + 1
        cur_gen = self._scan_generation

        # Prune dead threads from _orphaned_scanners
        if hasattr(self, '_orphaned_scanners'):
            self._orphaned_scanners = [s for s in self._orphaned_scanners if s.isRunning()]
        else:
            self._orphaned_scanners = []

        old = getattr(self, 'scanner_thread', None)
        if old is not None and old.isRunning():
            old.requestInterruption()
            for sig in (old.progress, old.file_found, old.scan_complete, old.status_update):
                try:
                    sig.disconnect()
                except (TypeError, RuntimeError):
                    pass
            if not old.wait(2000):
                self._orphaned_scanners.append(old)
                old.finished.connect(old.deleteLater)
        elif old is not None:
            for sig in (old.progress, old.file_found, old.scan_complete, old.status_update):
                try:
                    sig.disconnect()
                except (TypeError, RuntimeError):
                    pass
                
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
        self.scanner_thread.progress.connect(lambda cur, tot, g=cur_gen: self._on_scan_progress(cur, tot) if g == getattr(self, '_scan_generation', 0) else None)
        self.scanner_thread.file_found.connect(lambda info, g=cur_gen: self._on_file_found(info) if g == getattr(self, '_scan_generation', 0) else None)
        self.scanner_thread.scan_complete.connect(lambda tot, g=cur_gen: self._on_scan_complete(tot) if g == getattr(self, '_scan_generation', 0) else None)
        self.scanner_thread.status_update.connect(lambda msg, g=cur_gen: self.status_label.setText(msg) if g == getattr(self, '_scan_generation', 0) else None)
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
            apply_glow(self.btn_watch, getattr(self.window(), 'theme_accent2', None) or Nebula.ACCENT2, 16, 140)  # "live" glow (theme accent)
            self._show_toast(f"Watching {len(self.directories)} folder(s)...", 'success')
        else:
            self._watch_timer.stop()
            apply_glow(self.btn_watch, None)
            self._show_toast("Watch folder disabled.", 'info')

    def _check_for_changes(self):
        if not getattr(self, '_watch_enabled', False) or not self.directories:
            return
        if getattr(self, '_modal_depth', 0) > 0:
            return  # timer paused during modals; belt-and-suspenders guard
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
                            elif entry.is_file(follow_symlinks=True):
                                if entry.name.startswith('.'):
                                    continue  # dotfiles (.DS_Store, .gitignore) are never media
                                ext = os.path.splitext(entry.name)[1].lower()
                                # Match ScannerThread semantics: known extensions
                                # plus extensionless files only ('all' already
                                # unions every supported set).
                                if ext == '' or ext in valid_exts:
                                    full_path = os.path.normpath(entry.path)
                                    norm_case = os.path.normcase(full_path)
                                    if not self._should_exclude(full_path):
                                        current_files[norm_case] = full_path
                        except OSError as e:
                            logger.debug("watch entry failed for %s: %s", getattr(entry, 'path', current_dir), e)
                except OSError as e:
                    logger.debug("watch scandir failed for %s: %s", current_dir, e)

        if not hasattr(self, '_known_files') or not isinstance(self._known_files, dict):
            self._known_files = {os.path.normcase(os.path.normpath(info.filepath)): info.filepath for info in self.media_infos}

        current_keys = set(current_files.keys())
        known_keys = set(self._known_files.keys())

        added_keys = current_keys - known_keys
        removed_keys = known_keys - current_keys

        # Never resurrect rows the user explicitly removed. Prune paths whose
        # files no longer exist so the exclusion set stays bounded.
        if added_keys and self._user_removed_paths:
            added_keys = {k for k in added_keys if k not in self._user_removed_paths}
        if self._user_removed_paths:
            self._user_removed_paths = {k for k in self._user_removed_paths if os.path.exists(k)}

        if not added_keys and not removed_keys:
            return

        # 1. Handle removals safely by table row lookup
        if removed_keys:
            rows_to_remove = []
            removed_paths = []
            for r in range(self.table.rowCount()):
                row_info = self._get_row_info(r)
                if row_info and os.path.normcase(os.path.normpath(row_info.filepath)) in removed_keys:
                    rows_to_remove.append(r)
                    removed_paths.append(row_info.filepath)

            if removed_paths:
                self._release_file_locks(removed_paths)

            was_sorting = self.table.isSortingEnabled()
            self.table.setSortingEnabled(False)
            for r in sorted(rows_to_remove, reverse=True):
                self._remove_row_from_list(r)
            self.table.setSortingEnabled(was_sorting)
            self._update_selection_buttons_and_preview()

        # 2. Handle additions — extract metadata OFF the GUI thread (each
        # MediaInfo can block on cv2/ffprobe for seconds); results are batched
        # through _flush_pending_watch_infos() so the UI stays responsive.
        if added_keys:
            if not hasattr(self, '_watch_info_pool'):
                self._watch_info_pool = QThreadPool(self)
                self._watch_info_pool.setMaxThreadCount(2)
            for k in added_keys:
                runnable = _MediaInfoRunnable(current_files[k], self.media_type, self)
                runnable.watch_generation = self._watch_generation
                # Cross-thread queued connection — handler runs on main thread
                runnable.signals.ready.connect(self._on_watch_info_ready, Qt.ConnectionType.QueuedConnection)
                self._watch_info_pool.start(runnable)

        self._known_files = current_files
        if added_keys or removed_keys:
            self.status_label.setText(f"Watch: +{len(added_keys)} added, -{len(removed_keys)} removed ({len(self.media_infos)} files total)")
            self._show_toast(f"Watch: +{len(added_keys)} added, -{len(removed_keys)} removed", 'info')

    def _on_watch_info_ready(self, info):
        """Called on the main thread when a watch-mode MediaInfo worker finishes."""
        if info is None:
            return
        if getattr(info, 'watch_generation', self._watch_generation) != self._watch_generation:
            return  # stale result — table was cleared/reloaded since this worker started
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
        added_rows = []
        try:
            for info in pending:
                if getattr(info, 'watch_generation', self._watch_generation) != self._watch_generation:
                    continue  # stale — table cleared since extraction started
                row = self.table.rowCount()
                self._on_file_found(info)
                if info.is_valid:
                    # Apply persisted artist/rating/tags for files restored from config
                    self._apply_saved_file_data_to_row(row)
                    self._update_row_preview(row)
                    added_rows.append(row)
        finally:
            self.table.setSortingEnabled(was_sorting)
        self._apply_filter()
        self._update_stats()
        self._load_visible_widgets()
        # FEATURE (Auto-watch): folder profile with auto-rename enabled renames new rows
        if added_rows:
            try:
                self._auto_process_new_rows(added_rows)
            except Exception:
                logger.exception("auto-watch auto-process failed")

    # ─── FEATURE: Auto-watch (folder profiles) ───

    def _preset_for_path(self, path: str, main_win):
        """Longest-prefix profile match for a file path → (preset_name, preset_dict).

        Only profiles with auto_rename enabled AND a preset that still exists
        are considered. Returns (None, None) when nothing matches.
        """
        profiles = getattr(main_win, 'folder_profiles', None) or {}
        presets = getattr(main_win, 'rename_presets', None) or {}
        if not profiles or not presets:
            return None, None
        key = os.path.normcase(os.path.normpath(path))
        best_name, best_preset, best_len = None, None, 0
        for folder_key, prof in profiles.items():
            if not isinstance(prof, dict) or not prof.get('auto_rename'):
                continue
            preset_name = prof.get('preset')
            preset = presets.get(preset_name or '')
            if not preset:
                continue
            fk = os.path.normcase(os.path.normpath(str(folder_key)))
            if key == fk or key.startswith(fk + os.sep):
                if len(fk) > best_len:
                    best_name, best_preset, best_len = preset_name, preset, len(fk)
        return best_name, best_preset

    def _auto_process_new_rows(self, rows):
        """Auto-watch: rename freshly discovered rows using the bound folder preset.

        Mirrors _on_process_all's safety behavior (conflict _N suffixes, UI
        validation BEFORE the filesystem touch, history-before-sidecars) and is
        idempotent: a file whose computed target equals its current name is
        skipped, which also prevents watcher feedback loops after a rename.
        """
        if not rows:
            return
        main_win = self.window()
        if not main_win:
            return
        if not (getattr(main_win, 'folder_profiles', None) and getattr(main_win, 'rename_presets', None)):
            return
        pending = []
        for row in rows:
            info = self._get_row_info(row)
            if not info or not info.is_valid:
                continue
            preset_name, preset = self._preset_for_path(info.filepath, main_win)
            if not preset:
                continue
            pending.append((row, info, preset_name, preset))
        if not pending:
            return
        used_preset = pending[0][2] or "preset"
        was_sorting = self.table.isSortingEnabled()
        self.table.setSortingEnabled(False)
        success = errors = skipped = 0
        error_msgs = []
        self._release_file_locks([info.filepath for _, info, _, _ in pending])
        try:
            for row, info, preset_name, preset in pending:
                fname_item = self.table.item(row, self.COL_FILENAME)
                status_item = self.table.item(row, self.COL_STATUS)
                if fname_item is None or status_item is None:
                    errors += 1
                    continue
                artist_widget = self.table.cellWidget(row, self.COL_ARTIST)
                rating_widget = self.table.cellWidget(row, self.COL_RATING)
                artist = artist_widget.text().strip() if artist_widget else (self.table.item(row, self.COL_ARTIST).text().strip() if self.table.item(row, self.COL_ARTIST) else "")
                rating = rating_widget.currentText() if rating_widget else (self.table.item(row, self.COL_RATING).text().strip() if self.table.item(row, self.COL_RATING) else "—")
                fields_checked = preset.get('fields', []) or []
                fields_ordered = preset.get('all_ordered', []) or []
                keep_ext = bool(preset.get('keep_extension', True))
                separator = preset.get('separator', ' ')
                if not self._is_naming_data_complete_for(fields_checked, artist, rating, info):
                    skipped += 1
                    continue
                new_name = self._get_templated_name_for(artist, rating, info, fields_checked, fields_ordered, separator)
                current_display = fname_item.text().strip()
                target_display = new_name + (info.extension if keep_ext else "") if new_name else ""
                if not target_display or target_display == current_display:
                    skipped += 1  # already conforms — prevents watch loops
                    continue
                src = info.filepath
                dst = os.path.join(os.path.dirname(src), target_display)
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
                    new_ext = os.path.splitext(dst)[1]
                    if new_ext:
                        info.extension = new_ext
                    self._updating_table = True
                    fname_item.setText(info.filename)
                    fname_item.setToolTip(dst)
                    status_item.setText(f"Auto ({preset_name})")
                    status_item.setForeground(QColor("#818cf8"))
                    self._updating_table = False
                    _gi = self._grid_item(info)
                    if _gi:
                        _gi.setText(info.filename)
                    # History BEFORE sidecars so a sidecar failure can't leave
                    # an auto-rename un-undoable (same contract as Process All).
                    self._add_to_history(src, dst, row, op=f"auto:{preset_name}")
                    try:
                        moved_extra = self._move_sidecars(src, dst)
                    except Exception as sidecar_err:
                        logger.warning("Auto-rename sidecar move error (%s -> %s): %s", src, dst, sidecar_err)
                        moved_extra = []
                    if moved_extra:
                        try:
                            self._rename_history[-1]['extra'].extend(moved_extra)
                        except Exception:
                            pass
                    self._refresh_row_dates(info)
                    self._update_date_items(row, info)
                    self._update_row_preview(row)
                    success += 1
                except Exception as e:
                    errors += 1
                    error_msgs.append(f"{info.filename}: {e}")
                    status_item.setText("Auto Error")
                    status_item.setForeground(QColor("#f87171"))
                    status_item.setToolTip(str(e))
        finally:
            self._updating_table = False
            self.table.setSortingEnabled(was_sorting)
        if success or errors:
            self._known_files_dirty = True
            self.status_label.setText(f"Auto-watch ('{used_preset}'): {success} renamed, {errors} errors, {skipped} skipped.")
        if success and not errors:
            self._show_toast(f"Auto-watch renamed {success} new file(s) with '{used_preset}'.", 'success')
        elif errors:
            detail = ""
            if error_msgs:
                detail = " — " + error_msgs[0]
            self._show_toast(f"Auto-watch: {success} renamed, {errors} failed{detail}.", 'warning' if success else 'error')

    # ─── FEATURE: rename preview collector (Preview Changes dialog) ───

    def _collect_rename_preview(self) -> list:
        """Compute the would-be rename for every visible row — WITHOUT executing.

        Mirrors _on_process_all's target computation (global naming config,
        keep-extension switch, on-disk conflict detection) and classifies each
        row as ready / conflict / unchanged / incomplete for the diff view.
        """
        results = []
        main_win = self.window()
        keep_ext = getattr(main_win, 'naming_keep_extension', True)
        for row in range(self.table.rowCount()):
            if self.table.isRowHidden(row):
                continue
            info = self._get_row_info(row)
            if not info or not info.is_valid:
                continue
            artist_widget = self.table.cellWidget(row, self.COL_ARTIST)
            rating_widget = self.table.cellWidget(row, self.COL_RATING)
            artist = artist_widget.text().strip() if artist_widget else (self.table.item(row, self.COL_ARTIST).text().strip() if self.table.item(row, self.COL_ARTIST) else "")
            rating = rating_widget.currentText() if rating_widget else (self.table.item(row, self.COL_RATING).text().strip() if self.table.item(row, self.COL_RATING) else "—")
            current_display = self.table.item(row, self.COL_FILENAME).text().strip() if self.table.item(row, self.COL_FILENAME) else ""
            if not self._is_naming_data_complete(artist, rating, info):
                missing = []
                fields = getattr(main_win, 'naming_fields', []) or []
                if "name" in fields and not artist:
                    missing.append("Name")
                if "rating" in fields and (not rating or rating == "—"):
                    missing.append("Rating")
                if ("date_taken" in fields or "ym" in fields) and get_media_datetime(info) is None:
                    missing.append("Date")
                results.append({'row': row, 'current': current_display or info.filename, 'target': "",
                                'final_target': "", 'status': 'incomplete',
                                'note': "Missing: " + (", ".join(missing) or "data")})
                continue
            new_name = self._get_templated_name(artist, rating, info)
            target_display = new_name + (info.extension if keep_ext else "") if new_name else ""
            if not target_display:
                results.append({'row': row, 'current': current_display or info.filename, 'target': "",
                                'final_target': "", 'status': 'unchanged', 'note': "Empty formula result"})
                continue
            if target_display == current_display:
                results.append({'row': row, 'current': current_display, 'target': target_display,
                                'final_target': target_display, 'status': 'unchanged',
                                'note': "Already matches the formula"})
                continue
            src = info.filepath
            dst = os.path.join(os.path.dirname(src), target_display)
            same_file = os.path.normcase(os.path.abspath(src)) == os.path.normcase(os.path.abspath(dst))
            final_target, note = target_display, ""
            status = 'ready'
            if os.path.exists(dst) and not same_file:
                status = 'conflict'
                base, ext = os.path.splitext(target_display)
                counter = 1
                probe = os.path.join(os.path.dirname(src), f"{base}_{counter}{ext}")
                while os.path.exists(probe):
                    counter += 1
                    probe = os.path.join(os.path.dirname(src), f"{base}_{counter}{ext}")
                final_target = f"{base}_{counter}{ext}"
                note = f"'{target_display}' already exists on disk — will get the _{counter} suffix"
            results.append({'row': row, 'current': current_display, 'target': target_display,
                            'final_target': final_target, 'status': status, 'note': note})
        return results


    def _on_clear(self, keep_watch: bool = False):
        if not keep_watch:
            self._watch_timer.stop()
            self._watch_enabled = False
            if hasattr(self, 'btn_watch') and self.btn_watch.isChecked():
                self.btn_watch.blockSignals(True)
                self.btn_watch.setChecked(False)
                self.btn_watch.blockSignals(False)
                apply_glow(self.btn_watch, None)
        if hasattr(self, '_watch_flush_timer') and self._watch_flush_timer.isActive():
            self._watch_flush_timer.stop()
        self._pending_watch_infos = []
        # Invalidate any in-flight watch-metadata workers: their results belong
        # to the old table and must not be inserted into the fresh one.
        self._watch_generation += 1
        if hasattr(self, '_watch_info_pool'):
            self._watch_info_pool.clear()
            self._watch_info_pool.waitForDone(300)
        self._known_files = {}
        # Invalidate rename history — undoing across a cleared/reloaded list
        # would rename files from the previous session on disk.
        self._rename_history.clear()
        self._redo_history.clear()
        self._release_file_locks()
        # Snapshot any live user edits from the table into _saved_file_data
        # so that Sync / Reload / Clear followed by Rescan doesn't lose user data
        if not hasattr(self, '_saved_file_data'):
            self._saved_file_data = {}
        for r in range(self.table.rowCount()):
            info = self._get_row_info(r)
            if not info or not getattr(info, 'filepath', None):
                continue
            artist_widget = self.table.cellWidget(r, self.COL_ARTIST)
            rating_widget = self.table.cellWidget(r, self.COL_RATING)
            tags_widget = self.table.cellWidget(r, self.COL_TAGS)
            
            artist = artist_widget.text().strip() if artist_widget else (self.table.item(r, self.COL_ARTIST).text().strip() if self.table.item(r, self.COL_ARTIST) else "")
            rating = rating_widget.currentText() if rating_widget else (self.table.item(r, self.COL_RATING).text().strip() if self.table.item(r, self.COL_RATING) else "—")
            if tags_widget:
                tags_str = tags_widget.text().strip()
                tags = [t.strip() for t in tags_str.split(',') if t.strip()]
            else:
                tags_item = self.table.item(r, self.COL_TAGS)
                tags_str = tags_item.text().strip() if tags_item else ""
                tags = [t.strip() for t in tags_str.split(',') if t.strip()] if tags_str else getattr(info, 'tags', [])
            if artist or rating != "—" or tags:
                self._saved_file_data[os.path.normcase(os.path.normpath(info.filepath))] = {
                    'artist': artist, 'rating': rating, 'tags': tags
                }
        self.table.setSortingEnabled(False)
        self.table.setUpdatesEnabled(True)
        self.grid_view.setUpdatesEnabled(True)
        self.table.setRowCount(0)
        self.grid_view.clear()
        self.media_infos.clear()
        self.filtered_rows.clear()
        self.view_stack.setCurrentIndex(2)  # empty state
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
            if self.media_type in ['pdf', 'all'] and hasattr(main_win, 'pdf_tab'):
                dirs.extend(main_win.pdf_tab.directories); exclude.extend(main_win.pdf_tab._exclude_patterns)
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
            'column_visibility': {},
            'column_widths': [self.table.columnWidth(c) for c in range(self.NUM_COLS)],
            'sort_column': self.table.horizontalHeader().sortIndicatorSection(),
            'sort_order': int(self.table.horizontalHeader().sortIndicatorOrder().value),
            'view_mode': self.view_stack.currentIndex() if self.view_stack.currentIndex() in (0, 1) else 0,
            'watch_enabled': bool(getattr(self, '_watch_enabled', False))
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
        if hasattr(self, 'content_splitter') and self.content_splitter:
            state['splitter_sizes'] = self.content_splitter.sizes()
        state['preview_open'] = bool(getattr(self, 'btn_toggle_preview', None) and self.btn_toggle_preview.isChecked())
        state['stats_open'] = bool(getattr(self, 'btn_toggle_stats', None) and self.btn_toggle_stats.isChecked())
        state['side_panel_width'] = getattr(self, '_side_panel_width', 340)
        return state

    def load_state_dict(self, state: dict):
        if not isinstance(state, dict): return
        if 'side_panel_width' in state and isinstance(state['side_panel_width'], int):
            self._side_panel_width = max(280, min(800, state['side_panel_width']))
        if 'splitter_sizes' in state and hasattr(self, 'content_splitter') and self.content_splitter:
            sizes = state.get('splitter_sizes')
            if isinstance(sizes, list) and len(sizes) == 2 and all(isinstance(s, int) for s in sizes):
                self.content_splitter.setSizes(sizes)
        if 'preview_open' in state and hasattr(self, '_toggle_preview'):
            po = bool(state.get('preview_open', False))
            if po:
                self._toggle_preview(True)
        elif 'stats_open' in state and hasattr(self, '_toggle_stats'):
            so = bool(state.get('stats_open', False))
            if so:
                self._toggle_stats(True)
        raw_excl = state.get('exclude_patterns', [])
        # A crafted config string ("foo") would iterate per-character as patterns
        # and over-exclude; non-string entries break the exclude line edit join.
        self._exclude_patterns = [p for p in raw_excl if isinstance(p, str) and p.strip()] if isinstance(raw_excl, list) else []
        if self._exclude_patterns and hasattr(self, 'exclude_input'):
            self.exclude_input.setText(', '.join(self._exclude_patterns))
        raw_hist = state.get('search_history', [])
        self._search_history = [h for h in raw_hist if isinstance(h, str)] if isinstance(raw_hist, list) else []
        self._refresh_search_combobox_items()
        col_visibility = state.get('column_visibility', {})
        if isinstance(col_visibility, dict):
            for col_str, is_visible in col_visibility.items():
                try:
                    col = int(col_str)
                    if 0 <= col < self.NUM_COLS:
                        self.table.setColumnHidden(col, not is_visible)
                except (ValueError, TypeError):
                    continue
        widths = state.get('column_widths', [])
        if isinstance(widths, list):
            for col, w in enumerate(widths):
                if 0 <= col < self.NUM_COLS and isinstance(w, int) and w > 0:
                    self.table.setColumnWidth(col, w)
        if 'sort_column' in state and 'sort_order' in state:
            try:
                sc = int(state.get('sort_column', -1))
                so = int(state.get('sort_order', 0))
                if 0 <= sc < self.NUM_COLS:
                    order = Qt.SortOrder.DescendingOrder if so == 1 else Qt.SortOrder.AscendingOrder
                    self.table.horizontalHeader().setSortIndicator(sc, order)
            except (ValueError, TypeError):
                pass
        if 'view_mode' in state:
            vm = state.get('view_mode', 0)
            if vm in (0, 1) and hasattr(self, '_toggle_view_mode') and hasattr(self, 'btn_view_mode'):
                self.btn_view_mode.blockSignals(True)
                self.btn_view_mode.setChecked(vm == 1)
                self.btn_view_mode.blockSignals(False)
                self._toggle_view_mode(vm == 1)
        if state.get('watch_enabled', False):
            self._watch_enabled = True
            if hasattr(self, 'btn_watch'):
                self.btn_watch.blockSignals(True)
                self.btn_watch.setChecked(True)
                self.btn_watch.blockSignals(False)
        raw_files = state.get('files', {})
        if isinstance(raw_files, dict):
            self._saved_file_data = {
                os.path.normcase(os.path.normpath(str(k))): v 
                for k, v in raw_files.items() 
                if isinstance(k, str) and isinstance(v, dict)
            }

    def _on_scan_progress(self, current: int, total: int):
        if total > 0:
            self.progress_bar.setMaximum(total)
            self.progress_bar.setValue(current)
            self.progress_bar.setFormat(f"Processing {current}/{total}…")

    def _on_file_found(self, info: MediaInfo):
        if getattr(self, '_modal_depth', 0) > 0:
            # A modal is open: inserting rows now would invalidate row indices
            # captured before the dialog opened (wrong-row edits/deletes).
            self._deferred_found_infos.append(info)
            return
        self._updating_table = True
        try:
            self._on_file_found_inner(info)
        finally:
            # Without try/finally any exception permanently left the table in
            # "updating" state, disabling live preview and visible-widget loads.
            self._updating_table = False
        # Keep filtered_rows in sync for rows added mid-scan (previously these
        # were invisible to context-menu "copy paths" and advanced filters
        # until the next manual filter pass).
        last_row = self.table.rowCount() - 1
        if last_row >= 0 and not self.table.isRowHidden(last_row):
            self.filtered_rows.add(last_row)
        if self.view_stack.currentIndex() == 2:
            # Leave the empty state as soon as the first file appears
            self.view_stack.setCurrentIndex(1 if self.btn_view_mode.isChecked() else 0)
        self._update_row_preview(last_row)

    def _on_file_found_inner(self, info: MediaInfo):
        self.media_infos.append(info)
        row = self.table.rowCount()
        self.table.insertRow(row)
        grid_item = QListWidgetItem(info.filename)
        grid_item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
        grid_item.setData(Qt.ItemDataRole.UserRole, info)
        if not info.is_valid: grid_item.setToolTip(info.error_message)
        pw, ph = self._thumb_dims()
        is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark'
        placeholder_pix = QPixmap(pw, ph)
        placeholder_pix.fill(QColor("#1e1b4b" if is_dark else "#f1f5f9"))
        type_icon_map = {'video': 'play', 'audio': 'audio', 'pdf': 'info', 'image': 'preview'}
        icon_name = type_icon_map.get(info.media_type, 'preview')
        icon_sz = min(pw, ph) // 2
        px = get_vector_icon(icon_name, is_dark).pixmap(icon_sz, icon_sz)
        with QPainter(placeholder_pix) as painter:
            painter.setRenderHint(QPainter.RenderHint.Antialiasing)
            painter.drawPixmap((pw - icon_sz) // 2, (ph - icon_sz) // 2, px)
        grid_item.setIcon(QIcon(placeholder_pix))
        self._set_grid_item(info, grid_item)
        search_text = (self.search_input.currentText() if hasattr(self.search_input, 'currentText') else self.search_input.text()).lower().strip()
        is_hidden = False
        if self.is_smart_folder and not matches_query(info, self.smart_query): is_hidden = True
        elif search_text and not matches_query(info, search_text): is_hidden = True
        if is_hidden:
            grid_item.setHidden(True)
            self.table.setRowHidden(row, True)
        self.grid_view.addItem(grid_item)
        if info.is_valid:
            thumb_label = SkeletonThumbLabel()
            thumb_label.setObjectName("thumbnailLabel")
            thumb_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
            thumb_label.setProperty("emoji", "…")
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
            status_item = NumericTableWidgetItem("Valid")
            status_item.setForeground(QColor("#34d399") if is_dark else QColor("#059669"))
        else:
            status_item = NumericTableWidgetItem("Unsupported")
            status_item.setForeground(QColor("#f87171") if is_dark else QColor("#dc2626"))
            status_item.setToolTip(info.error_message)
        status_item.setFlags(status_item.flags() & ~Qt.ItemFlag.ItemIsEditable)
        status_item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
        self.table.setItem(row, self.COL_STATUS, status_item)
        
        meta_font = QFont(BASE_FONT_FAMILY, 9, QFont.Weight.Light)
        bold_meta_font = QFont(BASE_FONT_FAMILY, 9, QFont.Weight.Bold)
        mono_meta_font = _mono_font(9, True)  # Nebula: aligned digits in data columns
        
        fname_item = NumericTableWidgetItem(info.filename)
        fname_item.setData(Qt.ItemDataRole.UserRole, info)
        fname_item.setToolTip(info.filepath)
        fname_item.setFont(QFont(BASE_FONT_FAMILY, 10, QFont.Weight.Bold))
        fname_item.setForeground(QColor("#c4b5fd") if is_dark else QColor("#1e3a8a"))
        fname_item.setTextAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
        self.table.setItem(row, self.COL_FILENAME, fname_item)
        
        size_item = NumericTableWidgetItem(info.size_formatted, sort_key=info.size_bytes)
        size_item.setFlags(size_item.flags() & ~Qt.ItemFlag.ItemIsEditable)
        size_item.setTextAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
        size_item.setFont(mono_meta_font)
        size_item.setForeground(QColor("#9ca3af") if is_dark else QColor("#64748b"))
        self.table.setItem(row, self.COL_SIZE, size_item)
        
        if info.is_valid:
            res_text = f"{info.width}×{info.height}\n({info.resolution_tag})"
            res_key = min(info.width, info.height)
        else:
            res_text = "—"
            res_key = -1
        res_item = NumericTableWidgetItem(res_text, sort_key=res_key)
        res_item.setFlags(res_item.flags() & ~Qt.ItemFlag.ItemIsEditable)
        res_item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
        res_item.setFont(mono_meta_font)
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
        dur_item.setTextAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
        dur_item.setFont(mono_meta_font)
        dur_item.setForeground(QColor("#9ca3af") if is_dark else QColor("#64748b"))
        self.table.setItem(row, self.COL_DURATION, dur_item)

        for col, attr in ((self.COL_DATE_MOD, 'mtime'), (self.COL_DATE_CREATED, 'ctime')):
            ts = float(getattr(info, attr, 0) or 0)
            dt_item = NumericTableWidgetItem(format_timestamp(ts), sort_key=ts)
            dt_item.setFlags(dt_item.flags() & ~Qt.ItemFlag.ItemIsEditable)
            dt_item.setTextAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
            dt_item.setFont(mono_meta_font)
            dt_item.setForeground(QColor("#9ca3af") if is_dark else QColor("#64748b"))
            self.table.setItem(row, col, dt_item)
        parsed_artist, parsed_rating = parse_naming_format(info.filename, getattr(info, 'media_type', None))
        is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark'
        text_color = QColor("#e0e0e0") if is_dark else QColor("#0f172a")
        
        if info.is_valid:
            artist_item = NumericTableWidgetItem(parsed_artist or "")
            artist_item.setFont(meta_font)
            artist_item.setForeground(text_color)
            artist_item.setTextAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
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
            tags_item.setTextAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
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
        preview_item.setTextAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
        preview_item.setForeground(QColor("#7c7c9a"))

        self.table.setItem(row, self.COL_PREVIEW, preview_item)
        _, row_h = self._thumb_dims()
        self.table.setRowHeight(row, row_h + 8)

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
        tw_, th_ = self._thumb_dims()
        runnable = _ThumbnailRunnable(row, info, label, tw_, th_)
        # Cross-thread queued connection — _on_thumbnail_ready runs on main thread
        runnable.signals.finished.connect(self._on_thumbnail_ready, Qt.ConnectionType.QueuedConnection)
        self._thumb_pool.start(runnable)

    def _on_thumbnail_ready(self, row: int, info: MediaInfo, label: QLabel, image):
        """Called on the main thread when a thumbnail worker finishes."""
        pixmap = QPixmap.fromImage(image) if image is not None else None
        if pixmap and not pixmap.isNull():
            cw, ch = self._thumb_dims()
            try:
                label.setFixedSize(cw, ch)
                label.setPixmap(pixmap.scaled(cw, ch, Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation))
            except RuntimeError:
                pass
            _gi = self._grid_item(info)
            if _gi is not None:
                try:
                    _gi.setIcon(QIcon(pixmap))
                except RuntimeError:
                    pass  # grid item deleted while the thumbnail was in flight
        else:
            try:
                fallback_icon = "—"
                if hasattr(label, 'stop_shimmer'):
                    label.stop_shimmer(fallback_text=fallback_icon)
                elif hasattr(label, 'setText'):
                    label.setText(fallback_icon)
            except RuntimeError:
                pass

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
        focus_w = QApplication.focusWidget()
        if isinstance(focus_w, (EditableCellLineEdit, EditableCellComboBox)) and focus_w.hasFocus():
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
        self.progress_bar.setVisible(False)
        self.table.setUpdatesEnabled(True)
        self.grid_view.setUpdatesEnabled(True)
        self.table.setSortingEnabled(True)
        loaded = len(self.media_infos)
        has_files = loaded > 0
        self.btn_relocate.setEnabled(has_files)
        self.btn_find_dupes.setEnabled(has_files)
        self.btn_clear.setVisible(has_files)
        if loaded == 0:
            self.view_stack.setCurrentIndex(2)  # empty state
        if self.media_type == 'video': media_word = "video"
        elif self.media_type == 'audio': media_word = "audio"
        elif self.media_type == 'pdf': media_word = "PDF"
        elif self.media_type == 'all': media_word = "media"
        else: media_word = "image"
        self.status_label.setText(f"Scan complete — {loaded} {media_word} file{'s' if loaded != 1 else ''} found.")
        self._apply_filter()
        self._stats_dirty = True
        self._update_stats()
        if self._saved_file_data:
            self._restore_file_data()
            # NOTE: the dict is intentionally NOT cleared — it stays as a lookup
            # table so files added later by watch mode also get their persisted
            # artist/rating/tags applied. Entries are consumed one-by-one in
            # _apply_saved_file_data_to_row.
        if getattr(self, '_watch_enabled', False):
            self._known_files = {os.path.normcase(os.path.normpath(info.filepath)): info.filepath for info in self.media_infos}
            if not self._watch_timer.isActive():
                self._watch_timer.start(3000)
        self._load_visible_widgets()

    def _ensure_widgets_for_row(self, row: int):
        info = self._get_row_info(row)
        if not info or not info.is_valid: return
        
        if not hasattr(info, 'parsed_artist'):
            info.parsed_artist, info.parsed_rating = parse_naming_format(info.filename, getattr(info, 'media_type', None))
            
        # Lazy Thumbnail Generation
        if not getattr(info, 'thumb_queued', False):
            info.thumb_queued = True
            thumb_label = self.table.cellWidget(row, self.COL_THUMB)
            if thumb_label and thumb_label.objectName() == "thumbnailLabel":
                self._generate_thumbnail_async(row, info, thumb_label)
                if hasattr(thumb_label, 'start_shimmer'):
                    thumb_label.start_shimmer()
                

        # Artist widget
        if not self.table.cellWidget(row, self.COL_ARTIST):
            artist_item = self.table.item(row, self.COL_ARTIST)
            val = artist_item.text().strip() if artist_item else ""
            if not val: val = info.parsed_artist
            artist_input = EditableCellLineEdit("Enter name…")
            artist_input.setMaxLength(100)
            if val: artist_input.setText(val)
            artist_input.textChanged.connect(self._on_input_changed_sender)
            artist_input.editingFinished.connect(self._on_artist_editing_finished)
            self.table.setCellWidget(row, self.COL_ARTIST, artist_input)
            artist_input.installEventFilter(artist_input)
            
        # Rating widget
        if not self.table.cellWidget(row, self.COL_RATING):
            rating_item = self.table.item(row, self.COL_RATING)
            val = rating_item.text().strip() if rating_item else "—"
            if val == "—" or not val:
                val = info.parsed_rating or "—"
            rating_combo = EditableCellComboBox()
            rating_combo.addItems(["—"] + [str(i) for i in range(1, 11)])
            idx = rating_combo.findText(val)
            if idx >= 0: rating_combo.setCurrentIndex(idx)
            rating_combo.currentTextChanged.connect(self._on_input_changed_sender)
            rating_combo.currentTextChanged.connect(self._on_rating_changed)
            rating_combo.currentTextChanged.connect(lambda text, cb=rating_combo: self._style_rating_combo(cb, text))
            self._style_rating_combo(rating_combo, rating_combo.currentText())
            self.table.setCellWidget(row, self.COL_RATING, rating_combo)
            rating_combo.installEventFilter(rating_combo)
            
        # Tags widget
        if not self.table.cellWidget(row, self.COL_TAGS):
            tags_item = self.table.item(row, self.COL_TAGS)
            val = tags_item.text().strip() if tags_item else ""
            if not val and hasattr(info, 'tags') and info.tags:
                val = ", ".join(info.tags)
            tag_input = EditableCellLineEdit("e.g. nature, 4k, favorite")
            if val: tag_input.setText(val)
            tag_input.editingFinished.connect(self._on_tags_edited)
            self.table.setCellWidget(row, self.COL_TAGS, tag_input)
            tag_input.installEventFilter(tag_input)

    def _thumb_dims(self):
        """Inner thumbnail label size derived from the thumb_size setting."""
        w = int(getattr(self, 'thumb_size', 130))
        return w, max(50, round(w * 0.567))

    def _set_grid_item(self, info, item):
        """FIX: per-tab grid item storage. MediaInfo objects are shared across
        smart-folder tabs; a single info.grid_item attribute clobbered the
        other tab's card (wrong thumbnails, broken selection, stale paths)."""
        if not hasattr(info, 'grid_items'):
            info.grid_items = {}
        info.grid_items[id(self)] = item

    def _grid_item(self, info):
        return getattr(info, 'grid_items', {}).get(id(self))

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
                info = self._get_row_info(row)
                if info:
                    info.parsed_rating = text
                rating_item = self.table.item(row, self.COL_RATING)
                if rating_item:
                    was_sorting = self.table.isSortingEnabled()
                    self.table.setSortingEnabled(False)
                    rating_item.setText(text)
                    rating_item.sort_key = int(text) if text.isdigit() else 0
                    self.table.setSortingEnabled(was_sorting)
                main_win = self.window()
                if main_win and hasattr(main_win, '_debounced_save_state'):
                    main_win._debounced_save_state()
                break

    def _get_row_info(self, row: int) -> MediaInfo | None:
        item = self.table.item(row, self.COL_FILENAME)
        if item: return item.data(Qt.ItemDataRole.UserRole)
        return None

    def _on_input_changed_sender(self):
        if getattr(self, '_updating_table', False): return
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
        pos = self.table.viewport().mapFromGlobal(sender.mapToGlobal(QPoint(sender.width() // 2, sender.height() // 2)))
        index = self.table.indexAt(pos)
        row = index.row() if index.isValid() else None
        if row is None:
            # L1: Fallback — iterate by widget identity (same approach as _on_tags_edited)
            for r in range(self.table.rowCount()):
                if self.table.cellWidget(r, self.COL_ARTIST) is sender:
                    row = r
                    break
        if row is not None:
            info = self._get_row_info(row)
            if info:
                info.parsed_artist = sender.text().strip()
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
        self._update_row_preview(row)

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
        failed = 0
        old_stem = os.path.basename(os.path.splitext(old_path)[0])
        new_stem = os.path.splitext(new_path)[0]
        for sidecar in find_sidecars(old_path):
            base = os.path.basename(sidecar)
            # find_sidecars matches case-insensitively; plain slicing by
            # len(old_stem) garbled names when case differed (VIDEO.mp4 +
            # video.srt → NewNamevideo.srt). Strip the prefix case-insensitively.
            if base.lower().startswith(old_stem.lower()):
                rel = base[len(old_stem):]
            else:
                rel = base
            target = new_stem + rel
            same_file = os.path.normcase(os.path.abspath(sidecar)) == os.path.normcase(os.path.abspath(target))
            try:
                if os.path.exists(target) and not same_file:
                    b, x = os.path.splitext(target)
                    counter = 1
                    while os.path.exists(target):
                        target = f"{b}_{counter}{x}"
                        counter += 1
                shutil.move(sidecar, target)
                moved.append((sidecar, target))
            except OSError as e:
                failed += 1
                logger.warning("Sidecar move failed (%s -> %s): %s", sidecar, target, e)
        if failed:
            # Previously silent: the video moved but its subtitles stayed behind
            # with no indication. Surface it so the user can move them manually.
            try:
                self._show_toast(f"{failed} sidecar file(s) could not follow the move.", 'warning')
            except Exception:
                pass
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
                    parts.append(sanitize_folder_name(artist))  # FIX: strip characters illegal in filenames
            elif config_key == "duration":
                if self.media_type != 'image' and info.duration_compact and info.duration_compact != "—":
                    parts.append(info.duration_compact)
            elif config_key == "resolution":
                if self.media_type != 'audio' and info.resolution_tag and info.resolution_tag != "—":
                    parts.append(info.resolution_tag)
            elif config_key == "rating":
                if rating and rating != "—":
                    parts.append(sanitize_folder_name(rating))
            elif config_key == "tags":
                tags = getattr(info, 'tags', [])
                if tags:
                    parts.append(sanitize_folder_name(" ".join(tags)))
            elif config_key in ("date_taken", "ym"):
                dt = get_media_datetime(info)
                if dt is not None:
                    parts.append(dt.strftime("%Y-%m-%d") if config_key == "date_taken" else dt.strftime("%Y%m"))
        res = separator.join(parts)
        if len(res) > 240:
            res = res[:240].rstrip(". ")
        return res

    def _get_templated_name_for(self, artist: str, rating: str, info, fields_checked, fields_ordered, separator) -> str:
        """_get_templated_name against an EXPLICIT naming config.

        The main path uses the window's live config; Auto-watch passes the
        folder profile's preset config instead, without touching the editor.
        """
        parts = []
        for f_name in fields_ordered:
            config_key = FIELD_MAP.get(f_name)
            if config_key not in fields_checked:
                continue
            if config_key == "name":
                if artist:
                    parts.append(sanitize_folder_name(artist))  # FIX: strip characters illegal in filenames
            elif config_key == "duration":
                if self.media_type != 'image' and info.duration_compact and info.duration_compact != "—":
                    parts.append(info.duration_compact)
            elif config_key == "resolution":
                if self.media_type != 'audio' and info.resolution_tag and info.resolution_tag != "—":
                    parts.append(info.resolution_tag)
            elif config_key == "rating":
                if rating and rating != "—":
                    parts.append(sanitize_folder_name(rating))
            elif config_key == "tags":
                tags = getattr(info, 'tags', [])
                if tags:
                    parts.append(sanitize_folder_name(" ".join(tags)))
            elif config_key in ("date_taken", "ym"):
                dt = get_media_datetime(info)
                if dt is not None:
                    parts.append(dt.strftime("%Y-%m-%d") if config_key == "date_taken" else dt.strftime("%Y%m"))
        res = separator.join(parts)
        if len(res) > 240:
            res = res[:240].rstrip(". ")
        return res

    def _is_naming_data_complete(self, artist: str, rating: str, info=None) -> bool:
        main_win = self.window()
        if not main_win:
            return False
        fields_checked = getattr(main_win, 'naming_fields', ["name", "duration", "resolution", "rating", "tags"])
        return self._is_naming_data_complete_for(fields_checked, artist, rating, info)

    def _is_naming_data_complete_for(self, fields_checked, artist: str, rating: str, info=None) -> bool:
        """Completeness check against an explicit field set (Auto-watch presets)."""
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


    def _update_row_preview(self, row: int, refresh_stats: bool = True):
        info = self._get_row_info(row)
        if not info or not info.is_valid: return
        # Mark stats dirty so the next _update_stats call will recompute ready_count
        self._stats_dirty = True
        artist_widget = self.table.cellWidget(row, self.COL_ARTIST)
        rating_widget = self.table.cellWidget(row, self.COL_RATING)
        artist = artist_widget.text().strip() if artist_widget else (self.table.item(row, self.COL_ARTIST).text().strip() if self.table.item(row, self.COL_ARTIST) else "")
        rating_text = rating_widget.currentText() if rating_widget else (self.table.item(row, self.COL_RATING).text().strip() if self.table.item(row, self.COL_RATING) else "—")
        
        was_sorting = self.table.isSortingEnabled()
        self.table.setSortingEnabled(False)
        try:
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
                _gi = self._grid_item(info)
                if _gi: _gi.setToolTip("")
            else:
                preview_item.setText(f"➜  {target_display}")
                preview_item.setFont(QFont(BASE_FONT_FAMILY, 10, QFont.Weight.Bold))
                preview_item.setForeground(QColor("#34d399") if is_dark else QColor("#059669"))
                _gi = self._grid_item(info)
                if _gi: _gi.setToolTip(f"Rename to: {target_display}")
        finally:
            self.table.setSortingEnabled(was_sorting)
        if refresh_stats:
            # Debounced: _update_row_preview runs once per file during scans —
            # a direct _update_stats() per row made the ready-count loop O(n²).
            self._schedule_update_stats()

    def _schedule_update_stats(self):
        """Coalesce rapid stats recomputations into one deferred _update_stats."""
        if not hasattr(self, '_stats_timer'):
            self._stats_timer = QTimer(self)
            self._stats_timer.setSingleShot(True)
            self._stats_timer.setInterval(120)
            self._stats_timer.timeout.connect(self._update_stats)
        self._stats_timer.start()

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
                _gi = self._grid_item(info) if info else None
                if _gi: _gi.setSelected(True)
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
        selected_infos = []
        for rng in self.table.selectedRanges():
            for row in range(rng.topRow(), rng.bottomRow() + 1):
                if self.table.isRowHidden(row):
                    continue
                info = self._get_row_info(row)
                if info and info.is_valid and info not in selected_infos:
                    selected_infos.append(info)
        if not selected_infos:
            QMessageBox.information(self, "No Valid Selection", "Please select at least one valid file."); return
        dialog = BatchEditDialog(self)
        accepted = False
        artist = rating = None
        self._enter_modal()
        try:
            accepted = dialog.exec() == QDialog.DialogCode.Accepted
            if accepted:
                artist, rating = dialog.get_values()
        finally:
            self._exit_modal()
        if accepted:
            self._apply_batch_edit(selected_infos, artist, rating)

    def _on_batch_tag(self):
        selected_infos = []
        for rng in self.table.selectedRanges():
            for row in range(rng.topRow(), rng.bottomRow() + 1):
                if self.table.isRowHidden(row):
                    continue
                info = self._get_row_info(row)
                if info and info.is_valid and info not in selected_infos:
                    selected_infos.append(info)
        if len(selected_infos) < 2:
            QMessageBox.information(self, "Selection Required", "Please select at least 2 valid files."); return

        dialog = BatchTagDialog(selected_infos, self)
        accepted = False
        self._enter_modal()
        try:
            accepted = dialog.exec() == QDialog.DialogCode.Accepted
        finally:
            self._exit_modal()
        if accepted:
            mode, input_tags = dialog.get_result()
            was_sorting = self.table.isSortingEnabled()
            self.table.setSortingEnabled(False)
            self._updating_table = True
            try:
                id_to_row = {}
                for r in range(self.table.rowCount()):
                    inf = self._get_row_info(r)
                    if inf is not None:
                        id_to_row[id(inf)] = r

                for info in selected_infos:
                    row = id_to_row.get(id(info))
                    if row is None:
                        continue
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
                    tags_text = ", ".join(new_tags)
                    tags_item = self.table.item(row, self.COL_TAGS)
                    if tags_item:
                        tags_item.setText(tags_text)
                    tags_widget = self.table.cellWidget(row, self.COL_TAGS)
                    if tags_widget and tags_widget.text() != tags_text:
                        tags_widget.setText(tags_text)
                    _gi = self._grid_item(info)
                    if _gi:
                        tag_str = tags_text if new_tags else ""
                        _gi.setToolTip(f"{info.filename}\nTags: {tag_str}" if tag_str else info.filename)
                    self._update_row_preview(row)
            finally:
                self._updating_table = False
                self.table.setSortingEnabled(was_sorting)

            if hasattr(self.window(), '_debounced_save_state'):
                self.window()._debounced_save_state()
            self._show_toast(f"Updated tags for {len(selected_infos)} files.", 'success')

    def _apply_batch_edit(self, items, artist: str | None, rating: str | None):
        was_sorting = self.table.isSortingEnabled()
        self.table.setSortingEnabled(False)
        self._updating_table = True
        try:
            id_to_row = {}
            for r in range(self.table.rowCount()):
                inf = self._get_row_info(r)
                if inf is not None:
                    id_to_row[id(inf)] = r
            for item in items:
                if isinstance(item, int):
                    row = item
                else:
                    row = id_to_row.get(id(item))
                if row is None or row < 0 or row >= self.table.rowCount():
                    continue
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
        finally:
            self._updating_table = False
            self.table.setSortingEnabled(was_sorting)
        self._update_stats()
        main_win = self.window()
        if main_win and hasattr(main_win, '_debounced_save_state'):
            main_win._debounced_save_state()

    def _on_smart_relocate(self):
        """Opens the Smart Relocate Dialog and executes the move."""
        if getattr(self, '_relocating', False):
            return
        selected_infos = []
        for rng in self.table.selectedRanges():
            for row in range(rng.topRow(), rng.bottomRow() + 1):
                if self.table.isRowHidden(row):
                    continue
                info = self._get_row_info(row)
                if info is not None and info not in selected_infos:
                    selected_infos.append(info)

        dialog = SmartRelocateDialog(selected_infos, self.media_infos, self)
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

        # Allowed-root inputs: the literal template prefix (everything before the
        # first {variable}). The root itself is resolved per file inside the loop
        # because relative templates anchor to each source file's directory.
        first_var = template.find('{')
        if first_var > 0:
            literal_prefix = template[:first_var]
        elif first_var == -1:
            # No variable — template is a literal directory; anchor to it
            literal_prefix = template
        else:
            # Template starts with a variable — no literal prefix to anchor to.
            literal_prefix = ""

        success_count = 0
        error_count = 0
        error_details = []  # capture for the completion dialog

        was_sorting = self.table.isSortingEnabled()
        self.table.setSortingEnabled(False)
        self._updating_table = True
        self._relocating = True
        for _b in (self.btn_process, self.btn_relocate, self.btn_delete,
                   self.btn_batch_edit, self.btn_batch_tag, self.btn_find_dupes):
            _b.setEnabled(False)

        # Release locks on all target files before moving
        self._release_file_locks([info.filepath for info in target_infos])

        # Build id(info) -> row map ONCE for O(1) lookup
        id_to_row = {}
        for r in range(self.table.rowCount()):
            ri = self._get_row_info(r)
            if ri is not None:
                id_to_row[id(ri)] = r

        progress = QProgressDialog("Moving files…", "Cancel", 0, len(target_infos), self)
        progress.setWindowModality(Qt.WindowModality.ApplicationModal)
        progress.setMinimumDuration(0)
        progress.setValue(0)

        # Pause watch/scan row mutations for the whole loop: processEvents()
        # below still delivers timer events, and _check_for_changes firing
        # mid-loop shifted rows and corrupted the id_to_row map (UI updates
        # written to the wrong rows).
        self._enter_modal()
        try:
            for idx, info in enumerate(target_infos):
                if progress.wasCanceled():
                    error_details.append(f"Cancelled by user after {success_count} files moved.")
                    break
                try:
                    src = info.filepath
                    tags = getattr(info, 'tags', [])
                    dest_dir = parse_destination_template(template, info, tags)

                    # Anchor relative destination template to source file parent directory
                    if not os.path.isabs(dest_dir):
                        dest_dir = os.path.join(os.path.dirname(src), dest_dir)

                    # Path-traversal safety: ensure resolved dest_dir stays under the
                    # allowed root. Relative literal prefixes anchor to THIS file's
                    # directory (same rule as dest_dir above); absolute ones stand
                    # alone; a leading-variable template is confined to the source dir.
                    if literal_prefix:
                        anchor_base = literal_prefix if os.path.isabs(literal_prefix) else os.path.join(os.path.dirname(src), literal_prefix)
                    else:
                        anchor_base = os.path.dirname(src) or os.path.expanduser("~")
                    try:
                        allowed_root = os.path.normcase(os.path.realpath(os.path.abspath(anchor_base)))
                    except Exception:
                        allowed_root = os.path.normcase(os.path.abspath(anchor_base))
                    try:
                        abs_dest = os.path.normcase(os.path.realpath(os.path.abspath(dest_dir)))
                    except Exception:
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
                        moved_extra = self._move_sidecars(src, dest_file)
                        self._refresh_row_dates(info)
                        if row_idx >= 0:
                            fname_item = self.table.item(row_idx, self.COL_FILENAME)
                            if fname_item:
                                fname_item.setText(info.filename)
                                fname_item.setToolTip(dest_file)
                            _gi = self._grid_item(info)
                            if _gi:
                                _gi.setText(info.filename)
                                _gi.setToolTip(dest_file)
                            self._update_date_items(row_idx, info)
                        self._add_to_history(src, dest_file, row_idx, extra=moved_extra)

                        success_count += 1

                    except Exception as e:
                        error_count += 1
                        error_details.append(f"{info.filename}: {e}")
                        logger.exception("Failed to move %s", info.filename)
                finally:
                    progress.setValue(idx + 1)
                    QApplication.processEvents(QEventLoop.ProcessEventsFlag.ExcludeUserInputEvents)
        finally:
            progress.close()
            self._exit_modal()
            self._updating_table = False
            self.table.setSortingEnabled(was_sorting)
            self._relocating = False
            self._update_selection_buttons_and_preview()
            self._stats_dirty = True
            self._update_stats()
            has_files = self.table.rowCount() > 0
            self.btn_relocate.setEnabled(has_files)
            self.btn_find_dupes.setEnabled(has_files)

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
                player_win = None
                if info.media_type == 'video':
                    player_win = NativeVideoPlayerWindow(filepath, parent=main_win)
                elif info.media_type == 'image':
                    player_win = NativeImagePlayerWindow(filepath, parent=main_win)
                elif info.media_type == 'audio':
                    player_win = NativeAudioPlayerWindow(filepath, parent=main_win)
                if player_win:
                    player_win.show()
                    main_win._native_players.append(player_win)
                    return

        if player_path and player_path != "native" and os.path.exists(player_path):
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

        is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark'
        menu = QMenu(self)
        if is_four_videos:
            play4_action = QAction("Play 4 (Split Screen)", self)
            play4_action.setIcon(get_vector_icon('play', is_dark))
            play4_action.triggered.connect(lambda: self._play_four_videos(selected_video_paths))
            menu.addAction(play4_action)
            menu.addSeparator()

        if len(selected_rows) == 2:
            compare_action = QAction("Compare Selected (2 Files)", self)
            compare_action.setIcon(get_vector_icon('search', is_dark))
            compare_action.triggered.connect(self._on_compare_selected)
            menu.addAction(compare_action)
            menu.addSeparator()

        play_action = QAction("Play / Open", self)
        play_action.setIcon(get_vector_icon('play', is_dark))
        play_action.triggered.connect(lambda: self._play_video(row))
        menu.addAction(play_action)

        if info.media_type == 'video':
            trim_action = QAction("Quick Trim / Cut Video", self)
            trim_action.setIcon(get_vector_icon('scissors', is_dark))
            trim_action.triggered.connect(lambda checked=False, r=row: self._on_quick_trim(r))
            menu.addAction(trim_action)

            random_action = QAction("🎲 Random Discovery Player", self)
            random_action.setIcon(get_vector_icon('shuffle', is_dark))
            random_action.triggered.connect(lambda checked=False, r=row: self._play_random_shuffle(r))
            menu.addAction(random_action)

        # ─── Open With Submenu ───
        open_with_menu = menu.addMenu("Open with…")
        win_dialog_action = QAction("System open with...", self)
        win_dialog_action.triggered.connect(lambda checked=False, fp=info.filepath: self._open_with_system(fp))
        open_with_menu.addAction(win_dialog_action)
        
        if info.media_type != 'pdf':
            native_player_action = QAction("MediaFlow Native Player", self)
            native_player_action.triggered.connect(lambda checked=False, fp=info.filepath: self._play_native(fp))
            open_with_menu.addAction(native_player_action)

        if info.media_type == 'video':
            random_action_ow = QAction("🎲 Random Discovery Player", self)
            random_action_ow.setIcon(get_vector_icon('shuffle', is_dark))
            random_action_ow.triggered.connect(lambda checked=False, fp=info.filepath: self._play_random_shuffle_filepath(fp))
            open_with_menu.addAction(random_action_ow)
        
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
        config_action = QAction("Configure Applications...", self)
        config_action.setIcon(get_vector_icon('presets', is_dark))
        config_action.triggered.connect(self._configure_open_with_apps)
        open_with_menu.addAction(config_action)

        info_action = QAction("Detailed Info", self)
        info_action.setIcon(get_vector_icon('info', is_dark))
        info_action.triggered.connect(lambda: self._show_detailed_info(row))
        menu.addAction(info_action)
        open_folder = QAction("Open Containing Folder", self)
        open_folder.setIcon(get_vector_icon('folder', is_dark))
        open_folder.triggered.connect(lambda checked=False, fp=info.filepath: self._open_folder_for_filepath(fp))
        menu.addAction(open_folder)
        menu.addSeparator()
        sel_infos = []
        for r in sorted(selected_rows):
            if self.filtered_rows and r not in self.filtered_rows: continue
            r_info = self._get_row_info(r)
            if r_info is not None: sel_infos.append(r_info)
        if len(sel_infos) > 1:
            copy_paths = QAction(f"Copy {len(sel_infos)} File Paths", self)
            copy_paths.triggered.connect(
                lambda: QApplication.clipboard().setText("\n".join(i.filepath for i in sel_infos)))
            menu.addAction(copy_paths)
            copy_names = QAction(f"Copy {len(sel_infos)} File Names", self)
            copy_names.triggered.connect(
                lambda: QApplication.clipboard().setText("\n".join(i.filename for i in sel_infos)))
            menu.addAction(copy_names)
        else:
            copy_path = QAction("Copy File Path", self)
            copy_path.triggered.connect(lambda: self._copy_path_for_row(row))
            menu.addAction(copy_path)
        target_row = -1 if (len(selected_rows) > 1 and row in selected_rows) else row
        if len(selected_rows) > 1 and row in selected_rows:
            remove_action = QAction(f"Remove {len(selected_rows)} Selected From List", self)
            remove_action.setIcon(get_vector_icon('clear', is_dark))
            remove_action.triggered.connect(self._on_remove_selected)
            menu.addAction(remove_action)
            delete_action = QAction(f"Delete {len(selected_rows)} Selected from Disk...", self)
            delete_action.setIcon(get_vector_icon('delete', is_dark))
            delete_action.triggered.connect(lambda checked=False, t=target_row: self._on_delete_selected(t))
            menu.addAction(delete_action)
        else:
            remove_action = QAction("Remove From List", self)
            remove_action.setIcon(get_vector_icon('clear', is_dark))
            remove_action.triggered.connect(lambda checked=False, r=row: self._remove_row_from_list(r))
            menu.addAction(remove_action)
            delete_action = QAction("Delete from Disk...", self)
            delete_action.setIcon(get_vector_icon('delete', is_dark))
            delete_action.triggered.connect(lambda checked=False, r=row: self._on_delete_selected(r))
            menu.addAction(delete_action)
        menu.addSeparator()
        export_csv_action = QAction("Export List to CSV", self)
        export_csv_action.setIcon(get_vector_icon('stats', is_dark))
        export_csv_action.setToolTip("Export the visible rows (current filters/duplicate view) to a CSV file")
        export_csv_action.triggered.connect(self._export_list_csv)
        menu.addAction(export_csv_action)
        if info.media_type == 'audio':
            audio_tags_action = QAction("Edit Audio Tags\u2026", self)
            audio_tags_action.setIcon(get_vector_icon('tag', is_dark))
            audio_tags_action.triggered.connect(lambda checked=False, r=row: self._edit_audio_tags(r))
            menu.addAction(audio_tags_action)
        if info.is_valid:
            menu.addSeparator()
            rating_menu = menu.addMenu("Set Rating")
            for r in ["—"] + [str(i) for i in range(1, 11)]:
                action = QAction(r if r != "—" else "Clear", self)
                action.triggered.connect(lambda checked=False, rr=r, t=target_row: self._set_rating_for_row(t, rr))
                rating_menu.addAction(action)
        # Modal guard: rows must not shift while the (modal) menu is open, or
        # the captured row/target_row indices resolve to different files.
        self._enter_modal()
        try:
            menu.exec(global_pos)
        finally:
            self._exit_modal()
            menu.deleteLater()

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
            # M4: Resolve media type from file extension rather than tab type,
            # so native player works on smart folder / 'all' tabs.
            ext = os.path.splitext(filepath)[1].lower()
            if ext in VIDEO_EXTENSIONS:
                player_win = NativeVideoPlayerWindow(filepath, parent=main_win)
            elif ext in IMAGE_EXTENSIONS:
                player_win = NativeImagePlayerWindow(filepath, parent=main_win)
            elif ext in AUDIO_EXTENSIONS:
                player_win = NativeAudioPlayerWindow(filepath, parent=main_win)
            else:
                player_win = None
            if player_win:
                player_win.show()
                main_win._native_players.append(player_win)

    def _play_random_shuffle(self, row: int = -1):
        """Open the hidden Random Discovery Video Player."""
        filepath = None
        if row >= 0:
            info = self._get_row_info(row)
            if info and getattr(info, 'media_type', '') == 'video':
                filepath = info.filepath
        
        main_win = self.window()
        candidate_pool = []
        for info in getattr(self, 'media_infos', []):
            if getattr(info, 'media_type', '') == 'video' and os.path.exists(info.filepath):
                candidate_pool.append(info.filepath)
        
        if not candidate_pool and filepath:
            folder = os.path.dirname(filepath)
            if os.path.isdir(folder):
                try:
                    for entry in os.scandir(folder):
                        if entry.is_file() and os.path.splitext(entry.name)[1].lower() in VIDEO_EXTENSIONS:
                            candidate_pool.append(entry.path)
                except Exception:
                    pass
        if not candidate_pool and filepath:
            candidate_pool = [filepath]
        if not candidate_pool:
            QMessageBox.information(self, "No Videos", "No video files found to play in Random Discovery mode.")
            return

        target_parent = main_win if main_win else self
        shuffle_win = RandomShufflePlayerWindow(candidate_pool, initial_file=filepath, parent=target_parent)
        if main_win:
            if not hasattr(main_win, '_native_players'):
                main_win._native_players = []
            prune_native_players(main_win)
            main_win._native_players.append(shuffle_win)
        shuffle_win.show()

    def _play_random_shuffle_filepath(self, filepath: str):
        row = -1
        for r in range(self.table.rowCount()):
            info = self._get_row_info(r)
            if info and info.filepath == filepath:
                row = r
                break
        self._play_random_shuffle(row)

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
        if main_win and hasattr(main_win, '_debounced_save_state'):
            main_win._debounced_save_state()
        elif main_win and hasattr(main_win, '_save_state'):
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
        if info and getattr(info, 'filepath', None):
            self._open_folder_for_filepath(info.filepath)

    def _open_folder_for_filepath(self, filepath: str):
        if not filepath or not isinstance(filepath, str):
            return
        filepath = os.path.abspath(filepath)
        folder = os.path.dirname(filepath)
        if sys.platform == "win32":
            norm_file = os.path.normpath(filepath)
            norm_folder = os.path.normpath(folder)
            # Pass command string directly to Popen with shell=False.
            # This ensures CreateProcessW receives explorer.exe /select,"C:\path"
            # without list2cmdline placing quotes before /select, (which broke paths with spaces).
            if os.path.isfile(norm_file):
                try:
                    subprocess.Popen(f'explorer.exe /select,"{norm_file}"', shell=False)
                    return
                except Exception as e:
                    logger.warning("explorer.exe /select failed: %s", e)
            if os.path.isdir(norm_folder):
                try:
                    os.startfile(norm_folder)
                    return
                except Exception as e:
                    logger.warning("os.startfile failed: %s", e)
                    try:
                        subprocess.Popen(f'explorer.exe "{norm_folder}"', shell=False)
                        return
                    except Exception as e2:
                        logger.warning("explorer.exe folder failed: %s", e2)
            QMessageBox.warning(self, "Location Unavailable", f"Cannot open folder location:\n{filepath}\n\nThe file or containing folder does not exist on disk.")
        elif sys.platform == "darwin":
            if os.path.isfile(filepath):
                try:
                    subprocess.Popen(["open", "-R", filepath])
                    return
                except Exception:
                    pass
            if os.path.isdir(folder):
                subprocess.Popen(["open", folder])
            else:
                QMessageBox.warning(self, "Location Unavailable", f"Folder does not exist:\n{folder}")
        else:
            if os.path.isdir(folder):
                subprocess.Popen(["xdg-open", folder])
            else:
                QMessageBox.warning(self, "Location Unavailable", f"Folder does not exist:\n{folder}")

    def _copy_path_for_row(self, row: int):
        info = self._get_row_info(row)
        if info:
            QApplication.clipboard().setText(info.filepath)
            self.status_label.setText("Path copied to clipboard")
            self._show_toast("Path copied to clipboard", 'success')
            QTimer.singleShot(2000, lambda: self.status_label.setText("Ready"))

    def _remove_row_from_list(self, row: int):
        info = self._get_row_info(row)
        if info:
            # Identity match: filepath-string comparison misses case variants
            # on Windows (C:\A.mp4 vs c:\a.mp4) and drops wrong rows if paths repeat.
            self.media_infos = [v for v in self.media_infos if v is not info]
            # Remember user-removed files so watch mode doesn't re-add them on
            # the next poll while they still exist on disk.
            self._user_removed_paths.add(os.path.normcase(os.path.normpath(info.filepath)))
            self.table.removeRow(row)
            _gi = self._grid_item(info)
            if _gi:
                row_item = self.grid_view.row(_gi)
                if row_item >= 0: self.grid_view.takeItem(row_item)
            # Keep filtered_rows consistent: every index above the removed row
            # shifts down by one (prevents later bulk ops targeting stale rows).
            self.filtered_rows.discard(row)
            self.filtered_rows = {r - 1 if r > row else r for r in self.filtered_rows}
            # Renames/deletes invalidate the watch-mode path baseline
            self._known_files_dirty = True
            self._stats_dirty = True
            if self.table.rowCount() == 0:
                self.view_stack.setCurrentIndex(2)
                self.btn_process.setEnabled(False)
                self.btn_relocate.setEnabled(False)
                self.btn_find_dupes.setEnabled(False)
                self.btn_clear.setVisible(False)
            self._update_stats()

    def _on_remove_selected(self):
        selected_rows = set()
        for rng in self.table.selectedRanges():
            for row in range(rng.topRow(), rng.bottomRow() + 1): selected_rows.add(row)
        was_sorting = self.table.isSortingEnabled()
        self.table.setSortingEnabled(False)
        try:
            for row in sorted(list(selected_rows), reverse=True):
                # Skip filtered-out (hidden) rows: they aren't really part of
                # the user's visible selection (mirrors _on_delete_selected).
                if row < self.table.rowCount() and not self.table.isRowHidden(row):
                    self._remove_row_from_list(row)
        finally:
            self.table.setSortingEnabled(was_sorting)

    def _find_row_for_info(self, target_info) -> int:
        """Find the current row index of a MediaInfo object by identity."""
        if target_info is None:
            return -1
        for row in range(self.table.rowCount()):
            if self._get_row_info(row) is target_info:
                return row
        return -1

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
                    if self.table.isRowHidden(row):
                        continue  # filtered-out rows are not really selected for delete
                    info = self._get_row_info(row)
                    if info: selected_rows[row] = info
        if not selected_rows:
            QMessageBox.information(self, "No Selection", "Please select files to delete."); return
        msg_box = QMessageBox(self)
        msg_box.setWindowTitle("Delete Files")
        msg_box.setText(f"Are you sure you want to send {len(selected_rows)} file(s) to the Recycle Bin?")
        recycle_btn = msg_box.addButton("Send to Recycle Bin", QMessageBox.ButtonRole.YesRole)
        cancel_btn = msg_box.addButton("Cancel", QMessageBox.ButtonRole.RejectRole)
        msg_box.setDefaultButton(recycle_btn)
        self._enter_modal()
        try:
            msg_box.exec()
        finally:
            self._exit_modal()
        clicked = msg_box.clickedButton()
        if clicked == cancel_btn: return
        target_infos = list(selected_rows.values())
        self._release_file_locks([info.filepath for info in target_infos])
        success_count = 0
        error_files = []
        was_sorting = self.table.isSortingEnabled()
        self.table.setSortingEnabled(False)
        self._updating_table = True
        try:
            for info in target_infos:
                filepath = info.filepath
                sidecars = find_sidecars(filepath)
                if send_to_recycle_bin(filepath):
                    trashed = [filepath]
                    for sidecar in sidecars:
                        if send_to_recycle_bin(sidecar):
                            trashed.append(sidecar)
                        else:
                            error_files.append(f"{os.path.basename(sidecar)}: Could not recycle sidecar")
                    append_rename_audit([(p, "(recycle bin)") for p in trashed], op="delete")
                    cur_row = self._find_row_for_info(info)
                    if cur_row >= 0:
                        self._remove_row_from_list(cur_row)
                    success_count += 1
                else: error_files.append(f"{info.filename}: Could not recycle")
        finally:
            self._updating_table = False
            self.table.setSortingEnabled(was_sorting)
        self._update_stats()
        if error_files:
            QMessageBox.warning(self, "Deletion Errors", f"Failed to delete {len(error_files)} file(s):\n\n" + "\n".join(error_files[:10]))
        else:
            self.status_label.setText(f"Deleted {success_count} file(s).")
            self._show_toast(f"Deleted {success_count} file(s).", 'success')

    def _set_rating_for_row(self, row: int, rating: str):
        target_rows = []
        if row == -1:
            for rng in self.table.selectedRanges():
                for r in range(rng.topRow(), rng.bottomRow() + 1):
                    if r not in target_rows:
                        target_rows.append(r)
        else:
            target_rows = [row]

        was_sorting = self.table.isSortingEnabled()
        self.table.setSortingEnabled(False)
        try:
            for r in target_rows:
                if r >= self.table.rowCount(): continue
                self._ensure_widgets_for_row(r)
                rating_widget = self.table.cellWidget(r, self.COL_RATING)
                if rating_widget:
                    idx = rating_widget.findText(rating)
                    if idx >= 0:
                        rating_widget.setCurrentIndex(idx)
                rating_item = self.table.item(r, self.COL_RATING)
                if rating_item:
                    rating_item.setText(rating)
                    rating_item.sort_key = int(rating) if rating.isdigit() else 0
                self._update_row_preview(r, refresh_stats=False)
        finally:
            self.table.setSortingEnabled(was_sorting)
        self._update_stats()

    def _on_item_changed(self, item: QTableWidgetItem):
        if self._updating_table: return
        if item.column() != self.COL_FILENAME: return
        row = item.row()
        info = self._get_row_info(row)
        if not info: return
        new_text = item.text().strip()
        old_text = info.filename
        if not new_text:
            # Empty edit: restore the cell so it doesn't desync from
            # info.filename and advertise a ghost "pending rename" in previews.
            if item.text() != old_text:
                self._updating_table = True
                item.setText(old_text)
                self._updating_table = False
            return
        if new_text == old_text: return
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
            if sys.platform == "win32" and same_file and os.path.abspath(src) != os.path.abspath(dst):
                tmp_dst = dst + f".__mf_tmp_{random.randint(10000, 99999)}__"
                os.rename(src, tmp_dst)
                os.rename(tmp_dst, dst)
            else:
                os.rename(src, dst)
        except Exception as e:
            self.table.setSortingEnabled(was_sorting)
            QMessageBox.warning(self, "Rename Error", f"Cannot rename file:\n{e}")
            self._updating_table = True
            try:
                item.setText(old_text)
            finally:
                self._updating_table = False
            return

        try:
            info.filepath = dst
            info.filename = os.path.basename(dst)
            info.extension = os.path.splitext(dst)[1]
            item.setToolTip(dst)
            self._updating_table = True
            try:
                item.setText(info.filename)
            finally:
                self._updating_table = False
            _gi = self._grid_item(info)
            if _gi:
                _gi.setText(info.filename)
                _gi.setToolTip(dst)
            self._known_files_dirty = True
            # Record undo BEFORE follow-up work: a sidecar/UI failure after a
            # successful os.rename must not leave the rename un-undoable.
            self._add_to_history(src, dst, row)
            try:
                moved_extra = self._move_sidecars(src, dst)
            except Exception as sidecar_err:
                logger.warning("Sidecar move error after rename (%s -> %s): %s", src, dst, sidecar_err)
                moved_extra = []
            if moved_extra:
                # Attach sidecar pairs to the history entry just created
                try:
                    self._rename_history[-1]['extra'].extend(moved_extra)
                except Exception:
                    pass
            self._refresh_row_dates(info)
            self._update_date_items(row, info)
            self._update_row_preview(row)
            self._update_stats()
            self.btn_undo.setEnabled(True)
        except Exception as e:
            logger.error("UI update error after rename (%s -> %s): %s", src, dst, e)
        finally:
            self.table.setSortingEnabled(was_sorting)

    def _on_process_all(self):
        ready_rows = []
        main_win = self.window()
        keep_ext = getattr(main_win, 'naming_keep_extension', True)
        
        for row in range(self.table.rowCount()):
            if self.table.isRowHidden(row): continue
            info = self._get_row_info(row)
            if not info or not info.is_valid: continue
            artist_widget = self.table.cellWidget(row, self.COL_ARTIST)
            rating_widget = self.table.cellWidget(row, self.COL_RATING)
            artist = artist_widget.text().strip() if artist_widget else (self.table.item(row, self.COL_ARTIST).text().strip() if self.table.item(row, self.COL_ARTIST) else getattr(info, 'parsed_artist', ''))
            rating = rating_widget.currentText() if rating_widget else (self.table.item(row, self.COL_RATING).text().strip() if self.table.item(row, self.COL_RATING) else (getattr(info, 'parsed_rating', '—') or "—"))
            if self._is_naming_data_complete(artist, rating, info):
                new_name = self._get_templated_name(artist, rating, info)
                current_display_name = self.table.item(row, self.COL_FILENAME).text().strip() if self.table.item(row, self.COL_FILENAME) else ""
                target_display = new_name + (info.extension if keep_ext else "") if new_name else ""
                if target_display and target_display != current_display_name:
                    ready_rows.append((row, info, target_display))
        if not ready_rows:
            QMessageBox.information(self, "Nothing to Process", "No files are ready to rename."); return

        self._enter_modal()
        try:
            reply = QMessageBox.question(self, "Confirm Rename", f"This will rename {len(ready_rows)} file{'s' if len(ready_rows) != 1 else ''}.\n\nYou can undo via Ctrl+Z. Continue?", QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No, QMessageBox.StandardButton.No)
            if reply != QMessageBox.StandardButton.Yes: return
            success_count = 0
            auto_renamed = 0
            error_count = 0
            errors = []
            was_sorting = self.table.isSortingEnabled()
            self.table.setSortingEnabled(False)
            self._release_file_locks([info.filepath for _, info, _ in ready_rows])

            # Re-map row by info identity to avoid row shifts from background timers
            id_to_row = {}
            for r in range(self.table.rowCount()):
                ri = self._get_row_info(r)
                if ri is not None:
                    id_to_row[id(ri)] = r

            try:
                for _, info, target_display in ready_rows:
                    row = id_to_row.get(id(info), -1)
                    if row < 0 or row >= self.table.rowCount():
                        continue
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
                        auto_renamed += 1
                    # Validate UI handles BEFORE touching the filesystem so a missing
                    # table item can't orphan a successful rename from undo history.
                    fname_item = self.table.item(row, self.COL_FILENAME)
                    status_item = self.table.item(row, self.COL_STATUS)
                    if fname_item is None or status_item is None:
                        # Skip the row instead of raising: an unhandled exception in
                        # a Qt slot aborts the whole batch (and PyQt6 the process).
                        error_count += 1
                        errors.append(f"{target_display}: table row {row} is missing UI items; rename skipped")
                        continue
                    try:
                        if sys.platform == "win32" and same_file and os.path.abspath(src) != os.path.abspath(dst):
                            tmp_dst = dst + f".__mf_tmp_{random.randint(10000, 99999)}__"
                            os.rename(src, tmp_dst)
                            os.rename(tmp_dst, dst)
                        else:
                            os.rename(src, dst)
                        info.filepath = dst
                        info.filename = os.path.basename(dst)
                        new_ext = os.path.splitext(dst)[1]
                        if new_ext:
                            # keep_extension=False yields an extensionless dst — never
                            # clobber the known extension with "" or it can't be restored.
                            info.extension = new_ext
                        self._updating_table = True
                        try:
                            fname_item.setText(info.filename)
                            fname_item.setToolTip(dst)
                            status_item.setText("Renamed")
                            status_item.setForeground(QColor("#6dd5ed"))
                        finally:
                            self._updating_table = False
                        _gi = self._grid_item(info)
                        if _gi: _gi.setText(info.filename)
                        # Record undo BEFORE follow-up work so a sidecar/UI failure
                        # can't leave a successful rename un-undoable + falsely
                        # marked Error.
                        self._add_to_history(src, dst, row)
                        try:
                            moved_extra = self._move_sidecars(src, dst)
                        except Exception as sidecar_err:
                            logger.warning("Sidecar move error after rename (%s -> %s): %s", src, dst, sidecar_err)
                            moved_extra = []
                        if moved_extra:
                            # Attach sidecar pairs to the history entry just created
                            try:
                                self._rename_history[-1]['extra'].extend(moved_extra)
                            except Exception:
                                pass
                        self._refresh_row_dates(info)
                        self._update_date_items(row, info)
                        self._update_row_preview(row)
                        success_count += 1
                    except Exception as e:
                        error_count += 1
                        errors.append(f"{info.filename}: {e}")
                        status_item = self.table.item(row, self.COL_STATUS)
                        if status_item:
                            self._updating_table = True
                            try:
                                status_item.setText("Error")
                                status_item.setForeground(QColor("#f87171"))
                                status_item.setToolTip(str(e))
                            finally:
                                self._updating_table = False
                if success_count > 0:
                    self._known_files_dirty = True
            finally:
                self._updating_table = False
                self.table.setSortingEnabled(was_sorting)
        finally:
            self._exit_modal()
        msg = f"Successfully renamed {success_count} file{'s' if success_count != 1 else ''}."
        if auto_renamed > 0:
            # The preview can't know about on-disk collisions ahead of time —
            # tell the user some files got an automatic _N suffix.
            msg += f"\n\n• {auto_renamed} file{'s' if auto_renamed != 1 else ''} already existed under the target name and {'were' if auto_renamed != 1 else 'was'} auto-renamed with a _N suffix."
        if error_count > 0:
            msg += f"\n\n• {error_count} error{'s' if error_count != 1 else ''}:\n"
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

    def _add_to_history(self, src: str, dst: str, row: int, clear_redo=True, extra=None, op=None):
        extra = list(extra or [])
        self._rename_history.append({'timestamp': datetime.now().isoformat(), 'src': src, 'dst': dst, 'row': row,
                                     'filename': os.path.basename(dst), 'extra': extra})
        # C3: append-only audit trail (forward renames; undo/redo are implied)
        append_rename_audit([(src, dst)] + extra, op=op)
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
        same_file = os.path.normcase(os.path.abspath(src)) == os.path.normcase(os.path.abspath(dst))
        if os.path.exists(dst) and (not os.path.exists(src) or same_file):
            self._release_file_locks([dst, src])
            try:
                shutil.move(dst, src)
                # Revert sidecar moves (best-effort; failures never block undo)
                extra_done = []
                for o_, n_ in reversed(last.get('extra') or []):
                    if os.path.exists(n_) and (not os.path.exists(o_) or os.path.normcase(os.path.abspath(n_)) == os.path.normcase(os.path.abspath(o_))):
                        try:
                            shutil.move(n_, o_)
                            extra_done.append((o_, n_))
                        except OSError as e_:
                            logger.warning("Undo sidecar (%s -> %s): %s", n_, o_, e_)
                
                # Locate row dynamically by matching dst path (sort-safe)
                target_row = -1
                for r in range(self.table.rowCount()):
                    inf = self._get_row_info(r)
                    if inf and os.path.normcase(os.path.abspath(inf.filepath)) == os.path.normcase(os.path.abspath(dst)):
                        target_row = r
                        break
                
                try:
                    if target_row >= 0 and target_row < self.table.rowCount():
                        info = self._get_row_info(target_row)
                        if info:
                            self._updating_table = True
                            info.filepath = src
                            info.filename = os.path.basename(src)
                            undo_ext = os.path.splitext(src)[1]
                            if undo_ext:
                                info.extension = undo_ext
                            self._refresh_row_dates(info)
                            self.table.item(target_row, self.COL_FILENAME).setText(info.filename)
                            self.table.item(target_row, self.COL_FILENAME).setToolTip(src)
                            self.table.item(target_row, self.COL_STATUS).setText("Valid")
                            self.table.item(target_row, self.COL_STATUS).setForeground(QColor("#34d399"))
                            _gi = self._grid_item(info)
                            if _gi: _gi.setText(info.filename)
                            self._update_date_items(target_row, info)
                            self._update_row_preview(target_row)
                except Exception as te:
                    # Table update failed after successful move — attempt to roll back
                    logger.exception("Table update failed after move; rolling back")
                    try:
                        shutil.move(src, dst)
                    except Exception:
                        logger.error("ROLLBACK FAILED for %s -> %s; filesystem and UI are out of sync", src, dst)
                        # Keep the history entry so the operation remains visible
                        # in the undo stack and retryable; dropping it silently
                        # turned the rename permanently un-undoable.
                        self._rename_history.append(last)
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
                self.status_label.setText(f"Undone: {os.path.basename(dst)}")
                self._show_toast(f"Undone: {os.path.basename(dst)}", 'success')
                self._update_stats()
                self._known_files_dirty = True
                append_rename_audit([(dst, src)] + [(n_, o_) for o_, n_ in extra_done], op="undo")
                self._redo_history.append(last)
                self.btn_redo.setEnabled(True)
            except Exception as e:
                QMessageBox.warning(self, "Undo Failed", f"Cannot undo rename:\n{e}")
                if not self._rename_history or self._rename_history[-1] is not last:
                    self._rename_history.append(last)
        else:
            self._rename_history.append(last)
            QMessageBox.warning(self, "Undo Unavailable", "Cannot undo: file has been moved or renamed again.")
        self.btn_undo.setEnabled(len(self._rename_history) > 0)
        self.btn_redo.setEnabled(len(self._redo_history) > 0)

    def _on_redo_rename(self):
        if not self._redo_history: return
        last = self._redo_history.pop()
        src = last['src']
        dst = last['dst']
        same_file = os.path.normcase(os.path.abspath(src)) == os.path.normcase(os.path.abspath(dst))
        if os.path.exists(src) and (not os.path.exists(dst) or same_file):
            self._release_file_locks([src, dst])
            try:
                shutil.move(src, dst)
                extra_done = []
                for o_, n_ in (last.get('extra') or []):
                    if os.path.exists(o_) and (not os.path.exists(n_) or os.path.normcase(os.path.abspath(o_)) == os.path.normcase(os.path.abspath(n_))):
                        try:
                            shutil.move(o_, n_)
                            extra_done.append((o_, n_))
                        except OSError as e_:
                            logger.warning("Redo sidecar (%s -> %s): %s", o_, n_, e_)
                
                # Locate row dynamically by matching src path (sort-safe)
                target_row = -1
                for r in range(self.table.rowCount()):
                    inf = self._get_row_info(r)
                    if inf and os.path.normcase(os.path.abspath(inf.filepath)) == os.path.normcase(os.path.abspath(src)):
                        target_row = r
                        break
                
                try:
                    if target_row >= 0 and target_row < self.table.rowCount():
                        info = self._get_row_info(target_row)
                        if info:
                            self._updating_table = True
                            info.filepath = dst
                            info.filename = os.path.basename(dst)
                            redo_ext = os.path.splitext(dst)[1]
                            if redo_ext:
                                info.extension = redo_ext
                            self._refresh_row_dates(info)
                            self.table.item(target_row, self.COL_FILENAME).setText(info.filename)
                            self.table.item(target_row, self.COL_FILENAME).setToolTip(dst)
                            self.table.item(target_row, self.COL_STATUS).setText("Renamed")
                            self.table.item(target_row, self.COL_STATUS).setForeground(QColor("#6dd5ed"))
                            _gi = self._grid_item(info)
                            if _gi: _gi.setText(info.filename)
                            self._update_date_items(target_row, info)
                            self._update_row_preview(target_row)
                except Exception as te:
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
                self.status_label.setText(f"Redone: {os.path.basename(dst)}")
                self._show_toast(f"Redone: {os.path.basename(dst)}", 'success')
                self._update_stats()
                self._known_files_dirty = True
                self._add_to_history(src, dst, target_row, clear_redo=False, extra=last.get('extra'), op="redo")
            except Exception as e:
                QMessageBox.warning(self, "Redo Failed", f"Cannot redo rename:\n{e}")
                self._redo_history.append(last)
        else:
            self._redo_history.append(last)
            QMessageBox.warning(self, "Redo Unavailable", "Cannot redo: file has been deleted, moved, or renamed again.")
        self.btn_redo.setEnabled(len(self._redo_history) > 0)
        self.btn_undo.setEnabled(len(self._rename_history) > 0)

    def _apply_saved_file_data_to_row(self, row: int):
        """Apply persisted artist/rating/tags (from config) to a single row."""
        info = self._get_row_info(row)
        if not info: return
        data = self._saved_file_data.get(os.path.normcase(os.path.normpath(info.filepath)))
        if not data: return

        artist = data.get('artist', '')
        if artist:
            info.parsed_artist = artist
            artist_item = self.table.item(row, self.COL_ARTIST)
            if artist_item: artist_item.setText(artist)
            artist_widget = self.table.cellWidget(row, self.COL_ARTIST)
            if artist_widget: artist_widget.setText(artist)

        rating = data.get('rating', '—')
        if rating != '—':
            info.parsed_rating = rating
            rating_item = self.table.item(row, self.COL_RATING)
            if rating_item:
                rating_item.setText(rating)
                rating_item.sort_key = int(rating) if rating.isdigit() else 0
            rating_widget = self.table.cellWidget(row, self.COL_RATING)
            if rating_widget:
                idx = rating_widget.findText(rating)
                if idx >= 0: rating_widget.setCurrentIndex(idx)

        raw_tags = data.get('tags', [])
        if isinstance(raw_tags, str):
            tags = [t.strip() for t in raw_tags.split(',') if t.strip()]
        elif isinstance(raw_tags, list):
            tags = [str(t).strip() for t in raw_tags if str(t).strip()]
        else:
            tags = []
        if tags:
            info.tags = tags
            tags_item = self.table.item(row, self.COL_TAGS)
            if tags_item: tags_item.setText(", ".join(tags))
            tags_widget = self.table.cellWidget(row, self.COL_TAGS)
            if tags_widget: tags_widget.setText(", ".join(tags))
        # Keep entries in _saved_file_data so future rescans/reloads preserve user metadata
        pass

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
        if mode == 'visual' and self.media_type in ('audio', 'pdf'):
            media_name = "Audio" if self.media_type == 'audio' else "PDF"
            QMessageBox.warning(self, "Unsupported", f"Visual duplicates scanning is not supported for {media_name} files."); return
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
        prog_dlg = QProgressDialog(f"Scanning duplicates ({task_name})…", "Cancel", 0, len(valid_infos), self)
        prog_dlg.setWindowModality(Qt.WindowModality.ApplicationModal)
        prog_dlg.setMinimumDuration(300)
        prog_dlg.setValue(0)
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
            skipped = 0
            for idx, info in enumerate(valid_infos):
                if prog_dlg.wasCanceled():
                    break
                # Head-only fingerprint first (fast on multi-GB videos); exact
                # groups are confirmed with a full-file hash below so files
                # that differ only in the middle are never labeled "exact".
                if mode == 'exact': h = calculate_file_hash(info.filepath, head_only=True)
                else: h = calculate_perceptual_hash(info.filepath, info.media_type)
                if h: hashes[id(info)] = h
                else: skipped += 1
                self.progress_bar.setValue(idx + 1)
                prog_dlg.setValue(idx + 1)
                # Keep UI responsive while EXCLUDING user input events — plain
                # processEvents() let sort clicks / Delete shortcut mutate rows
                # mid-hash, which mislabeled the wrong files as duplicates.
                QApplication.processEvents(QEventLoop.ProcessEventsFlag.ExcludeUserInputEvents)
        finally:
            prog_dlg.close()
            self.btn_find_dupes.setEnabled(True)
            if watch_was_active and getattr(self, '_watch_enabled', False):
                self._watch_timer.start(3000)
        self.progress_bar.setVisible(False)
        if prog_dlg.wasCanceled():
            self.status_label.setText("Duplicate scan cancelled.")
            return
        self.status_label.setText("Processing duplicates list…")
        QApplication.processEvents(QEventLoop.ProcessEventsFlag.ExcludeUserInputEvents)
        groups = []  # each group is a list of id(info)
        if mode == 'exact':
            hash_to_ids = {}
            for i, h in hashes.items(): hash_to_ids.setdefault(h, []).append(i)
            id_to_info = {id(info): info for info in valid_infos}
            # Full-file hashing can take MINUTES on multi-GB head-matches.
            # Without progress + event pumping this loop hard-froze the GUI.
            confirm_total = sum(len(grp) for grp in hash_to_ids.values() if len(grp) >= 2)
            self.progress_bar.setVisible(True)
            self.progress_bar.setMaximum(max(1, confirm_total))
            self.progress_bar.setValue(0)
            self.progress_bar.setFormat("Confirming duplicates (full hash): %v/%m…")
            confirm_prog = QProgressDialog("Confirming duplicates (full-file hashing)…", "Cancel", 0, max(1, confirm_total), self)
            confirm_prog.setWindowModality(Qt.WindowModality.ApplicationModal)
            confirm_prog.setMinimumDuration(300)
            confirm_prog.setValue(0)
            confirmed = 0
            confirmation_cancelled = False
            try:
                for h, grp in hash_to_ids.items():
                    if len(grp) < 2: continue
                    if confirm_prog.wasCanceled():
                        confirmation_cancelled = True
                        break
                    # Confirm with a full-file hash: same size + head/tail does
                    # NOT prove the middles match. Only full-hash-equal files group.
                    full_to_ids = {}
                    for iid in grp:
                        if confirm_prog.wasCanceled():
                            confirmation_cancelled = True
                            break
                        info = id_to_info.get(iid)
                        full = calculate_file_hash(info.filepath, head_only=False) if info is not None else None
                        if full: full_to_ids.setdefault(full, []).append(iid)
                        else: skipped += 1
                        confirmed += 1
                        self.progress_bar.setValue(confirmed)
                        confirm_prog.setValue(confirmed)
                        QApplication.processEvents(QEventLoop.ProcessEventsFlag.ExcludeUserInputEvents)
                    if confirmation_cancelled:
                        break
                    for full_grp in full_to_ids.values():
                        if len(full_grp) > 1: groups.append(full_grp)
            finally:
                confirm_prog.close()
                self.progress_bar.setVisible(False)
            if confirmation_cancelled:
                self._clear_highlights()
                self.status_label.setText("Duplicate confirmation cancelled.")
                return
        else:
            # Single-linkage grouping: compare against ANY member of the group,
            # not just the representative.
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
                        if any(hamming_distance(hashes[m], hashes[cand]) <= 5 for m in current_group):
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
            skip_note = f" ({skipped} unreadable, skipped)" if skipped else ""
            self.status_label.setText(f"No duplicates found.{skip_note}")
            QMessageBox.information(self, "No Duplicates", f"No {mode} duplicates found in the current list.{skip_note}")
            for row in range(self.table.rowCount()):
                self.table.setRowHidden(row, False)
                info = self._get_row_info(row)
                _gi = self._grid_item(info) if info else None
                if _gi: _gi.setHidden(False)
            self._update_stats()
            return
        was_sorting = self.table.isSortingEnabled()
        self.table.setSortingEnabled(False)
        total_dupes = 0
        for group_idx, grp in enumerate(groups):
            bg_color = QColor(239, 68, 68, 38) if group_idx % 2 == 0 else QColor(245, 158, 11, 38)
            for iid in grp:
                row = id_to_row.get(iid, -1)
                if row < 0: continue
                total_dupes += 1
                status_item = self.table.item(row, self.COL_STATUS)
                if status_item:
                    status_item.setText(f"Dup Group {group_idx + 1}")
                    status_item.setForeground(QColor("#f87171"))
                    status_item.sort_key = group_idx
                for col in range(self.table.columnCount()):
                    item = self.table.item(row, col)
                    if item: item.setBackground(bg_color)
        # Sort so duplicate groups appear at top
        self.table.setSortingEnabled(True)
        self.table.sortByColumn(self.COL_STATUS, Qt.SortOrder.AscendingOrder)
        self.table.setSortingEnabled(was_sorting)
        # Hide non-duplicates based on post-sort positions
        self.filtered_rows.clear()
        for row in range(self.table.rowCount()):
            status_item = self.table.item(row, self.COL_STATUS)
            is_dupe = bool(status_item and (status_item.text().startswith("Dup Group") or status_item.text().startswith("⚠️ Dup Group")))
            self.table.setRowHidden(row, not is_dupe)
            info = self._get_row_info(row)
            _gi = self._grid_item(info) if info else None
            if _gi: _gi.setHidden(not is_dupe)
            if is_dupe:
                self.filtered_rows.add(row)
        self.status_label.setText(f"Found {len(groups)} duplicate group(s) ({total_dupes} files total){f', {skipped} skipped' if skipped else ''}. Click 'Sync Files' to reset view.")
        self._update_stats()

    def _clear_highlights(self):
        for row in range(self.table.rowCount()):
            info = self._get_row_info(row)
            if info:
                status_item = self.table.item(row, self.COL_STATUS)
                if status_item:
                    if info.is_valid:
                        status_item.setText("Valid"); status_item.setForeground(QColor("#34d399"))
                    else:
                        status_item.setText("Unsupported"); status_item.setForeground(QColor("#f87171"))
                    status_item.sort_key = None
                for col in range(self.table.columnCount()):
                    item = self.table.item(row, col)
                    if item: item.setBackground(QBrush(Qt.BrushStyle.NoBrush))

    def _toggle_view_mode(self, checked):
        if self.table.rowCount() == 0:
            self.view_stack.setCurrentIndex(2)  # empty state
        elif checked:
            self.view_stack.setCurrentIndex(1)
        else:
            self.view_stack.setCurrentIndex(0)
        if checked:
            self.btn_view_mode.setText("List View")
        else:
            self.btn_view_mode.setText("Grid View")

    def _update_theme_styling(self, is_dark: bool):
        self._update_shadow_color()

    def _update_shadow_color(self):
        if not hasattr(self, '_panel_shadow') or not self._panel_shadow:
            return
        is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark' if self.window() else True
        if is_dark:
            self._panel_shadow.setColor(QColor(0, 0, 0, 160))
        else:
            self._panel_shadow.setColor(QColor(15, 23, 42, 65))

    def _get_overlay_target_rect(self):
        if not hasattr(self, 'content_container') or not self.content_container:
            return QRect(0, 0, 350, 400)
        c_w = self.content_container.width()
        c_h = self.content_container.height()
        margin_r = 10
        margin_t = 8
        margin_b = 8
        max_w = max(280, int(c_w * 0.70))
        target_w = max(280, min(getattr(self, '_side_panel_width', 350), max_w))
        target_x = max(0, c_w - target_w - margin_r)
        target_y = margin_t
        target_h = max(100, c_h - margin_t - margin_b)
        return QRect(target_x, target_y, target_w, target_h)

    def _reposition_side_panel(self, animate=False):
        if not hasattr(self, 'side_panel') or not hasattr(self, 'content_container'):
            return
        if not self.side_panel.isVisible():
            self._sync_resize_handle()
            return
        target_rect = self._get_overlay_target_rect()
        if animate:
            if hasattr(self, '_panel_anim') and self._panel_anim:
                try:
                    self._panel_anim.stop()
                    self._panel_anim.finished.disconnect()
                except Exception:
                    pass
            start_rect = QRect(self.content_container.width() + 10, target_rect.y(), target_rect.width(), target_rect.height())
            self.side_panel.setGeometry(start_rect)
            self._panel_anim = QPropertyAnimation(self.side_panel, b"geometry")
            self._panel_anim.setDuration(180)
            self._panel_anim.setStartValue(start_rect)
            self._panel_anim.setEndValue(target_rect)
            self._panel_anim.setEasingCurve(QEasingCurve.Type.OutCubic)
            self._panel_anim.valueChanged.connect(self._sync_resize_handle)
            self._panel_anim.start()
        else:
            self.side_panel.setGeometry(target_rect)
            self._sync_resize_handle()

    def _sync_resize_handle(self):
        if hasattr(self, '_panel_resize_handle') and self._panel_resize_handle:
            if hasattr(self, 'side_panel') and self.side_panel.isVisible():
                p_geo = self.side_panel.geometry()
                self._panel_resize_handle.setGeometry(p_geo.x() - 6, p_geo.y(), 12, p_geo.height())
                self._panel_resize_handle.setVisible(True)
                self._panel_resize_handle.raise_()
            else:
                self._panel_resize_handle.setVisible(False)

    def _show_overlay_panel(self, target_widget):
        if hasattr(self, '_panel_anim') and self._panel_anim:
            try:
                self._panel_anim.stop()
                self._panel_anim.finished.disconnect()
            except Exception:
                pass

        was_visible = self.side_panel.isVisible()
        self.side_panel.setCurrentWidget(target_widget)
        target_widget.setVisible(True)

        if not was_visible:
            self.side_panel.setVisible(True)
            self.side_panel.raise_()
            self._update_shadow_color()
            self._reposition_side_panel(animate=True)
        else:
            self.side_panel.raise_()
            self._sync_resize_handle()

    def _hide_overlay_panel(self):
        if not hasattr(self, 'side_panel') or not self.side_panel.isVisible():
            if hasattr(self, '_panel_resize_handle'):
                self._panel_resize_handle.setVisible(False)
            return

        if hasattr(self, '_panel_resize_handle'):
            self._panel_resize_handle.setVisible(False)

        if hasattr(self, '_panel_anim') and self._panel_anim:
            try:
                self._panel_anim.stop()
                self._panel_anim.finished.disconnect()
            except Exception:
                pass

        cur_rect = self.side_panel.geometry()
        end_rect = QRect(self.content_container.width() + 10, cur_rect.y(), cur_rect.width(), cur_rect.height())
        self._panel_anim = QPropertyAnimation(self.side_panel, b"geometry")
        self._panel_anim.setDuration(160)
        self._panel_anim.setStartValue(cur_rect)
        self._panel_anim.setEndValue(end_rect)
        self._panel_anim.setEasingCurve(QEasingCurve.Type.InCubic)
        self._panel_anim.finished.connect(self._on_overlay_hidden)
        self._panel_anim.start()

    def _on_overlay_hidden(self):
        if not (self.btn_toggle_preview.isChecked() or self.btn_toggle_stats.isChecked()):
            self.side_panel.setVisible(False)
        self._sync_resize_handle()

    def _on_splitter_moved(self, pos, index):
        pass

    def _update_splitter_sizes(self, open_panel: bool):
        pass

    def _toggle_preview(self, checked):
        self.btn_toggle_preview.setChecked(checked)
        if checked:
            if self.btn_toggle_stats.isChecked():
                self.btn_toggle_stats.setChecked(False)
            self._show_overlay_panel(self.preview_panel)
            self.stats_panel.setVisible(False)
            if self.table.rowCount() > 0 and len(self.table.selectedRanges()) == 0:
                cur = self.table.currentRow()
                target = cur if cur >= 0 else 0
                self.table.selectRow(target)
            self._update_preview_pane()
        else:
            self.preview_panel.setVisible(False)
            self._stop_and_clear_media_player()
            if not self.btn_toggle_stats.isChecked():
                self._hide_overlay_panel()

    def _close_preview_pane(self):
        self._toggle_preview(False)

    def _build_stats_panel(self):
        is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark' if self.window() else True
        self.stats_panel = QFrame()
        self.stats_panel.setObjectName("statsSidePanel")
        self.stats_panel.setMinimumWidth(280)
        self.stats_panel.setVisible(False)
        layout = QVBoxLayout(self.stats_panel)
        layout.setContentsMargins(12, 12, 12, 12)
        layout.setSpacing(12)

        header_layout = QHBoxLayout()
        title = QLabel("Library Statistics")
        title.setStyleSheet("font-weight: bold; font-size: 13px; color: #a78bfa;")
        header_layout.addWidget(title)
        header_layout.addStretch()
        
        self.btn_close_stats = QPushButton("")
        self.btn_close_stats.setObjectName("btnClosePreview")
        self.btn_close_stats.setFixedSize(24, 24)
        self.btn_close_stats.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_close_stats.setIcon(get_vector_icon('close', is_dark))
        self.btn_close_stats.setIconSize(QSize(16, 16))
        self.btn_close_stats.setToolTip("Close Stats")
        self.btn_close_stats.clicked.connect(lambda: self._toggle_stats(False))
        header_layout.addWidget(self.btn_close_stats)
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
        if checked:
            if self.btn_toggle_preview.isChecked():
                self.btn_toggle_preview.setChecked(False)
                self._stop_and_clear_media_player()
            self._show_overlay_panel(self.stats_panel)
            self.preview_panel.setVisible(False)
            self._update_stats_dashboard()
        else:
            self.stats_panel.setVisible(False)
            if not self.btn_toggle_preview.isChecked():
                self._hide_overlay_panel()

    def _update_stats_dashboard(self):
        if not hasattr(self, 'stats_panel') or not self.stats_panel.isVisible():
            return
            
        # Clear old stats
        while self.stats_layout.count():
            item = self.stats_layout.takeAt(0)
            if item.widget():
                item.widget().deleteLater()
                
        visible_infos = []
        for r in range(self.table.rowCount()):
            if not self.table.isRowHidden(r):
                inf = self._get_row_info(r)
                if inf is not None:
                    visible_infos.append(inf)

        if not visible_infos:
            self.stats_layout.addWidget(QLabel("No media loaded or matching filters."))
            self.stats_layout.addStretch()
            return
            
        total_files = len(visible_infos)
        valid_files = sum(1 for i in visible_infos if i.is_valid)
        invalid_files = total_files - valid_files
        total_size = sum(i.size_bytes for i in visible_infos if getattr(i, 'size_bytes', 0))
        
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
        for i in visible_infos:
            if not i.is_valid: continue
            ext = os.path.splitext(i.filename)[1].lower() or "Unknown"
            formats[ext] = formats.get(ext, 0) + 1
            
        format_stats = {k: f"{v} ({(v/valid_files*100):.1f}%)" if valid_files > 0 else str(v) for k, v in sorted(formats.items(), key=lambda x: x[1], reverse=True)[:10]}
        if format_stats:
            add_section("Format Breakdown", format_stats)

        # Resolutions
        if self.media_type in ('video', 'image', 'all'):
            res = {}
            for i in visible_infos:
                if not i.is_valid: continue
                tag = getattr(i, 'resolution_tag', '') or (f"{i.width}x{i.height}" if i.width and i.height else "")
                if tag:
                    res[tag] = res.get(tag, 0) + 1
            res_stats = {k: str(v) for k, v in sorted(res.items(), key=lambda x: x[1], reverse=True)[:10]}
            if res_stats:
                add_section("Resolutions", res_stats)
                
        # Durations
        if self.media_type in ('video', 'audio', 'all'):
            durs = [i.duration_seconds for i in visible_infos if i.is_valid and hasattr(i, 'duration_seconds') and i.duration_seconds > 0]
            if durs:
                add_section("Duration", {
                    "Total": format_duration(sum(durs)),
                    "Average": format_duration(sum(durs)/len(durs)) if len(durs) > 0 else "0:00",
                    "Shortest": format_duration(min(durs)),
                    "Longest": format_duration(max(durs))
                })

        # Ratings
        ratings = {}
        for i in visible_infos:
            if not i.is_valid: continue
            _, parsed_rating = parse_naming_format(i.filename, getattr(i, 'media_type', None))
            r = parsed_rating or "Unrated"
            ratings[r] = ratings.get(r, 0) + 1
        rat_stats = {k: str(v) for k, v in sorted(ratings.items(), key=lambda x: (x[0] != "Unrated", float(x[0]) if x[0].replace('.','',1).isdigit() else 0), reverse=True)[:10]}
        if rat_stats:
            add_section("Ratings", rat_stats)
            
        # Tags
        tags = {}
        for i in visible_infos:
            if not i.is_valid: continue
            for t in getattr(i, 'tags', []):
                tags[t] = tags.get(t, 0) + 1
        tag_stats = {k: str(v) for k, v in sorted(tags.items(), key=lambda x: x[1], reverse=True)[:10]}
        if tag_stats:
            add_section("Top Tags", tag_stats)

        self.stats_layout.addStretch()

    def _build_preview_pane(self):
        is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark' if self.window() else True
        self.preview_panel = QFrame()
        self.preview_panel.setObjectName("previewPanel")
        self.preview_panel.setMinimumWidth(280)
        self.preview_panel.setVisible(False)
        preview_layout = QVBoxLayout(self.preview_panel)
        preview_layout.setContentsMargins(12, 12, 12, 12)
        preview_layout.setSpacing(10)
        header_layout = QHBoxLayout()
        self.preview_title = QLabel("Inspector")
        self.preview_title.setStyleSheet("font-size: 13px; font-weight: bold; color: #a78bfa;")
        self.preview_title.setWordWrap(True)
        self.btn_close_preview = QPushButton("")
        self.btn_close_preview.setObjectName("btnClosePreview")
        self.btn_close_preview.setFixedSize(24, 24)
        self.btn_close_preview.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_close_preview.clicked.connect(self._close_preview_pane)
        self.btn_close_preview.setIcon(get_vector_icon('close', is_dark))
        self.btn_close_preview.setIconSize(QSize(16, 16))
        self.btn_close_preview.setToolTip("Close Inspector")
        header_layout.addWidget(self.preview_title, 1)
        header_layout.addWidget(self.btn_close_preview)
        preview_layout.addLayout(header_layout)

        # Scroll area prevents widgets from squashing/overlapping in non-fullscreen or Large UI
        self.preview_scroll = QScrollArea()
        self.preview_scroll.setWidgetResizable(True)
        self.preview_scroll.setFrameShape(QFrame.Shape.NoFrame)
        self.preview_scroll.setStyleSheet("background: transparent;")

        self.preview_content = QWidget()
        content_layout = QVBoxLayout(self.preview_content)
        content_layout.setContentsMargins(0, 0, 0, 0)
        content_layout.setSpacing(10)

        self.preview_stack = QStackedWidget()
        self.preview_stack.setMinimumHeight(190)
        self.preview_stack.setMaximumHeight(240)
        self.preview_image = QLabel()
        self.preview_image.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.preview_image.setStyleSheet("background: rgba(10, 10, 20, 0.6); border-radius: 8px;")
        self.video_widget = QVideoWidget()
        self.video_widget.setStyleSheet("background: rgba(10, 10, 20, 0.6); border-radius: 8px;")
        self.no_preview_label = QLabel("Select a file to inspect")
        self.no_preview_label.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.no_preview_label.setStyleSheet("color: #7c7c9a; font-size: 12px; background: rgba(10, 10, 20, 0.4); border-radius: 8px;")
        self.preview_stack.addWidget(self.preview_image)
        self.preview_stack.addWidget(self.video_widget)
        self.preview_stack.addWidget(self.no_preview_label)
        self.preview_stack.setCurrentIndex(2)
        content_layout.addWidget(self.preview_stack)

        self.preview_controls = QFrame()
        self.preview_controls.setVisible(False)
        controls_layout = QVBoxLayout(self.preview_controls)
        controls_layout.setContentsMargins(4, 4, 4, 4)
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
        content_layout.addWidget(self.preview_controls)

        self.player = QMediaPlayer(self)
        self.audio_output = QAudioOutput(self)
        self.player.setAudioOutput(self.audio_output)
        self.player.setVideoOutput(self.video_widget)
        self.player.positionChanged.connect(self._on_player_position_changed)
        self.player.durationChanged.connect(self._on_player_duration_changed)
        self.player.playbackStateChanged.connect(self._on_player_state_changed)
        self.seek_slider.valueChanged.connect(self._on_slider_moved)

        # Inspector Metadata Grid
        self.insp_meta_frame = QFrame()
        self.insp_meta_frame.setObjectName("inspectorMetaFrame")
        self.insp_meta_frame.setVisible(False)
        meta_grid = QGridLayout(self.insp_meta_frame)
        meta_grid.setContentsMargins(8, 8, 8, 8)
        meta_grid.setHorizontalSpacing(8)
        meta_grid.setVerticalSpacing(4)
        
        lbl_fmt = QLabel("Format:")
        lbl_fmt.setStyleSheet("color: #7c7c9a; font-size: 11px;")
        self.insp_format = QLabel("—")
        self.insp_format.setStyleSheet("font-weight: 600; font-size: 11px;")
        
        lbl_res = QLabel("Resolution:")
        lbl_res.setStyleSheet("color: #7c7c9a; font-size: 11px;")
        self.insp_res = QLabel("—")
        self.insp_res.setStyleSheet("font-weight: 600; font-size: 11px;")
        
        lbl_dur = QLabel("Duration:")
        lbl_dur.setStyleSheet("color: #7c7c9a; font-size: 11px;")
        self.insp_dur = QLabel("—")
        self.insp_dur.setStyleSheet("font-weight: 600; font-size: 11px;")
        
        lbl_sz = QLabel("Size:")
        lbl_sz.setStyleSheet("color: #7c7c9a; font-size: 11px;")
        self.insp_size = QLabel("—")
        self.insp_size.setStyleSheet("font-weight: 600; font-size: 11px;")
        
        lbl_mod = QLabel("Modified:")
        lbl_mod.setStyleSheet("color: #7c7c9a; font-size: 11px;")
        self.insp_mtime = QLabel("—")
        self.insp_mtime.setStyleSheet("font-weight: 600; font-size: 11px;")
        
        meta_grid.addWidget(lbl_fmt, 0, 0)
        meta_grid.addWidget(self.insp_format, 0, 1)
        meta_grid.addWidget(lbl_res, 1, 0)
        meta_grid.addWidget(self.insp_res, 1, 1)
        meta_grid.addWidget(lbl_dur, 2, 0)
        meta_grid.addWidget(self.insp_dur, 2, 1)
        meta_grid.addWidget(lbl_sz, 3, 0)
        meta_grid.addWidget(self.insp_size, 3, 1)
        meta_grid.addWidget(lbl_mod, 4, 0)
        meta_grid.addWidget(self.insp_mtime, 4, 1)
        content_layout.addWidget(self.insp_meta_frame)

        # Rename Preview Box
        self.insp_rename_frame = QFrame()
        self.insp_rename_frame.setObjectName("inspectorRenameFrame")
        self.insp_rename_frame.setVisible(False)
        rename_layout = QVBoxLayout(self.insp_rename_frame)
        rename_layout.setContentsMargins(8, 6, 8, 6)
        rename_layout.setSpacing(2)
        lbl_target = QLabel("Rename Preview:")
        lbl_target.setStyleSheet("color: #7c7c9a; font-size: 10px; font-weight: 600; text-transform: uppercase;")
        self.insp_target_name = QLabel("—")
        self.insp_target_name.setWordWrap(True)
        self.insp_target_name.setStyleSheet("color: #34d399; font-weight: bold; font-size: 11px;")
        rename_layout.addWidget(lbl_target)
        rename_layout.addWidget(self.insp_target_name)
        content_layout.addWidget(self.insp_rename_frame)

        # Quick Actions Grid (2-column layout to prevent clipping in all UI scales)
        self.insp_actions_frame = QFrame()
        self.insp_actions_frame.setObjectName("inspectorActionsFrame")
        self.insp_actions_frame.setVisible(False)
        self.insp_actions_layout = QGridLayout(self.insp_actions_frame)
        self.insp_actions_layout.setContentsMargins(0, 4, 0, 0)
        self.insp_actions_layout.setHorizontalSpacing(6)
        self.insp_actions_layout.setVerticalSpacing(6)
        
        is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark'
        
        self.insp_btn_info = QPushButton(" Details")
        self.insp_btn_info.setObjectName("inspectorActionButton")
        self.insp_btn_info.setCursor(Qt.CursorShape.PointingHandCursor)
        self.insp_btn_info.setIcon(get_vector_icon('info', is_dark))
        self.insp_btn_info.setIconSize(QSize(14, 14))
        self.insp_btn_info.setToolTip("View detailed file metadata and stream info")
        self.insp_btn_info.clicked.connect(self._insp_on_info)
        
        self.insp_btn_folder = QPushButton(" Folder")
        self.insp_btn_folder.setObjectName("inspectorActionButton")
        self.insp_btn_folder.setCursor(Qt.CursorShape.PointingHandCursor)
        self.insp_btn_folder.setIcon(get_vector_icon('folder', is_dark))
        self.insp_btn_folder.setIconSize(QSize(14, 14))
        self.insp_btn_folder.setToolTip("Open containing folder in file explorer")
        self.insp_btn_folder.clicked.connect(self._insp_on_folder)
        
        self.insp_btn_trim = QPushButton(" Trim")
        self.insp_btn_trim.setObjectName("inspectorActionButton")
        self.insp_btn_trim.setCursor(Qt.CursorShape.PointingHandCursor)
        self.insp_btn_trim.setIcon(get_vector_icon('scissors', is_dark))
        self.insp_btn_trim.setIconSize(QSize(14, 14))
        self.insp_btn_trim.setToolTip("Quick trim video clip")
        self.insp_btn_trim.clicked.connect(self._insp_on_trim)
        
        self.insp_btn_play = QPushButton(" Open")
        self.insp_btn_play.setObjectName("inspectorActionButton")
        self.insp_btn_play.setCursor(Qt.CursorShape.PointingHandCursor)
        self.insp_btn_play.setIcon(get_vector_icon('play', is_dark))
        self.insp_btn_play.setIconSize(QSize(14, 14))
        self.insp_btn_play.setToolTip("Open file in external/default application")
        self.insp_btn_play.clicked.connect(self._insp_on_open)
        
        self._setup_inspector_actions(is_video=True)
        content_layout.addWidget(self.insp_actions_frame)
        content_layout.addStretch()

        self.preview_scroll.setWidget(self.preview_content)
        preview_layout.addWidget(self.preview_scroll)

    def _setup_inspector_actions(self, is_video: bool = True):
        while self.insp_actions_layout.count() > 0:
            self.insp_actions_layout.takeAt(0)
        self.insp_actions_layout.addWidget(self.insp_btn_info, 0, 0)
        self.insp_actions_layout.addWidget(self.insp_btn_folder, 0, 1)
        if is_video:
            self.insp_btn_trim.setVisible(True)
            self.insp_actions_layout.addWidget(self.insp_btn_trim, 1, 0)
            self.insp_actions_layout.addWidget(self.insp_btn_play, 1, 1)
        else:
            self.insp_btn_trim.setVisible(False)
            self.insp_actions_layout.addWidget(self.insp_btn_play, 1, 0, 1, 2)

    def _insp_on_info(self):
        row = getattr(self, '_current_inspector_row', -1)
        if row >= 0:
            self._show_detailed_info(row)

    def _insp_on_folder(self):
        row = getattr(self, '_current_inspector_row', -1)
        if row >= 0:
            self._open_folder_for_row(row)

    def _insp_on_trim(self):
        row = getattr(self, '_current_inspector_row', -1)
        if row >= 0:
            self._on_quick_trim(row)

    def _insp_on_open(self):
        row = getattr(self, '_current_inspector_row', -1)
        if row >= 0:
            self._play_video(row)

    def _stop_and_clear_media_player(self):
        if hasattr(self, 'player') and self.player:
            if self.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState:
                self.player.stop()
            self.player.setSource(QUrl())
        if hasattr(self, 'preview_image') and self.preview_image:
            self.preview_image.clear()

    def _release_file_locks(self, target_filepaths: list[str] = None):
        target_set = {os.path.normcase(os.path.abspath(p)) for p in target_filepaths} if target_filepaths else None
        if target_set and hasattr(self, 'player') and self.player.source().toLocalFile():
            current_preview = os.path.normcase(os.path.abspath(self.player.source().toLocalFile()))
            if current_preview in target_set:
                self._stop_and_clear_media_player()
        elif not target_set:
            self._stop_and_clear_media_player()
        main_win = self.window()
        if main_win:
            if hasattr(main_win, 'hover_overlay') and main_win.hover_overlay:
                overlay_info = getattr(main_win.hover_overlay, 'info', None)
                if not target_set or overlay_info is None or os.path.normcase(os.path.abspath(overlay_info.filepath)) in target_set:
                    main_win.hover_overlay.hide_preview()
            if hasattr(main_win, '_native_players') and main_win._native_players:
                for player_win in list(main_win._native_players):
                    try:
                        if player_win.isVisible():
                            p_path = getattr(player_win, 'filepath', None)
                            cur_path = getattr(player_win, '_current_filepath', None)
                            mult_paths = getattr(player_win, 'filepaths', None)
                            info_l = getattr(player_win, 'info_left', None)
                            info_r = getattr(player_win, 'info_right', None)
                            paths = set()
                            if p_path: paths.add(os.path.normcase(os.path.abspath(p_path)))
                            if cur_path: paths.add(os.path.normcase(os.path.abspath(cur_path)))
                            if mult_paths and isinstance(mult_paths, (list, tuple)):
                                for mp in mult_paths:
                                    if mp: paths.add(os.path.normcase(os.path.abspath(mp)))
                            if info_l: paths.add(os.path.normcase(os.path.abspath(info_l.filepath)))
                            if info_r: paths.add(os.path.normcase(os.path.abspath(info_r.filepath)))
                            if target_set is None or (paths & target_set):
                                player_win.close()
                    except RuntimeError:
                        pass

    def _update_preview_pane(self):
        if not self.btn_toggle_preview.isChecked():
            self._stop_and_clear_media_player()
            return
        selected_rows = []
        for rng in self.table.selectedRanges():
            for row in range(rng.topRow(), rng.bottomRow() + 1): selected_rows.append(row)
        selected_rows = list(set(selected_rows))

        # If in Grid View and table selection is empty, check grid selection
        if len(selected_rows) == 0 and hasattr(self, 'view_stack') and self.view_stack.currentIndex() == 1:
            grid_sel = self.grid_view.selectedItems()
            if len(grid_sel) == 1:
                g_info = grid_sel[0].data(Qt.ItemDataRole.UserRole)
                for r in range(self.table.rowCount()):
                    if self._get_row_info(r) is g_info:
                        selected_rows = [r]
                        break

        # Fallback: if no selection but files exist in table, inspect currentRow or row 0
        if len(selected_rows) == 0 and self.table.rowCount() > 0:
            cur = self.table.currentRow()
            fallback_row = cur if (cur >= 0 and cur < self.table.rowCount()) else 0
            if not self.table.isRowHidden(fallback_row):
                selected_rows = [fallback_row]

        if len(selected_rows) != 1:
            self._current_inspector_row = -1
            self._stop_and_clear_media_player()
            self.preview_stack.setCurrentIndex(2)
            self.preview_controls.setVisible(False)
            if hasattr(self, 'insp_meta_frame'): self.insp_meta_frame.setVisible(False)
            if hasattr(self, 'insp_rename_frame'): self.insp_rename_frame.setVisible(False)
            if hasattr(self, 'insp_actions_frame'): self.insp_actions_frame.setVisible(False)
            if len(selected_rows) > 1: self.no_preview_label.setText("Multiple files selected\nSelect a single file to inspect")
            elif self.table.rowCount() == 0: self.no_preview_label.setText("No media files loaded")
            else: self.no_preview_label.setText("Select a file to inspect")
            self.preview_title.setText("Inspector")
            return
        row = selected_rows[0]
        self._current_inspector_row = row
        info = self._get_row_info(row)
        if not info or not info.is_valid:
            self._stop_and_clear_media_player()
            self.preview_stack.setCurrentIndex(2)
            self.preview_controls.setVisible(False)
            if hasattr(self, 'insp_meta_frame'): self.insp_meta_frame.setVisible(False)
            if hasattr(self, 'insp_rename_frame'): self.insp_rename_frame.setVisible(False)
            if hasattr(self, 'insp_actions_frame'): self.insp_actions_frame.setVisible(False)
            self.no_preview_label.setText("No preview available\nfor invalid files")
            self.preview_title.setText(info.filename if info else "Inspector")
            return
        self.preview_title.setText(info.filename)
        # Populate inspector metadata grid
        if hasattr(self, 'insp_meta_frame'):
            self.insp_format.setText(info.extension.upper().lstrip('.') or "—")
            res_txt = f"{info.width}×{info.height}" if (info.width and info.height) else "—"
            if getattr(info, 'resolution_tag', ''):
                res_txt += f" ({info.resolution_tag})"
            self.insp_res.setText(res_txt)
            self.insp_dur.setText(getattr(info, 'duration_formatted', '') or "—")
            self.insp_size.setText(getattr(info, 'size_formatted', '') or "—")
            m_ts = getattr(info, 'mtime', 0)
            if m_ts:
                try:
                    from datetime import datetime
                    m_str = datetime.fromtimestamp(m_ts).strftime("%Y-%m-%d %H:%M")
                except Exception:
                    m_str = "—"
            else:
                m_str = "—"
            self.insp_mtime.setText(m_str)
            self.insp_meta_frame.setVisible(True)

        # Populate rename preview box
        if hasattr(self, 'insp_rename_frame'):
            preview_item = self.table.item(row, self.COL_PREVIEW)
            p_text = preview_item.text().strip() if preview_item else ""
            if p_text.startswith("➜  "):
                self.insp_target_name.setText(p_text[3:])
                self.insp_target_name.setStyleSheet("color: #34d399; font-weight: bold; font-size: 11px;")
            elif p_text and p_text != "—":
                self.insp_target_name.setText(p_text)
                self.insp_target_name.setStyleSheet("color: #34d399; font-weight: bold; font-size: 11px;")
            else:
                self.insp_target_name.setText("No changes pending")
                self.insp_target_name.setStyleSheet("color: #7c7c9a; font-style: italic; font-size: 11px;")
            self.insp_rename_frame.setVisible(True)

        # Show quick actions
        if hasattr(self, 'insp_actions_frame'):
            self.insp_actions_frame.setVisible(True)
            if hasattr(self, '_setup_inspector_actions'):
                self._setup_inspector_actions(is_video=(info.media_type == 'video'))
            elif hasattr(self, 'insp_btn_trim'):
                self.insp_btn_trim.setVisible(info.media_type == 'video')

        filepath = info.filepath
        if info.media_type == 'image':
            self._stop_and_clear_media_player()
            self.preview_controls.setVisible(False)
            self.preview_stack.setCurrentIndex(0)
            # Decode at the preview's display size: a full-resolution QPixmap
            # load of a 50MP photo on the GUI thread hitched the UI on every
            # selection change.
            from PyQt6.QtGui import QImageReader
            reader = QImageReader(filepath)
            reader.setAutoTransform(True)
            _isz = reader.size()
            if _isz.isValid() and _isz.width() > 580:
                reader.setScaledSize(QSize(580, max(1, int(_isz.height() * 580 / _isz.width()))))
            _pimg = reader.read()
            pixmap = QPixmap.fromImage(_pimg) if not _pimg.isNull() else QPixmap()
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
            main_win = self.window()
            is_dark = getattr(main_win, 'current_theme', 'dark') == 'dark'
            placeholder_pix.fill(QColor("#1e1b4b" if is_dark else "#f1f5f9"))
            audio_icon = get_vector_icon('audio', is_dark)
            icon_px = audio_icon.pixmap(64, 64)
            with QPainter(placeholder_pix) as painter:
                painter.setRenderHint(QPainter.RenderHint.Antialiasing)
                painter.drawPixmap((290 - 64) // 2, (220 - 64) // 2, icon_px)
            self.preview_image.setPixmap(placeholder_pix)
            self.player.setSource(QUrl.fromLocalFile(filepath))
            is_globally_muted = getattr(main_win, 'global_mute', False)
            self.audio_output.setMuted(is_globally_muted)
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
                if info is not None:
                    _gi = self._grid_item(info)
                    if _gi and _gi in selected_items:
                        for col in range(self.table.columnCount()):
                            item = self.table.item(row, col)
                            if item: item.setSelected(True)
        finally:
            # An exception with signals still blocked left the table permanently
            # unresponsive to selection changes.
            self.table.blockSignals(False)
            self._syncing_selection = False
        n_sel, total = 0, 0
        for item in self.grid_view.selectedItems():
            inf = item.data(Qt.ItemDataRole.UserRole)
            if inf is not None:
                n_sel += 1
                total += int(getattr(inf, 'size_bytes', 0) or 0)
        self.sel_stats_label.setText(f"{n_sel} selected \u00b7 {format_size(total)}" if n_sel > 1 else "")
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
        visible_rows = [r for r in range(self.table.rowCount()) if not self.table.isRowHidden(r)]
        visible_count = len(visible_rows)
        visible_infos = [self._get_row_info(r) for r in visible_rows]
        valid = sum(1 for v in visible_infos if v and v.is_valid)
        unsupported = visible_count - valid
        total_bytes = sum(getattr(v, 'size_bytes', 0) or 0 for v in visible_infos if v and v.is_valid)
        size_str = format_size(total_bytes)
        if hasattr(self, 'stat_total') and hasattr(self.stat_total, '_value_label'):
            self.stat_total._value_label.setText(str(visible_count))
        if hasattr(self, 'stat_valid') and hasattr(self.stat_valid, '_value_label'):
            self.stat_valid._value_label.setText(str(valid))
        if hasattr(self, 'stat_unsupported') and hasattr(self.stat_unsupported, '_value_label'):
            self.stat_unsupported._value_label.setText(str(unsupported))
        if hasattr(self, 'stat_size') and hasattr(self.stat_size, '_value_label'):
            self.stat_size._value_label.setText(size_str)
        if hasattr(self, '_update_stats_dashboard'):
            self._update_stats_dashboard()

        if hasattr(self, 'btn_process') and self.btn_process:
            ready_count = 0
            main_win = self.window()
            keep_ext = getattr(main_win, 'naming_keep_extension', True) if main_win else True
            for row in range(self.table.rowCount()):
                if self.table.isRowHidden(row): continue
                info = self._get_row_info(row)
                if not info or not info.is_valid: continue
                artist_widget = self.table.cellWidget(row, self.COL_ARTIST)
                rating_widget = self.table.cellWidget(row, self.COL_RATING)
                artist = artist_widget.text().strip() if artist_widget else (self.table.item(row, self.COL_ARTIST).text().strip() if self.table.item(row, self.COL_ARTIST) else getattr(info, 'parsed_artist', ''))
                rating = rating_widget.currentText() if rating_widget else (self.table.item(row, self.COL_RATING).text().strip() if self.table.item(row, self.COL_RATING) else (getattr(info, 'parsed_rating', '—') or "—"))
                if self._is_naming_data_complete(artist, rating, info):
                    new_name = self._get_templated_name(artist, rating, info)
                    current_display_name = self.table.item(row, self.COL_FILENAME).text().strip() if self.table.item(row, self.COL_FILENAME) else ""
                    target_display = new_name + (info.extension if keep_ext else "") if new_name else ""
                    if target_display and target_display != current_display_name:
                        ready_count += 1
            is_ready = ready_count > 0
            self.btn_process.setEnabled(is_ready)
            if is_ready:
                apply_glow(self.btn_process, getattr(self.window(), 'theme_accent', None) or Nebula.ACCENT, 20, 100)
            else:
                apply_glow(self.btn_process, None)
            self._stats_dirty = False

    def _update_row_colors(self):
        main_win = self.window()
        is_dark = getattr(main_win, 'current_theme', 'dark') == 'dark'
        ui_scale = getattr(main_win, 'ui_scale', 1.0) or 1.0
        bold_meta_font = _mono_font(max(7, int(round(9 * ui_scale))), True)
        fname_font = QFont(BASE_FONT_FAMILY, max(8, int(round(10 * ui_scale))), QFont.Weight.Bold)
        preview_bold_font = QFont(BASE_FONT_FAMILY, max(8, int(round(10 * ui_scale))), QFont.Weight.Bold)
        preview_norm_font = QFont(BASE_FONT_FAMILY, max(8, int(round(10 * ui_scale))), QFont.Weight.Normal)
        dim_color = QColor("#9ca3af") if is_dark else QColor("#64748b")
        for row in range(self.table.rowCount()):
            fname_item = self.table.item(row, self.COL_FILENAME)
            if fname_item:
                fname_item.setFont(fname_font)
                fname_item.setForeground(QColor("#c4b5fd") if is_dark else QColor("#1e3a8a"))
            for col in (self.COL_SIZE, self.COL_DURATION, self.COL_DATE_MOD, self.COL_DATE_CREATED):
                item = self.table.item(row, col)
                if item:
                    item.setFont(bold_meta_font)
                    item.setForeground(dim_color)
                    item.setTextAlignment(Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter)
            res_item = self.table.item(row, self.COL_RESOLUTION)
            if res_item:
                res_item.setFont(bold_meta_font)
                res_item.setForeground(dim_color)
                res_item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
            for col in (self.COL_ARTIST, self.COL_TAGS):
                item = self.table.item(row, col)
                if item:
                    item.setForeground(QColor("#f3f4f6") if is_dark else QColor("#0f172a"))
                    item.setTextAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
            rating_item = self.table.item(row, self.COL_RATING)
            if rating_item:
                rating_item.setForeground(QColor("#f3f4f6") if is_dark else QColor("#0f172a"))
                rating_item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
            preview_item = self.table.item(row, self.COL_PREVIEW)
            if preview_item:
                if preview_item.text() != "—":
                    preview_item.setFont(preview_bold_font)
                    preview_item.setForeground(QColor("#34d399") if is_dark else QColor("#059669"))
                else:
                    preview_item.setFont(preview_norm_font)
                    preview_item.setForeground(QColor("#7c7c9a") if is_dark else QColor("#64748b"))

    def keyPressEvent(self, event):
        if self.view_stack.currentIndex() == 0:  # table view
            if event.key() == Qt.Key.Key_Up:
                row = self.table.currentRow()
                prev_row = row - 1
                while prev_row >= 0 and self.table.isRowHidden(prev_row):
                    prev_row -= 1
                if prev_row >= 0:
                    self.table.setCurrentCell(prev_row, 0)
                elif row == -1 and self.table.rowCount() > 0:
                    first = 0
                    while first < self.table.rowCount() and self.table.isRowHidden(first):
                        first += 1
                    if first < self.table.rowCount():
                        self.table.setCurrentCell(first, 0)
                return
            elif event.key() == Qt.Key.Key_Down:
                row = self.table.currentRow()
                next_row = row + 1 if row != -1 else 0
                while next_row < self.table.rowCount() and self.table.isRowHidden(next_row):
                    next_row += 1
                if next_row < self.table.rowCount():
                    self.table.setCurrentCell(next_row, 0)
                return
            elif event.key() in (Qt.Key.Key_Enter, Qt.Key.Key_Return):
                row = self.table.currentRow()
                if row >= 0:
                    self._play_video(row)
                return
            elif event.key() == Qt.Key.Key_A and (event.modifiers() & Qt.KeyboardModifier.ControlModifier):
                self.table.blockSignals(True)
                try:
                    for i in range(self.table.rowCount()):
                        if not self.table.isRowHidden(i):
                            self.table.setRangeSelected(
                                QTableWidgetSelectionRange(i, 0, i, self.table.columnCount() - 1), True)
                finally:
                    self.table.blockSignals(False)
                self._on_selection_changed()
                return
        elif self.view_stack.currentIndex() == 1:  # grid view
            if event.key() in (Qt.Key.Key_Enter, Qt.Key.Key_Return):
                item = self.grid_view.currentItem()
                if item:
                    info = item.data(Qt.ItemDataRole.UserRole)
                    if info:
                        for r in range(self.table.rowCount()):
                            if self._get_row_info(r) is info:
                                self._play_video(r)
                                break
                return
            elif event.key() == Qt.Key.Key_A and (event.modifiers() & Qt.KeyboardModifier.ControlModifier):
                self.grid_view.selectAll()
                return
        super().keyPressEvent(event)

# ─── Main App Window ─────────────────────────────────────────────────────────

class NebulaProgressBar(QProgressBar):
    """Gradient progress bar with an animated shimmer sweep (cyan → violet).

    Animations stop while hidden and are disabled under reduced-motion.
    """

    def __init__(self, parent=None):
        super().__init__(parent)
        self._shimmer_pos = 0.0
        self._anim = QTimer(self)
        self._anim.setInterval(40)
        self._anim.timeout.connect(self._tick)

    def showEvent(self, event):
        super().showEvent(event)
        w = self.window()
        reduced = bool(getattr(w, 'reduced_motion', False)) if w is not None else False
        if not reduced:
            self._anim.start()

    def hideEvent(self, event):
        super().hideEvent(event)
        self._anim.stop()

    def _tick(self):
        # Reduced-motion may be toggled while the bar is visible — honor it
        # immediately instead of waiting for the next showEvent.
        w = self.window()
        if w is not None and bool(getattr(w, 'reduced_motion', False)):
            self._anim.stop()
            return
        self._shimmer_pos = (self._shimmer_pos + 0.03) % 1.2
        self.update()

    def paintEvent(self, event):
        w = self.window()
        is_dark = True
        if w is not None and hasattr(w, 'current_theme'):
            is_dark = (w.current_theme == 'dark')
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        rect = QRectF(self.rect().adjusted(2, 2, -2, -2))
        h = rect.height()
        painter.setPen(Qt.PenStyle.NoPen)
        track = QColor("#16132E") if is_dark else QColor("#E2E8F0")
        painter.setBrush(track)
        painter.drawRoundedRect(rect, h / 2, h / 2)
        lo, hi = self.minimum(), self.maximum()
        if hi > lo:
            frac = max(0.0, min(1.0, (self.value() - lo) / (hi - lo)))
            if frac > 0.0:
                fill_w = rect.width() * frac
                # Theme accents (cyan→violet on Dark; per-theme on new skins)
                _acc = getattr(w, 'theme_accent', None)
                _acc2 = getattr(w, 'theme_accent2', None)
                fill = QLinearGradient(rect.left(), 0.0, rect.left() + max(fill_w, h), 0.0)
                fill.setColorAt(0.0, QColor(_acc2 or "#22D3EE"))
                fill.setColorAt(1.0, QColor(_acc or "#8B5CF6"))
                painter.setBrush(QBrush(fill))
                painter.drawRoundedRect(QRectF(rect.left(), rect.top(), max(fill_w, h), h), h / 2, h / 2)
                if self._anim.isActive():
                    sweep = rect.width() * 0.15
                    x = rect.left() - sweep + self._shimmer_pos * (rect.width() + sweep)
                    painter.setClipRect(QRectF(rect.left(), rect.top(), fill_w, h))
                    shine = QLinearGradient(x, 0.0, x + sweep, 0.0)
                    shine.setColorAt(0.0, QColor(255, 255, 255, 0))
                    shine.setColorAt(0.5, QColor(255, 255, 255, 70))
                    shine.setColorAt(1.0, QColor(255, 255, 255, 0))
                    painter.setBrush(QBrush(shine))
                    painter.drawRoundedRect(QRectF(rect.left(), rect.top(), max(fill_w, h), h), h / 2, h / 2)
                    painter.setClipping(False)
        if self.isTextVisible():
            painter.setPen(QColor("#ECECF4") if is_dark else QColor("#0F172A"))
            painter.setFont(self.font())
            painter.drawText(self.rect(), Qt.AlignmentFlag.AlignCenter, self.text())
        painter.end()


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
class SettingsOverlayContainer(QWidget):
    """Hosts main content_layout at 100% width/height and coordinates settings overlay panel."""
    def __init__(self, main_win, parent=None):
        super().__init__(parent)
        self.main_win = main_win
        self.container_layout = QVBoxLayout(self)
        self.container_layout.setContentsMargins(0, 0, 0, 0)
        self.container_layout.setSpacing(0)

    def resizeEvent(self, event):
        super().resizeEvent(event)
        if hasattr(self.main_win, '_reposition_settings_panel'):
            self.main_win._reposition_settings_panel(animate=False)


class SettingsResizeHandle(QWidget):
    """A narrow grip along the left edge of the settings panel to drag and resize."""
    def __init__(self, main_win, parent=None):
        super().__init__(parent)
        self.main_win = main_win
        self.setCursor(Qt.CursorShape.SizeHorCursor)
        self.setFixedWidth(12)
        self._dragging = False
        self._hovering = False
        self._start_global_x = 0
        self._start_width = 420
        self.setAttribute(Qt.WidgetAttribute.WA_Hover, True)

    def enterEvent(self, event):
        self._hovering = True
        self.update()
        super().enterEvent(event)

    def leaveEvent(self, event):
        self._hovering = False
        self.update()
        super().leaveEvent(event)

    def paintEvent(self, event):
        if self._hovering or self._dragging:
            from PyQt6.QtGui import QPainter, QColor
            painter = QPainter(self)
            painter.setRenderHint(QPainter.RenderHint.Antialiasing)
            is_dark = getattr(self.main_win, 'current_theme', 'dark') == 'dark'
            color = QColor(167, 139, 250, 160) if is_dark else QColor(99, 102, 241, 140)
            painter.setPen(Qt.PenStyle.NoPen)
            painter.setBrush(color)
            h = min(48, max(24, int(self.height() * 0.15)))
            y = (self.height() - h) // 2
            painter.drawRoundedRect(4, y, 4, h, 2, 2)
            painter.end()

    def mousePressEvent(self, event):
        if event.button() == Qt.MouseButton.LeftButton:
            self._dragging = True
            self._start_global_x = int(event.globalPosition().x())
            self._start_width = getattr(self.main_win, '_settings_width', 420)
            self.update()
            event.accept()
        else:
            super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if self._dragging:
            delta = self._start_global_x - int(event.globalPosition().x())
            c_w = self.main_win.content_wrapper.width()
            base_min_w = self.main_win._get_settings_default_width() if hasattr(self.main_win, '_get_settings_default_width') else 460
            max_w = max(base_min_w, int(c_w * 0.75))
            new_w = max(base_min_w, min(max_w, self._start_width + delta))
            self.main_win._settings_width = new_w
            self.main_win._reposition_settings_panel(animate=False)
            event.accept()
        else:
            super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        if self._dragging and event.button() == Qt.MouseButton.LeftButton:
            self._dragging = False
            self.update()
            if hasattr(self.main_win, '_debounced_save_state'):
                self.main_win._debounced_save_state()
            event.accept()
        else:
            super().mouseReleaseEvent(event)


class MediaFlowWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("MediaFlow — Multimedia Manager & Renamer")
        self.setMinimumSize(1200, 700)
        self.resize(1380, 860)
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
        # FEATURE (v2.5): rename presets + folder profiles
        self.rename_presets = {}
        self.folder_profiles = {}
        self._build_ui()
        self._build_tools_bar()

        self.hover_overlay = HoverPreviewOverlay(self)
        self._setup_shortcuts()
        self._active_toasts = []
        self._load_state()
        # Seed the "Default" preset from naming config on first run
        self._seed_default_preset()
        # Center on first launch OR whenever geometry was not restored (missing
        # or corrupt config) — previously the corrupt-config path fell through
        # to an OS-default position instead of the centered default.
        if not getattr(self, '_geometry_restored', False):
            self._center_on_screen()

    def show_toast(self, message, toast_type='info'):
        toast = ToastNotification(message, toast_type, parent=self)
        self._active_toasts.append(toast)

        start_y = self.height() - 20 - toast.sizeHint().height()
        
        for t in reversed(self._active_toasts[:-1]):
            if t.isVisible():
                start_y -= t.height() + 10
                
        # FIX: sizeHint() — toast.width() is unreliable before show() (stacked
        # toasts could overlap horizontally)
        target_pos = QPoint(self.width() - toast.sizeHint().width() - 20, start_y)
        
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
        sidebar_layout.setContentsMargins(0, 20, 0, 16)
        sidebar_layout.setSpacing(6)
        logo_label = QLabel()
        logo_pix = QPixmap(get_resource_path("logo.png"))
        if not logo_pix.isNull(): logo_label.setPixmap(logo_pix.scaled(72, 72, Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation))
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
        sidebar_layout.addSpacing(16)
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
        self.smart_scroll.setMinimumHeight(40)
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

        # Bottom-left: Tools Section
        tools_section = QWidget()
        tools_section_layout = QVBoxLayout(tools_section)
        tools_section_layout.setContentsMargins(12, 4, 12, 6)
        tools_section_layout.setSpacing(2)

        sidebar_divider = QFrame()
        sidebar_divider.setObjectName("sidebarDivider")
        sidebar_divider.setFrameShape(QFrame.Shape.HLine)
        sidebar_divider.setFrameShadow(QFrame.Shadow.Sunken)
        tools_section_layout.addWidget(sidebar_divider)

        tools_header = QLabel("TOOLS")
        tools_header.setObjectName("sidebarToolHeader")
        tools_section_layout.addWidget(tools_header)

        self._sidebar_tool_buttons = []
        is_dark = getattr(self, 'current_theme', 'dark') == 'dark'

        tool_actions_def = [
            ("Rename Presets", "presets", self._open_preset_manager, "Rename Presets (Ctrl+Shift+P)"),
            ("Preview Changes", "preview", self._open_preview_changes, "Preview Changes (Ctrl+Shift+V)"),
            ("Dashboard", "stats", self._open_library_dashboard, "Library Dashboard (Ctrl+Shift+B)"),
            ("Dedupe Resolver", "duplicate", self._open_duplicate_resolver, "Find & Resolve Duplicates (Ctrl+Alt+D)"),
            ("Tag Editor", "tag", self._open_tag_editor, "Media Tag Editor (Ctrl+Shift+T)"),
            ("Folder Profiles", "folder", self._open_folder_profiles, "Folder Profiles & Auto-Watch (Ctrl+Alt+P)"),
        ]

        for text, icon_name, slot, tooltip in tool_actions_def:
            btn = QPushButton(f" {text}")
            btn.setObjectName("sidebarToolButton")
            btn.setCursor(Qt.CursorShape.PointingHandCursor)
            btn.setIcon(get_vector_icon(icon_name, is_dark))
            btn.setIconSize(QSize(15, 15))
            btn.setMinimumHeight(28)
            btn.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
            btn.setToolTip(tooltip)
            btn.clicked.connect(slot)
            tools_section_layout.addWidget(btn)
            self._sidebar_tool_buttons.append((btn, icon_name))

        sidebar_layout.addWidget(tools_section)
        main_layout.addWidget(sidebar)
        self.content_wrapper = SettingsOverlayContainer(self)
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
        self.progress_bar = NebulaProgressBar()
        self.progress_bar.setFixedHeight(18)
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
        self.content_wrapper.container_layout.addWidget(header_bar)
        self.stacked_widget = QStackedWidget()
        self.content_wrapper.container_layout.addWidget(self.stacked_widget, 1)
        self.video_tab = MediaTab('video')
        self.image_tab = MediaTab('image')
        self.audio_tab = MediaTab('audio')
        self.pdf_tab = MediaTab('pdf')
        self.stacked_widget.addWidget(self.video_tab)
        self.stacked_widget.addWidget(self.image_tab)
        self.stacked_widget.addWidget(self.audio_tab)
        self.stacked_widget.addWidget(self.pdf_tab)
        main_layout.addWidget(self.content_wrapper, 1)

        self.settings_panel = QFrame(self.content_wrapper)
        self.settings_panel.setObjectName("settingsPanel")
        self.settings_panel.setMinimumWidth(320)
        self._settings_width = 460
        self._settings_visible = False
        self._settings_anim = None
        self.settings_panel.setVisible(False)

        # Drop shadow for elevated floating settings card
        self._settings_shadow = QGraphicsDropShadowEffect(self.settings_panel)
        self._settings_shadow.setBlurRadius(28)
        self._settings_shadow.setOffset(-4, 2)
        self._update_settings_shadow_color()
        self.settings_panel.setGraphicsEffect(self._settings_shadow)

        # Drag handle on the left edge of settings overlay
        self._settings_resize_handle = SettingsResizeHandle(self, self.content_wrapper)
        self._settings_resize_handle.setVisible(False)

        outer_layout = QVBoxLayout(self.settings_panel)
        outer_layout.setContentsMargins(16, 24, 16, 24)
        outer_layout.setSpacing(16)
        settings_header = QHBoxLayout()
        settings_title = QLabel("Settings & Folders")
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
        scroll_area.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.settings_scroll_area = scroll_area
        scroll_widget = QWidget()
        settings_layout = QVBoxLayout(scroll_widget)
        settings_layout.setContentsMargins(0, 0, 0, 0)
        settings_layout.setSpacing(16)
        
        # Appearance
        appearance_sec = QGroupBox("Appearance")
        appearance_sec_layout = QVBoxLayout(appearance_sec)
        theme_row = QHBoxLayout()
        theme_lbl = QLabel("Theme Mode:")
        self.theme_combo = QComboBox()
        self.theme_combo.addItems(["System (Auto)", "Light", "Dark"])
        self.theme_combo.setToolTip("System (Auto): matches OS preference · Light: clean light theme · Dark: futuristic dark theme")
        self.theme_combo.currentTextChanged.connect(self._on_theme_changed)
        theme_row.addWidget(theme_lbl)
        theme_row.addWidget(self.theme_combo, 1)
        appearance_sec_layout.addLayout(theme_row)

        accent_row = QHBoxLayout()
        accent_lbl = QLabel("Color Accent:")
        self.accent_combo = QComboBox()
        self.accent_combo.addItems(["Deep Space", "Orange", "Red", "Blue", "Violet", "Emerald"])
        self.accent_combo.setToolTip("Customizes primary neon accent and highlight glows across all tabs and controls")
        self.accent_combo.currentTextChanged.connect(self._on_theme_changed)
        accent_row.addWidget(accent_lbl)
        accent_row.addWidget(self.accent_combo, 1)
        appearance_sec_layout.addLayout(accent_row)

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
        naming_sec = QGroupBox("Custom Naming Template")
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


        apps_sec = QGroupBox("Default Applications")
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
        ff_sec = QGroupBox("Deep Metadata (FFprobe)")
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
        videos_sec = QGroupBox("Videos Directories")
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
        images_sec = QGroupBox("Images Directories")
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
        audio_sec = QGroupBox("Audio Directories")
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

        pdf_sec = QGroupBox("PDFs Directories")
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
        open_with_sec = QGroupBox("'Open With' Applications")
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
        self._update_template_preview()

    def _manage_open_with_apps(self):
        dialog = ConfigureOpenWithDialog(self.open_with_apps, self)
        if dialog.exec() == QDialog.DialogCode.Accepted:
            self.open_with_apps = dialog.get_apps()
            self._save_state()

    def _show_help_dialog(self):
        dialog = AboutDialog(self)
        dialog.exec()

    def _on_theme_changed(self, _text=None):
        mode = self.theme_combo.currentText()
        accent = self.accent_combo.currentText()
        ThemeManager.apply_theme(self, mode, accent)
        # Debounced: _save_state serializes every row of every tab + fsyncs —
        # a synchronous call per toggle froze the GUI on large libraries.
        self._debounced_save_state()

    UI_SCALES = {"Compact": 0.85, "Normal": 1.0, "Large": 1.2}

    def _on_ui_size_changed(self, text):
        if getattr(self, '_ui_size_syncing', False): return
        self.ui_scale = self.UI_SCALES.get(text, 1.0)
        ThemeManager.apply_theme(self, self.theme_combo.currentText(), self.accent_combo.currentText())
        if getattr(self, '_settings_visible', False):
            self._reposition_settings_panel(animate=False)
        self._debounced_save_state()

    def _on_reduced_motion_changed(self, checked: bool):
        self.reduced_motion = bool(checked)
        self._debounced_save_state()

    # Thumbnail size — live label updates while dragging; layout reflow on release
    def _on_thumb_size_live(self, value: int):
        self.thumb_size = int(value)

    def _on_thumb_size_changed(self):
        size = int(getattr(self, 'thumb_size', 130))
        for tab in [self.video_tab, self.image_tab, self.audio_tab, self.pdf_tab] + list(getattr(self, 'smart_folder_tabs', {}).values()):
            tab.apply_thumbnail_size(size)
        self._debounced_save_state()

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
            # Persist the CLI-provided folders — previously they vanished on
            # restart unless the user later changed something else.
            self._debounced_save_state()

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
        ("Ctrl+Shift+P", "Rename Presets manager"),
        ("Ctrl+Shift+V", "Preview Changes (rename diff)"),
        ("Ctrl+Shift+B", "Library Dashboard"),
        ("Ctrl+Shift+T", "Tag Editor (audio & JPEG)"),
        ("Ctrl+Alt+D", "Duplicate Resolver (batch recycle)"),
        ("Ctrl+Alt+P", "Folder Profiles & Auto-watch"),
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
        curr_tab = self.stacked_widget.currentWidget()
        if curr_tab and hasattr(curr_tab, 'player') and curr_tab.player is not None:
            try:
                if curr_tab.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState:
                    curr_tab.player.pause()
            except (RuntimeError, AttributeError):
                pass

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
        if any(isinstance(f, dict) and f.get('name', '').lower() == name.lower() for f in self.smart_folders_config):
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
        is_current = False
        if name in self.smart_folder_nav_items:
            nav_item = self.smart_folder_nav_items.pop(name)
            self.smart_container_layout.removeWidget(nav_item)
            nav_item.deleteLater()
        if name in self.smart_folder_tabs:
            smart_tab = self.smart_folder_tabs.pop(name)
            is_current = (self.stacked_widget.currentWidget() is smart_tab)
            if hasattr(smart_tab, '_on_clear'):
                try:
                    smart_tab._on_clear()
                except Exception:
                    pass
            self.stacked_widget.removeWidget(smart_tab)
            smart_tab.deleteLater()
        # Case-insensitive filter to match the case-insensitive dedupe used at
        # creation time (previously exact-case, so 'Videos' vs 'videos' drifted)
        self.smart_folders_config = [f for f in self.smart_folders_config if isinstance(f, dict) and f.get('name', '').lower() != name.lower()]
        self._save_state()
        if is_current:
            self._switch_page(0)

    def switch_to_smart_folder(self, name: str):
        if name not in self.smart_folder_tabs: return
        curr_tab = self.stacked_widget.currentWidget()
        if curr_tab and hasattr(curr_tab, 'player') and curr_tab.player is not None:
            try:
                if curr_tab.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState:
                    curr_tab.player.pause()
            except (RuntimeError, AttributeError):
                pass

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
        smart_tab._load_visible_widgets()

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
        def _delete_shortcut_gate():
            w = self.stacked_widget.currentWidget()
            # Only fire when the media list itself has focus: Delete pressed in
            # a settings QListWidget (to remove a folder entry) previously
            # recycled the selected media files in the active tab.
            if w is not None and hasattr(w, 'table'):
                if not (w.table.hasFocus() or w.grid_view.hasFocus()):
                    return
            _gated_call('_on_delete_selected', 'btn_delete')
        shortcut_delete.triggered.connect(_delete_shortcut_gate)
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

        # FEATURE (v2.5): feature-suite shortcuts
        for title, keys, slot in (
            ("Rename Presets", "Ctrl+Shift+P", self._open_preset_manager),
            ("Preview Changes", "Ctrl+Shift+V", self._open_preview_changes),
            ("Library Dashboard", "Ctrl+Shift+B", self._open_library_dashboard),
            ("Tag Editor", "Ctrl+Shift+T", self._open_tag_editor),
            ("Duplicate Resolver", "Ctrl+Alt+D", self._open_duplicate_resolver),
            ("Folder Profiles", "Ctrl+Alt+P", self._open_folder_profiles),
        ):
            act = QAction(title, self)
            act.setShortcut(QKeySequence(keys))
            act.triggered.connect(slot)
            self.addAction(act)

    # ─── FEATURE SUITE (v2.5): toolbar, Tools menu, dialog launchers, presets ───

    _TOOLS_BAR_ACTIONS = (
        ("Rename Presets", "presets", "_open_preset_manager"),
        ("Preview Changes", "preview", "_open_preview_changes"),
        ("Dashboard", "stats", "_open_library_dashboard"),
        ("Dedupe Resolver", "duplicate", "_open_duplicate_resolver"),
        ("Tag Editor", "tag", "_open_tag_editor"),
        ("Folder Profiles", "folder", "_open_folder_profiles"),
    )

    def _build_tools_bar(self):
        is_dark = getattr(self, 'current_theme', 'dark') == 'dark'
        tools_menu = self.menuBar().addMenu("Tools")
        self._tools_menu = tools_menu
        self._tools_menu_actions = []
        for text, icon_name, slot_name in self._TOOLS_BAR_ACTIONS:
            act = QAction(get_vector_icon(icon_name, is_dark), text, self)
            act.triggered.connect(getattr(self, slot_name))
            tools_menu.addAction(act)
            self._tools_menu_actions.append((act, icon_name))
        tools_menu.addSeparator()
        act_dupes = QAction(get_vector_icon('duplicate', is_dark), "Find Duplicates (active tab)", self)
        act_dupes.triggered.connect(self._menu_find_duplicates)
        tools_menu.addAction(act_dupes)
        self._tools_menu_actions.append((act_dupes, 'duplicate'))
        act_export = QAction(get_vector_icon('sync', is_dark), "Export CSV (active tab)", self)
        act_export.triggered.connect(self._menu_export_csv)
        tools_menu.addAction(act_export)
        self._tools_menu_actions.append((act_export, 'sync'))
        tools_menu.addSeparator()
        act_keys = QAction("Keyboard Shortcuts (F1)", self)
        act_keys.triggered.connect(self._show_shortcut_cheatsheet)
        tools_menu.addAction(act_keys)

    def _refresh_tools_bar_icons(self, is_dark: bool):
        for btn, icon_name in getattr(self, '_sidebar_tool_buttons', []):
            btn.setIcon(get_vector_icon(icon_name, is_dark))
        for act, icon_name in getattr(self, '_tools_menu_actions', []):
            act.setIcon(get_vector_icon(icon_name, is_dark))

    def _active_media_tab(self):
        w = self.stacked_widget.currentWidget()
        if w is not None and hasattr(w, 'table') and hasattr(w, 'media_infos'):
            return w
        return None

    def _menu_find_duplicates(self):
        tab = self._active_media_tab()
        if tab is not None and hasattr(tab, '_find_exact_duplicates'):
            tab._find_exact_duplicates()

    def _menu_export_csv(self):
        tab = self._active_media_tab()
        if tab is not None and hasattr(tab, '_export_list_csv'):
            tab._export_list_csv()

    # ── preset / profile helpers ──

    def _current_naming_as_preset(self):
        return {'fields': list(self.naming_fields),
                'all_ordered': list(self.naming_all_fields_ordered),
                'separator': self.naming_separator,
                'keep_extension': bool(self.naming_keep_extension)}

    def _seed_default_preset(self):
        if not getattr(self, 'rename_presets', None):
            self.rename_presets = {DEFAULT_PRESET_NAME: self._current_naming_as_preset()}

    def _apply_naming_config(self, fields, ordered, separator, keep_extension):
        separator = re.sub(r'[\\/:*?"<>|]', '', str(separator or ' '))[:8] or ' '
        fields = [f for f in (fields or []) if f in FIELD_MAP.values()]
        reconciled, seen = [], set()
        for f_name in list(ordered or []) + list(DEFAULT_NAMING_FIELDS_ORDERED):
            if isinstance(f_name, str) and f_name in FIELD_MAP and f_name not in seen:
                reconciled.append(f_name)
                seen.add(f_name)
        self.naming_fields = fields
        self.naming_all_fields_ordered = reconciled
        self.naming_separator = separator
        self.naming_keep_extension = bool(keep_extension)
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
            item.setCheckState(Qt.CheckState.Checked if FIELD_MAP[f_name] in self.naming_fields else Qt.CheckState.Unchecked)
            self.template_list.addItem(item)
        self.template_list.model().blockSignals(False)
        self.template_list.blockSignals(False)
        self._update_template_preview()
        self._on_naming_template_changed()

    def _maybe_apply_folder_profile(self, folders):
        for folder in folders or []:
            if not folder:
                continue
            prof = (getattr(self, 'folder_profiles', {}) or {}).get(_norm_key(folder))
            if not isinstance(prof, dict):
                continue
            preset_name = prof.get('preset')
            preset = (getattr(self, 'rename_presets', {}) or {}).get(preset_name or '')
            if not preset:
                continue
            label = os.path.basename(folder.rstrip('\\/')) or folder
            if prof.get('auto_rename'):
                self.show_toast(f"Profile: new files in '{label}' will be auto-renamed with '{preset_name}'.", 'info')
            else:
                current = self._current_naming_as_preset()
                if (current['fields'] == preset.get('fields') and
                        current['separator'] == preset.get('separator') and
                        current['keep_extension'] == preset.get('keep_extension', True)):
                    continue
                try:
                    self._apply_naming_config(preset.get('fields', []), preset.get('all_ordered', []),
                                              preset.get('separator', ' '), preset.get('keep_extension', True))
                    self.show_toast(f"Profile applied: '{preset_name}' (bound to '{label}').", 'info')
                except Exception:
                    logger.exception("folder profile apply failed")
                return

    # ── dialog launchers ──

    def _open_preset_manager(self):
        RenamePresetManagerDialog(self, self).exec()

    def _open_preview_changes(self):
        tab = self._active_media_tab()
        if tab is None:
            QMessageBox.information(self, "No Library Tab", "Open a library tab (Videos / Images / Audio / PDFs) first.")
            return
        dlg = PreviewChangesDialog(tab, self)
        tab._enter_modal()
        try:
            accepted = dlg.exec() == QDialog.DialogCode.Accepted
        finally:
            tab._exit_modal()
        if accepted and dlg.process_requested:
            tab._on_process_all()

    def _open_library_dashboard(self):
        LibraryDashboardDialog(self, self).exec()

    def _open_duplicate_resolver(self):
        tab = self._active_media_tab()
        if tab is None:
            QMessageBox.information(self, "No Library Tab", "Open a library tab (Videos / Images / Audio / PDFs) first.")
            return
        if not list(getattr(tab, 'media_infos', []) or []):
            QMessageBox.information(self, "No Files", "Load files into this tab first (Add Folder, then Reload).")
            return
        dlg = DuplicateResolverDialog(tab, self)
        tab._enter_modal()
        try:
            dlg.exec()
        finally:
            tab._exit_modal()

    def _open_tag_editor(self):
        tab = self._active_media_tab()
        if tab is None:
            QMessageBox.information(self, "No Library Tab", "Open a library tab (Videos / Images / Audio / PDFs) first.")
            return
        selected = []
        for rng in tab.table.selectedRanges():
            for row in range(rng.topRow(), rng.bottomRow() + 1):
                if row in tab.filtered_rows or not tab.filtered_rows:
                    info = tab._get_row_info(row)
                    if info and info.is_valid and info not in selected:
                        selected.append(info)
        if not selected:
            QMessageBox.information(self, "No Selection", "Select at least one valid file in the list first.")
            return
        dlg = MediaTagEditorDialog(selected, self)
        tab._enter_modal()
        try:
            dlg.exec()
        finally:
            tab._exit_modal()

    def _open_folder_profiles(self):
        FolderProfilesDialog(self, self).exec()

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
        sep_text = self.separator_input.text()
        if any(ch in sep_text for ch in '\\/:*?"<>|'):
            # FIX: an illegal separator would poison every generated filename
            sep_text = re.sub(r'[\\/:*?"<>|]', '', sep_text) or ' '
            self.separator_input.blockSignals(True)
            self.separator_input.setText(sep_text)
            self.separator_input.blockSignals(False)
            self.show_toast("Separator can't contain characters illegal in filenames — removed.", 'warning')
        # Cap at 8 chars to match _load_state's round-trip — a longer separator
        # was silently truncated to 8 on the next launch.
        self.naming_separator = (sep_text[:8] or ' ')
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
                    tab._update_row_preview(row, refresh_stats=False)
                tab._update_stats()

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
            elif self.isMinimized():
                # Saving minimized geometry (~-32000 x/y on Windows) silently
                # replaced the user's normal position with a centered default
                # on next launch — restore from the tracked normal geometry.
                geo = dict(self._normal_geometry) if hasattr(self, '_normal_geometry') and self._normal_geometry else {'x': self.x(), 'y': self.y(), 'width': self.width(), 'height': self.height()}
            else: geo = {'x': self.x(), 'y': self.y(), 'width': self.width(), 'height': self.height()}
            state = {
                'version': 1, 'app_version': __version__,
                'geometry': geo, 'maximized': is_maximized,
                'video_folders': video_folders, 'image_folders': image_folders, 'audio_folders': audio_folders, 'pdf_folders': pdf_folders,
                'default_video_player': self.video_tab.default_player, 'default_image_opener': self.image_tab.default_player, 'default_audio_player': self.audio_tab.default_player, 'default_pdf_opener': self.pdf_tab.default_player,
                'ffprobe_path': getattr(self, 'ffprobe_path', ''),
                'video_tab': self.video_tab.get_state_dict(), 'image_tab': self.image_tab.get_state_dict(), 'audio_tab': self.audio_tab.get_state_dict(), 'pdf_tab': self.pdf_tab.get_state_dict(),
                'smart_folders': getattr(self, 'smart_folders_config', []),
                'theme': self.theme_combo.currentText(),
                'theme_accent': self.accent_combo.currentText(),
                # FIX: global mute was never persisted — every launch reset it
                'global_mute': bool(getattr(self, 'global_mute', False)),
                'ui_scale': float(getattr(self, 'ui_scale', 1.0)),
                'reduced_motion': bool(getattr(self, 'reduced_motion', False)),
                'thumb_size': int(getattr(self, 'thumb_size', 130)),
                'naming_separator': self.naming_separator,
                'naming_fields': self.naming_fields,
                'naming_all_fields_ordered': self.naming_all_fields_ordered,
                'naming_keep_extension': self.naming_keep_extension,
                'open_with_apps': getattr(self, 'open_with_apps', []),
                # FEATURE (v2.5): presets + folder profiles
                'rename_presets': getattr(self, 'rename_presets', {}),
                'folder_profiles': getattr(self, 'folder_profiles', {}),
                'settings_width': getattr(self, '_settings_width', 420)
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
        self._geometry_restored = False
        if not os.path.exists(CONFIG_FILE):
            ThemeManager.apply_theme(self, "System (Auto)", "Deep Space")
            return
        try:
            with open(CONFIG_FILE, 'r', encoding='utf-8') as f: state = json.load(f)
            if not isinstance(state, dict):
                raise TypeError("config root is not a JSON object")
        except json.JSONDecodeError as e:
            logger.warning("Corrupt config file (%s); starting fresh: %s", CONFIG_FILE, e)
            self._load_failed = True
            ThemeManager.apply_theme(self, "System (Auto)", "Deep Space")
            return
        except OSError as e:
            logger.warning("Could not read config %s; starting fresh: %s", CONFIG_FILE, e)
            self._load_failed = True
            ThemeManager.apply_theme(self, "System (Auto)", "Deep Space")
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
            if 'settings_width' in state and isinstance(state['settings_width'], int):
                self._settings_width = max(320, min(800, state['settings_width']))
        run_section('accessibility', _a11y, destructive=False)

        # ── Theme (non-destructive) ──
        def _theme():
            saved_theme = state.get('theme', 'System (Auto)')
            saved_accent = state.get('theme_accent', None)

            # Backwards compatibility: migrate legacy combined skin names
            if saved_accent is None:
                if saved_theme == "Deep Space":
                    saved_theme = "Dark"
                    saved_accent = "Deep Space"
                elif saved_theme == "Aurora":
                    saved_theme = "Dark"
                    saved_accent = "Emerald"
                elif saved_theme == "Glass Morph":
                    saved_theme = "Light"
                    saved_accent = "Deep Space"
                elif saved_theme == "Dark Mode":
                    saved_theme = "Dark"
                    saved_accent = "Deep Space"
                elif saved_theme == "Light Mode":
                    saved_theme = "Light"
                    saved_accent = "Deep Space"
                else:
                    saved_accent = "Deep Space"

            # Normalize mode
            valid_modes = [self.theme_combo.itemText(i) for i in range(self.theme_combo.count())]
            if saved_theme not in valid_modes:
                if "light" in str(saved_theme).lower():
                    saved_theme = "Light"
                elif "dark" in str(saved_theme).lower():
                    saved_theme = "Dark"
                else:
                    saved_theme = "System (Auto)"

            # Normalize accent
            valid_accents = [self.accent_combo.itemText(i) for i in range(self.accent_combo.count())]
            if saved_accent not in valid_accents:
                saved_accent = "Deep Space"

            self.theme_combo.blockSignals(True)
            self.theme_combo.setCurrentText(saved_theme)
            self.theme_combo.blockSignals(False)

            self.accent_combo.blockSignals(True)
            self.accent_combo.setCurrentText(saved_accent)
            self.accent_combo.blockSignals(False)

            ThemeManager.apply_theme(self, saved_theme, saved_accent)
        run_section('theme', _theme, destructive=False)

        # ── Custom Naming Template ──
        def _naming():
            sep = state.get('naming_separator', ' ')
            if not isinstance(sep, str):
                sep = ' '
            # Same rule as the live editor: a crafted config must not inject
            # path separators into every generated filename.
            sep = re.sub(r'[\\/:*?"<>|]', '', sep)[:8] or ' '
            self.naming_separator = sep
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
                        target_rect = QRect(x, y, w, h)
                        screens = QApplication.screens()
                        if screens and any(s.availableGeometry().intersects(target_rect) for s in screens):
                            # move()+resize(), not setGeometry(): x()/y() saved on
                            # close are FRAME coordinates while setGeometry() sets
                            # the CLIENT area — the old call shifted the window
                            # up-left by the title-bar height on every restart.
                            self.move(x, y)
                            self.resize(w, h)
                            self._normal_geometry = {'x': x, 'y': y, 'width': w, 'height': h}
                            has_geo = True
            if state.get('maximized', False): self.showMaximized()
            self._geometry_restored = has_geo or bool(state.get('maximized', False))
        run_section('geometry', _geometry, destructive=False)

        # ── Source folder lists + per-tab directories ──
        video_folders, image_folders, audio_folders, pdf_folders = [], [], [], []

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

        # ── FEATURE SUITE: presets + folder profiles (non-destructive) ──
        def _features():
            presets = state.get('rename_presets', {})
            loaded = {}
            if isinstance(presets, dict):
                for name, p in presets.items():
                    if not isinstance(name, str) or not name.strip() or not isinstance(p, dict):
                        continue
                    p_fields = p.get('fields', [])
                    p_ordered = p.get('all_ordered', [])
                    p_sep = p.get('separator', ' ')
                    if not isinstance(p_fields, list) or not isinstance(p_ordered, list) or not isinstance(p_sep, str):
                        continue
                    p_sep = re.sub(r'[\\/:*?"<>|]', '', p_sep)[:8] or ' '
                    loaded[name] = {
                        'fields': [f for f in p_fields if f in FIELD_MAP.values()],
                        'all_ordered': [f for f in p_ordered if isinstance(f, str) and f in FIELD_MAP],
                        'separator': p_sep,
                        'keep_extension': bool(p.get('keep_extension', True)),
                    }
            self.rename_presets = loaded
            profiles = state.get('folder_profiles', {})
            prof_loaded = {}
            if isinstance(profiles, dict):
                for folder, prof in profiles.items():
                    if not isinstance(folder, str) or not folder.strip() or not isinstance(prof, dict):
                        continue
                    preset_name = prof.get('preset')
                    if preset_name is not None and not isinstance(preset_name, str):
                        preset_name = None
                    prof_loaded[os.path.normcase(os.path.normpath(folder))] = {
                        'preset': preset_name or None,
                        'auto_rename': bool(prof.get('auto_rename', False)),
                    }
            self.folder_profiles = prof_loaded
        run_section('feature suite (presets/profiles)', _features, destructive=False)

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
                    if name.strip().lower() in self.BUILTIN_PAGE_TITLES:
                        logger.warning("Skipping smart folder with reserved name %r", name)
                        continue
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
        if hasattr(self, '_preview_refresh_timer'):
            self._preview_refresh_timer.stop()
        if hasattr(self, 'hover_overlay') and self.hover_overlay:
            try:
                self.hover_overlay.hide_preview()
            except Exception:
                pass
        # Stop watch timers, flush timers, and request interruption for any running scanners
        for tab in list(getattr(self, 'smart_folder_tabs', {}).values()) + [getattr(self, n, None) for n in ('video_tab','image_tab','audio_tab','pdf_tab')]:
            if tab is None:
                continue
            try:
                if hasattr(tab, '_watch_timer') and tab._watch_timer.isActive():
                    tab._watch_timer.stop()
                if hasattr(tab, '_watch_flush_timer') and tab._watch_flush_timer.isActive():
                    tab._watch_flush_timer.stop()
                if hasattr(tab, '_filter_timer') and tab._filter_timer.isActive():
                    tab._filter_timer.stop()
                if hasattr(tab, 'hover_timer') and tab.hover_timer.isActive():
                    tab.hover_timer.stop()
                if hasattr(tab, '_exclude_timer') and tab._exclude_timer.isActive():
                    tab._exclude_timer.stop()
                st = getattr(tab, 'scanner_thread', None)
                if st is not None and st.isRunning():
                    st.requestInterruption()
                for ow in list(getattr(tab, '_orphaned_scanners', [])):
                    try:
                        if ow.isRunning():
                            ow.requestInterruption()
                    except RuntimeError:
                        pass
            except RuntimeError:
                pass
        # Give scanners a brief grace period to exit cleanly
        for tab in list(getattr(self, 'smart_folder_tabs', {}).values()) + [getattr(self, n, None) for n in ('video_tab','image_tab','audio_tab','pdf_tab')]:
            if tab is None:
                continue
            try:
                st = getattr(tab, 'scanner_thread', None)
                if st is not None and st.isRunning():
                    st.wait(1800)
                for ow in list(getattr(tab, '_orphaned_scanners', [])):
                    try:
                        if ow.isRunning():
                            ow.wait(1200)
                    except RuntimeError:
                        pass
                # Release file handles held by preview players before teardown
                if hasattr(tab, '_release_file_locks'):
                    try:
                        tab._release_file_locks()
                    except Exception:
                        pass
                if hasattr(tab, '_thumb_pool'):
                    try:
                        tab._thumb_pool.clear()
                        tab._thumb_pool.waitForDone(400)
                    except RuntimeError:
                        pass
                if hasattr(tab, '_watch_info_pool'):
                    try:
                        tab._watch_info_pool.clear()
                        tab._watch_info_pool.waitForDone(400)
                    except RuntimeError:
                        pass
            except RuntimeError:
                pass
        # Close any open native players
        for np in list(getattr(self, '_native_players', []) or []):
            try:
                np.close()
            except Exception:
                pass
        # Cancel and wait for still-running metadata workers
        for _mw in list(getattr(self, '_orphaned_metadata_workers', [])):
            try:
                if _mw.isRunning():
                    if hasattr(_mw, 'cancel'):
                        _mw.cancel()
                    _mw.wait(600)
            except RuntimeError:
                pass
        # Cancel and wait for still-running trim exports
        for _w in list(getattr(self, '_orphaned_trim_workers', [])):
            try:
                if _w.isRunning():
                    if hasattr(_w, 'cancel'):
                        _w.cancel()
                    _w.wait(1000)
            except RuntimeError:
                pass
        # Never overwrite a config we failed to load
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
        # Persist the toggle immediately: only closeEvent happened to save it
        # before, so a crash/power-loss silently reverted the setting.
        self._debounced_save_state()

    def _browse_ffprobe_path(self):
        path, _ = QFileDialog.getOpenFileName(self, "Select ffprobe Executable", os.environ.get('PROGRAMFILES', 'C:\\'), "Executables (ffprobe.exe);;All Files (*)")
        if path:
            path = os.path.normpath(path)
            app_name = os.path.splitext(os.path.basename(path))[0]
            self.ffprobe_path_label.setText(f"{app_name}\n{path}")
            self.ffprobe_path = path
            self._debounced_save_state()

    def _clear_ffprobe_path(self):
        self.ffprobe_path_label.setText("System PATH (Default)")
        self.ffprobe_path = ""
        self._debounced_save_state()

    def _update_settings_shadow_color(self):
        if not hasattr(self, '_settings_shadow') or not self._settings_shadow:
            return
        is_dark = getattr(self, 'current_theme', 'dark') == 'dark'
        if is_dark:
            self._settings_shadow.setColor(QColor(0, 0, 0, 160))
        else:
            self._settings_shadow.setColor(QColor(15, 23, 42, 65))

    def _get_settings_default_width(self):
        scale = getattr(self, 'ui_scale', 1.0)
        if scale >= 1.15:
            base_min_w = 520
        elif scale <= 0.9:
            base_min_w = 420
        else:
            base_min_w = 460

        if hasattr(self, 'settings_scroll_area') and self.settings_scroll_area and self.settings_scroll_area.widget():
            w_hint = self.settings_scroll_area.widget().sizeHint().width()
            if w_hint > 100:
                base_min_w = max(base_min_w, w_hint + 68)
        return base_min_w

    def _get_settings_target_rect(self):
        if not hasattr(self, 'content_wrapper') or not self.content_wrapper:
            return QRect(0, 0, 460, 500)
        c_w = self.content_wrapper.width()
        c_h = self.content_wrapper.height()
        margin_r = 10
        margin_t = 8
        margin_b = 8
        base_min_w = self._get_settings_default_width()
        max_w = max(base_min_w, int(c_w * 0.75))
        curr_w = getattr(self, '_settings_width', base_min_w)
        target_w = max(base_min_w, min(curr_w, max_w))
        target_x = max(0, c_w - target_w - margin_r)
        target_y = margin_t
        target_h = max(100, c_h - margin_t - margin_b)
        return QRect(target_x, target_y, target_w, target_h)

    def _reposition_settings_panel(self, animate=False):
        if not hasattr(self, 'settings_panel') or not hasattr(self, 'content_wrapper'):
            return
        if not self._settings_visible:
            self._sync_settings_resize_handle()
            return
        target_rect = self._get_settings_target_rect()
        if animate:
            if hasattr(self, '_settings_anim') and self._settings_anim:
                try:
                    self._settings_anim.stop()
                    self._settings_anim.finished.disconnect()
                except Exception:
                    pass
            start_rect = QRect(self.content_wrapper.width() + 10, target_rect.y(), target_rect.width(), target_rect.height())
            self.settings_panel.setGeometry(start_rect)
            self._settings_anim = QPropertyAnimation(self.settings_panel, b"geometry")
            self._settings_anim.setDuration(180)
            self._settings_anim.setStartValue(start_rect)
            self._settings_anim.setEndValue(target_rect)
            self._settings_anim.setEasingCurve(QEasingCurve.Type.OutCubic)
            self._settings_anim.valueChanged.connect(self._sync_settings_resize_handle)
            self._settings_anim.start()
        else:
            self.settings_panel.setGeometry(target_rect)
            self._sync_settings_resize_handle()

    def _sync_settings_resize_handle(self):
        if hasattr(self, '_settings_resize_handle') and self._settings_resize_handle:
            if hasattr(self, 'settings_panel') and self.settings_panel.isVisible():
                p_geo = self.settings_panel.geometry()
                self._settings_resize_handle.setGeometry(p_geo.x() - 6, p_geo.y(), 12, p_geo.height())
                self._settings_resize_handle.setVisible(True)
                self._settings_resize_handle.raise_()
            else:
                self._settings_resize_handle.setVisible(False)

    def _toggle_settings(self):
        self._settings_visible = not self._settings_visible
        if self._settings_visible:
            self._show_settings_overlay()
        else:
            self._hide_settings_overlay()

    def _show_settings_overlay(self):
        if hasattr(self, '_settings_anim') and self._settings_anim:
            try:
                self._settings_anim.stop()
                self._settings_anim.finished.disconnect()
            except Exception:
                pass
        self.settings_panel.setVisible(True)
        self.settings_panel.raise_()
        self._update_settings_shadow_color()
        if getattr(self, 'reduced_motion', False):
            self.settings_panel.setGeometry(self._get_settings_target_rect())
            self._sync_settings_resize_handle()
        else:
            self._reposition_settings_panel(animate=True)

    def _hide_settings_overlay(self):
        if not hasattr(self, 'settings_panel') or not self.settings_panel.isVisible():
            if hasattr(self, '_settings_resize_handle'):
                self._settings_resize_handle.setVisible(False)
            return

        if hasattr(self, '_settings_resize_handle'):
            self._settings_resize_handle.setVisible(False)

        if hasattr(self, '_settings_anim') and self._settings_anim:
            try:
                self._settings_anim.stop()
                self._settings_anim.finished.disconnect()
            except Exception:
                pass

        if getattr(self, 'reduced_motion', False):
            self.settings_panel.setVisible(False)
            self._sync_settings_resize_handle()
            return

        cur_rect = self.settings_panel.geometry()
        end_rect = QRect(self.content_wrapper.width() + 10, cur_rect.y(), cur_rect.width(), cur_rect.height())
        self._settings_anim = QPropertyAnimation(self.settings_panel, b"geometry")
        self._settings_anim.setDuration(160)
        self._settings_anim.setStartValue(cur_rect)
        self._settings_anim.setEndValue(end_rect)
        self._settings_anim.setEasingCurve(QEasingCurve.Type.InCubic)
        self._settings_anim.finished.connect(self._on_settings_hidden)
        self._settings_anim.start()

    def _on_settings_hidden(self):
        if not self._settings_visible:
            self.settings_panel.setVisible(False)
        self._sync_settings_resize_handle()

    def _add_video_folder(self):
        folder = QFileDialog.getExistingDirectory(self, "Select Video Folder")
        if folder:
            folder = os.path.normpath(folder)
            items = [self.videos_list_widget.item(i).text() for i in range(self.videos_list_widget.count())]
            if folder not in items:
                self.videos_list_widget.addItem(folder)
                self._update_video_directories()
                self._maybe_apply_folder_profile([folder])

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
                self._maybe_apply_folder_profile([folder])

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
                self._maybe_apply_folder_profile([folder])

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
                self._maybe_apply_folder_profile([folder])

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
        else:
            active_tab = self.stacked_widget.currentWidget()
            if active_tab and hasattr(active_tab, 'media_type'):
                if active_tab.media_type == 'image': self._add_image_folder()
                elif active_tab.media_type == 'audio': self._add_audio_folder()
                elif active_tab.media_type == 'pdf': self._add_pdf_folder()
                else: self._add_video_folder()

    def _guess_page_for_dirs(self, directories):
        """Sample file extensions in the given directories to pick the tab page
        (0=video, 1=image, 2=audio, 3=pdf) — same heuristic as open_folders_from_args."""
        exts = set()
        for d in directories[:3]:
            try:
                all_names = os.listdir(d)
                file_names = [n for n in all_names if os.path.isfile(os.path.join(d, n))][:300]
                for name in file_names:
                    exts.add(os.path.splitext(name)[1].lower())
            except OSError:
                continue
        if exts and (exts & IMAGE_EXTENSIONS) and not (exts & VIDEO_EXTENSIONS): return 1
        if exts and (exts & AUDIO_EXTENSIONS) and not (exts & VIDEO_EXTENSIONS): return 2
        if exts and (exts & PDF_EXTENSIONS) and not (exts & VIDEO_EXTENSIONS): return 3
        return 0

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
            if not url.isLocalFile():
                # Remote URLs (dragged from a browser) have an empty localFile;
                # normpath("") = "." and isdir(".") is True — the process CWD
                # was silently added as a media folder AND persisted to config.
                continue
            path = os.path.normpath(url.toLocalFile())
            if os.path.isdir(path): directories.append(path)
            elif os.path.isfile(path): files.append(path)
        if directories:
            idx = self.stacked_widget.currentIndex()
            list_widget = None
            update_func = None
            if idx == 0: list_widget = self.videos_list_widget; update_func = self._update_video_directories
            elif idx == 1: list_widget = self.images_list_widget; update_func = self._update_image_directories
            elif idx == 2: list_widget = self.audio_list_widget; update_func = self._update_audio_directories
            elif idx == 3: list_widget = self.pdf_list_widget; update_func = self._update_pdf_directories
            elif hasattr(active_tab, 'is_smart_folder') and active_tab.is_smart_folder:
                if active_tab.media_type == 'video': list_widget = self.videos_list_widget; update_func = self._update_video_directories
                elif active_tab.media_type == 'image': list_widget = self.images_list_widget; update_func = self._update_image_directories
                elif active_tab.media_type == 'audio': list_widget = self.audio_list_widget; update_func = self._update_audio_directories
                elif active_tab.media_type == 'pdf': list_widget = self.pdf_list_widget; update_func = self._update_pdf_directories
                else:
                    # 'all' smart folder: guess the media type from the dropped
                    # directories' contents instead of always routing to Videos.
                    page = self._guess_page_for_dirs(directories)
                    list_widget = {0: self.videos_list_widget, 1: self.images_list_widget,
                                   2: self.audio_list_widget, 3: self.pdf_list_widget}[page]
                    update_func = {0: self._update_video_directories, 1: self._update_image_directories,
                                   2: self._update_audio_directories, 3: self._update_pdf_directories}[page]

            if list_widget is not None and update_func is not None:
                existing = set(list_widget.item(i).text() for i in range(list_widget.count()))
                added_any = False
                for d in directories:
                    if d not in existing:
                        list_widget.addItem(d)
                        existing.add(d)
                        added_any = True
                if added_any:
                    update_func()
                    if hasattr(active_tab, 'is_smart_folder') and active_tab.is_smart_folder:
                        self.refresh_smart_folder_tab(active_tab)
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
                existing_paths = {os.path.normcase(v.filepath) for v in active_tab.media_infos}
                was_sorting = active_tab.table.isSortingEnabled()
                active_tab.table.setSortingEnabled(False)
                try:
                    for filepath in valid_files:
                        # Set lookup: the old list-comprehension-per-file was O(n²)
                        if os.path.normcase(filepath) in existing_paths: continue
                        info = MediaInfo(filepath, active_tab.media_type)
                        active_tab._on_file_found(info)
                finally:
                    active_tab.table.setSortingEnabled(was_sorting)
                total = len(active_tab.media_infos)
                if total > 0:
                    if active_tab.view_stack.currentIndex() == 2:
                        active_tab.view_stack.setCurrentIndex(1 if active_tab.btn_view_mode.isChecked() else 0)
                    active_tab.btn_process.setEnabled(True)
                    active_tab.btn_relocate.setEnabled(True)
                    active_tab.btn_find_dupes.setEnabled(True)
                    active_tab.btn_clear.setVisible(True)
                    active_tab._load_visible_widgets()
                active_tab._update_stats()

AUDIT_LOG_FILE = os.path.join(CONFIG_DIR, "rename_audit.csv")

def append_rename_audit(entries, op=None):
    """C3: append-only audit trail of every rename/move (old → new).

    CSV rows: timestamp, operation, old_path, new_path. Best-effort — failures
    are logged and never interrupt renames. Portable mode keeps this beside
    the exe automatically via CONFIG_DIR.
    `op` overrides the operation label of the main (first) entry so undo/redo/
    delete are distinguishable from fresh renames; sidecars stay "sidecar".
    """
    if not entries:
        return
    try:
        os.makedirs(CONFIG_DIR, exist_ok=True)
        # Size-based rotation: the log grew without bound (years of renames →
        # multi-MB CSV fsynced on every rename). Keep one generation at 5 MB.
        try:
            if os.path.exists(AUDIT_LOG_FILE) and os.path.getsize(AUDIT_LOG_FILE) > 5 * 1024 * 1024:
                rotated = AUDIT_LOG_FILE + ".1"
                if os.path.exists(rotated):
                    os.remove(rotated)
                os.replace(AUDIT_LOG_FILE, rotated)
        except OSError as e:
            logger.debug("audit log rotation failed: %s", e)
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
            def _csv_safe(val):
                # Guard against Excel formula injection: a path starting with
                # =,+,-,@ would execute as a formula when the CSV is opened.
                s = str(val)
                if s[:1] in ('=', '+', '-', '@'):
                    return "'" + s
                return s
            for old_p, new_p in entries:
                if old_p != first_old:
                    row_op = "sidecar"
                else:
                    row_op = op or "rename"
                wr.writerow([ts, row_op, _csv_safe(old_p), _csv_safe(new_p)])
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
        hint_dirs = [os.path.abspath(a) for a in sys.argv[1:] if os.path.isdir(a)]
        try:
            _sock.write(("open\t" + "\n".join(hint_dirs)).encode("utf-8"))
            _sock.flush()
            _sock.waitForBytesWritten(300)
        except Exception:
            pass
        _sock.disconnectFromServer()
        print("MediaFlow is already running \u2014 focusing the existing window.")
        return
    if _sock.error() in (QLocalSocket.LocalSocketError.ServerNotFoundError, QLocalSocket.LocalSocketError.ConnectionRefusedError, QLocalSocket.LocalSocketError.UnknownSocketError):
        QLocalServer.removeServer("MediaFlowSingleInstance")  # stale lock from crash
    _instance_server = QLocalServer()
    app._instance_server = _instance_server  # Keep reference alive on QApplication
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

        def _handle_payload():
            data = bytes(conn.readAll()).decode("utf-8", "replace")
            conn.disconnectFromServer()
            window.setWindowState(window.windowState() & ~Qt.WindowState.WindowMinimized | Qt.WindowState.WindowActive)
            window.raise_()
            window.activateWindow()
            if data.startswith("open\t"):
                dirs = [d for d in data.split("\t", 1)[1].split("\n") if d]
                if dirs:
                    QTimer.singleShot(0, lambda: window.open_folders_from_args(dirs))

        conn.disconnected.connect(conn.deleteLater)
        if conn.bytesAvailable():
            _handle_payload()
        else:
            conn.readyRead.connect(_handle_payload)
            # Focus existing window immediately without waiting for payload
            window.setWindowState(window.windowState() & ~Qt.WindowState.WindowMinimized | Qt.WindowState.WindowActive)
            window.raise_()
            window.activateWindow()

    _instance_server.newConnection.connect(_second_instance_connected)
    app.aboutToQuit.connect(_instance_server.close)

    window.show()

    # ── C2: launch folders from the command line ──
    cli_dirs = [os.path.abspath(a) for a in sys.argv[1:] if os.path.isdir(a)]
    if cli_dirs:
        QTimer.singleShot(0, lambda: window.open_folders_from_args(cli_dirs))

    sys.exit(app.exec())

if __name__ == "__main__":
    main()
