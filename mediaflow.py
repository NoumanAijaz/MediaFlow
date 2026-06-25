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
from datetime import datetime
import numpy as np
import cv2

from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout, QGridLayout,
    QPushButton, QLabel, QFileDialog, QTableWidget, QTableWidgetItem,
    QHeaderView, QComboBox, QLineEdit, QMessageBox, QProgressBar,
    QFrame, QAbstractItemView, QMenu, QCheckBox, QDialog, QDialogButtonBox, QRadioButton,
    QFormLayout, QGroupBox, QStackedWidget, QListWidget, QListWidgetItem,
    QStyledItemDelegate, QSlider, QScrollArea, QStyle
)
from PyQt6.QtCore import (
    Qt, QThread, pyqtSignal, QPropertyAnimation, QEasingCurve,
    QTimer, QSize, QRect, QUrl, QPoint, QPointF, QRectF, QEvent
)
from PyQt6.QtGui import (
    QFont, QColor, QIcon, QPalette, QPainter,
    QAction, QPixmap, QKeySequence, QImage, QBrush, QGuiApplication,
    QPen, QPainterPath, QCursor, QImageReader
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

CONFIG_DIR = os.path.join(os.environ.get('APPDATA', '.'), 'MediaFlow')
CONFIG_FILE = os.path.join(CONFIG_DIR, 'config.json')

def get_resource_path(relative_path):
    """Get absolute path to resource, works for dev and for PyInstaller"""
    try:
        base_path = sys._MEIPASS
    except AttributeError:
        base_path = os.path.dirname(os.path.abspath(__file__))
    return os.path.join(base_path, relative_path)

def update_metadata_cache(entries_to_add: dict, paths_to_delete: list = None):
    cache_path = os.path.join(CONFIG_DIR, 'scan_cache.json')
    try:
        os.makedirs(CONFIG_DIR, exist_ok=True)
        import time
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
                with open(temp_path, 'w', encoding='utf-8') as f:
                    json.dump(current_cache, f, ensure_ascii=False, indent=2)
                if os.path.exists(cache_path):
                    os.remove(cache_path)
                os.rename(temp_path, cache_path)
                break
            except Exception:
                time.sleep(0.05)
    except Exception:
        pass

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

def parse_naming_format(filename: str) -> tuple[str | None, str | None]:
    match = re.match(r"^(.+)\s+(\d+)\s+(4K|2K|1K|k)(?:\s+(\d+|—))?(?:\.[^.]+)?$", filename, re.IGNORECASE)
    if match:
        artist = match.group(1).strip()
        rating = match.group(4)
        return artist, (None if rating == "—" else rating)
    
    match_img = re.match(r"^(.+)\s+(4K|2K|1K|k)(?:\s+(\d+|—))?(?:\.[^.]+)?$", filename, re.IGNORECASE)
    if match_img:
        artist = match_img.group(1).strip()
        rating = match_img.group(3)
        return artist, (None if rating == "—" else rating)
        
    match_aud = re.match(r"^(.+)\s+(\d+)\s+(\d+|—)(?:\.[^.]+)?$", filename, re.IGNORECASE)
    if match_aud:
        artist = match_aud.group(1).strip()
        rating = match_aud.group(3)
        return artist, (None if rating == "—" else rating)
        
    return None, None

def calculate_file_hash(filepath: str) -> str | None:
    try:
        if not os.path.exists(filepath): return None
        hasher = hashlib.md5()
        with open(filepath, 'rb') as f:
            for chunk in iter(lambda: f.read(65536), b''):
                hasher.update(chunk)
        return hasher.hexdigest()
    except Exception: return None

def calculate_perceptual_hash(filepath: str, media_type: str) -> str | None:
    try:
        if not os.path.exists(filepath): return None
        img = None
        if media_type == 'image':
            img = cv2.imdecode(np.fromfile(filepath, dtype=np.uint8), cv2.IMREAD_GRAYSCALE)
        elif media_type == 'video':
            cap = cv2.VideoCapture(filepath)
            if cap.isOpened():
                total_frames = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))
                mid_frame = total_frames // 2 if total_frames > 0 else 0
                cap.set(cv2.CAP_PROP_POS_FRAMES, mid_frame)
                ret, frame = cap.read()
                if ret: img = cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY)
                cap.release()
        if img is None: return None
        resized = cv2.resize(img, (9, 8), interpolation=cv2.INTER_AREA)
        diff = resized[:, 1:] > resized[:, :-1]
        hash_val = 0
        for bit in diff.flatten(): hash_val = (hash_val << 1) | int(bit)
        return f"{hash_val:016x}"
    except Exception: return None

def hamming_distance(h1: str, h2: str) -> int:
    try:
        val1 = int(h1, 16)
        val2 = int(h2, 16)
        return bin(val1 ^ val2).count('1')
    except Exception: return 999

def matches_query(info: 'MediaInfo', query_str: str, preview_name: str = "") -> bool:
    if not query_str: return True
    import shlex
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
    # Remove leading/trailing spaces and dots
    clean = clean.strip(" .")
    return clean or "Unknown"

def parse_destination_template(template: str, info: 'MediaInfo', tags: list[str] = None) -> str:
    """
    Replaces {variables} in a path template with actual MediaInfo data.
    Example: 'D:\Media\{type}\{name}' -> 'D:\Media\video\John Doe'
    """
    parsed_artist, parsed_rating = parse_naming_format(info.filename)
    
    # Fallback to tags if artist isn't in the filename
    artist = parsed_artist or (tags[0] if tags else "Unknown Artist")
    rating = parsed_rating or "Unrated"
    
    # Map variables to data
    replacements = {
        '{type}': info.media_type,
        '{ext}': info.extension.replace('.', ''),
        '{name}': sanitize_folder_name(artist),
        '{rating}': sanitize_folder_name(rating),
        '{resolution}': info.resolution_tag or "Unknown",
        '{tag}': sanitize_folder_name(tags[0]) if tags else "Untagged",
        '{tags}': sanitize_folder_name(", ".join(tags)) if tags else "Untagged"
    }
    
    result = template
    for key, val in replacements.items():
        result = result.replace(key, val)
        
    return result

def get_ffprobe_command(custom_path=None) -> str | None:
    if custom_path and os.path.exists(custom_path): return custom_path
    sh_path = shutil.which("ffprobe")
    return sh_path

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

def generate_thumbnail(filepath: str, media_type: str = 'video', width: int = 120, height: int = 68) -> QPixmap | None:
    try:
        if media_type == 'audio':
            pixmap = QPixmap(width, height)
            pixmap.fill(QColor("#1e1b4b"))
            painter = QPainter(pixmap)
            painter.setRenderHint(QPainter.RenderHint.Antialiasing)
            painter.setFont(QFont("Segoe UI", 24))
            painter.setPen(QColor("#a78bfa"))
            painter.drawText(QRect(0, 0, width, height), Qt.AlignmentFlag.AlignCenter, "🎵")
            painter.end()
            return pixmap
        if media_type == 'pdf':
            pixmap = QPixmap(width, height)
            pixmap.fill(QColor("#1e1b4b"))
            painter = QPainter(pixmap)
            painter.setRenderHint(QPainter.RenderHint.Antialiasing)
            painter.setFont(QFont("Segoe UI", 24))
            painter.setPen(QColor("#f87171"))
            painter.drawText(QRect(0, 0, width, height), Qt.AlignmentFlag.AlignCenter, "📄")
            painter.end()
            return pixmap
        if media_type == 'video':
            cap = cv2.VideoCapture(filepath)
            if not cap.isOpened(): return None
            total_frames = cap.get(cv2.CAP_PROP_FRAME_COUNT)
            if total_frames <= 0: cap.release(); return None
            target_frame = int(total_frames * 0.1)
            cap.set(cv2.CAP_PROP_POS_FRAMES, target_frame)
            ret, frame = cap.read()
            if not ret or frame is None:
                cap.set(cv2.CAP_PROP_POS_FRAMES, 0)
                ret, frame = cap.read()
            cap.release()
        else:
            frame = cv2.imdecode(np.fromfile(filepath, dtype=np.uint8), cv2.IMREAD_COLOR)
            ret = frame is not None
        if not ret or frame is None: return None
        frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
        h, w = frame.shape[:2]
        if h == 0 or w == 0: return None
        aspect = w / h
        if width / height > aspect: new_h = height; new_w = int(height * aspect)
        else: new_w = width; new_h = int(width / aspect)
        if new_w <= 0 or new_h <= 0: return None
        frame = cv2.resize(frame, (new_w, new_h), interpolation=cv2.INTER_AREA).copy()
        bytes_per_line = new_w * 3
        qimg = QImage(frame.data, new_w, new_h, bytes_per_line, QImage.Format.Format_RGB888).copy()
        pixmap = QPixmap(width, height)
        pixmap.fill(QColor("#1e1b4b"))
        painter = QPainter(pixmap)
        painter.drawImage((width - new_w) // 2, (height - new_h) // 2, qimg)
        painter.end()
        return pixmap
    except Exception: return None

def send_to_recycle_bin(path: str) -> bool:
    if sys.platform == "win32":
        from ctypes import windll, Structure, c_int, c_void_p, c_wchar_p, byref, create_unicode_buffer, cast
        from ctypes.wintypes import HWND, UINT
        class SHFILEOPSTRUCTW(Structure):
            _fields_ = [("hwnd", HWND), ("wFunc", UINT), ("pFrom", c_wchar_p), ("pTo", c_wchar_p), ("fFlags", ctypes.c_uint16), ("fAnyOperationsAborted", c_int), ("hNameMappings", c_void_p), ("lpszProgressTitle", c_wchar_p)]
        try:
            path = os.path.abspath(path)
            p_from_buf = create_unicode_buffer(path + "\0")
            fileop = SHFILEOPSTRUCTW()
            fileop.hwnd = None; fileop.wFunc = 3; fileop.pFrom = cast(p_from_buf, c_wchar_p); fileop.pTo = None
            fileop.fFlags = 0x0040 | 0x0010 | 0x0004; fileop.fAnyOperationsAborted = 0; fileop.hNameMappings = None; fileop.lpszProgressTitle = None
            return windll.shell32.SHFileOperationW(byref(fileop)) == 0
        except Exception: return False
    else:
        try:
            from send2trash import send2trash
            send2trash(path); return True
        except ImportError: return False

def get_vector_icon(name: str, is_dark: bool) -> QIcon:
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
        is_dark = True
        window = getattr(self.parent(), 'window', lambda: None)()
        if window and hasattr(window, 'current_theme'):
            is_dark = (window.current_theme == 'dark')
        
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
        
        painter.setFont(QFont("Segoe UI", 9, QFont.Weight.Bold))
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
#statsPanel { background: rgba(30, 27, 75, 0.60); border: 1px solid rgba(167, 139, 250, 0.2); border-left: 4px solid #8b5cf6; border-radius: 8px; padding: 0px; }
#statValue { font-size: 18px; font-weight: 800; color: #ffffff; }
#statLabel { font-size: 9px; color: #a78bfa; text-transform: uppercase; letter-spacing: 1px; font-weight: bold; }
QPushButton { border: none; border-radius: 8px; padding: 10px 24px; font-size: 13px; font-weight: 600; letter-spacing: 0.5px; }
#btnSelectFolder { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #6366f1, stop:1 #8b5cf6); color: white; min-width: 180px; }
#btnSelectFolder:hover { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #4f46e5, stop:1 #7c3aed); }
#btnSelectFolder:pressed { background: #4338ca; }
#btnSelectFolder:disabled { background: rgba(255, 255, 255, 0.05); color: rgba(255, 255, 255, 0.2); }
#btnProcessAll { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #10b981, stop:1 #06d6a0); color: white; min-width: 180px; font-size: 14px; padding: 12px 32px; }
#btnProcessAll:hover { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #059669, stop:1 #10b981); }
#btnProcessAll:pressed { background: #047857; }
#btnProcessAll:disabled { background: rgba(255, 255, 255, 0.05); color: rgba(255, 255, 255, 0.2); }
#btnClearAll { background: rgba(239, 68, 68, 0.15); color: #f87171; border: 1px solid rgba(239, 68, 68, 0.3); min-width: 100px; }
#btnClearAll:hover { background: rgba(239, 68, 68, 0.25); color: #ffffff; border: 1px solid #ef4444; }
#btnClearAll:pressed { background: #b91c1c; }
#btnClearAll:disabled { background: rgba(255, 255, 255, 0.05); color: rgba(255, 255, 255, 0.2); }
#btnLoadFiles { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #3b82f6, stop:1 #60a5fa); color: white; min-width: 140px; }
#btnLoadFiles:hover { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #2563eb, stop:1 #3b82f6); }
#btnLoadFiles:pressed { background: #1d4ed8; }
#btnLoadFiles:disabled { background: rgba(255, 255, 255, 0.05); color: rgba(255, 255, 255, 0.2); }
#btnStopLoading { background: rgba(239, 68, 68, 0.25); color: #f87171; border: 1px solid rgba(239, 68, 68, 0.4); min-width: 120px; }
#btnStopLoading:hover { background: rgba(239, 68, 68, 0.35); color: #ffffff; }
#btnStopLoading:pressed { background: rgba(185, 28, 28, 0.5); }
#btnStopLoading:disabled { background: rgba(255, 255, 255, 0.05); color: rgba(255, 255, 255, 0.2); }
#btnBatchEdit { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #f59e0b, stop:1 #fbbf24); color: #1f2937; min-width: 140px; }
#btnBatchEdit:hover { background: qlineargradient(x1:0, y1:0, x2:1, y2:0, stop:0 #d97706, stop:1 #f59e0b); color: #ffffff; }
#btnBatchEdit:pressed { background: #b45309; }
#btnBatchEdit:disabled { background: rgba(255, 255, 255, 0.05); color: rgba(255, 255, 255, 0.2); }
#btnFindDuplicates { background: rgba(14, 165, 233, 0.15); color: #38bdf8; border: 1px solid rgba(14, 165, 233, 0.3); min-width: 140px; }
#btnFindDuplicates:hover { background: rgba(14, 165, 233, 0.25); color: #ffffff; border: 1px solid #0ea5e9; }
#btnFindDuplicates:pressed { background: #0369a1; }
#btnFindDuplicates:disabled { background: transparent; color: rgba(255, 255, 255, 0.15); border: 1px solid rgba(255, 255, 255, 0.05); }
#btnViewMode, #btnTogglePreview { background: rgba(167, 139, 250, 0.15); color: #c4b5fd; border: 1px solid rgba(167, 139, 250, 0.3); min-width: 100px; padding: 6px 12px; font-size: 11px; border-radius: 6px; }
#btnViewMode:hover, #btnTogglePreview:hover { background: rgba(167, 139, 250, 0.25); color: #ffffff; }
#btnViewMode:pressed, #btnTogglePreview:pressed { background: rgba(139, 92, 246, 0.4); }
#btnViewMode:checked, #btnTogglePreview:checked { background: rgba(99, 102, 241, 0.4); color: #ffffff; border: 1px solid rgba(99, 102, 241, 0.6); }
#btnViewMode:disabled, #btnTogglePreview:disabled { background: transparent; color: rgba(255, 255, 255, 0.05); }
#previewPanel { background: rgba(15, 12, 41, 0.7); border: 1px solid rgba(167, 139, 250, 0.2); border-radius: 12px; }
#btnUndo, #btnRedo { background: rgba(139, 92, 246, 0.2); color: #a78bfa; border: 1px solid rgba(139, 92, 246, 0.4); min-width: 100px; }
#btnUndo:hover, #btnRedo:hover { background: rgba(139, 92, 246, 0.3); color: #ffffff; border: 1px solid #8b5cf6; }
#btnUndo:pressed, #btnRedo:pressed { background: #6d28d9; }
#btnUndo:disabled, #btnRedo:disabled { background: transparent; color: rgba(255, 255, 255, 0.15); border: 1px solid rgba(255, 255, 255, 0.05); }
#btnDelete { background: rgba(239, 68, 68, 0.15); color: #f87171; border: 1px solid rgba(239, 68, 68, 0.3); min-width: 120px; }
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
QLineEdit { background: rgba(45, 40, 90, 0.8); border: 1px solid rgba(167, 139, 250, 0.25); border-radius: 6px; padding: 4px 8px; color: #e0e0e0; font-size: 12px; }
QLineEdit:focus { border: 1px solid #8b5cf6; background: rgba(55, 48, 110, 0.9); }
QComboBox { background: rgba(45, 40, 90, 0.8); border: 1px solid rgba(167, 139, 250, 0.25); border-radius: 6px; padding: 4px 8px; color: #e0e0e0; font-size: 12px; min-width: 55px; }
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
#btnGlobalMute, #btnSettingsToggle { background: rgba(167, 139, 250, 0.15); color: #c4b5fd; border: 1px solid rgba(167, 139, 250, 0.3); border-radius: 8px; padding: 0px; font-size: 16px; }
#btnGlobalMute:hover, #btnSettingsToggle:hover { background: rgba(167, 139, 250, 0.3); color: #ffffff; }
#btnGlobalMute:pressed, #btnSettingsToggle:pressed { background: rgba(99, 102, 241, 0.4); }
#btnHelp { background: rgba(167, 139, 250, 0.15); color: #c4b5fd; border: 1px solid rgba(167, 139, 250, 0.3); border-radius: 18px; padding: 0px; font-size: 16px; font-weight: bold; }
#btnHelp:hover { background: rgba(167, 139, 250, 0.3); color: #ffffff; }
#btnHelp:pressed { background: rgba(99, 102, 241, 0.4); }
#btnCloseSettings, #btnClosePreview { background: rgba(239, 68, 68, 0.15); color: #f87171; border: 1px solid rgba(239, 68, 68, 0.3); border-radius: 6px; padding: 0px; font-weight: bold; font-size: 12px; }
#btnCloseSettings:hover, #btnClosePreview:hover { background: rgba(239, 68, 68, 0.3); color: #ffffff; }
#btnCloseSettings:pressed, #btnClosePreview:pressed { background: #b91c1c; }
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
#statsPanel { background: #ffffff; border: 1px solid #e2e8f0; border-left: 4px solid #6366f1; border-radius: 8px; padding: 0px; }
#statValue { font-size: 18px; font-weight: 800; color: #0f172a; }
#statLabel { font-size: 9px; color: #6366f1; text-transform: uppercase; letter-spacing: 1px; font-weight: bold; }
QPushButton { border: none; border-radius: 8px; padding: 10px 24px; font-size: 13px; font-weight: 600; letter-spacing: 0.5px; }
#btnSelectFolder { background: #6366f1; color: white; min-width: 180px; }
#btnSelectFolder:hover { background: #4f46e5; }
#btnSelectFolder:pressed { background: #3730a3; }
#btnSelectFolder:disabled { background: #cbd5e1; color: #94a3b8; }
#btnProcessAll { background: #10b981; color: white; min-width: 180px; font-size: 14px; padding: 12px 32px; }
#btnProcessAll:hover { background: #059669; }
#btnProcessAll:pressed { background: #047857; }
#btnProcessAll:disabled { background: #e2e8f0; color: #94a3b8; }
#btnClearAll { background: #fee2e2; color: #dc2626; border: 1px solid #fecaca; min-width: 100px; }
#btnClearAll:hover { background: #fca5a5; color: #991b1b; border: 1px solid #fca5a5; }
#btnClearAll:pressed { background: #ef4444; }
#btnClearAll:disabled { background: #f1f5f9; color: #94a3b8; }
#btnLoadFiles { background: #3b82f6; color: white; min-width: 140px; }
#btnLoadFiles:hover { background: #2563eb; }
#btnLoadFiles:pressed { background: #1d4ed8; }
#btnLoadFiles:disabled { background: #cbd5e1; color: #94a3b8; }
#btnStopLoading { background: #fee2e2; color: #dc2626; border: 1px solid #fecaca; min-width: 120px; }
#btnStopLoading:hover { background: #fca5a5; color: #991b1b; }
#btnStopLoading:pressed { background: #ef4444; }
#btnStopLoading:disabled { background: #f1f5f9; color: #94a3b8; }
#btnBatchEdit { background: #f59e0b; color: white; min-width: 140px; }
#btnBatchEdit:hover { background: #d97706; }
#btnBatchEdit:pressed { background: #b45309; }
#btnBatchEdit:disabled { background: #cbd5e1; color: #94a3b8; }
#btnFindDuplicates { background: #e0f2fe; color: #0284c7; border: 1px solid #bae6fd; min-width: 140px; }
#btnFindDuplicates:hover { background: #bae6fd; color: #0369a1; border: 1px solid #7dd3fc; }
#btnFindDuplicates:pressed { background: #0284c7; }
#btnFindDuplicates:disabled { background: #f1f5f9; color: #94a3b8; border: 1px solid #cbd5e1; }
#btnViewMode, #btnTogglePreview { background: #f1f5f9; color: #475569; border: 1px solid #cbd5e1; min-width: 100px; padding: 6px 12px; font-size: 11px; border-radius: 6px; }
#btnViewMode:hover, #btnTogglePreview:hover { background: #e2e8f0; color: #0f172a; }
#btnViewMode:pressed, #btnTogglePreview:pressed { background: #cbd5e1; }
#btnViewMode:checked, #btnTogglePreview:checked { background: #e0e7ff; color: #4338ca; border: 1px solid #c7d2fe; }
#previewPanel { background: #ffffff; border: 1px solid #e2e8f0; border-radius: 12px; }
#btnUndo, #btnRedo { background: #f3e8ff; color: #7e22ce; border: 1px solid #e9d5ff; min-width: 100px; }
#btnUndo:hover, #btnRedo:hover { background: #e9d5ff; color: #6b21a8; border: 1px solid #d8b4fe; }
#btnUndo:pressed, #btnRedo:pressed { background: #7e22ce; }
#btnUndo:disabled, #btnRedo:disabled { background: #f1f5f9; color: #94a3b8; border: 1px solid #e2e8f0; }
#btnDelete { background: #fee2e2; color: #dc2626; border: 1px solid #fecaca; min-width: 120px; }
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
QLineEdit { background: #ffffff; border: 1px solid #cbd5e1; border-radius: 6px; padding: 4px 8px; color: #0f172a; font-size: 12px; }
QLineEdit:focus { border: 1px solid #6366f1; }
QComboBox { background: #ffffff; border: 1px solid #cbd5e1; border-radius: 6px; padding: 4px 8px; color: #0f172a; font-size: 12px; min-width: 55px; }
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
#btnGlobalMute, #btnSettingsToggle { background: #f1f5f9; color: #475569; border: 1px solid #cbd5e1; border-radius: 8px; padding: 0px; font-size: 16px; }
#btnGlobalMute:hover, #btnSettingsToggle:hover { background: #e2e8f0; color: #0f172a; }
#btnGlobalMute:pressed, #btnSettingsToggle:pressed { background: #cbd5e1; }
#btnHelp { background: #f1f5f9; color: #475569; border: 1px solid #cbd5e1; border-radius: 18px; padding: 0px; font-size: 16px; font-weight: bold; }
#btnHelp:hover { background: #e2e8f0; color: #0f172a; }
#btnHelp:pressed { background: #cbd5e1; }
#btnCloseSettings, #btnClosePreview { background: #fee2e2; color: #dc2626; border: 1px solid #fecaca; border-radius: 6px; padding: 0px; font-weight: bold; font-size: 12px; }
#btnCloseSettings:hover, #btnClosePreview:hover { background: #fca5a5; color: #b91c1c; }
#btnCloseSettings:pressed, #btnClosePreview:pressed { background: #ef4444; }
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
    def apply_theme(window, theme_choice):
        app = QApplication.instance()
        if theme_choice == "System (Auto)":
            actual_theme = ThemeManager.get_system_theme()
        else:
            actual_theme = "dark" if "Dark" in theme_choice else "light"
            
        window.current_theme = actual_theme
        is_dark = (actual_theme == "dark")
        
        app.setStyleSheet(DARK_STYLESHEET if is_dark else LIGHT_STYLESHEET)
        
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
        for widget in app.allWidgets():
            widget.style().unpolish(widget)
            widget.style().polish(widget)
            widget.update()
        app.processEvents()

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
            try:
                if os.path.exists(filepath):
                    self.size_bytes = os.path.getsize(filepath)
                    if self.size_bytes >= 1024**3: self.size_formatted = f"{self.size_bytes / (1024**3):.2f} GB"
                    elif self.size_bytes >= 1024**2: self.size_formatted = f"{self.size_bytes / (1024**2):.1f} MB"
                    elif self.size_bytes >= 1024: self.size_formatted = f"{self.size_bytes / 1024:.0f} KB"
                    else: self.size_formatted = f"{self.size_bytes} B"
            except Exception: pass
            self._extract_metadata()

    def _extract_metadata(self):
        try:
            if self.media_type == 'video':
                cap = cv2.VideoCapture(self.filepath)
                if not cap.isOpened():
                    self.error_message = "Cannot open video file"; return
                self.width = int(cap.get(cv2.CAP_PROP_FRAME_WIDTH))
                self.height = int(cap.get(cv2.CAP_PROP_FRAME_HEIGHT))
                fps = cap.get(cv2.CAP_PROP_FPS)
                frame_count = cap.get(cv2.CAP_PROP_FRAME_COUNT)
                if fps > 0 and frame_count > 0: self.duration_seconds = frame_count / fps
                else: self.error_message = "Cannot determine duration"; cap.release(); return
                cap.release()
                self.duration_compact = format_duration_compact(self.duration_seconds)
                total_sec = int(round(self.duration_seconds))
                h = total_sec // 3600; m = (total_sec % 3600) // 60; s = total_sec % 60
                if h > 0: self.duration_formatted = f"{h}h {m:02d}m {s:02d}s"
                else: self.duration_formatted = f"{m}m {s:02d}s"
            elif self.media_type == 'audio':
                self.width = 0; self.height = 0; self.resolution_tag = ""
                cap = cv2.VideoCapture(self.filepath)
                duration_ok = False
                if cap.isOpened():
                    fps = cap.get(cv2.CAP_PROP_FPS)
                    frame_count = cap.get(cv2.CAP_PROP_FRAME_COUNT)
                    if fps > 0 and frame_count > 0: self.duration_seconds = frame_count / fps; duration_ok = True
                    cap.release()
                if not duration_ok and self.extension == '.wav':
                    try:
                        import wave
                        with wave.open(self.filepath, 'rb') as f:
                            frames = f.getnframes(); rate = f.getframerate()
                            if rate > 0: self.duration_seconds = frames / float(rate); duration_ok = True
                    except Exception: pass
                if not duration_ok and self.extension == '.mp3':
                    try: self.duration_seconds = os.path.getsize(self.filepath) / 24000.0; duration_ok = True
                    except Exception: pass
                if not duration_ok: self.error_message = "Cannot determine audio duration"; return
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
        except Exception as e: self.error_message = str(e)

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
                            if ext == '' or ext in valid_exts:
                                full_path = os.path.normpath(entry.path)
                                if full_path not in seen_paths:
                                    if not self._should_exclude(full_path):
                                        try:
                                            st = entry.stat(follow_symlinks=False)
                                            paths_with_stats.append((full_path, st.st_size, st.st_mtime))
                                            seen_paths.add(full_path)
                                        except Exception:
                                            pass
                except Exception:
                    pass

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

        def process_path(item):
            vpath, size, mtime = item
            cached_entry = cache.get(vpath)
            if not self.force_full and cached_entry and cached_entry.get('size') == size and cached_entry.get('mtime') == mtime:
                info = MediaInfo(vpath, self.media_type, cached_data=cached_entry)
                return info, None
            else:
                info = MediaInfo(vpath, self.media_type)
                entry_data = {
                    'size': size,
                    'mtime': mtime,
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

        new_entries = {}
        from concurrent.futures import ThreadPoolExecutor, as_completed
        
        # Use a safe worker pool for CPU/IO operations
        num_workers = min(8, os.cpu_count() or 4)
        with ThreadPoolExecutor(max_workers=num_workers) as executor:
            futures = {executor.submit(process_path, item): idx for idx, item in enumerate(paths_with_stats)}
            for idx, future in enumerate(as_completed(futures)):
                if self.isInterruptionRequested():
                    executor.shutdown(wait=False, cancel_futures=True)
                    self.scan_complete.emit(idx)
                    return
                try:
                    info, entry_data = future.result()
                    if entry_data:
                        new_entries[info.filepath] = entry_data
                    self.file_found.emit(info)
                    self.progress.emit(idx + 1, total)
                except Exception:
                    pass

        deleted_paths = []
        for cached_path in cache:
            is_under_scanned = False
            for d in self.directories:
                try:
                    rel = os.path.relpath(cached_path, d)
                    if not rel.startswith('..') and not os.path.isabs(rel):
                        is_under_scanned = True
                        break
                except ValueError:
                    pass
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
        file_path, _ = QFileDialog.getOpenFileName(
            self, 
            "Select Application Executable", 
            "C:\\Program Files", 
            "Executable Files (*.exe)"
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
        rating = self.rating_combo.currentText() if self.apply_rating.isChecked() else None
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
        
        base_dir = ""
        if media_infos:
            base_dir = os.path.dirname(media_infos[0].filepath)
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
        
        meta = get_file_deep_metadata(filepath, custom_ffprobe_path)
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
        scroll_widget = QWidget()
        scroll_widget.setStyleSheet("background: transparent;")
        scroll_layout = QVBoxLayout(scroll_widget)
        scroll_layout.setContentsMargins(0, 0, 0, 0)
        scroll_layout.setSpacing(12)
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
            scroll_layout.addWidget(gen_group)
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
                scroll_layout.addWidget(v_group)
            if meta['audio']:
                a = meta['audio']
                a_group = QGroupBox("🎵 Audio Stream")
                a_layout = QFormLayout(a_group)
                a_layout.addRow(self._make_label("Codec:", sub_text_color), self._make_value(a['codec'], text_color))
                a_layout.addRow(self._make_label("Channels:", sub_text_color), self._make_value(a['channel_layout'], text_color))
                if a['sample_rate_hz'] > 0: a_layout.addRow(self._make_label("Sample Rate:", sub_text_color), self._make_value(f"{a['sample_rate_hz'] / 1000:.1f} kHz", text_color))
                if a['bitrate_kbps'] > 0: a_layout.addRow(self._make_label("Bitrate:", sub_text_color), self._make_value(f"{a['bitrate_kbps']} kbps", text_color))
                scroll_layout.addWidget(a_group)
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
                try:
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
                        cap.release()
                except Exception: pass
            scroll_layout.addWidget(fallback_group)
        scroll.setWidget(scroll_widget)
        layout.addWidget(scroll, 1)
        buttons = QDialogButtonBox(QDialogButtonBox.StandardButton.Ok)
        buttons.accepted.connect(self.accept)
        layout.addWidget(buttons)
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
        
        self.player.mediaStatusChanged.connect(self._on_media_status_changed)
        
        self.start_times = []
        self.current_part_index = 0
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
        self.current_part_index = 0
        
        D = info.duration_seconds
        if D < 2.0:
            self.start_times = [0.0] * 5
        else:
            self.start_times = [random.uniform(0.0, D - 2.0) for _ in range(5)]
            
        self.update_theme()
        self.adjust_layout()
        
        # Audio setting based on global volume button
        is_globally_muted = getattr(self.parent_window, 'global_mute', False)
        self.audio_output.setMuted(is_globally_muted)
        
        self.player.setSource(QUrl.fromLocalFile(info.filepath))
        
        self.show()
        self.raise_()
        
        self.mouse_check_timer = QTimer(self)
        self.mouse_check_timer.timeout.connect(self._check_mouse_position)
        self.mouse_check_timer.start(50)

    def hide_preview(self):
        self.segment_timer.stop()
        if hasattr(self, 'mouse_check_timer'):
            self.mouse_check_timer.stop()
        self.player.stop()
        self.player.setSource(QUrl())
        self.hide()

    def _check_mouse_position(self):
        if not self.target_global_rect.contains(QCursor.pos()):
            self.hide_preview()

    def _on_media_status_changed(self, status):
        if not self.has_started and status in (QMediaPlayer.MediaStatus.LoadedMedia, QMediaPlayer.MediaStatus.BufferedMedia):
            self.has_started = True
            self.player.setPosition(int(self.start_times[0] * 1000))
            self.player.play()
            self.segment_timer.start(2000)

    def _on_segment_timeout(self):
        if not self.has_started or not self.isVisible():
            return
        self.current_part_index = (self.current_part_index + 1) % 5
        self.player.setPosition(int(self.start_times[self.current_part_index] * 1000))
        self.player.play()

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
        self.setWindowTitle(f"MediaFlow Image Viewer — {os.path.basename(filepath)}")
        self.resize(800, 600)
        self.setWindowFlags(Qt.WindowType.Window)
        
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

class NativeAudioPlayerWindow(QMainWindow):
    def __init__(self, filepath, parent=None):
        super().__init__(parent)
        self.setWindowTitle(f"MediaFlow Audio Player — {os.path.basename(filepath)}")
        self.resize(450, 160)
        self.setWindowFlags(Qt.WindowType.Window)
        
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
        self._is_slider_pressed = False
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
        is_dark = getattr(parent_window.parent_window, 'current_theme', 'dark') == 'dark' if parent_window.parent_window else True
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
        
        global_mute = getattr(parent_window.parent_window, 'global_mute', False) if parent_window.parent_window else False
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
        is_dark = getattr(self.parent_window.parent_window, 'current_theme', 'dark') == 'dark' if self.parent_window.parent_window else True
        self.btn_mute.setIcon(get_vector_icon('mute' if not is_muted else 'unmute', is_dark))

    def _on_volume_changed(self, value):
        self.audio_output.setVolume(value / 100.0)
        if value > 0 and self.audio_output.isMuted():
            self._toggle_mute()

    def _on_player_state_changed(self, state):
        is_dark = getattr(self.parent_window.parent_window, 'current_theme', 'dark') == 'dark' if self.parent_window.parent_window else True
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
        for sp in self.sub_players:
            sp.player.stop()
        super().closeEvent(event)


# ─── Main Window Tab ─────────────────────────────────────────────────────────────

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
    NUM_COLS       = 10
    HEADERS = ["Preview", "Status", "File Name", "Size", "Resolution", "Duration", "Name", "Rating", "Tags", "New Name Preview"]

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
        self._exclude_timer = QTimer()
        self._exclude_timer.setSingleShot(True)
        self._exclude_timer.setInterval(500)
        self._exclude_timer.timeout.connect(self._apply_exclude_and_scan)
        
        self.hover_timer = QTimer(self)
        self.hover_timer.setSingleShot(True)
        self.hover_timer.setInterval(1500)
        self.hover_timer.timeout.connect(self._on_hover_timeout)
        self._hovered_info = None
        self._hovered_global_rect = None
        self._hovered_grid_info = None
        self._dismissed_info = None
        
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
        row1_layout.addWidget(self.btn_load)
        row1_layout.addWidget(self.btn_stop)
        row1_layout.addWidget(self.btn_clear)
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
        row1_layout.addWidget(self.btn_view_mode)
        row1_layout.addWidget(self.btn_toggle_preview)
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
        self.search_input = QLineEdit()
        self.search_input.setPlaceholderText("Filter by filename, name, or rating...")
        self.search_input.textChanged.connect(self._on_filter_changed)
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
        root_layout.addWidget(filter_panel)
        self.table = QTableWidget()
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
        self.grid_view.setIconSize(QSize(120, 68))
        self.grid_view.setGridSize(QSize(150, 120))
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
        self.content_layout.addWidget(self.preview_panel)
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
        bottom_row2 = QHBoxLayout()
        bottom_row2.setContentsMargins(0, 0, 0, 0)
        bottom_row2.setSpacing(12)
        self.btn_find_dupes = QPushButton("Find Duplicates")
        self.btn_find_dupes.setObjectName("btnFindDuplicates")
        self.btn_find_dupes.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_find_dupes.setEnabled(False)
        self.btn_find_dupes.setIconSize(QSize(16, 16))
        self.dupe_menu = QMenu(self)
        self.header_menu = QMenu(self)
        action_exact = QAction("Exact Duplicates (MD5)", self)
        action_exact.triggered.connect(self._find_exact_duplicates)
        self.dupe_menu.addAction(action_exact)
        action_visual = QAction("Visual Duplicates (pHash)", self)
        action_visual.triggered.connect(self._find_visual_duplicates)
        self.dupe_menu.addAction(action_visual)
        self.btn_find_dupes.setMenu(self.dupe_menu)
        self.btn_batch_edit = QPushButton("Batch Edit Selected")
        self.btn_batch_edit.setObjectName("btnBatchEdit")
        self.btn_batch_edit.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_batch_edit.clicked.connect(self._on_batch_edit)
        self.btn_batch_edit.setEnabled(False)
        self.btn_batch_edit.setIconSize(QSize(16, 16))
        self.btn_relocate = QPushButton("Relocate Files")
        self.btn_relocate.setObjectName("btnBatchEdit")
        self.btn_relocate.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_relocate.clicked.connect(self._on_smart_relocate)
        self.btn_relocate.setEnabled(False)
        self.btn_relocate.setIconSize(QSize(16, 16))
        self.btn_delete = QPushButton("Delete Selected")
        self.btn_delete.setObjectName("btnDelete")
        self.btn_delete.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_delete.clicked.connect(self._on_delete_selected)
        self.btn_delete.setEnabled(False)
        self.btn_delete.setIconSize(QSize(16, 16))
        self.btn_process = QPushButton("Process All — Rename Files")
        self.btn_process.setObjectName("btnProcessAll")
        self.btn_process.setCursor(Qt.CursorShape.PointingHandCursor)
        self.btn_process.setEnabled(False)
        self.btn_process.clicked.connect(self._on_process_all)
        self.btn_process.setIconSize(QSize(18, 18))
        bottom_row2.addWidget(self.btn_find_dupes)
        bottom_row2.addWidget(self.btn_batch_edit)
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

    def _on_filter_changed(self, text: str):
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
        self._update_stats()
        self._load_visible_widgets()

    def _on_save_search_clicked(self):
        query = self.search_input.text().strip()
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

    def _start_scan(self, folders: list[str], force_full: bool = False):
        self._on_clear()
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

    def _on_clear(self):
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

    def get_state_dict(self) -> dict:
        state = {
            'exclude_patterns': self._exclude_patterns,
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
        placeholder_pix = QPixmap(120, 68)
        placeholder_pix.fill(QColor("#1e1b4b"))
        painter = QPainter(placeholder_pix)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing)
        painter.setFont(QFont("Segoe UI", 20))
        painter.setPen(QColor("#a78bfa"))
        emoji = "🎬" if info.media_type == 'video' else ("🎵" if info.media_type == 'audio' else ("📄" if info.media_type == 'pdf' else "🖼️"))
        painter.drawText(QRect(0, 0, 120, 68), Qt.AlignmentFlag.AlignCenter, emoji)
        painter.end()
        grid_item.setIcon(QIcon(placeholder_pix))
        info.grid_item = grid_item
        search_text = self.search_input.text().lower().strip()
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
            thumb_label.setText("🎬" if info.media_type == 'video' else ("🎵" if info.media_type == 'audio' else ("📄" if info.media_type == 'pdf' else "🖼️")))
            thumb_label.setFixedSize(120, 68)
            QTimer.singleShot(0, lambda r=row, i=info, l=thumb_label: self._generate_thumbnail_async(r, i, l))
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
        
        meta_font = QFont("Segoe UI", 9, QFont.Weight.Light)
        bold_meta_font = QFont("Segoe UI", 9, QFont.Weight.Bold)
        
        fname_item = NumericTableWidgetItem(info.filename)
        fname_item.setData(Qt.ItemDataRole.UserRole, info)
        fname_item.setToolTip(info.filepath)
        fname_item.setFont(QFont("Segoe UI", 10, QFont.Weight.Bold))
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
        self.table.setRowHeight(row, 75)
        self._updating_table = False
        self._update_row_preview(row)

    def _generate_thumbnail_async(self, row: int, info: MediaInfo, label: QLabel):
        if row >= self.table.rowCount(): return
        pixmap = generate_thumbnail(info.filepath, info.media_type)
        if pixmap:
            current_widget = self.table.cellWidget(row, self.COL_THUMB)
            if current_widget is label:
                label.setPixmap(pixmap.scaled(120, 68, Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation))
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
        self._load_visible_widgets()

    def _ensure_widgets_for_row(self, row: int):
        info = self._get_row_info(row)
        if not info or not info.is_valid: return
        
        # Artist widget
        if not self.table.cellWidget(row, self.COL_ARTIST):
            artist_item = self.table.item(row, self.COL_ARTIST)
            val = artist_item.text().strip() if artist_item else ""
            if not val:
                val, _ = parse_naming_format(info.filename)
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
                _, parsed_rating = parse_naming_format(info.filename)
                val = parsed_rating or "—"
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
        for row in range(self.table.rowCount()):
            if (self.table.cellWidget(row, self.COL_ARTIST) is sender or self.table.cellWidget(row, self.COL_RATING) is sender):
                if row in self.filtered_rows or not self.filtered_rows: self._update_row_preview(row)
                break

    def _on_artist_editing_finished(self):
        sender = self.sender()
        if not sender: return
        for row in range(self.table.rowCount()):
            if self.table.cellWidget(row, self.COL_ARTIST) is sender:
                artist_item = self.table.item(row, self.COL_ARTIST)
                if artist_item:
                    was_sorting = self.table.isSortingEnabled()
                    self.table.setSortingEnabled(False)
                    artist_item.setText(sender.text().strip())
                    self.table.setSortingEnabled(was_sorting)
                break

    def _on_tags_edited(self):
        sender = self.sender()
        if not sender: return
        for row in range(self.table.rowCount()):
            if self.table.cellWidget(row, self.COL_TAGS) is sender:
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
                if main_win and hasattr(main_win, '_save_state'):
                    main_win._save_state()
                break

    def _get_templated_name(self, artist: str, rating: str, info) -> str:
        main_win = self.window()
        if not main_win:
            return ""
        fields_ordered = getattr(main_win, 'naming_all_fields_ordered', ["Name", "Duration", "Resolution", "Rating", "Tags"])
        fields_checked = getattr(main_win, 'naming_fields', ["name", "duration", "resolution", "rating", "tags"])
        separator = getattr(main_win, 'naming_separator', ' ')
        parts = []
        for f_name in fields_ordered:
            config_key = {"Name": "name", "Duration": "duration", "Resolution": "resolution", "Rating": "rating", "Tags": "tags"}[f_name]
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
        return separator.join(parts)

    def _is_naming_data_complete(self, artist: str, rating: str) -> bool:
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
        return True

    def _update_row_preview(self, row: int):
        info = self._get_row_info(row)
        if not info or not info.is_valid: return
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
        
        is_complete = self._is_naming_data_complete(artist, rating_text)
        new_name = self._get_templated_name(artist, rating_text, info) if is_complete else ""
        
        current_display_name = self.table.item(row, self.COL_FILENAME).text().strip() if self.table.item(row, self.COL_FILENAME) else ""
        target_display = new_name + (info.extension if keep_ext else "") if new_name else ""
        
        is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark'
        if not is_complete or not new_name or target_display == current_display_name:
            preview_item.setText("—")
            preview_item.setFont(QFont("Segoe UI", 10, QFont.Weight.Normal))
            preview_item.setForeground(QColor("#7c7c9a") if is_dark else QColor("#64748b"))
            if hasattr(info, 'grid_item') and info.grid_item: info.grid_item.setToolTip("")
        else:
            preview_item.setText(f"➜  {target_display}")
            preview_item.setFont(QFont("Segoe UI", 10, QFont.Weight.Bold))
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

        success_count = 0
        error_count = 0
        
        was_sorting = self.table.isSortingEnabled()
        self.table.setSortingEnabled(False)
        self._updating_table = True
        
        for info in target_infos:
            src = info.filepath
            tags = getattr(info, 'tags', [])
            dest_dir = parse_destination_template(template, info, tags)
            
            try:
                os.makedirs(dest_dir, exist_ok=True)
                
                dest_file = os.path.join(dest_dir, info.filename)
                if os.path.exists(dest_file) and os.path.normpath(src) != os.path.normpath(dest_file):
                    base, ext = os.path.splitext(info.filename)
                    counter = 1
                    while os.path.exists(dest_file):
                        dest_file = os.path.join(dest_dir, f"{base}_{counter}{ext}")
                        counter += 1
                
                shutil.move(src, dest_file)
                
                # Update info and matching table items
                info.filepath = dest_file
                info.filename = os.path.basename(dest_file)
                
                row_idx = -1
                for r in range(self.table.rowCount()):
                    if self._get_row_info(r) is info:
                        row_idx = r
                        break
                
                if row_idx >= 0:
                    fname_item = self.table.item(row_idx, self.COL_FILENAME)
                    if fname_item:
                        fname_item.setText(info.filename)
                        fname_item.setToolTip(dest_file)
                    self._update_row_preview(row_idx)
                    self._add_to_history(src, dest_file, row_idx)
                
                success_count += 1
                
            except Exception as e:
                error_count += 1
                print(f"Failed to move {info.filename}: {e}")

        self._updating_table = False
        self.table.setSortingEnabled(was_sorting)
        
        self.table.viewport().update()
        self.btn_undo.setEnabled(len(self._rename_history) > 0)
        
        QMessageBox.information(
            self, "Relocation Complete", 
            f"Moved {success_count} files successfully.\nFailed: {error_count} files."
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
                main_win._native_players = [p for p in main_win._native_players if p.isVisible()]
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
        main_win = self.window()
        if main_win:
            if not hasattr(main_win, '_native_players'):
                main_win._native_players = []
            main_win._native_players = [p for p in main_win._native_players if p.isVisible()]
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
            
        play_action = QAction("▶️  Play / Open", self)
        play_action.triggered.connect(lambda: self._play_video(row))
        menu.addAction(play_action)

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
        copy_path = QAction("📋  Copy File Path", self)
        copy_path.triggered.connect(lambda: self._copy_path_for_row(row))
        menu.addAction(copy_path)
        remove_action = QAction("✕  Remove From List", self)
        remove_action.triggered.connect(lambda: self._remove_row_from_list(row))
        menu.addAction(remove_action)
        delete_action = QAction("🗑️  Delete from Disk...", self)
        delete_action.triggered.connect(lambda: self._on_delete_selected(row))
        menu.addAction(delete_action)
        if info.is_valid:
            menu.addSeparator()
            rating_menu = menu.addMenu("⭐  Set Rating")
            for r in ["—"] + [str(i) for i in range(1, 11)]:
                action = QAction(r if r != "—" else "Clear", self)
                action.triggered.connect(lambda checked, rr=r: self._set_rating_for_row(row, rr))
                rating_menu.addAction(action)
        menu.exec(global_pos)

    def _show_detailed_info(self, row: int):
        info = self._get_row_info(row)
        if not info: return
        main_win = self.window()
        ffprobe_path = getattr(main_win, 'ffprobe_path', None)
        dialog = DetailedInfoDialog(info.filepath, ffprobe_path, self)
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
            main_win._native_players = [p for p in main_win._native_players if p.isVisible()]
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
                filepath = os.path.normpath(info.filepath)
                subprocess.run(f'explorer /select,"{filepath}"')
            elif sys.platform == "darwin": subprocess.run(["open", folder])
            else: subprocess.run(["xdg-open", folder])

    def _copy_path_for_row(self, row: int):
        info = self._get_row_info(row)
        if info:
            QApplication.clipboard().setText(info.filepath)
            self.status_label.setText("📋 Path copied to clipboard")
            QTimer.singleShot(2000, lambda: self.status_label.setText("Ready"))

    def _remove_row_from_list(self, row: int):
        info = self._get_row_info(row)
        if info and info.filepath in [v.filepath for v in self.media_infos]:
            self.media_infos = [v for v in self.media_infos if v.filepath != info.filepath]
            self.table.removeRow(row)
            if hasattr(info, 'grid_item') and info.grid_item:
                row_item = self.grid_view.row(info.grid_item)
                if row_item >= 0: self.grid_view.takeItem(row_item)
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
        new_name_no_ext = os.path.splitext(new_text)[0]
        dst = os.path.join(os.path.dirname(src), new_name_no_ext + info.extension)
        if os.path.exists(dst) and os.path.normpath(src) != os.path.normpath(dst):
            base = new_name_no_ext
            ext = info.extension
            counter = 1
            while os.path.exists(dst):
                dst = os.path.join(os.path.dirname(src), f"{base}_{counter}{ext}")
                counter += 1
        was_sorting = self.table.isSortingEnabled()
        self.table.setSortingEnabled(False)
        try:
            os.rename(src, dst)
            info.filepath = dst
            info.filename = os.path.basename(dst)
            item.setToolTip(dst)
            self._updating_table = True
            item.setText(info.filename)
            self._updating_table = False
            if hasattr(info, 'grid_item') and info.grid_item: info.grid_item.setText(info.filename)
            self._add_to_history(src, dst, row)
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
            if self._is_naming_data_complete(artist, rating):
                new_name = self._get_templated_name(artist, rating, info)
                current_display_name = self.table.item(row, self.COL_FILENAME).text().strip() if self.table.item(row, self.COL_FILENAME) else ""
                target_display = new_name + (info.extension if keep_ext else "") if new_name else ""
                if target_display and target_display != current_display_name:
                    ready_rows.append((row, info, target_display))
        if not ready_rows:
            QMessageBox.information(self, "Nothing to Process", "No files are ready to rename."); return
        reply = QMessageBox.question(self, "Confirm Rename", f"This will rename {len(ready_rows)} file{'s' if len(ready_rows) != 1 else ''}.\n\nThis action cannot be undone. Continue?", QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No, QMessageBox.StandardButton.No)
        if reply != QMessageBox.StandardButton.Yes: return
        success_count = 0
        error_count = 0
        errors = []
        was_sorting = self.table.isSortingEnabled()
        self.table.setSortingEnabled(False)
        try:
            for row, info, target_display in ready_rows:
                src = info.filepath
                dst = os.path.join(os.path.dirname(src), target_display)
                if os.path.exists(dst) and os.path.normpath(src) != os.path.normpath(dst):
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
                    self._add_to_history(src, dst, row)
                    success_count += 1
                except Exception as e:
                    error_count += 1
                    errors.append(f"{info.filename}: {e}")
                    status_item = self.table.item(row, self.COL_STATUS)
                    status_item.setText("✕ Error")
                    status_item.setForeground(QColor("#f87171"))
                    status_item.setToolTip(str(e))
        finally:
            self.table.setSortingEnabled(was_sorting)
        msg = f"✅ Successfully renamed {success_count} file{'s' if success_count != 1 else ''}."
        if error_count > 0:
            msg += f"\n\n❌ {error_count} error{'s' if error_count != 1 else ''}:\n"
            msg += "\n".join(errors[:10])
            if len(errors) > 10: msg += f"\n… and {len(errors) - 10} more."
        self.status_label.setText(f"Done — {success_count} renamed, {error_count} errors.")
        self._update_stats()
        self.btn_undo.setEnabled(len(self._rename_history) > 0)
        QMessageBox.information(self, "Rename Complete", msg)

    def _add_to_history(self, src: str, dst: str, row: int, clear_redo=True):
        self._rename_history.append({'timestamp': datetime.now().isoformat(), 'src': src, 'dst': dst, 'row': row, 'filename': os.path.basename(dst)})
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
            try:
                shutil.move(dst, src)
                row = last['row']
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
                        self._updating_table = False
                        if hasattr(info, 'grid_item') and info.grid_item: info.grid_item.setText(info.filename)
                self.status_label.setText(f"↩️ Undone: {os.path.basename(dst)}")
                self._update_stats()
                self._redo_history.append(last)
                self.btn_redo.setEnabled(True)
            except Exception as e:
                QMessageBox.warning(self, "Undo Failed", f"Cannot undo rename:\n{e}")
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
            try:
                shutil.move(src, dst)
                row = last['row']
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
                        self._updating_table = False
                        if hasattr(info, 'grid_item') and info.grid_item: info.grid_item.setText(info.filename)
                self.status_label.setText(f"🔁 Redone: {os.path.basename(dst)}")
                self._update_stats()
                self._add_to_history(src, dst, row, clear_redo=False)
            except Exception as e:
                QMessageBox.warning(self, "Redo Failed", f"Cannot redo rename:\n{e}")
                self._redo_history.append(last)
        else:
            QMessageBox.warning(self, "Redo Unavailable", "Cannot redo: file has been deleted, moved, or renamed again.")
        self.btn_redo.setEnabled(len(self._redo_history) > 0)
        self.btn_undo.setEnabled(len(self._rename_history) > 0)

    def _restore_file_data(self):
        was_sorting = self.table.isSortingEnabled()
        self.table.setSortingEnabled(False)
        self._updating_table = True
        for row in range(self.table.rowCount()):
            info = self._get_row_info(row)
            if not info: continue
            data = self._saved_file_data.get(os.path.normpath(info.filepath))
            if not data: continue
            
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
                
            self._update_row_preview(row)
        self._updating_table = False
        self.table.setSortingEnabled(was_sorting)

    def _find_exact_duplicates(self): self._find_duplicates_logic(mode='exact')
    def _find_visual_duplicates(self): self._find_duplicates_logic(mode='visual')

    def _find_duplicates_logic(self, mode='exact'):
        if mode == 'visual' and self.media_type == 'audio':
            QMessageBox.warning(self, "Unsupported", "Visual duplicates scanning is not supported for Audio files."); return
        self._clear_highlights()
        valid_infos = [(row, info) for row, info in enumerate(self.media_infos) if info.is_valid]
        if not valid_infos:
            QMessageBox.information(self, "No Files", "No valid files loaded to scan for duplicates."); return
        self.progress_bar.setVisible(True)
        self.progress_bar.setMaximum(len(valid_infos))
        self.progress_bar.setValue(0)
        task_name = "MD5 exact" if mode == 'exact' else "pHash visual"
        self.progress_bar.setFormat(f"Scanning duplicates ({task_name}): %v/%m…")
        self.status_label.setText(f"Scanning duplicates ({task_name})…")
        hashes = {}
        from PyQt6.QtCore import QCoreApplication
        for idx, (row, info) in enumerate(valid_infos):
            if mode == 'exact': h = calculate_file_hash(info.filepath)
            else: h = calculate_perceptual_hash(info.filepath, self.media_type)
            if h: hashes[row] = h
            self.progress_bar.setValue(idx + 1)
            QCoreApplication.processEvents()
        self.progress_bar.setVisible(False)
        self.status_label.setText("Processing duplicates list…")
        QCoreApplication.processEvents()
        groups = []
        if mode == 'exact':
            hash_to_rows = {}
            for r, h in hashes.items(): hash_to_rows.setdefault(h, []).append(r)
            for h, grp in hash_to_rows.items():
                if len(grp) > 1: groups.append(grp)
        else:
            visited = set()
            rows_list = list(hashes.keys())
            for i in range(len(rows_list)):
                r1 = rows_list[i]
                if r1 in visited: continue
                h1 = hashes[r1]
                current_group = [r1]
                for j in range(i + 1, len(rows_list)):
                    r2 = rows_list[j]
                    if r2 in visited: continue
                    h2 = hashes[r2]
                    if hamming_distance(h1, h2) <= 10: current_group.append(r2)
                if len(current_group) > 1: groups.append(current_group)
                for r in current_group: visited.add(r)
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
            for row in grp:
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
        self._update_preview_pane()

    def _close_preview_pane(self): self._toggle_preview(False)

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

    def _update_preview_pane(self):
        if not self.btn_toggle_preview.isChecked():
            if self.player.playbackState() == QMediaPlayer.PlaybackState.PlayingState: self.player.stop()
            return
        selected_rows = []
        for rng in self.table.selectedRanges():
            for row in range(rng.topRow(), rng.bottomRow() + 1): selected_rows.append(row)
        selected_rows = list(set(selected_rows))
        if len(selected_rows) != 1:
            self.player.stop()
            self.preview_stack.setCurrentIndex(2)
            self.preview_controls.setVisible(False)
            if len(selected_rows) > 1: self.no_preview_label.setText("Multiple files selected\nSelect a single file to preview")
            else: self.no_preview_label.setText("Select a file to preview")
            self.preview_title.setText("Preview")
            return
        row = selected_rows[0]
        info = self._get_row_info(row)
        if not info or not info.is_valid:
            self.player.stop()
            self.preview_stack.setCurrentIndex(2)
            self.preview_controls.setVisible(False)
            self.no_preview_label.setText("No preview available\nfor invalid files")
            self.preview_title.setText(info.filename if info else "Preview")
            return
        self.preview_title.setText(info.filename)
        filepath = info.filepath
        if info.media_type == 'image':
            self.player.stop()
            self.preview_controls.setVisible(False)
            self.preview_stack.setCurrentIndex(0)
            pixmap = QPixmap(filepath)
            if not pixmap.isNull():
                scaled_pix = pixmap.scaled(290, 220, Qt.AspectRatioMode.KeepAspectRatio, Qt.TransformationMode.SmoothTransformation)
                self.preview_image.setPixmap(scaled_pix)
            else: self.preview_image.setText("Failed to load image")
        elif info.media_type == 'video':
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
            painter = QPainter(placeholder_pix)
            painter.setRenderHint(QPainter.RenderHint.Antialiasing)
            painter.setFont(QFont("Segoe UI", 48))
            painter.setPen(QColor("#a78bfa"))
            painter.drawText(QRect(0, 0, 290, 220), Qt.AlignmentFlag.AlignCenter, "🎵")
            painter.end()
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
            self.player.stop()
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
        has_valid = False
        for rng in selected_ranges:
            for row in range(rng.topRow(), rng.bottomRow() + 1):
                info = self._get_row_info(row)
                if info and info.is_valid: has_valid = True; break
            if has_valid: break
        self.btn_batch_edit.setEnabled(len(selected_ranges) > 0 and has_valid)
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

        # Enable or disable process renaming button dynamically based on whether renaming targets are ready
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
            if self._is_naming_data_complete(artist, rating):
                new_name = self._get_templated_name(artist, rating, info)
                current_display_name = self.table.item(row, self.COL_FILENAME).text().strip() if self.table.item(row, self.COL_FILENAME) else ""
                target_display = new_name + (info.extension if keep_ext else "") if new_name else ""
                if target_display and target_display != current_display_name:
                    ready_count += 1
        if hasattr(self, 'btn_process') and self.btn_process:
            self.btn_process.setEnabled(ready_count > 0)

    def _update_row_colors(self):
        is_dark = getattr(self.window(), 'current_theme', 'dark') == 'dark'
        meta_font = QFont("Segoe UI", 9, QFont.Weight.Light)
        bold_meta_font = QFont("Segoe UI", 9, QFont.Weight.Bold)
        for row in range(self.table.rowCount()):
            fname_item = self.table.item(row, self.COL_FILENAME)
            if fname_item:
                fname_item.setFont(QFont("Segoe UI", 10, QFont.Weight.Bold))
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
                    preview_item.setFont(QFont("Segoe UI", 10, QFont.Weight.Bold))
                    preview_item.setForeground(QColor("#34d399") if is_dark else QColor("#059669"))
                else:
                    preview_item.setFont(QFont("Segoe UI", 10, QFont.Weight.Normal))
                    preview_item.setForeground(QColor("#7c7c9a") if is_dark else QColor("#64748b"))

# ─── Main App Window ─────────────────────────────────────────────────────────────

class MediaFlowWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("MediaFlow — Multimedia Manager & Renamer")
        self.setMinimumSize(1300, 810)
        self.resize(1120, 630)
        self._settings_visible = False
        self.setAcceptDrops(True)
        self.global_mute = False
        self.ffprobe_path = ""
        self.current_theme = "dark"
        self.naming_separator = ' '
        self.naming_fields = ["name", "duration", "resolution", "rating"]
        self.naming_all_fields_ordered = ["Name", "Duration", "Resolution", "Rating"]
        self.naming_keep_extension = True
        self.open_with_apps = []
        self._build_ui()

        self.hover_overlay = HoverPreviewOverlay(self)
        self._setup_shortcuts()
        self._load_state()
        if not os.path.exists(CONFIG_FILE): self._center_on_screen()

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
            config_key = {"Name": "name", "Duration": "duration", "Resolution": "resolution", "Rating": "rating", "Tags": "tags"}[f_name]
            is_checked = config_key in self.naming_fields
            item.setCheckState(Qt.CheckState.Checked if is_checked else Qt.CheckState.Unchecked)
            self.template_list.addItem(item)
        self.template_list.model().blockSignals(False)
        self.template_list.blockSignals(False)
        
        self.template_list.itemChanged.connect(self._on_naming_template_changed)
        self.template_list.model().dataChanged.connect(lambda topLeft, bottomRight, roles=None: self._on_naming_template_changed())
        self.template_list.model().layoutChanged.connect(self._on_naming_template_changed)
        self.template_list.model().rowsMoved.connect(lambda parent, start, end, dest, row: self._on_naming_template_changed())
        self.template_list.model().rowsInserted.connect(lambda parent, start, end: self._on_naming_template_changed())
        self.template_list.model().rowsRemoved.connect(lambda parent, start, end: self._on_naming_template_changed())
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
        videos_sec_layout.addWidget(self.videos_list_widget)
        videos_sec_layout.addWidget(self.btn_add_video_folder)
        videos_sec_layout.addWidget(self.btn_remove_video_folder)
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
        images_sec_layout.addWidget(self.images_list_widget)
        images_sec_layout.addWidget(self.btn_add_image_folder)
        images_sec_layout.addWidget(self.btn_remove_image_folder)
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
        audio_sec_layout.addWidget(self.audio_list_widget)
        audio_sec_layout.addWidget(self.btn_add_audio_folder)
        audio_sec_layout.addWidget(self.btn_remove_audio_folder)
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
        pdf_sec_layout.addWidget(self.pdf_list_widget)
        pdf_sec_layout.addWidget(self.btn_add_pdf_folder)
        pdf_sec_layout.addWidget(self.btn_remove_pdf_folder)
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

    def add_smart_folder(self, name: str, media_type: str, query: str):
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
        self.smart_folders_config = [f for f in self.smart_folders_config if f['name'] != name]
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
        shortcut_reload = QAction("Reload Files", self)
        shortcut_reload.setShortcut(QKeySequence("Ctrl+R"))
        shortcut_reload.triggered.connect(lambda: self.stacked_widget.currentWidget()._on_load_files())
        self.addAction(shortcut_reload)
        shortcut_undo = QAction("Undo Rename", self)
        shortcut_undo.setShortcut(QKeySequence("Ctrl+Z"))
        shortcut_undo.triggered.connect(lambda: self.stacked_widget.currentWidget()._on_undo_rename())
        self.addAction(shortcut_undo)
        shortcut_redo = QAction("Redo Rename", self)
        shortcut_redo.setShortcut(QKeySequence("Ctrl+Y"))
        shortcut_redo.triggered.connect(lambda: self.stacked_widget.currentWidget()._on_redo_rename() if hasattr(self.stacked_widget.currentWidget(), '_on_redo_rename') else None)
        self.addAction(shortcut_redo)
        shortcut_search = QAction("Focus Search", self)
        shortcut_search.setShortcut(QKeySequence("Ctrl+F"))
        shortcut_search.triggered.connect(lambda: self.stacked_widget.currentWidget().search_input.setFocus())
        self.addAction(shortcut_search)
        shortcut_delete = QAction("Delete Selected", self)
        shortcut_delete.setShortcut(QKeySequence("Delete"))
        shortcut_delete.triggered.connect(lambda: self.stacked_widget.currentWidget()._on_delete_selected())
        self.addAction(shortcut_delete)
        shortcut_refresh = QAction("Refresh", self)
        shortcut_refresh.setShortcut(QKeySequence("F5"))
        shortcut_refresh.triggered.connect(lambda: self.stacked_widget.currentWidget()._on_load_files())
        self.addAction(shortcut_refresh)

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
        all_ordered = []
        checked_fields = []
        for i in range(self.template_list.count()):
            item = self.template_list.item(i)
            text = item.text()
            all_ordered.append(text)
            if item.checkState() == Qt.CheckState.Checked:
                config_key = {"Name": "name", "Duration": "duration", "Resolution": "resolution", "Rating": "rating", "Tags": "tags"}[text]
                checked_fields.append(config_key)
        self.naming_all_fields_ordered = all_ordered
        self.naming_fields = checked_fields
        self.naming_separator = self.separator_input.text()
        self.naming_keep_extension = self.keep_extension_checkbox.isChecked()
        self._update_template_preview()
        self._save_state()
        self._refresh_all_tab_previews()

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
                else: geo = self._normal_geometry if hasattr(self, '_normal_geometry') else {'x': self.x(), 'y': self.y(), 'width': 1120, 'height': 630}
            else: geo = {'x': self.x(), 'y': self.y(), 'width': self.width(), 'height': self.height()}
            state = {
                'geometry': geo, 'maximized': is_maximized,
                'video_folders': video_folders, 'image_folders': image_folders, 'audio_folders': audio_folders, 'pdf_folders': pdf_folders,
                'default_video_player': self.video_tab.default_player, 'default_image_opener': self.image_tab.default_player, 'default_audio_player': self.audio_tab.default_player, 'default_pdf_opener': self.pdf_tab.default_player,
                'ffprobe_path': getattr(self, 'ffprobe_path', ''),
                'video_tab': self.video_tab.get_state_dict(), 'image_tab': self.image_tab.get_state_dict(), 'audio_tab': self.audio_tab.get_state_dict(), 'pdf_tab': self.pdf_tab.get_state_dict(),
                'smart_folders': getattr(self, 'smart_folders_config', []),
                'theme': self.theme_combo.currentText(),
                'naming_separator': self.naming_separator,
                'naming_fields': self.naming_fields,
                'naming_all_fields_ordered': self.naming_all_fields_ordered,
                'naming_keep_extension': self.naming_keep_extension,
                'open_with_apps': getattr(self, 'open_with_apps', [])
            }
            with open(CONFIG_FILE, 'w', encoding='utf-8') as f: json.dump(state, f, indent=2, ensure_ascii=False)
        except Exception: pass

    def _load_state(self):
        try:
            if not os.path.exists(CONFIG_FILE):
                ThemeManager.apply_theme(self, "System (Auto)")
                return
            with open(CONFIG_FILE, 'r', encoding='utf-8') as f: state = json.load(f)
            
            theme = state.get('theme', 'System (Auto)')
            self.theme_combo.blockSignals(True)
            self.theme_combo.setCurrentText(theme)
            self.theme_combo.blockSignals(False)
            ThemeManager.apply_theme(self, theme)

            # Restore Custom Naming Template configuration
            self.naming_separator = state.get('naming_separator', ' ')
            self.naming_fields = state.get('naming_fields', ["name", "duration", "resolution", "rating", "tags"])
            self.naming_all_fields_ordered = state.get('naming_all_fields_ordered', ["Name", "Duration", "Resolution", "Rating", "Tags"])
            if "Tags" not in self.naming_all_fields_ordered:
                self.naming_all_fields_ordered.append("Tags")
            self.naming_keep_extension = state.get('naming_keep_extension', True)
            self.open_with_apps = state.get('open_with_apps', [])
            
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
                config_key = {"Name": "name", "Duration": "duration", "Resolution": "resolution", "Rating": "rating", "Tags": "tags"}[f_name]
                is_checked = config_key in self.naming_fields
                item.setCheckState(Qt.CheckState.Checked if is_checked else Qt.CheckState.Unchecked)
                self.template_list.addItem(item)
            self.template_list.model().blockSignals(False)
            self.template_list.blockSignals(False)
            
            self._update_template_preview()

            geo = state.get('geometry', {})
            if geo:
                self.setGeometry(geo['x'], geo['y'], geo['width'], geo['height'])
                self._normal_geometry = geo
            if state.get('maximized', False): self.showMaximized()
            elif not geo: self._center_on_screen()
            video_folders = state.get('video_folders', [])
            self.videos_list_widget.clear()
            self.videos_list_widget.addItems(video_folders)
            self.video_tab.set_directories(video_folders)
            image_folders = state.get('image_folders', [])
            self.images_list_widget.clear()
            self.images_list_widget.addItems(image_folders)
            self.image_tab.set_directories(image_folders)
            audio_folders = state.get('audio_folders', [])
            self.audio_list_widget.clear()
            self.audio_list_widget.addItems(audio_folders)
            self.audio_tab.set_directories(audio_folders)
            pdf_folders = state.get('pdf_folders', [])
            self.pdf_list_widget.clear()
            self.pdf_list_widget.addItems(pdf_folders)
            self.pdf_tab.set_directories(pdf_folders)
            vp = state.get('default_video_player', '')
            if vp:
                if vp == "native":
                    self.video_tab.default_player = "native"
                    self.video_player_label.setText("Native Player")
                elif os.path.exists(vp):
                    self.video_tab.default_player = vp
                    app_name = os.path.splitext(os.path.basename(vp))[0]
                    self.video_player_label.setText(f"{app_name}\n{vp}")
            self._update_native_button_text()

            io = state.get('default_image_opener', '')
            if io:
                if io == "native":
                    self.image_tab.default_player = "native"
                    self.image_opener_label.setText("Native Viewer")
                elif os.path.exists(io):
                    self.image_tab.default_player = io
                    app_name = os.path.splitext(os.path.basename(io))[0]
                    self.image_opener_label.setText(f"{app_name}\n{io}")
            ap = state.get('default_audio_player', '')
            if ap:
                if ap == "native":
                    self.audio_tab.default_player = "native"
                    self.audio_player_label.setText("Native Player")
                elif os.path.exists(ap):
                    self.audio_tab.default_player = ap
                    app_name = os.path.splitext(os.path.basename(ap))[0]
                    self.audio_player_label.setText(f"{app_name}\n{ap}")
            po = state.get('default_pdf_opener', '')
            if po and po != "native":
                if os.path.exists(po):
                    self.pdf_tab.default_player = po
                    app_name = os.path.splitext(os.path.basename(po))[0]
                    self.pdf_opener_label.setText(f"{app_name}\n{po}")
            self._update_native_button_text()
            fp = state.get('ffprobe_path', '')
            self.ffprobe_path = fp
            if fp and os.path.exists(fp):
                app_name = os.path.splitext(os.path.basename(fp))[0]
                self.ffprobe_path_label.setText(f"{app_name}\n{fp}")
            if 'video_tab' in state: self.video_tab.load_state_dict(state['video_tab'])
            if 'image_tab' in state: self.image_tab.load_state_dict(state['image_tab'])
            if 'audio_tab' in state: self.audio_tab.load_state_dict(state['audio_tab'])
            if 'pdf_tab' in state: self.pdf_tab.load_state_dict(state['pdf_tab'])
            if video_folders: self.video_tab._start_scan(video_folders)
            if image_folders: self.image_tab._start_scan(image_folders)
            if audio_folders: self.audio_tab._start_scan(audio_folders)
            if pdf_folders: self.pdf_tab._start_scan(pdf_folders)
            smart_folders = state.get('smart_folders', [])
            for sf in smart_folders:
                name = sf['name']; media_type = sf['type']; query = sf['query']
                if any(f['name'].lower() == name.lower() for f in self.smart_folders_config): continue
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
        except Exception: pass

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
            items = [list_widget.item(i).text() for i in range(list_widget.count())]
            added_any = False
            for d in directories:
                if d not in items: list_widget.addItem(d); added_any = True
            if added_any: update_func()
        if files:
            allowed_exts = set()
            if active_tab.media_type == 'video': allowed_exts = VIDEO_EXTENSIONS
            elif active_tab.media_type == 'image': allowed_exts = IMAGE_EXTENSIONS
            elif active_tab.media_type == 'audio': allowed_exts = AUDIO_EXTENSIONS
            elif active_tab.media_type == 'pdf': allowed_exts = PDF_EXTENSIONS
            valid_files = [f for f in files if os.path.splitext(f)[1].lower() in allowed_exts]
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

def main():
    if sys.platform == 'win32':
        try:
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("antigravity.mediaflow.app.1")
        except Exception:
            pass

    app = QApplication(sys.argv)
    app.setApplicationName("MediaFlow")
    app.setOrganizationName("MediaFlow")

    # Set application-wide window icon (shows on top-left title bar and in the taskbar)
    logo_path = get_resource_path("logo.png")
    if os.path.exists(logo_path):
        app.setWindowIcon(QIcon(logo_path))

    font = QFont("Segoe UI", 10)
    app.setFont(font)
    
    palette = QPalette()
    palette.setColor(QPalette.ColorRole.Window, QColor("#0f0c29"))
    palette.setColor(QPalette.ColorRole.WindowText, QColor("#e0e0e0"))
    app.setPalette(palette)

    window = MediaFlowWindow()
    window.show()
    sys.exit(app.exec())

if __name__ == "__main__":
    main()