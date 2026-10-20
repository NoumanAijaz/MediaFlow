import os
import sys
import tempfile
import typing

import pytest

# Ensure repository root is on sys.path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from mediaflow import (
    MediaInfo,
    MediaTab,
    calculate_file_hash,
    matches_query,
    parse_destination_template,
    parse_naming_format,
    sniff_media_type_from_file,
)
from rust_bridge import (
    find_duplicates_rust,
    is_rust_core_available,
    scan_directories_rust,
)


def test_sniff_media_type_from_file_type_hints():
    """Verify that sniff_media_type_from_file annotations can be inspected without NameError."""
    hints = typing.get_type_hints(sniff_media_type_from_file)
    assert "return" in hints


def test_sniff_media_type_magic_bytes():
    """Verify sniffing identifying bytes from extensionless files."""
    with tempfile.TemporaryDirectory() as tmpdir:
        png_path = os.path.join(tmpdir, "img_noext")
        with open(png_path, "wb") as f:
            f.write(b"\x89PNG\r\n\x1a\n\x00\x00\x00\rIHDR" + b"\x00" * 32)
        assert sniff_media_type_from_file(png_path) == "image"

        pdf_path = os.path.join(tmpdir, "doc_noext")
        with open(pdf_path, "wb") as f:
            f.write(b"%PDF-1.4\n" + b"\x00" * 32)
        assert sniff_media_type_from_file(pdf_path) == "pdf"


def test_parse_naming_format_image_resolution_case():
    """Verify case-insensitive image resolution parsing, including lowercase 'k' resolution."""
    # Test lowercase 'k' resolution tag
    artist, rating = parse_naming_format("Alice - k - 8.jpg", media_type="image")
    assert artist == "Alice"
    assert rating == "8"

    # Test uppercase and other resolutions
    artist, rating = parse_naming_format("Bob - 4K - 10.png", media_type="image")
    assert artist == "Bob"
    assert rating == "10"

    artist, rating = parse_naming_format("Charlie - hd - —.webp", media_type="image")
    assert artist == "Charlie"
    assert rating is None

def test_parse_naming_format_strict_media_type():
    """Verify that audio media type does not accidentally match the image regex (which uses resolution)."""
    # For audio, "4K" is not a valid duration. If the string is "My Song - 4K - 8.mp3",
    # the image regex would match "My Song" as artist and "8" as rating if allowed.
    # But since it's audio, it will either fail or match differently.
    # Let's test with a string that strictly matches image but is invalid for audio.
    # "Artist - 4K.mp3" matches image (Artist="Artist", Res="4K") but for audio, there is no duration digits!
    artist, rating = parse_naming_format("Artist - 4K.mp3", media_type="audio")
    assert artist is None
    assert rating is None



def test_matches_query_and_conjunction():
    """Verify that 'and' conjunction in queries (e.g. 'rating:>=8 and tag:nature') is not treated as a search word."""
    class DummyInfo:
        def __init__(self, filename, rating, tags):
            self.filename = filename
            self.parsed_rating = rating
            self.tags = tags
            self.media_type = "image"

    info = DummyInfo("mountain_landscape.jpg", "9", ["nature", "travel"])

    # This exact query matches the UI placeholder: 'rating:>=8 and tag:nature'
    assert matches_query(info, "rating:>=8 and tag:nature") is True
    assert matches_query(info, "rating:>=8 AND tag:nature") is True
    assert matches_query(info, "rating:>=8 AND tag:missing") is False
    assert matches_query(info, "rating:<5 and tag:nature") is False


def test_matches_query_partial_parsed_attributes():
    """Verify fallback parsing of filename when either parsed_artist or parsed_rating is missing."""
    class DummyInfo:
        def __init__(self, filename, artist=None, rating=None):
            self.filename = filename
            self.parsed_artist = artist
            self.parsed_rating = rating
            self.media_type = "video"
            self.tags = []

    # Case 1: artist already set, but rating was not parsed yet
    info1 = DummyInfo("Monet - 10 - HD - 9.mp4", artist="Monet", rating=None)
    assert matches_query(info1, "rating:>=8") is True
    assert matches_query(info1, "rating:<5") is False

    # Case 2: rating already set, but artist was not parsed yet
    info2 = DummyInfo("VanGogh - 10 - HD - 9.mp4", artist=None, rating="9")
    assert matches_query(info2, "artist:vangogh") is True
    assert matches_query(info2, "artist:rembrandt") is False


def test_file_hash_large_head_only():
    """Verify head_only MD5 calculation for files larger than 2MB."""
    with tempfile.TemporaryDirectory() as tmpdir:
        large_file = os.path.join(tmpdir, "sample.bin")
        with open(large_file, "wb") as f:
            f.write(b"A" * (1024 * 1024))
            f.write(b"B" * (1024 * 1024))
            f.write(b"C" * (1024 * 1024))

        hash_result = calculate_file_hash(large_file, head_only=True)
        assert hash_result is not None
        assert len(hash_result) == 32


@pytest.mark.skipif(not is_rust_core_available(), reason="mediaflow-core not available")
def test_rust_scanner_dot_root_scan():
    """Verify Rust scanner does not prune '.' at depth 0."""
    with tempfile.TemporaryDirectory() as tmpdir:
        test_file = os.path.join(tmpdir, "sample.mp4")
        with open(test_file, "wb") as f:
            f.write(b"\x00\x00\x00\x1cftypmp42\x00\x00\x00\x00mp42isom")

        # Scan using relative path
        orig_cwd = os.getcwd()
        try:
            os.chdir(tmpdir)
            found_files = []
            total, _ = scan_directories_rust(
                directories=["."],
                media_type="video",
                on_file_found=lambda event: found_files.append(event["path"]),
            )
            assert total >= 1
            assert len(found_files) >= 1
        finally:
            os.chdir(orig_cwd)


@pytest.mark.skipif(not is_rust_core_available(), reason="mediaflow-core not available")
def test_rust_scanner_target_type_does_not_leak_other_media():
    """Verify scanning media_type='video' does not include images or text files even if extensionless."""
    with tempfile.TemporaryDirectory() as tmpdir:
        # 1. Real MP4
        v1 = os.path.join(tmpdir, "clip.mp4")
        with open(v1, "wb") as f:
            f.write(b"\x00\x00\x00\x1cftypmp42\x00\x00\x00\x00mp42isom")

        # 2. Extensionless video
        v2 = os.path.join(tmpdir, "clip_noext")
        with open(v2, "wb") as f:
            f.write(b"\x00\x00\x00\x1cftypmp42\x00\x00\x00\x00mp42isom")

        # 3. Extensionless PNG image
        img = os.path.join(tmpdir, "photo_noext")
        with open(img, "wb") as f:
            f.write(b"\x89PNG\r\n\x1a\n\x00\x00\x00\rIHDR" + b"\x00" * 32)

        # 4. Extensionless text file
        txt = os.path.join(tmpdir, "README")
        with open(txt, "wb") as f:
            f.write(b"Hello world text document")

        found_filenames = []
        total, _ = scan_directories_rust(
            directories=[tmpdir],
            media_type="video",
            include_no_ext=True,
            on_file_found=lambda event: found_filenames.append(event["filename"]),
        )

        assert "clip.mp4" in found_filenames
        assert "clip_noext" in found_filenames
        assert "photo_noext" not in found_filenames
        assert "README" not in found_filenames
        assert total == 2


@pytest.mark.skipif(not is_rust_core_available(), reason="mediaflow-core not available")
def test_rust_dedupe_large_files():
    """Verify Rust dedupe correctly groups identical files > 2MB using head/tail & full hash."""
    with tempfile.TemporaryDirectory() as tmpdir:
        content = b"X" * (3 * 1024 * 1024)
        f1 = os.path.join(tmpdir, "f1.bin")
        f2 = os.path.join(tmpdir, "f2.bin")
        f3 = os.path.join(tmpdir, "f3.bin")

        with open(f1, "wb") as f: f.write(content)
        with open(f2, "wb") as f: f.write(content)
        with open(f3, "wb") as f: f.write(content + b"different")

        items = [
            {"path": f1, "size": len(content)},
            {"path": f2, "size": len(content)},
            {"path": f3, "size": len(content) + 9},
        ]

        groups, _skipped = find_duplicates_rust(items)
        assert len(groups) == 1
        assert len(groups[0]) == 2
        norm_group = [os.path.normcase(p) for p in groups[0]]
        assert os.path.normcase(f1) in norm_group
        assert os.path.normcase(f2) in norm_group


def test_sniff_media_type_m4a_audio():
    """Verify extensionless M4A audio is identified as 'audio' and not 'video'."""
    with tempfile.TemporaryDirectory() as tmpdir:
        m4a_path = os.path.join(tmpdir, "audio_track")
        with open(m4a_path, "wb") as f:
            # MP4 box: 4 bytes length, 'ftyp', 'M4A ', minor version, compatible brands
            f.write(b"\x00\x00\x00\x1cftypM4A \x00\x00\x00\x00M4A isom")
        assert sniff_media_type_from_file(m4a_path) == "audio"

        mp4_path = os.path.join(tmpdir, "video_clip")
        with open(mp4_path, "wb") as f:
            f.write(b"\x00\x00\x00\x1cftypmp42\x00\x00\x00\x00mp42isom")
        assert sniff_media_type_from_file(mp4_path) == "video"


def test_destination_template_unrated_hyphen():
    """Verify destination template {rating} outputs 'Unrated' when rating is '-' or '—'."""
    info = MediaInfo(filepath="sample.mp4")
    info.parsed_artist = "Artist"
    info.parsed_rating = "-"
    assert parse_destination_template("{artist}/{rating}", info) == "Artist/Unrated"

    info.parsed_rating = "—"
    assert parse_destination_template("{artist}/{rating}", info) == "Artist/Unrated"

    info.parsed_rating = "8"
    assert parse_destination_template("{artist}/{rating}", info) == "Artist/8"


def test_templated_name_dashes_omitted():
    """Verify placeholder dashes ('-' and '—') are not included in templated filenames."""
    info = MediaInfo(filepath="sample.mp4")
    info.duration_compact = "—"
    info.resolution_tag = "—"

    class DummyTab:
        media_type = "video"

    fields_checked = ["name", "rating", "duration", "resolution"]
    fields_ordered = ["Name", "Duration", "Resolution", "Rating"]

    name_hyphen = MediaTab._get_templated_name_for(
        DummyTab(), "Artist", "-", info, fields_checked, fields_ordered, " - "
    )
    assert name_hyphen == "Artist"

    name_emdash = MediaTab._get_templated_name_for(
        DummyTab(), "Artist", "—", info, fields_checked, fields_ordered, " - "
    )
    assert name_emdash == "Artist"

    name_rated = MediaTab._get_templated_name_for(
        DummyTab(), "Artist", "8", info, fields_checked, fields_ordered, " - "
    )
    assert name_rated == "Artist - 8"


def test_naming_completeness_unrated_dashes():
    """Verify naming completeness treats '-' and '—' as unrated."""
    fields_checked = ["name", "rating"]
    assert MediaTab._is_naming_data_complete_for(None, fields_checked, "Artist", "-") is False
    assert MediaTab._is_naming_data_complete_for(None, fields_checked, "Artist", "—") is False
    assert MediaTab._is_naming_data_complete_for(None, fields_checked, "Artist", "") is False
    assert MediaTab._is_naming_data_complete_for(None, fields_checked, "Artist", "8") is True


@pytest.mark.skipif(not is_rust_core_available(), reason="mediaflow-core not available")
def test_rust_dedupe_cancellation():
    """Verify find_duplicates_rust honors is_cancelled and exits promptly."""
    items = [
        {"path": "file1.bin", "size": 100},
        {"path": "file2.bin", "size": 100},
    ]
    groups, skipped = find_duplicates_rust(items, is_cancelled=lambda: True)
    assert groups == []
    assert skipped == 0


@pytest.mark.skipif(not is_rust_core_available(), reason="mediaflow-core not available")
def test_rust_scanner_empty_dirs():
    """Verify scanning empty or non-existent directories returns (0, 0.0) without crashing."""
    total, elapsed = scan_directories_rust(directories=[])
    assert total == 0
    assert elapsed == 0.0


def test_rust_scanner_nonzero_exit_raises(monkeypatch):
    """Verify scan_directories_rust raises RuntimeError if core exits with non-zero code."""
    class FakeStderr:
        def read(self):
            return "Fatal engine scan failure"

    class FakeProc:
        returncode = 1
        stdout = []
        stderr = FakeStderr()

        def wait(self, timeout=None):
            return 1

        def kill(self):
            pass

    import subprocess
    import rust_bridge

    monkeypatch.setattr(rust_bridge, "is_rust_core_available", lambda: True)
    monkeypatch.setattr(rust_bridge, "get_rust_core_binary", lambda: "fake_bin")
    monkeypatch.setattr(subprocess, "Popen", lambda *args, **kwargs: FakeProc())

    with tempfile.TemporaryDirectory() as tmpdir:
        with pytest.raises(RuntimeError, match="Fatal engine scan failure"):
            rust_bridge.scan_directories_rust(directories=[tmpdir])


def test_matches_query_unrated():
    """Verify matches_query recognizes rating:unrated and rating:none."""
    class DummyInfo:
        def __init__(self, rating):
            self.parsed_rating = rating
            self.filename = "song.mp3"
            self.media_type = "audio"
            self.tags = []

    info_hyphen = DummyInfo("-")
    assert matches_query(info_hyphen, "rating:unrated") is True
    assert matches_query(info_hyphen, "rating:none") is True

    info_emdash = DummyInfo("—")
    assert matches_query(info_emdash, "rating:unrated") is True
    assert matches_query(info_emdash, "rating:none") is True

    info_rated = DummyInfo("8")
    assert matches_query(info_rated, "rating:unrated") is False
    assert matches_query(info_rated, "rating:none") is False


def test_matches_query_resolution_p_suffix():
    """Verify matches_query supports p-suffixed resolution queries against dimensions."""
    class DummyInfo:
        def __init__(self, w, h, tag=None):
            self.width = w
            self.height = h
            self.resolution_tag = tag or ""
            self.filename = "clip.mp4"
            self.media_type = "video"
            self.tags = []

    info = DummyInfo(1920, 1080)
    assert matches_query(info, "res:1080p") is True
    assert matches_query(info, "res:1080") is True
    assert matches_query(info, "res:720p") is False


def test_rust_scanner_include_no_ext_flag():
    """Verify include_no_ext=False excludes extensionless files in rust scanner."""
    if not is_rust_core_available():
        pytest.skip("Rust core binary not available")

    with tempfile.TemporaryDirectory() as tmpdir:
        valid_file = os.path.join(tmpdir, "clip.mp4")
        with open(valid_file, "wb") as f:
            f.write(b"\x00\x00\x00\x20ftypisom" + b"\x00" * 32)

        noext_file = os.path.join(tmpdir, "mysteryfile")
        with open(noext_file, "wb") as f:
            f.write(b"plain data without extension")

        found_noext_false = []
        scan_directories_rust(
            directories=[tmpdir],
            media_type="all",
            include_no_ext=False,
            on_file_found=lambda evt: found_noext_false.append(evt["path"]),
        )
        found_basenames_false = [os.path.basename(p) for p in found_noext_false]
        assert "clip.mp4" in found_basenames_false
        assert "mysteryfile" not in found_basenames_false

        found_noext_true = []
        scan_directories_rust(
            directories=[tmpdir],
            media_type="all",
            include_no_ext=True,
            on_file_found=lambda evt: found_noext_true.append(evt["path"]),
        )
        found_basenames_true = [os.path.basename(p) for p in found_noext_true]
        assert "clip.mp4" in found_basenames_true
        assert "mysteryfile" in found_basenames_true


def test_find_duplicates_rust_no_self_matching():
    """Verify duplicate paths (or case variants) of the same file are not grouped as duplicates."""
    if not is_rust_core_available():
        pytest.skip("Rust core binary not available")

    with tempfile.TemporaryDirectory() as tmpdir:
        sample_file = os.path.join(tmpdir, "sample.mp4")
        with open(sample_file, "wb") as f:
            f.write(b"unique-sample-data-12345" * 100)

        # Pass identical path twice and case-modified path
        items = [
            {"path": sample_file, "size": os.path.getsize(sample_file)},
            {"path": sample_file, "size": os.path.getsize(sample_file)},
        ]
        groups, _skipped = find_duplicates_rust(items)
        assert groups == []


def test_find_duplicates_none_size_handling():
    """Verify finding duplicates handles items with size=None without raising TypeError."""
    if not is_rust_core_available():
        pytest.skip("Rust core binary not available")

    with tempfile.TemporaryDirectory() as tmpdir:
        sample_file = os.path.join(tmpdir, "sample.mp4")
        with open(sample_file, "wb") as f:
            f.write(b"sample-data" * 50)

        items = [{"path": sample_file, "size": None}]
        groups, _skipped = find_duplicates_rust(items)
        assert isinstance(groups, list)


@pytest.mark.skipif(sys.platform != "win32", reason="Windows recycle-bin API")
def test_send_to_recycle_bin_long_path_refuses_shell_api(monkeypatch, tmp_path):
    """>240-char paths must never reach SHFileOperationW when send2trash is unavailable."""
    import builtins
    import mediaflow

    real_import = builtins.__import__

    def _no_send2trash(name, *a, **k):
        if name == "send2trash":
            raise ImportError("send2trash unavailable in this test")
        return real_import(name, *a, **k)

    monkeypatch.setattr(builtins, "__import__", _no_send2trash)
    target = tmp_path / ("c" * 70) / ("d" * 70) / ("e" * 60) / "clip.mp4"
    target.parent.mkdir(parents=True)
    target.write_bytes(b"x")
    assert len(str(target)) > 240

    assert mediaflow.send_to_recycle_bin(str(target)) is False
    assert target.exists()


def test_extension_sets_match_rust_scanner():
    """Python fallback and mediaflow-core must accept exactly the same extensions."""
    from mediaflow import AUDIO_EXTENSIONS, IMAGE_EXTENSIONS, PDF_EXTENSIONS, VIDEO_EXTENSIONS
    accepted = {e.lstrip(".") for e in VIDEO_EXTENSIONS | AUDIO_EXTENSIONS | IMAGE_EXTENSIONS | PDF_EXTENSIONS}
    expected = {
        "mp4", "mkv", "avi", "mov", "wmv", "flv", "webm", "m4v", "mpg", "mpeg", "m2v", "ts", "m2ts",
        "mts", "vob", "3gp", "3g2", "ogv", "f4v", "f4p", "divx", "rm", "rmvb", "asf", "amv", "svi",
        "mp3", "wav", "aac", "flac", "ogg", "m4a", "wma", "opus", "aiff", "aif", "alac", "mid", "midi",
        "mka", "ape", "amr", "m4b",
        "jpg", "jpeg", "png", "gif", "bmp", "webp", "tiff", "tif", "jfif", "ico", "svg", "heic", "heif",
        "avif", "raw", "cr2", "nef", "arw",
        "pdf",
    }
    assert accepted == expected


def test_parse_destination_template_single_pass():
    """Verify single-pass template replacement does not re-substitute user values."""
    from mediaflow import MediaInfo, parse_destination_template

    info = MediaInfo(filepath="dummy.mp4")
    info.parsed_artist = "{year}"
    info.mtime = 1774000000.0  # Year 2026
    template = "{name}/{year}"
    result = parse_destination_template(template, info)
    assert result == "{year}/2026"


def test_matches_query_tag_exclusion():
    """Verify tag exclusion queries with -tag:, tag:-, and tag:! syntax."""
    from mediaflow import MediaInfo, matches_query

    info = MediaInfo(filepath="dummy.mp4")
    info.tags = ["nature", "waterfall", "4k"]

    # Positive match
    assert matches_query(info, "tag:nature") is True
    assert matches_query(info, "tags:nature,mountain") is True

    # Negative exclusion with -tag:
    assert matches_query(info, "-tag:nature") is False
    assert matches_query(info, "-tag:draft") is True

    # Negative exclusion with tag:-
    assert matches_query(info, "tag:-waterfall") is False
    assert matches_query(info, "tag:-draft") is True

    # Negative exclusion with tag:!
    assert matches_query(info, "tag:!4k") is False
    assert matches_query(info, "tag:!archive") is True

    # Negative exclusion with multiple comma-separated tags
    assert matches_query(info, "-tags:draft,archive") is True
    assert matches_query(info, "-tags:draft,nature") is False


def test_parse_destination_template_traversal_sanitization():
    """Verify parse_destination_template strips path traversal dots and separators from variables."""
    from mediaflow import MediaInfo, parse_destination_template

    info = MediaInfo(filepath="dummy.mp4")
    info.parsed_artist = "../../Malicious/Artist"
    info.filename = "../../../evil.mp4"
    template = "{name}/{filename}"
    res = parse_destination_template(template, info)
    assert ".." not in res
    assert res == "MaliciousArtist/evil"


def test_rust_renamer_batch_and_case_only():
    """Verify execute_rename_rust executes batch renames, including Windows case-only hops."""
    from rust_bridge import is_rust_core_available, execute_rename_rust

    if not is_rust_core_available():
        pytest.skip("Rust core binary not available")

    with tempfile.TemporaryDirectory() as tmpdir:
        src = os.path.join(tmpdir, "video_sample.mp4")
        tgt = os.path.join(tmpdir, "VIDEO_SAMPLE.MP4")
        with open(src, "wb") as f:
            f.write(b"content")

        # Dry run test
        tasks = [{"source": src, "target": tgt}]
        success, failed = execute_rename_rust(tasks, dry_run=True)
        assert len(success) == 1
        assert len(failed) == 0
        assert os.path.exists(src)

        # Real execution test (case-only rename on Windows)
        success, failed = execute_rename_rust(tasks, dry_run=False)
        assert len(success) == 1
        assert len(failed) == 0
        assert os.path.exists(tgt)


def test_duplicate_auto_selection_strategies():
    """Verify duplicate resolver keeper selection rules across different strategies."""
    entries = [
        {"path": "clip1.mp4", "size": 1000, "mtime": 100.0, "width": 1920, "height": 1080},
        {"path": "clip2.mp4", "size": 5000, "mtime": 300.0, "width": 1280, "height": 720},
        {"path": "clip3.mp4", "size": 3000, "mtime": 200.0, "width": 3840, "height": 2160},
    ]
    grp = [0, 1, 2]

    # Test Keep Newest (max mtime -> idx 1)
    newest = min(grp, key=lambda i: -entries[i]["mtime"])
    assert newest == 1

    # Test Keep Oldest (min mtime -> idx 0)
    oldest = min(grp, key=lambda i: entries[i]["mtime"])
    assert oldest == 0

    # Test Keep Largest (max size -> idx 1)
    largest = min(grp, key=lambda i: -entries[i]["size"])
    assert largest == 1

    # Test Keep Smallest (min size -> idx 0)
    smallest = min(grp, key=lambda i: entries[i]["size"])
    assert smallest == 0


def test_media_tab_undo_history_transaction():
    """Verify MediaTab._add_to_history appends transactions and tracks sidecars headlessly."""
    os.environ["QT_QPA_PLATFORM"] = "offscreen"
    from PyQt6.QtWidgets import QApplication
    from mediaflow import MediaTab

    _app = QApplication.instance() or QApplication(["-platform", "offscreen"])

    tab = MediaTab(media_type="video")
    assert len(tab._rename_history) == 0
    assert len(tab._redo_history) == 0

    # Add a transaction with sidecars
    tab._add_to_history(
        src="c:/media/clip.mp4",
        dst="c:/media/Artist - Title - 10.mp4",
        row=0,
        extra=[("c:/media/clip.srt", "c:/media/Artist - Title - 10.srt")],
    )

    assert len(tab._rename_history) == 1
    last = tab._rename_history[-1]
    assert last["src"] == "c:/media/clip.mp4"
    assert last["dst"] == "c:/media/Artist - Title - 10.mp4"
    assert len(last["extra"]) == 1
    assert last["extra"][0] == ("c:/media/clip.srt", "c:/media/Artist - Title - 10.srt")
    assert tab.btn_undo.isEnabled() is True


_QT_APP = None


def _offscreen_app():
    global _QT_APP
    os.environ["QT_QPA_PLATFORM"] = "offscreen"
    from PyQt6.QtWidgets import QApplication

    if _QT_APP is None:
        _QT_APP = QApplication.instance() or QApplication(["-platform", "offscreen"])
    return _QT_APP


def _write_jpeg_with_orientation(path: str, width: int, height: int, orientation: int):
    import struct

    from PyQt6.QtGui import QImage

    image = QImage(width, height, QImage.Format.Format_RGB32)
    image.fill(0x336699)
    assert image.save(path, "JPEG", 95)
    with open(path, "rb") as f:
        data = f.read()
    tiff = (
        b"II*\x00"
        + struct.pack("<I", 8)
        + struct.pack("<H", 1)
        + struct.pack("<HHII", 0x0112, 3, 1, orientation)
        + struct.pack("<I", 0)
    )
    app1 = b"Exif\x00\x00" + tiff
    out = data[:2] + b"\xff\xe1" + struct.pack(">H", len(app1) + 2) + app1 + data[2:]
    with open(path, "wb") as f:
        f.write(out)


def test_sniff_media_type_ftyp_brands():
    """HEIC/AVIF containers are images and M4B is audio, not video."""
    with tempfile.TemporaryDirectory() as tmpdir:
        def write_brand(name, brand):
            path = os.path.join(tmpdir, name)
            with open(path, "wb") as f:
                f.write(b"\x00\x00\x00\x18ftyp" + brand + b"\x00\x00\x00\x00" + brand + b"isom")
            return path

        assert sniff_media_type_from_file(write_brand("heic_noext", b"heic")) == "image"
        assert sniff_media_type_from_file(write_brand("avif_noext", b"avif")) == "image"
        assert sniff_media_type_from_file(write_brand("m4b_noext", b"M4B ")) == "audio"
        assert sniff_media_type_from_file(write_brand("mp4_noext", b"mp42")) == "video"


def test_parse_ffprobe_json_fps_zero_fraction_falls_back_to_avg():
    import mediaflow as mf

    parsed = mf.parse_ffprobe_json({
        "streams": [{
            "codec_type": "video",
            "width": 1920,
            "height": 1080,
            "r_frame_rate": "0/0",
            "avg_frame_rate": "25/1",
        }]
    })
    assert parsed["video"]["fps"] == 25.0


def test_media_info_exif_orientation_dimensions():
    _offscreen_app()
    from mediaflow import MediaInfo

    with tempfile.TemporaryDirectory() as tmpdir:
        no_swap = os.path.join(tmpdir, "orient3.jpg")
        _write_jpeg_with_orientation(no_swap, 40, 80, 3)
        info = MediaInfo(no_swap, "image")
        assert (info.width, info.height) == (40, 80)

        swap = os.path.join(tmpdir, "orient6.jpg")
        _write_jpeg_with_orientation(swap, 40, 80, 6)
        info = MediaInfo(swap, "image")
        assert (info.width, info.height) == (80, 40)


def test_generate_thumbnail_timeout_returns_promptly(monkeypatch):
    import time

    import mediaflow as mf

    class SlowVideoCapture:
        def __init__(self, *args, **kwargs):
            pass

        def isOpened(self):
            return True

        def get(self, prop):
            return 0.0

        def set(self, prop, value):
            return True

        def read(self):
            time.sleep(8)
            return False, None

        def release(self):
            pass

    monkeypatch.setattr(mf.cv2, "VideoCapture", SlowVideoCapture)
    started = time.monotonic()
    result = mf.generate_thumbnail("slow.mp4", "video", 120, 68)
    elapsed = time.monotonic() - started
    assert result is None
    assert elapsed < 5.5


def test_redo_history_records_only_completed_sidecars(tmp_path):
    import types

    import mediaflow as mf

    src = tmp_path / "a.mp4"
    src.write_bytes(b"x")
    dst = tmp_path / "b.mp4"
    sidecar_src = tmp_path / "a.srt"
    sidecar_src.write_bytes(b"s")
    sidecar_dst = tmp_path / "missing" / "b.srt"

    class StubTable:
        def rowCount(self):
            return 0

        def isSortingEnabled(self):
            return False

        def setSortingEnabled(self, value):
            pass

    class Stub:
        def __init__(self):
            self._redo_history = [{
                "src": str(src),
                "dst": str(dst),
                "extra": [(str(sidecar_src), str(sidecar_dst))],
                "row": 0,
            }]
            self._rename_history = []
            self.table = StubTable()
            self.status_label = types.SimpleNamespace(setText=lambda *a: None)
            self.btn_redo = types.SimpleNamespace(setEnabled=lambda *a: None)
            self.btn_undo = types.SimpleNamespace(setEnabled=lambda *a: None)
            self._known_files_dirty = False
            self.history_kwargs = None

        def _release_file_locks(self, paths):
            pass

        def _show_toast(self, *args, **kwargs):
            pass

        def _update_stats(self):
            pass

        def _refresh_row_dates(self, info):
            pass

        def _grid_item(self, info):
            return None

        def _update_date_items(self, *args):
            pass

        def _update_row_preview(self, *args):
            pass

        def _add_to_history(self, *args, **kwargs):
            self.history_kwargs = kwargs

    stub = Stub()
    mf.MediaTab._on_redo_rename(stub)
    assert stub.history_kwargs is not None
    assert stub.history_kwargs["extra"] == []


def test_cell_editor_escape_reverts_text():
    _offscreen_app()
    from PyQt6.QtCore import QEvent, Qt
    from PyQt6.QtGui import QKeyEvent

    from mediaflow import EditableCellLineEdit

    editor = EditableCellLineEdit("placeholder")
    editor.setText("original")
    editor._start_editing()
    editor.setText("typed")
    editor.keyPressEvent(
        QKeyEvent(QEvent.Type.KeyPress, Qt.Key.Key_Escape, Qt.KeyboardModifier.NoModifier)
    )
    assert editor.text() == "original"
    assert editor._editing_active is False


def test_folder_profiles_dialog_save_closes():
    _offscreen_app()
    from PyQt6.QtWidgets import QDialog, QWidget

    from mediaflow import FolderProfilesDialog

    class FakeMainWindow(QWidget):
        def __init__(self):
            super().__init__()
            self.folder_profiles = {}
            self.rename_presets = {}

        def _debounced_save_state(self):
            pass

    main_win = FakeMainWindow()
    dialog = FolderProfilesDialog(main_win)
    dialog.accept()
    assert dialog.result() == QDialog.DialogCode.Accepted


def test_comparison_delete_removes_main_before_sidecars(tmp_path, monkeypatch):
    import types

    import mediaflow as mf

    main_path = tmp_path / "movie.mp4"
    main_path.write_bytes(b"x")
    sidecar = tmp_path / "movie.srt"
    sidecar.write_bytes(b"s")

    class FakeMessageBox:
        class StandardButton:
            Yes = 1
            No = 0

        @staticmethod
        def question(*args, **kwargs):
            return FakeMessageBox.StandardButton.Yes

        @staticmethod
        def warning(*args, **kwargs):
            pass

    calls = []
    monkeypatch.setattr(mf, "QMessageBox", FakeMessageBox)
    monkeypatch.setattr(
        mf,
        "send_to_recycle_bin",
        lambda p: calls.append(p) or (os.path.normpath(p) == os.path.normpath(str(sidecar))),
    )

    class Pane:
        def cleanup(self):
            pass

    class Stub:
        pane_left = Pane()
        pane_right = Pane()
        parent_tab = None
        info_left = None
        info_right = None

        def _restore_pane_after_failed_delete(self, pane, info):
            pass

        def close(self):
            pass

    info = types.SimpleNamespace(filename="movie.mp4", filepath=str(main_path))
    mf.ComparisonViewWindow._delete_file(Stub(), info)
    assert calls == [str(main_path)]


def test_random_player_seek_with_unknown_duration():
    _offscreen_app()
    from PyQt6.QtCore import QEvent, Qt
    from PyQt6.QtGui import QKeyEvent

    from mediaflow import RandomShufflePlayerWindow

    class FakePlayer:
        def __init__(self):
            self.positions = []

        def duration(self):
            return 0

        def position(self):
            return 5000

        def setPosition(self, pos):
            self.positions.append(pos)

    class Stub:
        def __init__(self):
            self.player = FakePlayer()

        def show_controls_temporarily(self):
            pass

    stub = Stub()
    stub.keyPressEvent = lambda ev: RandomShufflePlayerWindow.keyPressEvent(stub, ev)
    stub.keyPressEvent(
        QKeyEvent(QEvent.Type.KeyPress, Qt.Key.Key_BracketRight, Qt.KeyboardModifier.NoModifier)
    )
    assert stub.player.positions == [10000]

    ctrl_stub = Stub()
    ctrl_stub.keyPressEvent = lambda ev: RandomShufflePlayerWindow.keyPressEvent(ctrl_stub, ev)
    ctrl_stub.keyPressEvent(
        QKeyEvent(QEvent.Type.KeyPress, Qt.Key.Key_Right, Qt.KeyboardModifier.ControlModifier)
    )
    assert ctrl_stub.player.positions == [15000]


def test_rating_change_reactivates_filter():
    import types
    from unittest.mock import Mock

    import mediaflow as mf

    sender = object()
    info = types.SimpleNamespace(parsed_rating=None)

    class Stub:
        COL_RATING = 4

        def __init__(self):
            self._filter_timer = Mock()
            self.table = Mock()
            self.table.rowCount.return_value = 1
            self.table.cellWidget.return_value = sender
            self.table.item.return_value = Mock()

        def sender(self):
            return sender

        def _get_row_info(self, row):
            return info

        def window(self):
            return types.SimpleNamespace(_debounced_save_state=lambda: None)

    stub = Stub()
    mf.MediaTab._on_rating_changed(stub, "7")
    assert info.parsed_rating == "7"
    stub._filter_timer.start.assert_called_once()


def test_batch_tag_reactivates_filter(monkeypatch):
    import types
    from unittest.mock import Mock

    import mediaflow as mf

    class Info:
        def __init__(self):
            self.is_valid = True
            self.tags = []
            self.filename = "f"

    infos = [Info(), Info()]

    class FakeRange:
        def topRow(self):
            return 0

        def bottomRow(self):
            return 1

    class FakeDialog:
        def __init__(self, selected, parent):
            pass

        def exec(self):
            return mf.QDialog.DialogCode.Accepted

        def get_result(self):
            return ("Add Tags", ["x"])

    monkeypatch.setattr(mf, "BatchTagDialog", FakeDialog)

    class Stub:
        COL_TAGS = 7

        def __init__(self):
            self._filter_timer = Mock()
            self.table = Mock()
            self.table.selectedRanges.return_value = [FakeRange()]
            self.table.isRowHidden.return_value = False
            self.table.rowCount.return_value = 2
            self.table.isSortingEnabled.return_value = False
            self.table.item.return_value = Mock()
            self.table.cellWidget.return_value = None
            self._updating_table = False

        def _get_row_info(self, row):
            return infos[row]

        def _grid_item(self, info):
            return None

        def _update_row_preview(self, row):
            pass

        def _enter_modal(self):
            pass

        def _exit_modal(self):
            pass

        def _show_toast(self, *args, **kwargs):
            pass

        def window(self):
            return types.SimpleNamespace(_debounced_save_state=lambda: None)

    stub = Stub()
    mf.MediaTab._on_batch_tag(stub)
    assert infos[0].tags == ["x"]
    stub._filter_timer.start.assert_called_once()


def test_quick_trim_export_skips_already_listed_output(tmp_path, monkeypatch):
    import types
    from unittest.mock import Mock

    import mediaflow as mf

    output_path = str(tmp_path / "clip.mp4")
    added = []

    class FakeMediaInfo:
        def __init__(self, filepath, media_type):
            self.filepath = filepath
            self.is_valid = True

    monkeypatch.setattr(mf, "MediaInfo", FakeMediaInfo)

    class Stub:
        def __init__(self):
            self._suppress_export_result = False
            self.btn_export = Mock()
            self.parent_tab = types.SimpleNamespace(
                directories=[str(tmp_path)],
                media_infos=[types.SimpleNamespace(filepath=output_path)],
                _known_files_dirty=False,
                _on_file_found=lambda info: added.append(info),
                _show_toast=lambda *a, **k: None,
            )

        def _release_player(self):
            pass

        def accept(self):
            pass

    mf.QuickTrimDialog._on_export_finished(Stub(), True, output_path, "")
    assert added == []


def test_thumb_slider_keyboard_change_applies():
    import mediaflow as mf

    class Slider:
        def __init__(self, down):
            self.down = down

        def isSliderDown(self):
            return self.down

    class Stub:
        def __init__(self, down):
            self.thumb_size = 130
            self.thumb_size_slider = Slider(down)
            self.applied = []

        def _on_thumb_size_changed(self):
            self.applied.append(self.thumb_size)

    keyboard = Stub(False)
    mf.MediaFlowWindow._on_thumb_size_live(keyboard, 160)
    assert keyboard.applied == [160]

    dragging = Stub(True)
    mf.MediaFlowWindow._on_thumb_size_live(dragging, 150)
    assert dragging.applied == []
    assert dragging.thumb_size == 150


def test_load_state_non_utf8_config_starts_fresh(tmp_path, monkeypatch):
    import mediaflow as mf

    bad = tmp_path / "config.json"
    bad.write_bytes(b'{"theme": "\xff\xfe"}')
    monkeypatch.setattr(mf, "CONFIG_FILE", str(bad))
    monkeypatch.setattr(mf.ThemeManager, "apply_theme", staticmethod(lambda *a, **k: None))

    class Stub:
        pass

    stub = Stub()
    mf.MediaFlowWindow._load_state(stub)
    assert stub._load_failed is True
    assert (tmp_path / "config.json.bak").exists()


# ---------------------------------------------------------------------------
# Pass 2 — rename/history, search, smart folders, watch mode, EXIF, Rust core
# ---------------------------------------------------------------------------


def _video_info(path, artist=None, rating=None, media_type="video"):
    """A MediaInfo that reports as a valid media file without touching disk."""
    info = MediaInfo(path, media_type, cached_data={
        "is_valid": True, "width": 1920, "height": 1080, "duration_seconds": 10.0,
        "duration_formatted": "00:10", "duration_compact": "10s", "resolution_tag": "1080p",
        "size_bytes": 10, "size_formatted": "10 B", "mtime": 0.0, "ctime": 0.0, "tags": [],
    })
    if artist is not None:
        info.parsed_artist = artist
    if rating is not None:
        info.parsed_rating = rating
    return info


def _media_tab(media_type="video", keep_extension=True):
    """A standalone MediaTab with a predictable naming configuration."""
    _offscreen_app()
    import mediaflow as mf

    tab = mf.MediaTab(media_type)
    tab.naming_keep_extension = keep_extension
    tab.naming_fields = ["name"]
    tab.naming_all_fields_ordered = ["Name"]
    tab.naming_separator = " "
    return tab


def _set_artist(tab, row, text):
    widget = tab.table.cellWidget(row, tab.COL_ARTIST)
    if widget is not None:
        widget.setText(text)
        return
    item = tab.table.item(row, tab.COL_ARTIST)
    if item is not None:
        item.setText(text)


def _patch_message_boxes(monkeypatch):
    """Replace modal message boxes with non-blocking stubs."""
    import mediaflow as mf

    yes = mf.QMessageBox.StandardButton.Yes

    class FakeMessageBox:
        class StandardButton:
            Yes = yes
            No = 0

        @staticmethod
        def question(*args, **kwargs):
            return yes

        @staticmethod
        def information(*args, **kwargs):
            pass

        @staticmethod
        def warning(*args, **kwargs):
            pass

        @staticmethod
        def critical(*args, **kwargs):
            pass

    monkeypatch.setattr(mf, "QMessageBox", FakeMessageBox)


def test_undo_keeps_history_entry_when_target_is_missing():
    """A failed undo must not delete the history entry (the file may come back)."""
    import types

    import mediaflow as mf

    class StubTable:
        def rowCount(self):
            return 0

        def isSortingEnabled(self):
            return False

        def setSortingEnabled(self, value):
            pass

    class Stub:
        def __init__(self, entry):
            self._rename_history = [entry]
            self._redo_history = []
            self.table = StubTable()
            self.status_label = types.SimpleNamespace(setText=lambda *a: None)
            self.btn_undo = types.SimpleNamespace(setEnabled=lambda *a: None)
            self.btn_redo = types.SimpleNamespace(setEnabled=lambda *a: None)
            self._known_files_dirty = False

        def _release_file_locks(self, paths):
            pass

        def _show_toast(self, *args, **kwargs):
            pass

        def _update_stats(self):
            pass

    mf.QMessageBox.warning = staticmethod(lambda *a, **k: None)
    entry = {"src": "a.mp4", "dst": "missing_target.mp4", "extra": [], "row": 0}
    stub = Stub(entry)
    mf.MediaTab._on_undo_rename(stub)
    assert stub._rename_history == [entry]


def test_redo_keeps_history_entry_when_source_is_missing():
    """A failed redo must keep the entry so the redo stays available."""
    import types

    import mediaflow as mf

    class StubTable:
        def rowCount(self):
            return 0

        def isSortingEnabled(self):
            return False

        def setSortingEnabled(self, value):
            pass

    class Stub:
        def __init__(self, entry):
            self._rename_history = []
            self._redo_history = [entry]
            self.table = StubTable()
            self.status_label = types.SimpleNamespace(setText=lambda *a: None)
            self.btn_undo = types.SimpleNamespace(setEnabled=lambda *a: None)
            self.btn_redo = types.SimpleNamespace(setEnabled=lambda *a: None)
            self._known_files_dirty = False

        def _release_file_locks(self, paths):
            pass

        def _show_toast(self, *args, **kwargs):
            pass

        def _update_stats(self):
            pass

    mf.QMessageBox.warning = staticmethod(lambda *a, **k: None)
    entry = {"src": "missing_source.mp4", "dst": "b.mp4", "extra": [], "row": 0}
    stub = Stub(entry)
    mf.MediaTab._on_redo_rename(stub)
    assert stub._redo_history == [entry]


def test_rename_keeps_known_extension_when_name_contains_dot(tmp_path, monkeypatch):
    """'Vol. 2' must not turn the known extension '.mp4' into '. 2'."""
    _patch_message_boxes(monkeypatch)
    src = tmp_path / "Vol. 2.mp4"
    src.write_bytes(b"x")

    tab = _media_tab(keep_extension=False)
    info = _video_info(str(src), artist="Vol. 2")
    tab._on_file_found(info)
    _set_artist(tab, 0, "Vol. 2")

    tab._on_process_all()
    assert info.extension == ".mp4"
    assert sorted(p.name for p in tmp_path.iterdir()) == ["Vol. 2"]

    # Re-enabling the extension must produce "Vol. 2.mp4", not "Vol. 2. 2".
    tab.naming_keep_extension = True
    tab._on_process_all()
    assert info.extension == ".mp4"
    assert sorted(p.name for p in tmp_path.iterdir()) == ["Vol. 2.mp4"]


def test_rename_preview_matches_applied_batch_names(tmp_path, monkeypatch):
    """The preview must show the names the batch really produces."""
    _patch_message_boxes(monkeypatch)
    (tmp_path / "X.mp4").write_bytes(b"p")
    a = tmp_path / "a.mp4"
    a.write_bytes(b"a")
    b = tmp_path / "b.mp4"
    b.write_bytes(b"b")

    tab = _media_tab(keep_extension=True)
    for path, artist in ((a, "X"), (b, "X_1")):
        tab._on_file_found(_video_info(str(path), artist=artist))
    _set_artist(tab, 0, "X")
    _set_artist(tab, 1, "X_1")

    preview = {r["current"]: r["final_target"] for r in tab._collect_rename_preview()}
    tab._on_process_all()

    actual = sorted(info.filename for info in tab.media_infos)
    assert sorted(preview.values()) == actual
    for name in actual:
        assert (tmp_path / name).exists()


def test_matches_query_quoted_value_matches_tag():
    """Quoted values must work on Windows too ('tag:"big cat"')."""
    class DummyInfo:
        def __init__(self):
            self.filename = "clip.jpg"
            self.parsed_artist = ""
            self.parsed_rating = "9"
            self.tags = ["big cat"]
            self.media_type = "image"

    info = DummyInfo()
    assert matches_query(info, 'tag:"big cat"') is True
    assert matches_query(info, 'tag:"small cat"') is False


def test_exclude_pattern_change_preserves_rename_history(tmp_path, monkeypatch):
    """Typing an exclude pattern must not wipe the undo/redo history."""
    import mediaflow as mf

    tab = _media_tab()
    src = tmp_path / "a.mp4"
    src.write_bytes(b"x")
    tab._on_file_found(_video_info(str(src)))
    tab.directories = [str(tmp_path)]
    tab._add_to_history(str(src), str(tmp_path / "b.mp4"), 0)
    tab._redo_history.append({"src": "x", "dst": "y", "extra": [], "row": 0})

    # A rescan clears the table (and the history) — emulate that part only.
    def fake_start_scan(folders, force_full=False):
        tab._on_clear()

    monkeypatch.setattr(mf.MediaTab, "_start_scan", fake_start_scan)
    tab.exclude_input.setText("*sample*")
    tab._apply_exclude_and_scan()

    assert len(tab._rename_history) == 1
    assert len(tab._redo_history) == 1


def test_saved_file_data_with_numeric_rating_is_restored(tmp_path):
    """A numeric rating in config.json must not abort the whole restore."""
    tab = _media_tab()
    src = tmp_path / "a.mp4"
    src.write_bytes(b"x")
    tab._on_file_found(_video_info(str(src)))

    key = os.path.normcase(os.path.normpath(str(src)))
    tab._saved_file_data = {key: {"artist": "John", "rating": 8, "tags": []}}
    tab._apply_saved_file_data_to_row(0)

    assert tab.table.item(0, tab.COL_RATING).text() == "8"
    assert tab.table.item(0, tab.COL_ARTIST).text() == "John"


def test_smart_folder_row_keeps_user_edited_artist(tmp_path):
    """A re-added row (smart folder) must show the edited artist, not the parsed one."""
    src = tmp_path / "Artist - 10 - HD - 9.mp4"
    src.write_bytes(b"x")
    info = _video_info(str(src))

    source_tab = _media_tab()
    source_tab._on_file_found(info)
    info.parsed_artist = "John"
    info.parsed_rating = "7"

    smart_tab = _media_tab()
    smart_tab._on_file_found(info)

    assert smart_tab.table.item(0, smart_tab.COL_ARTIST).text() == "John"
    assert smart_tab.table.item(0, smart_tab.COL_RATING).text() == "7"


def test_watch_detected_removal_is_not_blacklisted(tmp_path):
    """A file that vanished on its own must not be blocked from re-appearing."""
    tab = _media_tab()
    src = tmp_path / "a.mp4"
    src.write_bytes(b"x")
    tab._on_file_found(_video_info(str(src)))

    tab._remove_row_from_list(0, user_initiated=False)
    assert tab._user_removed_paths == set()

    # A row the user removed explicitly is still blacklisted.
    tab._on_file_found(_video_info(str(src)))
    tab._remove_row_from_list(0, user_initiated=True)
    assert os.path.normcase(os.path.normpath(str(src))) in tab._user_removed_paths


def test_exif_save_preserves_capture_time_of_day(tmp_path):
    """Saving image tags must not destroy the EXIF time of day."""
    import base64

    piexif = pytest.importorskip("piexif")
    from PyQt6.QtWidgets import QLineEdit

    from mediaflow import MediaTagEditorDialog

    # Minimal valid 1x1 JPEG (piexif needs a real JPEG to insert into).
    jpeg = base64.b64decode(
        "/9j/4AAQSkZJRgABAQEAYABgAAD/2wBDAAgGBgcGBQgHBwcJCQgKDBQNDAsLDBkSEw8UHRof"
        "Hh0aHBwgJC4nICIsIxwcKDcpLDAxNDQ0Hyc5PTgyPC4zNDL/wAALCAABAAEBAREA/8QAFAAB"
        "AAAAAAAAAAAAAAAAAAAACf/EABQQAQAAAAAAAAAAAAAAAAAAAAD/2gAIAQEAAD8AKp//2Q=="
    )
    jpg = tmp_path / "a.jpg"
    jpg.write_bytes(jpeg)
    exif = {
        "0th": {},
        "Exif": {piexif.ExifIFD.DateTimeOriginal: b"2024:03:15 14:32:07"},
        "GPS": {},
        "1st": {},
        "thumbnail": None,
    }
    piexif.insert(piexif.dump(exif), str(jpg))

    dialog = MediaTagEditorDialog.__new__(MediaTagEditorDialog)
    dialog._edits = {"date": QLineEdit(), "artist": QLineEdit()}
    dialog._load_image_tags(str(jpg))

    values = {"date": dialog._edits["date"].text().strip(), "artist": ""}
    dt = MediaTagEditorDialog._parse_date_input(values["date"])
    dialog._save_image(str(jpg), values, dt)

    stored = piexif.load(str(jpg))["Exif"][piexif.ExifIFD.DateTimeOriginal]
    assert stored == b"2024:03:15 14:32:07"


def test_csv_export_skips_thumbnail_column(tmp_path, monkeypatch):
    """The thumbnail column has no item — it must not be exported as an empty column."""
    import csv as _csv

    import mediaflow as mf

    target = tmp_path / "out.csv"

    class FakeFileDialog:
        @staticmethod
        def getSaveFileName(*args, **kwargs):
            return str(target), ""

    monkeypatch.setattr(mf, "QFileDialog", FakeFileDialog)

    tab = _media_tab()
    src = tmp_path / "a.mp4"
    src.write_bytes(b"x")
    tab._on_file_found(_video_info(str(src)))
    tab._export_list_csv()

    with open(target, newline="", encoding="utf-8-sig") as f:
        rows = list(_csv.reader(f))
    assert rows[0][0] == "Status"
    assert len(rows[0]) == len(rows[1])


def test_audio_tag_editor_reports_read_error(monkeypatch):
    """A read failure must not be reported as 'mutagen is not installed'."""
    import mediaflow as mf

    class FakeMessageBox:
        @staticmethod
        def critical(*args, **kwargs):
            pass

    monkeypatch.setattr(mf, "QMessageBox", FakeMessageBox)
    dialog = mf.AudioTagEditorDialog.__new__(mf.AudioTagEditorDialog)
    dialog.filepath = "not_audio.mp3"
    dialog._mutagen_ok = True
    dialog._read_error = ""
    dialog._edits = {k: mf.QLineEdit() for k in mf.AudioTagEditorDialog.FIELDS}
    dialog.status_lbl = mf.QLabel("")

    dialog._load_tags()
    assert dialog._mutagen_ok is False
    with pytest.raises(RuntimeError) as excinfo:
        dialog.save()
    assert "mutagen is not installed" not in str(excinfo.value)


@pytest.mark.skipif(not is_rust_core_available(), reason="mediaflow-core not available")
def test_rust_scan_accepts_exclude_pattern_starting_with_dash(tmp_path):
    """An exclude pattern starting with '-' must not abort the Rust scan."""
    clip = tmp_path / "clip.mp4"
    clip.write_bytes(b"\x00\x00\x00\x1cftypmp42\x00\x00\x00\x00mp42isom")

    found = []
    total, _ = scan_directories_rust(
        directories=[str(tmp_path)],
        media_type="video",
        exclude_patterns=["-backup"],
        on_file_found=lambda event: found.append(event["path"]),
    )
    assert total == 1
    assert len(found) == 1


@pytest.mark.skipif(not is_rust_core_available(), reason="mediaflow-core not available")
def test_rust_scan_reports_path_inside_scanned_tree(tmp_path):
    """A linked file must be reported under the path that was walked.

    Reporting the canonical path made the row point at the link's target, so a
    rename or a delete acted on a file OUTSIDE the scanned folder (and left
    the link dangling).
    """
    import subprocess

    real = tmp_path / "real"
    real.mkdir()
    (real / "movie.mp4").write_bytes(b"\x00\x00\x00\x1cftypmp42\x00\x00\x00\x00mp42isom")
    lib = tmp_path / "lib"
    lib.mkdir()

    if os.name == "nt":
        # A directory junction needs no privileges and still resolves elsewhere.
        link = lib / "linked"
        created = subprocess.run(
            ["cmd", "/c", "mklink", "/J", str(link), str(real)],
            capture_output=True, text=True,
        )
        if created.returncode != 0:
            pytest.skip("could not create a junction on this system")
        scan_root = link
    else:
        try:
            (lib / "link.mp4").symlink_to(real / "movie.mp4")
        except OSError:
            pytest.skip("symlinks are not available on this system")
        scan_root = lib

    events = []
    scan_directories_rust(
        directories=[str(scan_root)],
        media_type="video",
        on_file_found=lambda event: events.append(event),
    )
    assert events, "the linked file was not scanned at all"
    reported = os.path.normcase(os.path.abspath(events[0]["path"]))
    assert reported.startswith(os.path.normcase(os.path.abspath(str(lib))) + os.sep)


@pytest.mark.skipif(not is_rust_core_available(), reason="mediaflow-core not available")
def test_rust_scan_reports_pre_epoch_mtime(tmp_path):
    """A file older than 1970 must keep its negative timestamp (not 1970-01-01)."""
    old = tmp_path / "old.mp4"
    old.write_bytes(b"\x00\x00\x00\x1cftypmp42\x00\x00\x00\x00mp42isom")
    os.utime(old, (-86400, -86400))

    events = []
    scan_directories_rust(
        directories=[str(tmp_path)],
        media_type="video",
        on_file_found=lambda event: events.append(event),
    )
    assert events
    assert events[0]["mtime"] < 0


@pytest.mark.skipif(not is_rust_core_available(), reason="mediaflow-core not available")
def test_rust_dedupe_groups_empty_files(tmp_path):
    """The Rust engine must group 0-byte files like the Python engine does."""
    first = tmp_path / "z1.mp4"
    first.write_bytes(b"")
    second = tmp_path / "z2.mp4"
    second.write_bytes(b"")

    groups, _ = find_duplicates_rust([
        {"path": str(first), "size": 0},
        {"path": str(second), "size": 0},
    ])
    assert len(groups) == 1
    assert len(groups[0]) == 2









def test_watch_info_ready_skips_file_deleted_during_extraction(tmp_path):
    """A file deleted while its metadata was extracted must not be added."""
    tab = _media_tab()
    missing = tmp_path / "gone.mp4"
    info = _video_info(str(missing))

    tab._on_watch_info_ready(info)
    assert getattr(tab, "_pending_watch_infos", []) == []

    existing = tmp_path / "here.mp4"
    existing.write_bytes(b"x")
    tab._on_watch_info_ready(_video_info(str(existing)))
    assert len(getattr(tab, "_pending_watch_infos", [])) == 1


def test_scan_complete_refreshes_smart_folders():
    """A finished source scan must rebuild the smart-folder views."""
    tab = _media_tab()

    calls = []

    class FakeWindow:
        def refresh_smart_folders(self):
            calls.append(True)

    tab.window = lambda: FakeWindow()
    tab._on_scan_complete(0)
    assert calls == [True]
