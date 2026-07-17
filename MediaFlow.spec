# -*- mode: python ; coding: utf-8 -*-


a = Analysis(
    ['F:\\Dev\\MediaFlow\\mediaflow.py'],
    pathex=[],
    binaries=[],
    datas=[('logo.png', '.')],
    hiddenimports=[],
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=['PyQt6.QtWebEngineWidgets', 'PyQt6.QtWebEngineCore', 'PyQt6.QtWebEngine'],
    noarchive=False,
    optimize=0,
)
pyz = PYZ(a.pure)

exe = EXE(
    pyz,
    a.scripts,
    a.binaries,
    a.datas,
    [],
    name='MediaFlow',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    upx_exclude=[],
    runtime_tmpdir=None,
    console=False,
    disable_windowed_traceback=False,
    argv_emulation=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
    icon=['logo.ico'],
)
