#!/usr/bin/env python3
"""
ATEM Auto-Switcher
Monitors Dante Virtual Soundcard audio levels and switches ATEM Television Studio 4K
automatically based on which microphone is loudest.
Each row picks its own audio device (DVS stereo pair) and channel (0=left, 1=right).
"""

import sys
import time
import math
import random
import threading
import socket
import struct
import datetime
import json
import os
import zlib
import base64
from collections import defaultdict
from http.server import HTTPServer, BaseHTTPRequestHandler


# ── Tee stdout to atem_log.txt ────────────────────────────────────────────────
class _Tee:
    def __init__(self, *streams):
        # windowed exe (pythonw/PyInstaller --windowed) has no console:
        # sys.__stdout__/__stderr__ are None there, so drop them
        self._streams = [f for f in streams if f is not None]
        self._gui_cb = None   # set to signals.log_line.emit after Qt starts
    def write(self, s):
        for f in self._streams:
            f.write(s)
            f.flush()
        if self._gui_cb and s.strip():
            try:
                self._gui_cb(s)
            except Exception:
                pass
    def flush(self):
        for f in self._streams:
            f.flush()

import os as _os
_APP_DIR = _os.path.join(_os.path.expanduser('~'), 'Desktop', 'atem-switcher')
_os.makedirs(_APP_DIR, exist_ok=True)
_SETTINGS_FILE = _os.path.join(_APP_DIR, 'atem_settings.json')
_LOG_PATH = _os.path.join(_APP_DIR, 'atem_log.txt')
# Keep the previous session's log (e.g. after a crash) as atem_log.prev.txt
try:
    if _os.path.exists(_LOG_PATH):
        _os.replace(_LOG_PATH, _os.path.join(_APP_DIR, 'atem_log.prev.txt'))
except OSError:
    pass
_log_file = open(_LOG_PATH, 'w', encoding='utf-8')
_log_file.write(f'=== ATEM log started {datetime.datetime.now()} ===\n')
sys.stdout = _Tee(sys.__stdout__, _log_file)
sys.stderr = _Tee(sys.__stderr__, _log_file)

# Write arrow SVGs used by the stylesheet
_ARROW_UP_SVG  = _os.path.join(_APP_DIR, 'arrow_up.svg')
_ARROW_DN_SVG  = _os.path.join(_APP_DIR, 'arrow_dn.svg')
open(_ARROW_UP_SVG, 'w').write('<svg xmlns="http://www.w3.org/2000/svg" width="8" height="8"><polygon points="4,1 7,7 1,7" fill="#d4d4d4"/></svg>')
open(_ARROW_DN_SVG, 'w').write('<svg xmlns="http://www.w3.org/2000/svg" width="8" height="8"><polygon points="1,1 7,1 4,7" fill="#d4d4d4"/></svg>')

import numpy as np
import sounddevice as sd

from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QLabel, QPushButton, QLineEdit, QSpinBox, QDoubleSpinBox,
    QComboBox, QGroupBox, QProgressBar, QGridLayout, QSizePolicy,
    QTabWidget, QPlainTextEdit, QCheckBox, QScrollArea, QFrame,
)
from PyQt6.QtCore import Qt, pyqtSignal, QObject, QUrl
from PyQt6.QtGui import QFont, QColor, QPalette, QDesktopServices, QIcon, QPixmap


# ── Minimal built-in ATEM UDP client ──────────────────────────────────────────

class ATEMConnection:
    """
    Minimal ATEM UDP client — connect, keepalive, switch program input.

    Packet header (12 bytes big-endian):
      [0:2]  (flags<<11)|length   0x01=RELIABLE  0x02=SYN  0x10=ACK
      [2:4]  session_id
      [4:6]  remote_ack_id  (for ACK packets)
      [6:10] unused
      [10:12] local_packet_id
    """
    PORT = 9910

    CLIENT_SESSION = 0x53AB   # standard client session (used by sofie-atem-connection)

    def __init__(self, ip: str):
        self.ip = ip
        self._sock:   socket.socket | None = None
        self._session: int  = self.CLIENT_SESSION
        self._pkt_id:  int  = 0   # first command gets id=1
        self._last_rid: int = 0
        self._lock = threading.Lock()
        # Populated during connect() from the ATEM state dump
        self.model_name: str = ""
        self.me_count:   int = 1
        self.inputs: dict[int, dict] = {}   # inputId → {name, short_name}
        self.preview: dict[int, int] = {}   # me_idx → current preview source
        self.program: dict[int, int] = {}   # me_idx → current program source
        self.init_complete = False          # True once InCm parsed from the dump
        # Called (from keepalive thread) when connection drops — set by ATEMController
        self.on_disconnect = None
        # Called with (me_idx, source) whenever the preview/program bus changes
        self.on_preview = None
        self.on_program = None

    # ── Public API ────────────────────────────────────────────────────────────

    def connect(self) -> None:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.settimeout(8.0)
        # Large receive buffer — the state dump arrives as a fast burst of
        # hundreds of packets; the OS default buffer can overflow and drop some.
        try:
            s.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 1 << 20)
        except OSError:
            pass

        # SYN / hello — must match sofie's COMMAND_CONNECT_HELLO exactly:
        # 10 14 53 ab 00 00 00 00 00 3a 00 00 01 00 00 00 00 00 00 00
        # bytes 8-9 = 0x003A (protocol version/capability), local_id = 0
        hello = self._build(0x02, b'\x01\x00\x00\x00\x00\x00\x00\x00',
                            local_id=0, word4=0x003A)
        s.sendto(hello, (self.ip, self.PORT))
        print(f"ATEM ▶ SYN → {self.ip}:{self.PORT}  session=0x{self._session:04X}  hex={hello.hex()}")

        data, addr = s.recvfrom(4096)
        # Update session from every ATEM packet (sofie does this unconditionally)
        self._session = struct.unpack('!H', data[2:4])[0] or self._session
        print(f"ATEM ◀ SYN-ACK  session=0x{self._session:04X}  raw={data.hex()}")

        rid_a = struct.unpack('!H', data[10:12])[0]
        s.sendto(self._ack(s, rid_a), (self.ip, self.PORT))

        # Drain state dump — MUST wait for InCm before sending any commands.
        # The ATEM silently ignores commands received before InCm.
        s.settimeout(1.0)
        n = 0
        n_acked = 0
        incm_received = False
        deadline = time.time() + 15.0   # never wait more than 15s total
        while time.time() < deadline:
            try:
                data, _ = s.recvfrom(4096)
                n += 1
                # Always update session from incoming packets (sofie does this unconditionally)
                pkt_sess = struct.unpack('!H', data[2:4])[0]
                if pkt_sess:
                    self._session = pkt_sess
                rid = struct.unpack('!H', data[10:12])[0]
                in_order = True
                if rid:
                    # Cumulative ACK: only advance on the next in-order packet id.
                    # On a gap (lost packet) keep acking the last in-order id so
                    # the ATEM retransmits the missing packets — otherwise InCm
                    # can be lost forever and the dump never completes.
                    in_order = ((rid - self._last_rid) & 0x7FFF) == 1
                    if in_order:
                        self._last_rid = rid
                    ack_pkt = self._ack(s, self._last_rid)
                    s.sendto(ack_pkt, (self.ip, self.PORT))
                    n_acked += 1
                if not in_order:
                    continue   # duplicate or out-of-order — wait for retransmit
                # Parse commands from this packet to learn model/topology
                self._parse_state_packet(data)
                if self.init_complete:
                    incm_received = True
                    print(f"  ✓ InCm received at packet {n} — ATEM ready for commands")
                    break
            except (socket.timeout, TimeoutError):
                if incm_received:
                    break
                # Keep waiting — InCm may come after a brief pause
        if not incm_received:
            print("  ⚠ InCm not received — commands may be ignored by ATEM")
        print(f"ATEM ✓ connected  drained {n} pkts  acked {n_acked}  last_rid={self._last_rid}")

        s.settimeout(0.5)
        self._sock = s
        threading.Thread(target=self._keepalive, daemon=True).start()

    def switch_program(self, inp: int, me: int = 0) -> bool:
        """Send CPgI (Change Program Input) command. me is 0-indexed."""
        return self._send_bus_command(b'CPgI', inp, me)

    def switch_preview(self, inp: int, me: int = 0) -> bool:
        """Send CPvI (Change Preview Input) command. me is 0-indexed."""
        return self._send_bus_command(b'CPvI', inp, me)

    def _send_bus_command(self, cmd: bytes, inp: int, me: int) -> bool:
        with self._lock:
            s = self._sock
            if s is None:
                return False
            try:
                self._pkt_id = (self._pkt_id + 1) & 0x7FFF
                cmd_data = struct.pack('!BxH', me, inp)          # ME (0-indexed), pad, source
                cmd_env  = struct.pack('!H2s4s', 12, b'\x00\x00', cmd) + cmd_data
                # sofie leaves ack_id=0 in command packets (bytes 4-5 not written)
                pkt      = self._build(0x01, cmd_env,
                                       local_id=self._pkt_id,
                                       ack_id=0)
                print(f"ATEM ▶ {cmd.decode()} ME{me+1} input={inp}  pkt_id={self._pkt_id}  hex={pkt.hex()}")
                s.sendto(pkt, (self.ip, self.PORT))
                return True
            except Exception as e:
                print(f"ATEM ✗ switch error: {e}")
                return False

    def disconnect(self) -> None:
        with self._lock:
            s, self._sock = self._sock, None
        if s:
            try:
                s.close()
            except Exception:
                pass

    # ── Keepalive loop ────────────────────────────────────────────────────────

    def _keepalive(self) -> None:
        print("ATEM keepalive thread started")
        no_data_ticks = 0
        while True:
            with self._lock:
                s = self._sock
            if s is None:
                break
            try:
                data, _ = s.recvfrom(4096)
                no_data_ticks = 0
                if len(data) < 12:
                    continue
                first_word = struct.unpack('!H', data[0:2])[0]
                flags = first_word >> 11
                rid   = struct.unpack('!H', data[10:12])[0]
                # Always update session from incoming packets (sofie does this unconditionally)
                pkt_sess = struct.unpack('!H', data[2:4])[0]
                if pkt_sess:
                    self._session = pkt_sess

                # ATEM sent SYN — it reset the connection
                if flags & 0x02:
                    print("ATEM ◀ SYN — ATEM reset connection")
                    self._drop_connection(s)
                    break

                in_order = True
                if (flags & 0x01) and rid:          # RELIABLE → ACK it
                    with self._lock:
                        # Only advance on the next in-order id (wrap-aware).
                        # On a gap, re-ack the last in-order id so the ATEM
                        # retransmits the lost packet.
                        in_order = ((rid - self._last_rid) & 0x7FFF) == 1
                        if in_order:
                            self._last_rid = rid
                        if self._sock:
                            try:
                                self._sock.sendto(self._ack(s, self._last_rid), (self.ip, self.PORT))
                            except Exception:
                                pass

                if in_order:
                    # Parse state updates (PrgI/PrvI/InPr…) — fires on_preview callback
                    self._parse_state_packet(data)
            except (socket.timeout, TimeoutError):
                no_data_ticks += 1
                if no_data_ticks >= 20:   # 10 s of silence → connection lost
                    print(f"ATEM: no data for {no_data_ticks * 0.5:.0f}s — connection lost")
                    self._drop_connection(s)
                    break
            except OSError as e:
                print(f"ATEM keepalive OSError (ignored): {e}")
            except Exception as e:
                print(f"ATEM keepalive error: {e}")
                break
        print("ATEM: keepalive ended")

    def _drop_connection(self, sock) -> None:
        """Close socket and notify controller — no automatic reconnect."""
        with self._lock:
            if self._sock is sock:
                self._sock = None
        try:
            sock.close()
        except Exception:
            pass
        cb = self.on_disconnect
        if cb:
            cb()

    # ── Helpers ───────────────────────────────────────────────────────────────

    def _parse_state_packet(self, data: bytes) -> None:
        """Extract model name and ME count from ATEM state-dump commands."""
        offset = 12  # skip 12-byte UDP header
        while offset + 8 <= len(data):
            length = struct.unpack('!H', data[offset:offset + 2])[0]
            if length < 8 or offset + length > len(data):
                break
            name = data[offset + 4:offset + 8]
            payload = data[offset + 8:offset + length]
            if name == b'_pin' and len(payload) >= 41:
                end = payload.find(b'\x00')
                new_name = payload[:end if end != -1 else 40].decode('ascii', errors='replace').strip()
                if new_name != self.model_name:
                    self.model_name = new_name
                    print(f"  ATEM model: {self.model_name!r}")
            elif name == b'_top' and len(payload) >= 1:
                new_me = max(1, payload[0])
                if new_me != self.me_count:
                    self.me_count = new_me
                    print(f"  ATEM topology: {self.me_count} M/E(s)")
            elif name == b'InPr' and len(payload) >= 22:
                input_id = struct.unpack('!H', payload[0:2])[0]
                end = payload[2:22].find(b'\x00')
                long_name = payload[2:2 + (end if end != -1 else 20)].decode('ascii', errors='replace').strip()
                end2 = payload[22:26].find(b'\x00')
                short_name = payload[22:22 + (end2 if end2 != -1 else 4)].decode('ascii', errors='replace').strip()
                port_type = payload[32] if len(payload) > 32 else 0
                self.inputs[input_id] = {'name': long_name, 'short_name': short_name, 'type': port_type}
            elif name == b'PrgI' and len(payload) >= 4:
                me_idx = payload[0]
                src    = struct.unpack('!H', payload[2:4])[0]
                if self.program.get(me_idx) != src:
                    self.program[me_idx] = src
                    print(f"  PrgI ME{me_idx+1}=source {src}")
                    cb = self.on_program
                    if cb:
                        cb(me_idx, src)
            elif name == b'InCm':
                self.init_complete = True
            elif name == b'PrvI' and len(payload) >= 4:
                me_idx = payload[0]
                src    = struct.unpack('!H', payload[2:4])[0]
                if self.preview.get(me_idx) != src:
                    self.preview[me_idx] = src
                    print(f"  PrvI ME{me_idx+1}=source {src}")
                    cb = self.on_preview
                    if cb:
                        cb(me_idx, src)
            offset += length

    def _build(self, flags: int, payload: bytes = b'', local_id: int = 0,
               ack_id: int = 0, session=None, word4: int = 0) -> bytes:
        length = 12 + len(payload)
        sess = session if session is not None else self._session
        hdr = struct.pack('!HHHHHH',
                          (flags << 11) | length,
                          sess, ack_id, 0, word4, local_id)
        return hdr + payload

    def _ack(self, _sock, rid: int) -> bytes:
        return struct.pack('!HHHHHH',
                           (0x10 << 11) | 12,
                           self._session, rid, 0, 0, 0)


# ── Constants ─────────────────────────────────────────────────────────────────

APP_VERSION = "1.27"   # bump on every release (matches the GitHub commit count)

AUDIO_SAMPLERATE    = 48000
AUDIO_BLOCKSIZE     = 1024
DEFAULT_SILENCE_INPUT = 4   # No audio → Camera 4

# Default rows: channel within the stereo pair (0=L, 1=R), ATEM input
# Device index is set at runtime from the dropdown (defaults to first DVS found)
DEFAULT_ROWS = [
    {"ch": 0, "atem_input": 1, "name": "Camera 1"},
    {"ch": 1, "atem_input": 2, "name": "Camera 2"},
    {"ch": 0, "atem_input": 3, "name": "Camera 3"},
    {"ch": 1, "atem_input": 4, "name": "Camera 4"},
]


# ── Signals ───────────────────────────────────────────────────────────────────

class Signals(QObject):
    levels_updated     = pyqtSignal(list)   # [float] * num_rows
    gates_updated      = pyqtSignal(list)   # ['open'|'releasing'|'closed'] * num_rows
    input_switched     = pyqtSignal(int)    # we triggered a switch
    atem_disconnected  = pyqtSignal()
    atem_connected     = pyqtSignal()
    atem_connect_finished = pyqtSignal(bool)   # manual connect attempt done (ok?)
    automation_changed = pyqtSignal(bool)   # Companion HTTP triggered a toggle
    preview_changed    = pyqtSignal(int, int)  # (me_idx, source) — ATEM preview bus changed
    program_changed    = pyqtSignal(int, int)  # (me_idx, source) — ATEM program bus changed
    log_line           = pyqtSignal(str)    # new log line for the GUI log tab


# ── ATEM Controller ───────────────────────────────────────────────────────────

class ATEMController:

    def __init__(self, on_disconnect=None, on_connect=None, on_preview=None,
                 on_program=None):
        self.atem: ATEMConnection | None = None
        self.connected = False
        self._ip = ""
        self._reconnecting = False
        self._last_disconnect = -9999.0
        self._on_disconnect_cb = on_disconnect   # called on connection drop (from any thread)
        self._on_connect_cb    = on_connect      # called on successful connect/reconnect
        self._on_preview_cb    = on_preview      # called with (me_idx, src) on preview change
        self._on_program_cb    = on_program      # called with (me_idx, src) on program change

    def connect(self, ip: str) -> bool:
        self._ip = ip
        try:
            if self.atem:
                self._silent_disconnect()
            self.atem = ATEMConnection(ip)
            self.atem.on_disconnect = self._handle_drop
            self.atem.on_preview    = self._on_preview_cb
            self.atem.on_program    = self._on_program_cb
            self.atem.connect()
            self.connected = True
            if self._on_connect_cb:
                self._on_connect_cb()
            return True
        except Exception as e:
            print(f"ATEM connect failed: {e}")
            self.connected = False
            return False

    def disconnect(self):
        self._ip = ""   # manual disconnect — stops the auto-reconnect loop
        self._silent_disconnect()
        self.atem = None
        self.connected = False

    def _silent_disconnect(self):
        """Close existing connection without triggering the drop callback."""
        try:
            if self.atem:
                self.atem.on_disconnect = None
                self.atem.disconnect()
        except Exception:
            pass

    def _handle_drop(self):
        """Called from keepalive thread when ATEM drops the connection."""
        self.connected = False
        if self._on_disconnect_cb:
            self._on_disconnect_cb()
        # Auto-reconnect after a short pause
        if not self._reconnecting and self._ip:
            self._reconnecting = True
            threading.Thread(target=self._auto_reconnect, daemon=True).start()

    def _auto_reconnect(self):
        """Retry until connected, or until a manual disconnect clears _ip."""
        try:
            attempt = 0
            while self._ip and not self.connected:
                time.sleep(3)
                if not self._ip or self.connected:
                    break   # manually disconnected or reconnected while waiting
                attempt += 1
                if self.connect(self._ip):
                    break
                print(f"ATEM auto-reconnect attempt {attempt} failed — retrying in 3s")
        finally:
            self._reconnecting = False

    def switch_program(self, input_number: int, me: int = 0) -> bool:
        if not self.connected or self.atem is None:
            return False
        return self.atem.switch_program(input_number, me)

    def switch_preview(self, input_number: int, me: int = 0) -> bool:
        if not self.connected or self.atem is None:
            return False
        return self.atem.switch_preview(input_number, me)


# ── Audio Engine ──────────────────────────────────────────────────────────────

class AudioEngine:
    def __init__(self, signals: Signals):
        self.signals = signals
        self.atem = ATEMController(
            on_disconnect=self._on_atem_drop,
            on_connect=self._on_atem_connect,
            on_preview=self._on_atem_preview,
            on_program=self._on_atem_program,
        )

        self.running = False
        self.automation_active = False
        self._streams: dict = {}   # device_idx → sd.InputStream

        # Config (list per row) — updated from GUI before start
        # mic_device_channels: list of (device_index, channel_within_device)
        self.mic_device_channels: list[tuple[int, int]] = []
        self.mic_atem_inputs:  list[int]   = []
        self.mic_weights:      list[float] = []   # priority weight per row (1.0 = normal)
        self.gate_thresholds:  list[float] = []   # level to open gate
        self.gate_attacks:     list[float] = []   # attack time (s) per channel
        self.gate_releases:    list[float] = []   # release time (s) per channel
        self.silence_input  = DEFAULT_SILENCE_INPUT
        self.holdoff        = 0.8
        self.silence_delay  = 2.0
        self.silence_loop_enabled = False    # cycle cameras while everything is quiet
        self.silence_loop_min     = 5.0      # random hold time per camera is picked
        self.silence_loop_max     = 8.0      # between these two bounds (seconds)
        self.extra_loop_inputs: list[int] = []   # loop cameras without a mic row
        self.me_index       = 0   # 0-based M/E index for auto-switching

        self._levels: list[float] = []
        self._levels_lock = threading.Lock()
        # Gate states: 'closed' → 'attack' → 'open' → 'releasing' → 'closed'
        self._gate_states:        list[str]   = []
        self._gate_attack_until:  list[float] = []
        self._gate_release_until: list[float] = []
        self._current_input: int | None = None
        self._last_switch_time = 0.0
        self._silence_since: float | None = None
        self._silence_loop_hold: float | None = None   # current random hold time

    def _on_atem_drop(self):
        self.signals.atem_disconnected.emit()

    def _on_atem_connect(self):
        self.signals.atem_connected.emit()

    def _on_atem_preview(self, me_idx: int, src: int):
        self.signals.preview_changed.emit(me_idx, src)

    def _on_atem_program(self, me_idx: int, src: int):
        # Track the real program source so automation stays in sync with
        # switches made elsewhere (PGM buttons, ATEM panel, other software)
        if me_idx == self.me_index:
            self._current_input = src
        self.signals.program_changed.emit(me_idx, src)

    def start_audio(self):
        self.stop_audio()
        n = len(self.mic_device_channels)
        with self._levels_lock:
            self._levels = [0.0] * n
        self._gate_states        = ['closed'] * n
        self._gate_attack_until  = [0.0]     * n
        self._gate_release_until = [0.0]     * n

        # Group rows by device so we open one stream per device
        groups: dict[int, list[tuple[int, int]]] = defaultdict(list)
        for row_idx, (dev_idx, ch) in enumerate(self.mic_device_channels):
            groups[dev_idx].append((row_idx, ch))

        self.running = True
        for dev_idx, row_list in groups.items():
            max_ch = max(ch for _, ch in row_list) + 1
            try:
                dev_info = sd.query_devices(dev_idx)
                max_ch = min(max_ch, int(dev_info['max_input_channels']))
            except Exception:
                pass

            def make_callback(rows_for_device):
                def cb(indata, frames, time_info, status):
                    with self._levels_lock:
                        for row_idx, ch in rows_for_device:
                            if ch < indata.shape[1]:
                                self._levels[row_idx] = float(np.abs(indata[:, ch]).mean())
                            else:
                                self._levels[row_idx] = 0.0
                return cb

            try:
                stream = sd.InputStream(
                    device=dev_idx,
                    channels=max_ch,
                    samplerate=AUDIO_SAMPLERATE,
                    blocksize=AUDIO_BLOCKSIZE,
                    callback=make_callback(row_list),
                )
                stream.start()
                self._streams[dev_idx] = stream
            except Exception as e:
                print(f"Error opening device {dev_idx}: {e}")

        threading.Thread(target=self._switcher_loop, daemon=True).start()

    def stop_audio(self):
        self.running = False
        for stream in self._streams.values():
            try:
                stream.stop()
                stream.close()
            except Exception:
                pass
        self._streams.clear()

    def _switcher_loop(self):
        last_emit = 0.0
        while self.running:
            time.sleep(0.04)
            now = time.time()

            with self._levels_lock:
                levels = self._levels[:]

            n = len(levels)

            # ── Per-channel gate state machine ────────────────────────────────
            # closed → (signal ≥ thr) → attack → (held for attack_time) → open
            # open   → (signal < thr) → releasing → (after release_time) → closed
            # releasing → (signal ≥ thr) → open  (re-trigger during release)
            # attack  → (signal < thr) → closed  (abort attack)
            for i in range(n):
                lvl = levels[i]
                thr = self.gate_thresholds[i] if i < len(self.gate_thresholds) else 0.02
                atk = self.gate_attacks[i]    if i < len(self.gate_attacks)    else 0.05
                rel = self.gate_releases[i]   if i < len(self.gate_releases)   else 0.5
                s   = self._gate_states[i]

                if s == 'closed':
                    if lvl >= thr:
                        self._gate_states[i]       = 'attack'
                        self._gate_attack_until[i] = now + atk
                elif s == 'attack':
                    if lvl < thr:
                        self._gate_states[i] = 'closed'       # signal dropped, abort
                    elif now >= self._gate_attack_until[i]:
                        self._gate_states[i]        = 'open'  # held long enough → open
                        self._gate_release_until[i] = now + rel
                elif s == 'open':
                    if lvl >= thr:
                        self._gate_release_until[i] = now + rel  # refresh release timer
                    else:
                        self._gate_states[i] = 'releasing'
                elif s == 'releasing':
                    if lvl >= thr:
                        self._gate_states[i]        = 'open'  # re-triggered
                        self._gate_release_until[i] = now + rel
                    elif now >= self._gate_release_until[i]:
                        self._gate_states[i] = 'closed'

            # Emit to GUI at ~25 Hz
            if now - last_emit >= 0.04:
                self.signals.levels_updated.emit(levels)
                self.signals.gates_updated.emit(list(self._gate_states))
                last_emit = now

            if not self.automation_active:
                continue

            # Only switch TO a channel whose gate is fully open (loudest wins)
            open_channels = [(i, levels[i]) for i in range(n)
                             if self._gate_states[i] == 'open']

            if open_channels:
                self._silence_since = None
                # Weighted loudness: priority weight biases which camera wins
                # when several gates are open at the same time
                def weighted(pair):
                    i, lvl = pair
                    w = self.mic_weights[i] if i < len(self.mic_weights) else 1.0
                    return lvl * w
                loudest = max(open_channels, key=weighted)[0]
                if loudest >= len(self.mic_atem_inputs):
                    continue   # a row was removed mid-run — skip until state is consistent
                target = self.mic_atem_inputs[loudest]
            elif any(s == 'releasing' for s in self._gate_states):
                # Someone is in release — hold current camera, don't cut yet
                continue
            else:
                # All gates closed → silence timer
                if self._silence_since is None:
                    self._silence_since = now
                if (now - self._silence_since) < self.silence_delay:
                    continue
                target = self.silence_input
                if self.silence_loop_enabled:
                    # Wander: while silence lasts, hold each camera for a random
                    # time between loop min/max, then jump to a random *other*
                    # camera — feels like a human operator instead of a pattern
                    loop_inputs = [self.silence_input]
                    for inp in self.extra_loop_inputs:
                        if inp not in loop_inputs:
                            loop_inputs.append(inp)
                    if self._current_input in loop_inputs:
                        if self._silence_loop_hold is None:
                            self._silence_loop_hold = random.uniform(
                                self.silence_loop_min, self.silence_loop_max)
                        if (now - self._last_switch_time) >= self._silence_loop_hold:
                            others = [x for x in loop_inputs if x != self._current_input]
                            target = random.choice(others) if others else self._current_input
                        else:
                            target = self._current_input   # hold until the time is up
                    else:
                        # Entering the loop — start at a random camera
                        target = random.choice(loop_inputs)

            if target == self._current_input:
                continue
            if (now - self._last_switch_time) < self.holdoff:
                continue

            if self.atem.switch_program(target, self.me_index):
                self._current_input = target
                self._last_switch_time = now
                self._silence_loop_hold = None   # pick a fresh random hold time
                self.signals.input_switched.emit(target)


# ── Companion HTTP Server ─────────────────────────────────────────────────────

class CompanionServer:
    """
    Tiny HTTP server so Bitfocus Companion (and Stream Deck) can toggle
    auto-switching over the local network.

    Endpoints
    ---------
    GET  /status              → {"automation_active": true/false}
    POST /automation/on       → enable auto-switching
    POST /automation/off      → disable auto-switching
    POST /automation/toggle   → flip current state
    """

    def __init__(self, engine: 'AudioEngine', signals: 'Signals'):
        self._engine  = engine
        self._signals = signals
        self._server: HTTPServer | None = None

    def start(self, port: int) -> bool:
        self.stop()
        engine  = self._engine
        signals = self._signals

        def _solid_png(r: int, g: int, b: int, w: int = 72, h: int = 58) -> bytes:
            """Generate a minimal solid-color PNG using only stdlib."""
            def _chunk(tag: bytes, data: bytes) -> bytes:
                crc = zlib.crc32(tag + data) & 0xFFFFFFFF
                return struct.pack('>I', len(data)) + tag + data + struct.pack('>I', crc)
            sig  = b'\x89PNG\r\n\x1a\n'
            ihdr = _chunk(b'IHDR', struct.pack('>IIBBBBB', w, h, 8, 2, 0, 0, 0))
            row  = b'\x00' + bytes([r, g, b]) * w   # filter=None + RGB pixels
            idat = _chunk(b'IDAT', zlib.compress(row * h, 9))
            iend = _chunk(b'IEND', b'')
            return sig + ihdr + idat + iend

        _PNG_ON  = _solid_png(0,   180, 80)   # green
        _PNG_OFF = _solid_png(200, 40,  40)   # red

        class _Handler(BaseHTTPRequestHandler):
            def log_message(self, fmt, *args):
                pass  # suppress HTTP request logging

            def _json(self, code: int, data: dict):
                body = json.dumps(data).encode()
                self.send_response(code)
                self.send_header('Content-Type', 'application/json')
                self.send_header('Content-Length', str(len(body)))
                self.end_headers()
                self.wfile.write(body)

            def _png(self, data: bytes):
                self.send_response(200)
                self.send_header('Content-Type', 'image/png')
                self.send_header('Content-Length', str(len(data)))
                self.send_header('Cache-Control', 'no-store')
                self.end_headers()
                self.wfile.write(data)

            def do_GET(self):
                if self.path == '/status':
                    self._json(200, {'automation_active': engine.automation_active})
                elif self.path == '/status/image':
                    self._png(_PNG_ON if engine.automation_active else _PNG_OFF)
                else:
                    self._json(404, {'error': 'not found'})

            def do_POST(self):
                if self.path == '/automation/on':
                    new_state = True
                elif self.path == '/automation/off':
                    new_state = False
                elif self.path == '/automation/toggle':
                    new_state = not engine.automation_active
                else:
                    self._json(404, {'error': 'not found'})
                    return
                engine.automation_active = new_state
                signals.automation_changed.emit(new_state)
                self._json(200, {'automation_active': new_state})

        try:
            self._server = HTTPServer(('0.0.0.0', port), _Handler)
            threading.Thread(target=self._server.serve_forever, daemon=True).start()
            print(f"Companion HTTP server listening on port {port}")
            return True
        except Exception as e:
            print(f"Companion HTTP server failed to start on port {port}: {e}")
            self._server = None
            return False

    def stop(self):
        if self._server:
            self._server.shutdown()
            self._server = None
            print("Companion HTTP server stopped")


# ── Main Window ───────────────────────────────────────────────────────────────

class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("HBS – ATEM Auto Switcher")
        self.setMinimumWidth(700)

        self.signals = Signals()
        self.engine = AudioEngine(self.signals)
        self.companion = CompanionServer(self.engine, self.signals)
        self.signals.levels_updated.connect(self._on_levels)
        self.signals.gates_updated.connect(self._on_gates)
        self.signals.input_switched.connect(self._on_switched)
        self.signals.atem_disconnected.connect(self._on_atem_disconnected)
        self.signals.atem_connected.connect(self._on_atem_connected)
        self.signals.atem_connect_finished.connect(self._on_connect_finished)
        self.signals.automation_changed.connect(self._on_automation_changed)
        self.signals.preview_changed.connect(self._on_preview_changed)
        self.signals.program_changed.connect(self._on_program_changed)
        self.signals.log_line.connect(self._on_log_line)
        sys.stdout._gui_cb = self.signals.log_line.emit

        self._input_devices: list[tuple[int, str]] = []   # (device_idx, label)
        # Each entry: (row_widget, device_combo, ch_spin, inp_spin, bar)
        self._mic_rows: list[tuple] = []
        self._pvw_buttons: dict[int, QPushButton] = {}   # inputId → PVW button
        self._pgm_buttons: dict[int, QPushButton] = {}   # inputId → PGM button
        self.extra_loop_inputs: list[int] = []           # loop cameras without a mic row
        self._extra_chips: list[QPushButton] = []

        self._build_ui()
        self._refresh_devices()
        self._load_settings()

    # ── UI ────────────────────────────────────────────────────────────────────

    def _build_ui(self):
        root = QWidget()
        self.setCentralWidget(root)
        layout = QVBoxLayout(root)
        layout.setSpacing(10)
        layout.setContentsMargins(0, 0, 0, 14)

        # ── HBS brand header ──────────────────────────────────────────────────
        header = QWidget()
        header.setFixedHeight(52)
        header.setStyleSheet("background: #141414;")
        header_row = QHBoxLayout(header)
        header_row.setContentsMargins(16, 0, 16, 0)
        header_row.setSpacing(0)

        hbs_lbl = QLabel("//HBS")
        hbs_lbl.setFont(QFont("Arial", 20, QFont.Weight.Bold))
        hbs_lbl.setStyleSheet("color: #d4d4d4; letter-spacing: 3px;")
        header_row.addWidget(hbs_lbl)

        divider = QLabel()
        divider.setFixedSize(1, 28)
        divider.setStyleSheet("background: #444; margin: 0 12px;")
        header_row.addSpacing(12)
        header_row.addWidget(divider)
        header_row.addSpacing(12)

        title_lbl = QLabel("ATEM Auto Switcher")
        title_lbl.setFont(QFont("Arial", 11))
        title_lbl.setStyleSheet("color: #909090;")
        header_row.addWidget(title_lbl)

        version_lbl = QLabel(f"v{APP_VERSION}")
        version_lbl.setStyleSheet("color: #555; font-size: 10px; margin-left: 8px;")
        header_row.addWidget(version_lbl)

        header_row.addStretch()

        help_btn = QPushButton("?")
        help_btn.setFixedSize(22, 22)
        help_btn.setToolTip("Open documentation")
        help_btn.setStyleSheet("""
            QPushButton {
                background: #2a2a2a; color: #888; border: 1px solid #444;
                border-radius: 11px; font-weight: bold; font-size: 12px; padding: 0;
            }
            QPushButton:hover { background: #3a3a3a; color: #ccc; border-color: #666; }
        """)
        help_btn.clicked.connect(lambda: QDesktopServices.openUrl(
            QUrl("https://github.com/nickfromsad/HBS---Atem-Auto-Switcher#readme")
        ))
        header_row.addWidget(help_btn)
        header_row.addSpacing(10)

        url_lbl = QLabel("hofbroadcast.nl")
        url_lbl.setStyleSheet("color: #555; font-size: 10px;")
        header_row.addWidget(url_lbl)

        layout.addWidget(header)

        # add side margins for everything below the header
        content = QWidget()
        content_layout = QVBoxLayout(content)
        content_layout.setSpacing(10)
        content_layout.setContentsMargins(14, 8, 14, 0)
        layout.addWidget(content)
        layout = content_layout   # shadow outer layout so the rest of the method uses this

        # ── ATEM connection ───────────────────────────────────────────────────
        atem_box = QGroupBox("ATEM Connection")
        atem_row = QHBoxLayout(atem_box)
        atem_row.addWidget(QLabel("IP:"))
        self.ip_edit = QLineEdit("192.168.10.240")
        self.ip_edit.setMaximumWidth(130)
        atem_row.addWidget(self.ip_edit)
        self.connect_btn = QPushButton("Connect")
        self.connect_btn.setFixedWidth(90)
        self.connect_btn.clicked.connect(self._toggle_atem)
        atem_row.addWidget(self.connect_btn)
        self.atem_status = QLabel("● Disconnected")
        self.atem_status.setStyleSheet("color: #ff4444; font-weight: bold;")
        atem_row.addWidget(self.atem_status)
        atem_row.addStretch()
        layout.addWidget(atem_box)

        # ── Audio → Camera mapping ────────────────────────────────────────────
        mics_box = QGroupBox("Channels")
        mics_outer = QVBoxLayout(mics_box)

        # Single QGridLayout for both headers and data rows — guarantees column alignment
        self._rows_grid = QGridLayout()
        self._rows_grid.setHorizontalSpacing(6)
        self._rows_grid.setVerticalSpacing(4)
        self._rows_grid.setContentsMargins(0, 0, 0, 0)
        # Col 0=tally  1=name  2=device(stretch)  3=ch  4=gate  5=atk  6=rel
        # 7=camera(stretch)  8=prio  9=level  10=state
        self._rows_grid.setColumnStretch(2, 1)
        self._rows_grid.setColumnStretch(7, 1)
        self._rows_grid.setColumnMinimumWidth(0, 6)
        self._rows_grid.setColumnMinimumWidth(1, 90)
        self._rows_grid.setColumnMinimumWidth(3, 38)
        self._rows_grid.setColumnMinimumWidth(4, 72)
        self._rows_grid.setColumnMinimumWidth(5, 52)
        self._rows_grid.setColumnMinimumWidth(6, 52)
        self._rows_grid.setColumnMinimumWidth(8, 68)
        self._rows_grid.setColumnMinimumWidth(9, 180)
        self._rows_grid.setColumnMinimumWidth(10, 38)

        # Header row (grid row 0)
        for col, text in enumerate(["", "Name", "Device", "Ch", "Gate", "Atk", "Rel", "Camera", "Prio", "Level", "State"]):
            if not text:
                continue
            lbl = QLabel(text)
            lbl.setStyleSheet("color: #888; font-size: 11px;")
            self._rows_grid.addWidget(lbl, 0, col)

        grid_w = QWidget()
        grid_w.setLayout(self._rows_grid)
        mics_outer.addWidget(grid_w)

        btn_row = QHBoxLayout()
        add_btn = QPushButton("+ Add")
        add_btn.setFixedWidth(70)
        add_btn.clicked.connect(lambda: self._add_mic_row())
        btn_row.addWidget(add_btn)
        rem_btn = QPushButton("− Remove")
        rem_btn.setFixedWidth(75)
        rem_btn.clicked.connect(self._remove_mic_row)
        btn_row.addWidget(rem_btn)
        refresh_btn = QPushButton("Refresh")
        refresh_btn.setFixedWidth(70)
        refresh_btn.clicked.connect(self._refresh_devices)
        btn_row.addWidget(refresh_btn)
        btn_row.addSpacing(16)
        self.audio_btn = QPushButton("▶  Start")
        self.audio_btn.setFixedWidth(80)
        self.audio_btn.clicked.connect(self._toggle_audio)
        btn_row.addWidget(self.audio_btn)
        btn_row.addStretch()
        mics_outer.addLayout(btn_row)

        layout.addWidget(mics_box)

        # ── Bottom tabs: Settings | Test Switch ───────────────────────────────
        bottom_tabs = QTabWidget()

        # Settings tab
        cfg_tab = QWidget()
        cfg_outer = QVBoxLayout(cfg_tab)
        cfg_outer.setContentsMargins(10, 10, 10, 10)
        cfg_outer.setSpacing(0)

        # A vertical stack: label+control row, then a full-width description
        # under each setting. (A QVBoxLayout sizes word-wrapped labels reliably;
        # QGridLayout under-sizes them so the texts overlap or clip.)
        cfg = QVBoxLayout()
        cfg.setSpacing(2)

        def _desc(text):
            lbl = QLabel(text)
            lbl.setStyleSheet("color: #777; font-size: 11px; padding-bottom: 10px;")
            lbl.setWordWrap(True)
            return lbl

        def _setting(label_text, control, desc_text):
            row = QHBoxLayout()
            lbl = QLabel(label_text)
            lbl.setFixedWidth(150)
            row.addWidget(lbl)
            row.addWidget(control)
            row.addStretch()
            cfg.addLayout(row)
            cfg.addWidget(_desc(desc_text))

        # M/E
        self.me_spin = QSpinBox()
        self.me_spin.setRange(1, 4)
        self.me_spin.setValue(1)
        self.me_spin.setFixedWidth(55)
        self.me_spin.valueChanged.connect(lambda _v: self._refresh_bus_highlights())
        _setting("M/E for auto-switching:", self.me_spin,
                 "Which M/E bus the switcher controls. M/E 1 is the main program output. Most setups only have one M/E.")

        # No-audio camera
        self.silence_combo = QComboBox()
        self.silence_combo.setMinimumWidth(160)
        for i in range(1, 21):
            self.silence_combo.addItem(str(i), i)
        idx = self.silence_combo.findData(DEFAULT_SILENCE_INPUT)
        if idx >= 0:
            self.silence_combo.setCurrentIndex(idx)
        sil_w = QWidget()
        sil_row = QHBoxLayout(sil_w)
        sil_row.setContentsMargins(0, 0, 0, 0)
        sil_row.setSpacing(6)
        sil_row.addWidget(self.silence_combo)
        self.silence_loop_check = QCheckBox("Loop every")
        self.silence_loop_check.setToolTip(
            "While everything stays silent, keep jumping between the loop cameras\n"
            "instead of staying on the no-audio camera. Each camera is held for a\n"
            "random time between the two values."
        )
        sil_row.addWidget(self.silence_loop_check)

        def _loop_spin(value):
            sp = QDoubleSpinBox()
            sp.setRange(1.0, 120.0)
            sp.setValue(value)
            sp.setSingleStep(1.0)
            sp.setDecimals(0)
            sp.setSuffix(" s")
            sp.setFixedWidth(60)
            return sp

        self.silence_loop_min_spin = _loop_spin(5.0)
        sil_row.addWidget(self.silence_loop_min_spin)
        sil_row.addWidget(QLabel("–"))
        self.silence_loop_max_spin = _loop_spin(8.0)
        sil_row.addWidget(self.silence_loop_max_spin)
        sil_row.addStretch()
        _setting("No-audio camera:", sil_w,
                 "Camera to cut to when all microphones are silent and the silence delay has expired. With Loop enabled, the switcher keeps jumping between this camera and the Extra loop cameras below, holding each for a random time between the two values, until audio returns.")

        # Extra loop cameras (no mic row)
        extra_w = QWidget()
        extra_row = QHBoxLayout(extra_w)
        extra_row.setContentsMargins(0, 0, 0, 0)
        extra_row.setSpacing(6)
        self.extra_loop_combo = QComboBox()
        self.extra_loop_combo.setMinimumWidth(130)
        for i in range(1, 21):
            self.extra_loop_combo.addItem(str(i), i)
        extra_row.addWidget(self.extra_loop_combo)
        extra_add_btn = QPushButton("+ Add")
        extra_add_btn.setFixedWidth(60)
        extra_add_btn.clicked.connect(self._add_extra_loop_cam)
        extra_row.addWidget(extra_add_btn)
        self._extra_chips_row = extra_row
        extra_row.addStretch()
        _setting("Extra loop cameras:", extra_w,
                 "The cameras the silence loop cycles through, together with the no-audio camera. Add wide or beauty shots here — any camera works, with or without a microphone row. Click an added camera to remove it again.")

        # Holdoff
        self.holdoff_spin = QDoubleSpinBox()
        self.holdoff_spin.setRange(0.0, 5.0)
        self.holdoff_spin.setValue(0.8)
        self.holdoff_spin.setSingleStep(0.1)
        self.holdoff_spin.setDecimals(1)
        self.holdoff_spin.setFixedWidth(55)
        _setting("Switch holdoff (s):", self.holdoff_spin,
                 "Minimum time between two camera switches. Prevents rapid cutting when multiple mics open at the same time. 0.5–1.0 s is a good starting point.")

        # Silence delay
        self.silence_delay_spin = QDoubleSpinBox()
        self.silence_delay_spin.setRange(0.0, 15.0)
        self.silence_delay_spin.setValue(2.0)
        self.silence_delay_spin.setSingleStep(0.5)
        self.silence_delay_spin.setDecimals(1)
        self.silence_delay_spin.setFixedWidth(55)
        _setting("Silence delay (s):", self.silence_delay_spin,
                 "How long all mics must be silent before cutting to the no-audio camera. Gives speakers a natural pause without immediately switching away.")

        # PVW automation link
        link_w = QWidget()
        link_row = QHBoxLayout(link_w)
        link_row.setContentsMargins(0, 0, 0, 0)
        link_row.setSpacing(6)
        self.pvw_link_check = QCheckBox()
        self.pvw_link_check.setToolTip("Enable PVW-controlled automation")
        link_row.addWidget(self.pvw_link_check)
        self.pvw_link_combo = QComboBox()
        self.pvw_link_combo.setMinimumWidth(130)
        for i in range(1, 21):
            self.pvw_link_combo.addItem(str(i), i)
        link_row.addWidget(self.pvw_link_combo)
        link_row.addStretch()
        _setting("PVW automation camera:", link_w,
                 "When checked: putting this camera on preview (PVW) turns automation ON; putting any other camera on preview turns automation OFF. Works from the PVW buttons below and from the ATEM panel itself.")

        cfg_outer.addLayout(cfg)

        # ── Companion integration ──────────────────────────────────────────────
        companion_box = QGroupBox("Companion / Stream Deck Integration")
        companion_row = QHBoxLayout(companion_box)
        companion_row.setSpacing(10)

        self.companion_enable_btn = QPushButton("Enable")
        self.companion_enable_btn.setCheckable(True)
        self.companion_enable_btn.setFixedWidth(75)
        self.companion_enable_btn.clicked.connect(self._toggle_companion)
        companion_row.addWidget(self.companion_enable_btn)

        companion_row.addWidget(QLabel("Port:"))
        self.companion_port_spin = QSpinBox()
        self.companion_port_spin.setRange(1024, 65535)
        self.companion_port_spin.setValue(8765)
        self.companion_port_spin.setFixedWidth(70)
        companion_row.addWidget(self.companion_port_spin)

        self.companion_status = QLabel("● Stopped")
        self.companion_status.setStyleSheet("color: #ff4444; font-weight: bold;")
        companion_row.addWidget(self.companion_status)
        companion_row.addStretch()

        cfg_outer.addWidget(companion_box)
        cfg_outer.addStretch()
        bottom_tabs.addTab(cfg_tab, "Settings")

        # ── Miscellaneous tab ─────────────────────────────────────────────────
        misc_tab = QWidget()
        misc_layout = QVBoxLayout(misc_tab)
        misc_layout.setContentsMargins(8, 8, 8, 8)
        misc_layout.setSpacing(8)

        # Test switch row
        test_row = QHBoxLayout()
        test_row.setSpacing(10)
        test_row.addWidget(QLabel("Manual switch — M/E:"))
        self.test_me_spin = QSpinBox()
        self.test_me_spin.setRange(1, 4)
        self.test_me_spin.setValue(1)
        self.test_me_spin.setFixedWidth(50)
        test_row.addWidget(self.test_me_spin)
        test_row.addWidget(QLabel("Input:"))
        self.test_inp_spin = QSpinBox()
        self.test_inp_spin.setRange(1, 20)
        self.test_inp_spin.setValue(1)
        self.test_inp_spin.setFixedWidth(55)
        test_row.addWidget(self.test_inp_spin)
        test_btn = QPushButton("Send")
        test_btn.setFixedWidth(70)
        test_btn.clicked.connect(self._test_switch)
        test_row.addWidget(test_btn)
        self.last_switched_label = QLabel("Last switched: —")
        self.last_switched_label.setStyleSheet("color: #888; font-size: 11px;")
        test_row.addWidget(self.last_switched_label)
        test_row.addStretch()
        misc_layout.addLayout(test_row)

        # Switching presets — editable
        presets_box = QGroupBox("Switching Presets")
        presets_grid = QGridLayout(presets_box)
        presets_grid.setHorizontalSpacing(10)
        presets_grid.setVerticalSpacing(6)
        for col, hdr in enumerate(["", "Attack (s)", "Release (s)", "Holdoff (s)", ""]):
            lbl = QLabel(hdr)
            lbl.setStyleSheet("color: #aaa; font-size: 11px;")
            presets_grid.addWidget(lbl, 0, col)

        self._preset_spins = []   # list of (atk_spin, rel_spin, hld_spin) per preset
        for row_i, (pname, atk, rel, hld) in enumerate([
            ("Fast",   0.01, 0.1, 0.2),
            ("Medium", 0.05, 0.5, 0.8),
            ("Slow",   0.15, 1.5, 1.5),
        ], start=1):
            presets_grid.addWidget(QLabel(pname), row_i, 0)

            atk_spin = QDoubleSpinBox()
            atk_spin.setRange(0.0, 2.0)
            atk_spin.setValue(atk)
            atk_spin.setSingleStep(0.01)
            atk_spin.setDecimals(2)
            atk_spin.setFixedWidth(65)
            presets_grid.addWidget(atk_spin, row_i, 1)

            rel_spin = QDoubleSpinBox()
            rel_spin.setRange(0.0, 10.0)
            rel_spin.setValue(rel)
            rel_spin.setSingleStep(0.1)
            rel_spin.setDecimals(1)
            rel_spin.setFixedWidth(65)
            presets_grid.addWidget(rel_spin, row_i, 2)

            hld_spin = QDoubleSpinBox()
            hld_spin.setRange(0.0, 5.0)
            hld_spin.setValue(hld)
            hld_spin.setSingleStep(0.1)
            hld_spin.setDecimals(1)
            hld_spin.setFixedWidth(65)
            presets_grid.addWidget(hld_spin, row_i, 3)

            apply_btn = QPushButton(f"Apply {pname}")
            apply_btn.setFixedWidth(90)
            apply_btn.clicked.connect(
                lambda checked, a=atk_spin, r=rel_spin, h=hld_spin:
                    self._apply_preset(a.value(), r.value(), h.value())
            )
            presets_grid.addWidget(apply_btn, row_i, 4)
            self._preset_spins.append((atk_spin, rel_spin, hld_spin))

        misc_layout.addWidget(presets_box)
        misc_layout.addStretch()
        bottom_tabs.addTab(misc_tab, "Miscellaneous")

        # ── Log tab ───────────────────────────────────────────────────────────
        log_tab = QWidget()
        log_layout = QVBoxLayout(log_tab)
        log_layout.setContentsMargins(4, 4, 4, 4)
        self._log_view = QPlainTextEdit()
        self._log_view.setReadOnly(True)
        self._log_view.setMaximumBlockCount(1000)
        self._log_view.setStyleSheet("""
            QPlainTextEdit {
                background: #111; color: #b0b0b0;
                border: none; font-family: monospace; font-size: 11px;
            }
        """)
        log_layout.addWidget(self._log_view)
        bottom_tabs.addTab(log_tab, "Log")

        layout.addWidget(bottom_tabs)

        # ── Program / Preview bus rows ────────────────────────────────────────
        self.bus_box = QGroupBox("Program / Preview Bus  (click to show/hide)")
        self.bus_box.setCheckable(True)
        self.bus_box.setChecked(True)
        bus_outer = QVBoxLayout(self.bus_box)
        bus_outer.setContentsMargins(8, 4, 8, 8)
        self._bus_content = QWidget()
        bus_outer.addWidget(self._bus_content)
        self.bus_box.toggled.connect(self._bus_content.setVisible)
        bus_h = QHBoxLayout(self._bus_content)
        bus_h.setContentsMargins(0, 0, 0, 0)
        bus_h.setSpacing(6)

        # Fixed PGM/PVW labels on the left — the button rows scroll horizontally,
        # so the panel height stays constant no matter how many inputs the ATEM has
        labels_v = QVBoxLayout()
        labels_v.setSpacing(6)
        for tag, color in (("PGM", "#ff5555"), ("PVW", "#00cc55")):
            lbl = QLabel(tag)
            lbl.setFixedSize(36, self._BUS_BTN_H)
            lbl.setStyleSheet(f"color: {color}; font-weight: bold; font-size: 12px;")
            labels_v.addWidget(lbl)
        labels_v.addStretch()
        bus_h.addLayout(labels_v)

        self._pgm_row = QHBoxLayout()
        self._pvw_row = QHBoxLayout()
        rows_w = QWidget()
        rows_v = QVBoxLayout(rows_w)
        rows_v.setContentsMargins(0, 0, 0, 0)
        rows_v.setSpacing(6)
        for row in (self._pgm_row, self._pvw_row):
            row.setContentsMargins(0, 0, 0, 0)
            row.setSpacing(6)
            row.addStretch()
            rows_v.addLayout(row)
        rows_v.addStretch()

        bus_scroll = QScrollArea()
        bus_scroll.setWidgetResizable(True)
        bus_scroll.setFrameShape(QFrame.Shape.NoFrame)
        bus_scroll.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        bus_scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        bus_scroll.setWidget(rows_w)
        # 2 button rows + spacing + room for the scrollbar
        bus_scroll.setFixedHeight(self._BUS_BTN_H * 2 + 6 + 12)
        bus_h.addWidget(bus_scroll, 1)

        layout.addWidget(self.bus_box)
        self._rebuild_bus_buttons()

        # ── Automation toggle ─────────────────────────────────────────────────
        self.auto_btn = QPushButton("AUTOMATION  OFF")
        self.auto_btn.setCheckable(True)
        self.auto_btn.setMinimumHeight(65)
        self.auto_btn.setFont(QFont("Arial", 15, QFont.Weight.Bold))
        self.auto_btn.setStyleSheet(BTN_STYLE_OFF)
        self.auto_btn.toggled.connect(self._toggle_automation)
        layout.addWidget(self.auto_btn)

    def _load_settings(self):
        rows = DEFAULT_ROWS
        try:
            with open(_SETTINGS_FILE, 'r', encoding='utf-8') as f:
                s = json.load(f)
            self.ip_edit.setText(s.get('atem_ip', self.ip_edit.text()))
            self.me_spin.setValue(s.get('me', 1))
            self.holdoff_spin.setValue(s.get('holdoff', 0.8))
            self.silence_delay_spin.setValue(s.get('silence_delay', 2.0))
            self.silence_loop_check.setChecked(s.get('silence_loop', False))
            # fall back to the old single-interval key from earlier versions
            old_iv = s.get('silence_loop_interval', 5.0)
            self.silence_loop_min_spin.setValue(s.get('silence_loop_min', old_iv))
            self.silence_loop_max_spin.setValue(s.get('silence_loop_max', max(old_iv, 8.0)))
            self.extra_loop_inputs = [int(x) for x in s.get('extra_loop_inputs', [])]
            self._rebuild_extra_chips()
            sil = s.get('silence_input', DEFAULT_SILENCE_INPUT)
            idx = self.silence_combo.findData(sil)
            if idx >= 0:
                self.silence_combo.setCurrentIndex(idx)
            rows = s.get('rows', DEFAULT_ROWS)
            for i, (a, r, h) in enumerate(s.get('presets', [])):
                if i < len(self._preset_spins):
                    self._preset_spins[i][0].setValue(a)
                    self._preset_spins[i][1].setValue(r)
                    self._preset_spins[i][2].setValue(h)
            if not s.get('bus_panel_open', True):
                self.bus_box.setChecked(False)
                self._bus_content.setVisible(False)
            self.pvw_link_check.setChecked(s.get('pvw_link_enabled', False))
            pvw_inp = s.get('pvw_link_input', 1)
            idx = self.pvw_link_combo.findData(pvw_inp)
            if idx >= 0:
                self.pvw_link_combo.setCurrentIndex(idx)
            self.companion_port_spin.setValue(s.get('companion_port', 8765))
            if s.get('companion_enabled', False):
                self.companion_enable_btn.setChecked(True)
                self._toggle_companion(True)
            print(f"Settings loaded from {_SETTINGS_FILE}")
        except FileNotFoundError:
            pass
        except Exception as e:
            print(f"Settings load error: {e}")
        for r in rows:
            self._add_mic_row(
                ch=r.get('ch', 0),
                atem_input=r.get('atem_input', 1),
                name=r.get('name', ''),
                device_name=r.get('device_name'),
                gate_db=r.get('gate_db', -34.0),
                attack=r.get('attack', 0.05),
                release=r.get('release', 0.5),
                weight=r.get('weight', 1.0),
            )

    def _save_settings(self):
        rows = []
        for row_w, ne, dc, cs, gs, ats, rs, ins, bar in self._mic_rows:
            rows.append({
                'name':        ne.text(),
                'device_name': dc.currentText(),
                'ch':          cs.value(),
                'gate_db':     gs.value(),
                'attack':      ats.value(),
                'release':     rs.value(),
                'atem_input':  ins.currentData() or 1,
                'weight':      row_w._prio_combo.currentData() or 1.0,
            })
        s = {
            'atem_ip':           self.ip_edit.text().strip(),
            'me':                self.me_spin.value(),
            'silence_input':     self.silence_combo.currentData() or DEFAULT_SILENCE_INPUT,
            'holdoff':           self.holdoff_spin.value(),
            'silence_delay':     self.silence_delay_spin.value(),
            'silence_loop':          self.silence_loop_check.isChecked(),
            'silence_loop_min':      self.silence_loop_min_spin.value(),
            'silence_loop_max':      self.silence_loop_max_spin.value(),
            'extra_loop_inputs':     self.extra_loop_inputs,
            'rows':              rows,
            'presets':           [(a.value(), r.value(), h.value()) for a, r, h in self._preset_spins],
            'companion_port':    self.companion_port_spin.value(),
            'companion_enabled': self.companion_enable_btn.isChecked(),
            'pvw_link_enabled':  self.pvw_link_check.isChecked(),
            'pvw_link_input':    self.pvw_link_combo.currentData() or 1,
            'bus_panel_open':    self.bus_box.isChecked(),
        }
        try:
            with open(_SETTINGS_FILE, 'w', encoding='utf-8') as f:
                json.dump(s, f, indent=2)
            print(f"Settings saved to {_SETTINGS_FILE}")
        except Exception as e:
            print(f"Settings save error: {e}")

    def _refresh_devices(self):
        """Rebuild the shared device list (deduplicated, WASAPI preferred)."""
        self._input_devices.clear()
        host_apis = sd.query_hostapis()

        # Find WASAPI host API index
        wasapi_idx = next(
            (i for i, a in enumerate(host_apis) if "wasapi" in a["name"].lower()), None
        )

        print("\n── Available audio INPUT devices (WASAPI) ──")
        all_devices = list(enumerate(sd.query_devices()))

        # Use WASAPI devices only; fall back to all if WASAPI not found
        candidates = [
            (i, d) for i, d in all_devices
            if d["max_input_channels"] > 0
            and (wasapi_idx is None or d["hostapi"] == wasapi_idx)
        ]
        if not candidates:
            candidates = [(i, d) for i, d in all_devices if d["max_input_channels"] > 0]

        for dev_idx, d in candidates:
            ch_count = int(d["max_input_channels"])
            label = f"{d['name']}  ({ch_count}ch)"
            self._input_devices.append((dev_idx, label))
            print(f"  {dev_idx}: {label}")
        print("────────────────────────────────────────────\n")

        # Update every existing row's device combo
        for row_w, name_edit, dev_combo, ch_spin, gate_spin, attack_spin, release_spin, inp_spin, bar in self._mic_rows:
            current_data = dev_combo.currentData()
            dev_combo.blockSignals(True)
            dev_combo.clear()
            for dev_idx, lbl in self._input_devices:
                dev_combo.addItem(lbl, dev_idx)
            # Restore previous selection or pick first DVS
            restored = False
            if current_data is not None:
                for j in range(dev_combo.count()):
                    if dev_combo.itemData(j) == current_data:
                        dev_combo.setCurrentIndex(j)
                        restored = True
                        break
            if not restored:
                self._auto_select_dvs(dev_combo)
            dev_combo.blockSignals(False)

    def _auto_select_dvs(self, combo: QComboBox):
        for j in range(combo.count()):
            name = combo.itemText(j).lower()
            if "dante" in name or "dvs" in name or "virtual soundcard" in name:
                combo.setCurrentIndex(j)
                return

    def _add_mic_row(self, ch: int = 0, atem_input: int = None, name: str = None,
                     device_name: str = None, gate_db: float = -34.0,
                     attack: float = 0.05, release: float = 0.5,
                     weight: float = 1.0):
        row_idx = len(self._mic_rows)
        if atem_input is None:
            atem_input = row_idx + 1
        if name is None:
            name = f"Camera {row_idx + 1}"
        grid_row = row_idx + 1   # row 0 is the header

        # Attribute bag — not added to any layout, just used for per-row widget refs
        row_w = QWidget()
        row_w.hide()

        # Col 0 — tally strip
        indicator = QLabel()
        indicator.setFixedSize(6, 20)
        indicator.setStyleSheet(TALLY_INACTIVE)
        row_w._indicator = indicator
        self._rows_grid.addWidget(indicator, grid_row, 0, Qt.AlignmentFlag.AlignVCenter)

        # Col 1 — name
        name_edit = QLineEdit(name)
        name_edit.setFixedWidth(90)
        name_edit.setPlaceholderText(f"Camera {row_idx + 1}")
        self._rows_grid.addWidget(name_edit, grid_row, 1)

        # Col 2 — device (stretch)
        dev_combo = QComboBox()
        dev_combo.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Preferred)
        for dev_idx, label in self._input_devices:
            dev_combo.addItem(label, dev_idx)
        if device_name:
            match = next((j for j in range(dev_combo.count()) if dev_combo.itemText(j) == device_name), -1)
            dev_combo.setCurrentIndex(match if match >= 0 else 0)
            if match < 0:
                self._auto_select_dvs(dev_combo)
        else:
            self._auto_select_dvs(dev_combo)
        self._rows_grid.addWidget(dev_combo, grid_row, 2)

        # Col 3 — channel (L/R)
        ch_spin = QSpinBox()
        ch_spin.setRange(0, 1)
        ch_spin.setValue(ch)
        ch_spin.setFixedWidth(38)
        ch_spin.setToolTip("0 = left  1 = right")
        self._rows_grid.addWidget(ch_spin, grid_row, 3)

        # Col 4 — gate threshold
        gate_spin = QDoubleSpinBox()
        gate_spin.setRange(-60.0, 0.0)
        gate_spin.setValue(gate_db)
        gate_spin.setSingleStep(1.0)
        gate_spin.setDecimals(0)
        gate_spin.setSuffix(" dB")
        gate_spin.setFixedWidth(72)
        gate_spin.setToolTip("Signal must exceed this level to open the gate")
        self._rows_grid.addWidget(gate_spin, grid_row, 4)

        # Col 5 — attack
        attack_spin = QDoubleSpinBox()
        attack_spin.setRange(0.0, 2.0)
        attack_spin.setValue(attack)
        attack_spin.setSingleStep(0.01)
        attack_spin.setDecimals(2)
        attack_spin.setFixedWidth(52)
        attack_spin.setToolTip("Signal must stay above gate threshold for this long before switching")
        self._rows_grid.addWidget(attack_spin, grid_row, 5)

        # Col 6 — release
        release_spin = QDoubleSpinBox()
        release_spin.setRange(0.0, 10.0)
        release_spin.setValue(release)
        release_spin.setSingleStep(0.1)
        release_spin.setDecimals(1)
        release_spin.setFixedWidth(52)
        release_spin.setToolTip("Gate stays open this long after signal drops below threshold")
        self._rows_grid.addWidget(release_spin, grid_row, 6)

        # Col 7 — ATEM camera input (stretch)
        inp_combo = QComboBox()
        inp_combo.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Preferred)
        inp_combo.setToolTip("ATEM input to switch to when this mic is loudest")
        for i in range(1, 21):
            inp_combo.addItem(str(i), i)
        found = inp_combo.findData(atem_input)
        if found >= 0:
            inp_combo.setCurrentIndex(found)
        self._rows_grid.addWidget(inp_combo, grid_row, 7)

        # Col 8 — priority weight
        prio_combo = QComboBox()
        prio_combo.setFixedWidth(68)
        prio_combo.setToolTip(
            "Priority when several mics are open at the same time.\n"
            "High: this camera wins unless another mic is much louder (2× boost).\n"
            "Low: only switches here when clearly the loudest (0.5×)."
        )
        for plabel, w in (("Low", 0.5), ("Normal", 1.0), ("High", 2.0)):
            prio_combo.addItem(plabel, w)
        pidx = prio_combo.findData(weight)
        prio_combo.setCurrentIndex(pidx if pidx >= 0 else 1)
        row_w._prio_combo = prio_combo
        self._rows_grid.addWidget(prio_combo, grid_row, 8)

        # Col 9 — stacked level + threshold bars
        bars_w = QWidget()
        bars_w.setFixedWidth(180)
        bars_layout = QVBoxLayout(bars_w)
        bars_layout.setContentsMargins(0, 0, 0, 0)
        bars_layout.setSpacing(2)

        bar = QProgressBar()
        bar.setRange(0, 100)
        bar.setValue(0)
        bar.setTextVisible(False)
        bar.setFixedHeight(13)
        bar.setStyleSheet(BAR_STYLE_CLOSED)
        bars_layout.addWidget(bar)

        thresh_bar = QProgressBar()
        thresh_bar.setRange(0, 100)
        thresh_bar.setTextVisible(False)
        thresh_bar.setFixedHeight(5)
        thresh_bar.setStyleSheet(THRESH_BAR_STYLE)
        thresh_bar.setValue(max(0, min(100, int((gate_db + 60) / 60 * 100))))
        bars_layout.addWidget(thresh_bar)

        row_w._thresh_bar = thresh_bar
        row_w._bars_w = bars_w
        gate_spin.valueChanged.connect(
            lambda db, tb=thresh_bar: tb.setValue(max(0, min(100, int((db + 60) / 60 * 100))))
        )
        self._rows_grid.addWidget(bars_w, grid_row, 9)

        # Col 10 — gate state label
        gate_lbl = QLabel("CLSD")
        gate_lbl.setFixedWidth(38)
        gate_lbl.setAlignment(Qt.AlignmentFlag.AlignCenter)
        gate_lbl.setStyleSheet(GATE_LBL_CLOSED)
        row_w._gate_lbl = gate_lbl
        self._rows_grid.addWidget(gate_lbl, grid_row, 10)

        self._mic_rows.append((row_w, name_edit, dev_combo, ch_spin, gate_spin, attack_spin, release_spin, inp_combo, bar))

    def _remove_mic_row(self):
        if len(self._mic_rows) <= 1:
            return
        row_w, name_edit, dev_combo, ch_spin, gate_spin, attack_spin, release_spin, inp_combo, bar = self._mic_rows.pop()
        grid_row = len(self._mic_rows) + 1
        for w in [row_w._indicator, name_edit, dev_combo, ch_spin, gate_spin,
                  attack_spin, release_spin, inp_combo, row_w._prio_combo,
                  row_w._bars_w, row_w._gate_lbl]:
            self._rows_grid.removeWidget(w)
            w.deleteLater()

    # ── Helpers ───────────────────────────────────────────────────────────────

    # internalPortType values to show: External=0, MP Fill=4, MP Key=5, SuperSource=6
    _SHOW_PORT_TYPES = {0, 4, 5, 6}

    def _update_input_combos(self):
        """Repopulate all input combos with names received from ATEM."""
        atem = self.engine.atem.atem
        if not atem or not atem.inputs:
            return
        # Only keep camera inputs, media players and supersource
        entries = [
            (inp_id, info)
            for inp_id, info in sorted(atem.inputs.items())
            if info.get('type', 0) in self._SHOW_PORT_TYPES
        ]
        combos = [inp_combo for _, ne, dc, cs, gs, ats, rs, inp_combo, bar in self._mic_rows]
        combos.append(self.silence_combo)
        combos.append(self.pvw_link_combo)
        combos.append(self.extra_loop_combo)
        for combo in combos:
            current = combo.currentData()
            combo.blockSignals(True)
            combo.clear()
            for inp_id, info in entries:
                label = f"{inp_id} — {info['name']}" if info['name'] else str(inp_id)
                combo.addItem(label, inp_id)
            idx = combo.findData(current)
            combo.setCurrentIndex(idx if idx >= 0 else 0)
            combo.blockSignals(False)

    _BUS_BTN_W = 54   # fixed bus button size — rows scroll horizontally instead
    _BUS_BTN_H = 26   # of wrapping, so the panel height never grows

    def _rebuild_bus_buttons(self):
        """(Re)create the PGM and PVW button rows — from ATEM inputs when connected."""
        atem = self.engine.atem.atem
        if atem and atem.inputs:
            # Cameras only (external inputs) — media players etc. stay available
            # in the dropdowns but would make the bus rows too tall
            entries = [
                (inp_id, info)
                for inp_id, info in sorted(atem.inputs.items())
                if info.get('type', 0) == 0
            ]
        else:
            entries = [(i, {'short_name': str(i), 'name': f'Input {i}'}) for i in range(1, 9)]

        for row, buttons, handler, style in (
            (self._pgm_row, self._pgm_buttons, self._pgm_clicked, PGM_BTN_OFF),
            (self._pvw_row, self._pvw_buttons, self._pvw_clicked, PVW_BTN_OFF),
        ):
            for btn in buttons.values():
                row.removeWidget(btn)
                btn.hide()             # deleteLater is deferred — hide now so the
                btn.setParent(None)    # old buttons can't paint over the new ones
                btn.deleteLater()
            buttons.clear()
            for inp_id, info in entries:
                btn = QPushButton(info.get('short_name') or str(inp_id))
                btn.setToolTip(info.get('name') or f"Input {inp_id}")
                btn.setFixedSize(self._BUS_BTN_W, self._BUS_BTN_H)
                btn.setStyleSheet(style)
                btn.clicked.connect(lambda checked, i2=inp_id, h=handler: h(i2))
                row.insertWidget(row.count() - 1, btn)   # keep trailing stretch last
                buttons[inp_id] = btn

        # Restore highlights from the last known bus state
        self._refresh_bus_highlights()

    def _add_extra_loop_cam(self):
        inp = self.extra_loop_combo.currentData()
        if inp and inp not in self.extra_loop_inputs:
            self.extra_loop_inputs.append(inp)
            self._rebuild_extra_chips()

    def _remove_extra_loop_cam(self, inp: int):
        if inp in self.extra_loop_inputs:
            self.extra_loop_inputs.remove(inp)
            self._rebuild_extra_chips()

    def _rebuild_extra_chips(self):
        """Show the extra loop cameras as removable chips next to the Add button."""
        for chip in self._extra_chips:
            self._extra_chips_row.removeWidget(chip)
            chip.hide()
            chip.setParent(None)
            chip.deleteLater()
        self._extra_chips.clear()
        atem = self.engine.atem.atem
        for inp in self.extra_loop_inputs:
            label = str(inp)
            if atem and inp in atem.inputs:
                label = atem.inputs[inp].get('short_name') or atem.inputs[inp].get('name') or label
            chip = QPushButton(f"{label}  ✕")
            chip.setToolTip(f"Input {inp} — click to remove from the loop")
            chip.setFixedHeight(22)
            chip.setStyleSheet(CHIP_STYLE)
            chip.clicked.connect(lambda checked, i=inp: self._remove_extra_loop_cam(i))
            self._extra_chips_row.insertWidget(self._extra_chips_row.count() - 1, chip)
            self._extra_chips.append(chip)

    def _refresh_bus_highlights(self):
        """Re-apply PGM/PVW highlights from the ATEM state for the current M/E."""
        atem = self.engine.atem.atem
        if not atem:
            return
        me = self.me_spin.value() - 1
        src = atem.program.get(me)
        if src is not None:
            self._apply_program(src)
        src = atem.preview.get(me)
        if src is not None:
            self._apply_preview(src)

    def _pgm_clicked(self, inp: int):
        me = self.me_spin.value() - 1
        ok = self.engine.atem.switch_program(inp, me)
        if not ok:
            print(f"PGM select → input {inp} failed (ATEM not connected)")
        # Highlight follows the PrgI confirmation from the ATEM

    def _pvw_clicked(self, inp: int):
        me = self.me_spin.value() - 1
        ok = self.engine.atem.switch_preview(inp, me)
        if not ok:
            print(f"PVW select → input {inp} failed (ATEM not connected)")
        # Highlight + automation follow the PrvI confirmation from the ATEM

    def _apply_program(self, src: int):
        """Highlight the active PGM button and the matching channel tally."""
        for inp_id, btn in self._pgm_buttons.items():
            btn.setStyleSheet(PGM_BTN_ON if inp_id == src else PGM_BTN_OFF)
        for row_w, ne, dc, cs, gs, ats, rs, ins, bar in self._mic_rows:
            active = ins.currentData() == src
            row_w._indicator.setStyleSheet(TALLY_ACTIVE if active else TALLY_INACTIVE)

    def _apply_preview(self, src: int):
        """Highlight the active PVW button and apply the automation link."""
        for inp_id, btn in self._pvw_buttons.items():
            btn.setStyleSheet(PVW_BTN_ON if inp_id == src else PVW_BTN_OFF)
        if self.pvw_link_check.isChecked():
            want = self.pvw_link_combo.currentData()
            self.auto_btn.setChecked(src == want)

    # ── Slots ─────────────────────────────────────────────────────────────────

    def _toggle_atem(self):
        if self.engine.atem.connected:
            self.engine.atem.disconnect()
            self._show_disconnected()
        else:
            # Connect in a worker thread — the state dump can take seconds and
            # would freeze the GUI if run on the main thread.
            ip = self.ip_edit.text().strip()
            self.connect_btn.setEnabled(False)
            self.atem_status.setText("● Connecting…")
            self.atem_status.setStyleSheet("color: orange; font-weight: bold;")
            threading.Thread(
                target=lambda: self.signals.atem_connect_finished.emit(
                    self.engine.atem.connect(ip)),
                daemon=True,
            ).start()

    def _on_connect_finished(self, ok: bool):
        """Slot — manual connect attempt finished (worker thread done)."""
        self.connect_btn.setEnabled(True)
        if not ok:
            self.atem_status.setText("● Failed — check IP")
            self.atem_status.setStyleSheet("color: #ff4444; font-weight: bold;")
        # on success, _on_atem_connected handles the UI via the connected signal

    def _show_disconnected(self):
        self.connect_btn.setText("Connect")
        self.atem_status.setText("● Disconnected")
        self.atem_status.setStyleSheet("color: #ff4444; font-weight: bold;")

    def _on_atem_disconnected(self):
        """Slot — called when keepalive detects ATEM dropped."""
        self._show_disconnected()

    def _on_atem_connected(self):
        """Slot — called on any successful connect (manual or auto-reconnect)."""
        atem = self.engine.atem.atem
        model    = atem.model_name if atem and atem.model_name else "ATEM"
        me_count = atem.me_count   if atem else 1
        self.connect_btn.setText("Disconnect")
        self.atem_status.setText(f"● Connected — {model}")
        self.atem_status.setStyleSheet("color: #00cc55; font-weight: bold;")
        self.me_spin.setRange(1, me_count)
        self.test_me_spin.setRange(1, me_count)
        self._update_input_combos()
        self._rebuild_bus_buttons()
        self._rebuild_extra_chips()   # pick up real input names

    def _toggle_audio(self):
        if self.engine.running:
            self.engine.stop_audio()
            self.audio_btn.setText("▶  Start")
        else:
            self._push_settings()
            self.engine.start_audio()
            self.audio_btn.setText("■  Stop")

    def _toggle_automation(self, on: bool):
        self.engine.automation_active = on
        if on:
            self.auto_btn.setText("AUTOMATION  ON")
            self.auto_btn.setStyleSheet(BTN_STYLE_ON)
        else:
            self.auto_btn.setText("AUTOMATION  OFF")
            self.auto_btn.setStyleSheet(BTN_STYLE_OFF)
            for row_w, *_ in self._mic_rows:
                row_w._indicator.setStyleSheet(TALLY_INACTIVE)

    def _on_automation_changed(self, on: bool):
        """Slot — called when Companion HTTP request toggles automation."""
        self.auto_btn.setChecked(on)   # triggers _toggle_automation via toggled signal

    def _on_preview_changed(self, me_idx: int, src: int):
        """Slot — ATEM preview bus changed (from our PVW buttons or the panel)."""
        if me_idx == self.me_spin.value() - 1:
            self._apply_preview(src)

    def _on_program_changed(self, me_idx: int, src: int):
        """Slot — ATEM program bus changed (automation, PGM buttons or the panel)."""
        if me_idx == self.me_spin.value() - 1:
            self._apply_program(src)

    def _on_log_line(self, text: str):
        self._log_view.appendPlainText(text.rstrip())
        self._log_view.verticalScrollBar().setValue(
            self._log_view.verticalScrollBar().maximum()
        )

    def _toggle_companion(self, checked: bool):
        if checked:
            port = self.companion_port_spin.value()
            ok = self.companion.start(port)
            if ok:
                self.companion_enable_btn.setText("Disable")
                self.companion_status.setText(f"● Running  :{port}")
                self.companion_status.setStyleSheet("color: #00cc55; font-weight: bold;")
                self.companion_port_spin.setEnabled(False)
            else:
                self.companion_enable_btn.setChecked(False)
                self.companion_status.setText("● Failed — port in use?")
                self.companion_status.setStyleSheet("color: #ff4444; font-weight: bold;")
        else:
            self.companion.stop()
            self.companion_enable_btn.setText("Enable")
            self.companion_status.setText("● Stopped")
            self.companion_status.setStyleSheet("color: #ff4444; font-weight: bold;")
            self.companion_port_spin.setEnabled(True)

    def _push_settings(self):
        e = self.engine
        e.mic_device_channels = [(dc.currentData(), cs.value()) for _, ne, dc, cs, gs, ats, rs, ins, _ in self._mic_rows]
        e.mic_atem_inputs  = [ins.currentData() or 1 for _, ne, dc, cs, gs, ats, rs, ins, _ in self._mic_rows]
        e.mic_weights      = [row_w._prio_combo.currentData() or 1.0 for row_w, *_ in self._mic_rows]
        e.gate_thresholds  = [10 ** (gs.value() / 20) for _, ne, dc, cs, gs, ats, rs, ins, _ in self._mic_rows]
        e.gate_attacks     = [ats.value() for _, ne, dc, cs, gs, ats, rs, ins, _ in self._mic_rows]
        e.gate_releases    = [rs.value()  for _, ne, dc, cs, gs, ats, rs, ins, _ in self._mic_rows]
        e.silence_input    = self.silence_combo.currentData() or DEFAULT_SILENCE_INPUT
        e.holdoff          = self.holdoff_spin.value()
        e.silence_delay    = self.silence_delay_spin.value()
        e.silence_loop_enabled  = self.silence_loop_check.isChecked()
        e.silence_loop_min      = self.silence_loop_min_spin.value()
        e.silence_loop_max      = max(self.silence_loop_min_spin.value(),
                                      self.silence_loop_max_spin.value())
        e.extra_loop_inputs     = list(self.extra_loop_inputs)
        e.me_index         = self.me_spin.value() - 1  # 0-based

    def _apply_preset(self, attack: float, release: float, holdoff: float):
        for _, ne, dc, cs, gs, ats, rs, ins, _ in self._mic_rows:
            ats.setValue(attack)
            rs.setValue(release)
        self.holdoff_spin.setValue(holdoff)

    def _on_levels(self, levels: list):
        for i, (_, ne, dc, cs, gs, ats, rs, ins, bar) in enumerate(self._mic_rows):
            if i < len(levels):
                lvl = levels[i]
                if lvl > 0:
                    db = 20 * math.log10(lvl)
                    # Map -60 dBFS → 0,  0 dBFS → 100
                    val = max(0, min(100, int((db + 60) / 60 * 100)))
                else:
                    val = 0
                bar.setValue(val)

    def _on_gates(self, states: list):
        self._push_settings()   # keep engine in sync with any live GUI changes
        for i, (row_w, ne, dc, cs, gs, ats, rs, ins, bar) in enumerate(self._mic_rows):
            if i < len(states):
                state = states[i]
                if state == 'open':
                    bar.setStyleSheet(BAR_STYLE_OPEN)
                    row_w._gate_lbl.setText("OPEN")
                    row_w._gate_lbl.setStyleSheet(GATE_LBL_OPEN)
                elif state == 'attack':
                    bar.setStyleSheet(BAR_STYLE_ATTACK)
                    row_w._gate_lbl.setText("ATCK")
                    row_w._gate_lbl.setStyleSheet(GATE_LBL_ATTACK)
                elif state == 'releasing':
                    bar.setStyleSheet(BAR_STYLE_RELEASING)
                    row_w._gate_lbl.setText("REL")
                    row_w._gate_lbl.setStyleSheet(GATE_LBL_RELEASING)
                else:
                    bar.setStyleSheet(BAR_STYLE_CLOSED)
                    row_w._gate_lbl.setText("CLSD")
                    row_w._gate_lbl.setStyleSheet(GATE_LBL_CLOSED)

    def _on_switched(self, inp: int):
        me = self.engine.me_index + 1
        names = {ins.currentData(): (ne.text() or f"Camera {i+1}")
                 for i, (_, ne, dc, cs, gs, ats, rs, ins, _) in enumerate(self._mic_rows)}
        label = names.get(inp, f"Input {inp}")
        self.last_switched_label.setText(f"Last switched: {label}  (M/E {me}, input {inp})")
        for row_w, ne, dc, cs, gs, ats, rs, ins, bar in self._mic_rows:
            active = ins.currentData() == inp
            row_w._indicator.setStyleSheet(TALLY_ACTIVE if active else TALLY_INACTIVE)

    def _test_switch(self):
        me  = self.test_me_spin.value() - 1   # 0-based
        inp = self.test_inp_spin.value()
        ok  = self.engine.atem.switch_program(inp, me)
        print(f"Test switch → M/E {me+1} input {inp}  result={ok}")
        if ok:
            self.last_switched_label.setText(f"Last switched: M/E {me+1} input {inp} (manual)")

    def closeEvent(self, event):
        self._save_settings()
        self.companion.stop()
        self.engine.stop_audio()
        self.engine.atem.disconnect()
        event.accept()


# ── Styles ────────────────────────────────────────────────────────────────────

# Level meter bars
BAR_STYLE_CLOSED = """
    QProgressBar { border: 1px solid #383838; border-radius: 2px; background: #1e1e1e; }
    QProgressBar::chunk { background: #2e2e2e; border-radius: 1px; }
"""
BAR_STYLE_ATTACK = """
    QProgressBar { border: 1px solid #505050; border-radius: 2px; background: #1e1e1e; }
    QProgressBar::chunk { background: #787878; border-radius: 1px; }
"""
BAR_STYLE_OPEN = """
    QProgressBar { border: 1px solid #606060; border-radius: 2px; background: #1e1e1e; }
    QProgressBar::chunk { background: #b8b8b8; border-radius: 1px; }
"""
BAR_STYLE_RELEASING = """
    QProgressBar { border: 1px solid #484848; border-radius: 2px; background: #1e1e1e; }
    QProgressBar::chunk { background: #505050; border-radius: 1px; }
"""
THRESH_BAR_STYLE = """
    QProgressBar { border: none; background: #1e1e1e; }
    QProgressBar::chunk { background: #555; }
"""

# Tally
TALLY_ACTIVE   = "background: #c8c8c8; border-radius: 2px;"
TALLY_INACTIVE = "background: #303030; border-radius: 2px;"

# Gate state label
GATE_LBL_CLOSED    = "color: #484848; background: transparent; font-size: 10px; font-weight: bold;"
GATE_LBL_ATTACK    = "color: #aaa; background: #2e2e2e; border-radius: 2px; font-size: 10px; font-weight: bold; padding: 0 2px;"
GATE_LBL_OPEN      = "color: #1e1e1e; background: #c8c8c8; border-radius: 2px; font-size: 10px; font-weight: bold; padding: 0 2px;"
GATE_LBL_RELEASING = "color: #787878; background: #2a2a2a; border-radius: 2px; font-size: 10px; font-weight: bold; padding: 0 2px;"

# PGM bus buttons — red like the ATEM program bus
PGM_BTN_OFF = """
    QPushButton { background: #252525; color: #c8c8c8; border: 1px solid #404040;
                  border-radius: 4px; font-weight: bold; }
    QPushButton:hover { border-color: #ff4444; background: #2e2e2e; }
"""
PGM_BTN_ON = """
    QPushButton { background: #e03030; color: #2a0808; border: none;
                  border-radius: 4px; font-weight: bold; }
    QPushButton:hover { background: #c82828; }
"""

# PVW bus buttons — green like the ATEM preview bus
PVW_BTN_OFF = """
    QPushButton { background: #252525; color: #c8c8c8; border: 1px solid #404040;
                  border-radius: 4px; font-weight: bold; }
    QPushButton:hover { border-color: #00cc55; background: #2e2e2e; }
"""
PVW_BTN_ON = """
    QPushButton { background: #00cc55; color: #0a2a14; border: none;
                  border-radius: 4px; font-weight: bold; }
    QPushButton:hover { background: #00b84d; }
"""

# Extra loop camera chips
CHIP_STYLE = """
    QPushButton { background: #2a2a2a; color: #b8b8b8; border: 1px solid #484848;
                  border-radius: 10px; padding: 0 8px; font-size: 11px; }
    QPushButton:hover { border-color: #ff5555; color: #ff8888; }
"""

# Automation button
BTN_STYLE_OFF = """
    QPushButton { background: #252525; color: #c8c8c8; border: 1px solid #404040; border-radius: 8px; }
    QPushButton:hover { border-color: #606060; background: #2e2e2e; }
"""
BTN_STYLE_ON = """
    QPushButton { background: #c8c8c8; color: #1e1e1e; border: none; border-radius: 8px; }
    QPushButton:hover { background: #b0b0b0; }
"""

# Global app stylesheet — soft dark gray theme
APP_STYLESHEET = """
    QMainWindow, QWidget {
        background: #1e1e1e;
        color: #d4d4d4;
    }
    QGroupBox {
        border: 1px solid #383838;
        border-radius: 4px;
        margin-top: 10px;
        color: #686868;
        font-size: 11px;
    }
    QGroupBox::title {
        subcontrol-origin: margin;
        left: 8px;
        padding: 0 4px;
    }
    QPushButton {
        background: #2a2a2a;
        color: #d4d4d4;
        border: 1px solid #404040;
        border-radius: 3px;
        padding: 3px 8px;
        min-height: 20px;
    }
    QPushButton:hover { border-color: #606060; background: #333; }
    QPushButton:pressed { background: #1a1a1a; }
    QLineEdit, QSpinBox, QDoubleSpinBox {
        background: #181818;
        color: #d4d4d4;
        border: 1px solid #3a3a3a;
        border-radius: 3px;
        padding: 1px 4px;
        selection-background-color: #c8c8c8;
        selection-color: #1e1e1e;
    }
    QLineEdit:focus, QSpinBox:focus, QDoubleSpinBox:focus {
        border-color: #686868;
    }
    QSpinBox::up-button, QDoubleSpinBox::up-button,
    QSpinBox::down-button, QDoubleSpinBox::down-button {
        background: #2a2a2a;
        border: none;
        width: 16px;
    }
    QSpinBox::up-button:hover, QDoubleSpinBox::up-button:hover,
    QSpinBox::down-button:hover, QDoubleSpinBox::down-button:hover {
        background: #3a3a3a;
    }
    QSpinBox::up-arrow, QDoubleSpinBox::up-arrow {
        image: url(ARROW_UP_PATH);
        width: 8px; height: 8px;
    }
    QSpinBox::down-arrow, QDoubleSpinBox::down-arrow {
        image: url(ARROW_DN_PATH);
        width: 8px; height: 8px;
    }
    QComboBox {
        background: #181818;
        color: #d4d4d4;
        border: 1px solid #3a3a3a;
        border-radius: 3px;
        padding: 1px 6px;
        min-height: 20px;
    }
    QComboBox:hover { border-color: #686868; }
    QComboBox::drop-down { border: none; width: 18px; }
    QComboBox::down-arrow { width: 8px; height: 8px; }
    QComboBox QAbstractItemView {
        background: #222;
        color: #d4d4d4;
        border: 1px solid #444;
        selection-background-color: #c8c8c8;
        selection-color: #1e1e1e;
    }
    QTabWidget::pane { border: 1px solid #383838; border-radius: 3px; }
    QTabBar::tab {
        background: #181818;
        color: #686868;
        border: 1px solid #383838;
        border-bottom: none;
        padding: 4px 14px;
        margin-right: 2px;
    }
    QTabBar::tab:selected { color: #d4d4d4; border-color: #555; background: #242424; }
    QTabBar::tab:hover { color: #aaa; }
    QLabel { color: #d4d4d4; }
    QScrollBar:vertical {
        background: #1e1e1e; width: 8px; border: none;
    }
    QScrollBar::handle:vertical { background: #484848; border-radius: 4px; }
    QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical { height: 0; }
    QScrollBar:horizontal {
        background: #1e1e1e; height: 8px; border: none;
    }
    QScrollBar::handle:horizontal { background: #484848; border-radius: 4px; min-width: 24px; }
    QScrollBar::add-line:horizontal, QScrollBar::sub-line:horizontal { width: 0; }
"""


# ── Palette ───────────────────────────────────────────────────────────────────

def dark_palette():
    p = QPalette()
    c = p.ColorRole
    p.setColor(c.Window,          QColor(30,  30,  30))
    p.setColor(c.WindowText,      QColor(212, 212, 212))
    p.setColor(c.Base,            QColor(24,  24,  24))
    p.setColor(c.AlternateBase,   QColor(34,  34,  34))
    p.setColor(c.Text,            QColor(212, 212, 212))
    p.setColor(c.Button,          QColor(42,  42,  42))
    p.setColor(c.ButtonText,      QColor(212, 212, 212))
    p.setColor(c.Highlight,       QColor(200, 200, 200))
    p.setColor(c.HighlightedText, QColor(30,  30,  30))
    p.setColor(c.Mid,             QColor(50,  50,  50))
    p.setColor(c.Dark,            QColor(20,  20,  20))
    p.setColor(c.Shadow,          QColor(10,  10,  10))
    return p


# ── Embedded window icon (hof_atem_autoswitcher.ico) ─────────────────────────
# Base64 so the .ico file itself doesn't have to ship alongside the script;
# the build workflow extracts this same data for the .exe icon.
_ICON_B64 = "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nHfeeQyXSsnzxcT/xje+kX/+53+mp6cnKS/nedx5x5188EMfIp/Pc/773sdJJ50UeSNcnl60iEsu+SSXX/YZ5syZG9lFwrZd9MwzXHnlldx7zz0c8bIjuewzn0EEHn3scc499xz+/cILOfm1J2NEuOzyyykWipx//nmA8Itf/IIrrriCvr4+LrjgfF5+3HGgkMu5PPzII7znPe+lVqvxzn/9V974hjeQz4eqy+DQEGeffQ7PP7eEfzjpJN7xjncwe9as8HmilGsPPPAg7//A+5lGyyFET6J3EyYAdghtAk1wADzPOz2XL2guXwiizym/FQpFvffee7UdfN/X1772tbr99jtopVJte86SJUt0r71fooBee+21bc+5+eabtVAo6py5c3XhwoVtz7nis59VEdG7776n7XFrrZ71T/+kgL77vPPanrPvfvvpwYccooNDgyOfJQj0zW9+iwJ6wQXvaXu9quo113xPT3zlK9seW7Rokc6cOUudnKdeoaiFjk4F9J3vfOeo5f3xj39UEdGvfe1rI449/vjjut9+++nq1avbXrty1Srdffc99IQTT0z2Pfzww+q6rn7/+422Puecc/Q/PvjB5Pe3v/MdNcbRX/7ylyPKvP+BB9QYRz/28U+MOFYql3W77XfQk04+WX3fb1unu+++WwuF4oT323Hcgly+oJ7nnZ6mdWgW8S1AzZi/a5giLAkSmg4YHh4mCALq9Xqyr1ar4TgO73vf+8kX8vQP9CeBLulzdtppJ84880z22XdfzjzzzBF6ue/7HHfccRz78mN57Wtfy3777dd0nzhQ5dxzzmbX3XZj1apVI+pSjySTd7/7PGbOnBmNdDoirl+A8887n67OLmopI169Xscxhnef925mzprFBRecH4rkG5gXoJFaE5+nqikpXaj7Pt3dPbznPe9N7tOKoaEh9thjT975zneOaBsxBmuVwaGhtm07e9Ys/vXf/pVSqZwcHx4eBqBcbuyr1evUqtXk9+pVqzns8MN47Wtfm/JMhKhUKuy8YAHnvfvdI2wfqkpHR5H3ve99OI7T1IaNc9bbZFMNChhVXVETuS/alxhx3JYThUplseQLdwMnMY3iAdJr4H30ox9lYHCQL33xi6gqc+bMpqMj1PEdx2FgYIALLriAI444grPPPhtVZdbMGew8f35isHrs8cf5yEUf4f3vfx9Hvuxl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"


# ── Entry point ───────────────────────────────────────────────────────────────

if __name__ == "__main__":
    if sys.platform == "win32":
        try:  # make the Windows taskbar show our icon instead of pythonw's
            import ctypes
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("HBS.AtemAutoSwitcher")
        except Exception:
            pass
    app = QApplication(sys.argv)
    app.setStyle("Fusion")
    app.setPalette(dark_palette())
    try:
        _icon_pm = QPixmap()
        _icon_pm.loadFromData(base64.b64decode(_ICON_B64))
        app.setWindowIcon(QIcon(_icon_pm))
    except Exception:
        pass
    app.setStyleSheet(
        APP_STYLESHEET
        .replace('ARROW_UP_PATH', _ARROW_UP_SVG.replace('\\', '/'))
        .replace('ARROW_DN_PATH', _ARROW_DN_SVG.replace('\\', '/'))
    )
    win = MainWindow()
    win.show()
    sys.exit(app.exec())
