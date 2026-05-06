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
import threading
import socket
import struct
import datetime
import json
import os
import zlib
from collections import defaultdict
from http.server import HTTPServer, BaseHTTPRequestHandler


# ── Tee stdout to atem_log.txt ────────────────────────────────────────────────
class _Tee:
    def __init__(self, *streams):
        self._streams = list(streams)
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
_log_file = open(_os.path.join(_APP_DIR, 'atem_log.txt'), 'w', encoding='utf-8')
_log_file.write(f'=== ATEM log started {datetime.datetime.now()} ===\n')
sys.stdout = _Tee(sys.__stdout__, _log_file)

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
    QTabWidget, QPlainTextEdit,
)
from PyQt6.QtCore import Qt, pyqtSignal, QObject, QUrl
from PyQt6.QtGui import QFont, QColor, QPalette, QDesktopServices


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
        # Called (from keepalive thread) when connection drops — set by ATEMController
        self.on_disconnect = None

    # ── Public API ────────────────────────────────────────────────────────────

    def connect(self) -> None:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.settimeout(8.0)

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
                if rid:
                    if rid > self._last_rid:
                        self._last_rid = rid
                    ack_pkt = self._ack(s, self._last_rid)
                    s.sendto(ack_pkt, (self.ip, self.PORT))
                    n_acked += 1
                # Parse commands from this packet to learn model/topology
                self._parse_state_packet(data)
                if b'InCm' in data:
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
        with self._lock:
            s = self._sock
            if s is None:
                return False
            try:
                self._pkt_id = (self._pkt_id + 1) & 0x7FFF
                cmd_data = struct.pack('!BxH', me, inp)          # ME (0-indexed), pad, source
                cmd_env  = struct.pack('!H2s4s', 12, b'\x00\x00', b'CPgI') + cmd_data
                # sofie leaves ack_id=0 in command packets (bytes 4-5 not written)
                pkt      = self._build(0x01, cmd_env,
                                       local_id=self._pkt_id,
                                       ack_id=0)
                print(f"ATEM ▶ CPgI ME{me+1} input={inp}  pkt_id={self._pkt_id}  hex={pkt.hex()}")
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

                # Log PrgI updates (ATEM confirming a program switch)
                if b'PrgI' in data:
                    offset = 12
                    while offset + 8 <= len(data):
                        clen = struct.unpack('!H', data[offset:offset + 2])[0]
                        if clen < 8 or offset + clen > len(data):
                            break
                        if data[offset + 4:offset + 8] == b'PrgI' and clen >= 12:
                            p = data[offset + 8:offset + clen]
                            me_idx = p[0]
                            src    = struct.unpack('!H', p[2:4])[0]
                            print(f"ATEM PrgI ME{me_idx+1}=source {src}")
                        offset += clen

                if (flags & 0x01) and rid:          # RELIABLE → ACK it
                    with self._lock:
                        if rid > self._last_rid:      # only advance, never go backwards
                            self._last_rid = rid
                        ack_rid = self._last_rid      # always ACK the highest seen
                        if self._sock:
                            try:
                                self._sock.sendto(self._ack(s, ack_rid), (self.ip, self.PORT))
                            except Exception:
                                pass
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
                print(f"  PrgI ME{me_idx+1}=source {src}")
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
    automation_changed = pyqtSignal(bool)   # Companion HTTP triggered a toggle
    log_line           = pyqtSignal(str)    # new log line for the GUI log tab


# ── ATEM Controller ───────────────────────────────────────────────────────────

class ATEMController:

    def __init__(self, on_disconnect=None, on_connect=None):
        self.atem: ATEMConnection | None = None
        self.connected = False
        self._ip = ""
        self._reconnecting = False
        self._last_disconnect = -9999.0
        self._on_disconnect_cb = on_disconnect   # called on connection drop (from any thread)
        self._on_connect_cb    = on_connect      # called on successful connect/reconnect

    def connect(self, ip: str) -> bool:
        self._ip = ip
        try:
            if self.atem:
                self._silent_disconnect()
            self.atem = ATEMConnection(ip)
            self.atem.on_disconnect = self._handle_drop
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
        time.sleep(3)
        try:
            self.connect(self._ip)
        except Exception as e:
            print(f"ATEM auto-reconnect failed: {e}")
        finally:
            self._reconnecting = False

    def switch_program(self, input_number: int, me: int = 0) -> bool:
        if not self.connected or self.atem is None:
            return False
        return self.atem.switch_program(input_number, me)


# ── Audio Engine ──────────────────────────────────────────────────────────────

class AudioEngine:
    def __init__(self, signals: Signals):
        self.signals = signals
        self.atem = ATEMController(
            on_disconnect=self._on_atem_drop,
            on_connect=self._on_atem_connect,
        )

        self.running = False
        self.automation_active = False
        self._streams: dict = {}   # device_idx → sd.InputStream

        # Config (list per row) — updated from GUI before start
        # mic_device_channels: list of (device_index, channel_within_device)
        self.mic_device_channels: list[tuple[int, int]] = []
        self.mic_atem_inputs:  list[int]   = []
        self.gate_thresholds:  list[float] = []   # level to open gate
        self.gate_attacks:     list[float] = []   # attack time (s) per channel
        self.gate_releases:    list[float] = []   # release time (s) per channel
        self.silence_input  = DEFAULT_SILENCE_INPUT
        self.holdoff        = 0.8
        self.silence_delay  = 2.0
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

    def _on_atem_drop(self):
        self.signals.atem_disconnected.emit()

    def _on_atem_connect(self):
        self.signals.atem_connected.emit()

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
                loudest = max(open_channels, key=lambda x: x[1])[0]
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

            if target == self._current_input:
                continue
            if (now - self._last_switch_time) < self.holdoff:
                continue

            if self.atem.switch_program(target, self.me_index):
                self._current_input = target
                self._last_switch_time = now
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
        self.signals.automation_changed.connect(self._on_automation_changed)
        self.signals.log_line.connect(self._on_log_line)
        sys.stdout._gui_cb = self.signals.log_line.emit

        self._input_devices: list[tuple[int, str]] = []   # (device_idx, label)
        # Each entry: (row_widget, device_combo, ch_spin, inp_spin, bar)
        self._mic_rows: list[tuple] = []

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
        # 7=camera(stretch)  8=level  9=state
        self._rows_grid.setColumnStretch(2, 1)
        self._rows_grid.setColumnStretch(7, 1)
        self._rows_grid.setColumnMinimumWidth(0, 6)
        self._rows_grid.setColumnMinimumWidth(1, 90)
        self._rows_grid.setColumnMinimumWidth(3, 38)
        self._rows_grid.setColumnMinimumWidth(4, 72)
        self._rows_grid.setColumnMinimumWidth(5, 52)
        self._rows_grid.setColumnMinimumWidth(6, 52)
        self._rows_grid.setColumnMinimumWidth(8, 180)
        self._rows_grid.setColumnMinimumWidth(9, 38)

        # Header row (grid row 0)
        for col, text in enumerate(["", "Name", "Device", "Ch", "Gate", "Atk", "Rel", "Camera", "Level", "State"]):
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

        cfg = QGridLayout()
        cfg.setHorizontalSpacing(14)
        cfg.setVerticalSpacing(0)
        cfg.setColumnMinimumWidth(1, 170)
        cfg.setColumnStretch(2, 1)

        def _desc(text):
            lbl = QLabel(text)
            lbl.setStyleSheet("color: #777; font-size: 11px;")
            lbl.setWordWrap(True)
            return lbl

        # Row 0 — M/E
        cfg.addWidget(QLabel("M/E for auto-switching:"), 0, 0)
        self.me_spin = QSpinBox()
        self.me_spin.setRange(1, 4)
        self.me_spin.setValue(1)
        self.me_spin.setFixedWidth(55)
        cfg.addWidget(self.me_spin, 0, 1)
        cfg.addWidget(_desc("Which M/E bus the switcher controls. M/E 1 is the main program output. Most setups only have one M/E."), 0, 2)

        # Row 1 — No-audio camera
        cfg.addWidget(QLabel("No-audio camera:"), 1, 0)
        self.silence_combo = QComboBox()
        self.silence_combo.setMinimumWidth(160)
        for i in range(1, 21):
            self.silence_combo.addItem(str(i), i)
        idx = self.silence_combo.findData(DEFAULT_SILENCE_INPUT)
        if idx >= 0:
            self.silence_combo.setCurrentIndex(idx)
        cfg.addWidget(self.silence_combo, 1, 1)
        cfg.addWidget(_desc("Camera to cut to when all microphones are silent and the silence delay has expired. Typically a wide shot or presenter cam."), 1, 2)

        # Row 2 — Holdoff
        cfg.addWidget(QLabel("Switch holdoff (s):"), 2, 0)
        self.holdoff_spin = QDoubleSpinBox()
        self.holdoff_spin.setRange(0.0, 5.0)
        self.holdoff_spin.setValue(0.8)
        self.holdoff_spin.setSingleStep(0.1)
        self.holdoff_spin.setDecimals(1)
        self.holdoff_spin.setFixedWidth(55)
        cfg.addWidget(self.holdoff_spin, 2, 1)
        cfg.addWidget(_desc("Minimum time between two camera switches. Prevents rapid cutting when multiple mics open at the same time. 0.5–1.0 s is a good starting point."), 2, 2)

        # Row 3 — Silence delay
        cfg.addWidget(QLabel("Silence delay (s):"), 3, 0)
        self.silence_delay_spin = QDoubleSpinBox()
        self.silence_delay_spin.setRange(0.0, 15.0)
        self.silence_delay_spin.setValue(2.0)
        self.silence_delay_spin.setSingleStep(0.5)
        self.silence_delay_spin.setDecimals(1)
        self.silence_delay_spin.setFixedWidth(55)
        cfg.addWidget(self.silence_delay_spin, 3, 1)
        cfg.addWidget(_desc("How long all mics must be silent before cutting to the no-audio camera. Gives speakers a natural pause without immediately switching away."), 3, 2)

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
            })
        s = {
            'atem_ip':           self.ip_edit.text().strip(),
            'me':                self.me_spin.value(),
            'silence_input':     self.silence_combo.currentData() or DEFAULT_SILENCE_INPUT,
            'holdoff':           self.holdoff_spin.value(),
            'silence_delay':     self.silence_delay_spin.value(),
            'rows':              rows,
            'presets':           [(a.value(), r.value(), h.value()) for a, r, h in self._preset_spins],
            'companion_port':    self.companion_port_spin.value(),
            'companion_enabled': self.companion_enable_btn.isChecked(),
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
                     attack: float = 0.05, release: float = 0.5):
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

        # Col 8 — stacked level + threshold bars
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
        self._rows_grid.addWidget(bars_w, grid_row, 8)

        # Col 9 — gate state label
        gate_lbl = QLabel("CLSD")
        gate_lbl.setFixedWidth(38)
        gate_lbl.setAlignment(Qt.AlignmentFlag.AlignCenter)
        gate_lbl.setStyleSheet(GATE_LBL_CLOSED)
        row_w._gate_lbl = gate_lbl
        self._rows_grid.addWidget(gate_lbl, grid_row, 9)

        self._mic_rows.append((row_w, name_edit, dev_combo, ch_spin, gate_spin, attack_spin, release_spin, inp_combo, bar))

    def _remove_mic_row(self):
        if len(self._mic_rows) <= 1:
            return
        row_w, name_edit, dev_combo, ch_spin, gate_spin, attack_spin, release_spin, inp_combo, bar = self._mic_rows.pop()
        grid_row = len(self._mic_rows) + 1
        for w in [row_w._indicator, name_edit, dev_combo, ch_spin, gate_spin,
                  attack_spin, release_spin, inp_combo, row_w._bars_w, row_w._gate_lbl]:
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

    # ── Slots ─────────────────────────────────────────────────────────────────

    def _toggle_atem(self):
        if self.engine.atem.connected:
            self.engine.atem.disconnect()
            self._show_disconnected()
        else:
            ip = self.ip_edit.text().strip()
            self.atem_status.setText("● Connecting…")
            self.atem_status.setStyleSheet("color: orange; font-weight: bold;")
            QApplication.processEvents()
            ok = self.engine.atem.connect(ip)
            if not ok:
                self.atem_status.setText("● Failed — check IP")
                self.atem_status.setStyleSheet("color: #ff4444; font-weight: bold;")
            # on success, _on_atem_connected is called via signal

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
        e.gate_thresholds  = [10 ** (gs.value() / 20) for _, ne, dc, cs, gs, ats, rs, ins, _ in self._mic_rows]
        e.gate_attacks     = [ats.value() for _, ne, dc, cs, gs, ats, rs, ins, _ in self._mic_rows]
        e.gate_releases    = [rs.value()  for _, ne, dc, cs, gs, ats, rs, ins, _ in self._mic_rows]
        e.silence_input    = self.silence_combo.currentData() or DEFAULT_SILENCE_INPUT
        e.holdoff          = self.holdoff_spin.value()
        e.silence_delay    = self.silence_delay_spin.value()
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


# ── Entry point ───────────────────────────────────────────────────────────────

if __name__ == "__main__":
    app = QApplication(sys.argv)
    app.setStyle("Fusion")
    app.setPalette(dark_palette())
    app.setStyleSheet(
        APP_STYLESHEET
        .replace('ARROW_UP_PATH', _ARROW_UP_SVG.replace('\\', '/'))
        .replace('ARROW_DN_PATH', _ARROW_DN_SVG.replace('\\', '/'))
    )
    win = MainWindow()
    win.show()
    sys.exit(app.exec())
