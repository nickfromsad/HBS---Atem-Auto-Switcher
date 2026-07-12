# HBS – ATEM Auto Switcher

Automatic camera switcher for ATEM production switchers. Monitors audio levels from a Dante Virtual Soundcard and switches the ATEM program input to whichever microphone is loudest — hands-free, in real time.

---

## What it does

In a multi-camera production each presenter or camera position has its own microphone. This tool listens to the incoming audio from a Dante Virtual Soundcard, measures the level of each channel, and tells the ATEM switcher which camera to put on air — automatically, based on who is speaking.

Each audio channel has its own noise gate. The gate filters out background noise so the switcher only reacts to real speech, not room ambience or handling noise. When a microphone opens (signal exceeds the gate threshold and holds for the attack time), the software switches the ATEM to the assigned camera. When the speaker stops, the gate waits for the release time before closing, preventing jumpy cuts during natural pauses.

---

## Features

- **Per-channel gate** — independent threshold, attack, and release per microphone
- **dBFS level meter** — real-time audio display from –60 dBFS to 0 dBFS with a gate threshold marker
- **Tally indicator** — strip highlights the currently active camera row
- **Gate state display** — shows CLSD / ATCK / OPEN / REL per channel
- **ATEM input names** — camera names pulled directly from the ATEM after connecting
- **Multi M/E support** — choose which M/E bus the auto-switcher controls
- **No-audio camera** — configurable fallback camera when all mics are silent
- **Switch holdoff** — minimum time between cuts to prevent rapid switching
- **Silence delay** — how long all mics must be silent before cutting to the fallback camera
- **Switching presets** — Fast / Medium / Slow presets with editable attack, release, and holdoff values
- **Manual test switch** — send a switch command manually to verify the ATEM connection
- **Stream Deck integration** — control automation on/off from Bitfocus Companion via HTTP
- **Settings persistence** — all settings saved automatically on close and restored on next launch
- **Auto-reconnect** — reconnects to the ATEM automatically if the connection drops

---

## Requirements

- Python 3.11+
- [PyQt6](https://pypi.org/project/PyQt6/)
- [sounddevice](https://pypi.org/project/sounddevice/)
- [numpy](https://pypi.org/project/numpy/)
- Dante Virtual Soundcard (or any multi-channel WASAPI audio input)
- Blackmagic ATEM switcher (connected over the local network)

Install dependencies:

```bash
pip install PyQt6 sounddevice numpy
```

---

## Setup

1. Connect your ATEM switcher to the same network as your computer.
2. Open Dante Virtual Soundcard and make sure your audio sources are routed to DVS channels.
3. Run the switcher:

```bash
python atem_switcher.pyw
```

Or on Windows, download `HBS-ATEM-Auto-Switcher.exe` from the [latest release](https://github.com/nickfromsad/HBS---Atem-Auto-Switcher/releases/latest) and double-click it — no Python install needed.

4. Enter the ATEM IP address and click **Connect**.
5. For each channel row, select the DVS device, the audio channel (0 = left, 1 = right), set the gate threshold, and choose which ATEM camera input to switch to.
6. Click **▶ Start** to begin audio monitoring.
7. Press **AUTOMATION ON** to enable automatic switching.

---

## How the gate works

```
Signal level
    │
    │       ┌─── OPEN (camera on air) ───┐
    │      /                              \
────┼─────/────── threshold ──────────────\────
    │    /  ↑ attack time                  \  ↑ release time
    │   /                                   \ /
    │  ATCK                               REL → CLSD
    │
```

- **CLSD** — signal below threshold, gate closed, camera not selected
- **ATCK** — signal above threshold, waiting for attack time to confirm it is real speech
- **OPEN** — gate open, this camera is eligible to go on air (loudest open gate wins)
- **REL** — signal dropped, gate holding open during the release time before closing

---

## Settings

| Setting | Description |
|---|---|
| M/E | Which M/E bus the switcher controls (M/E 1 = main program output) |
| No-audio camera | Camera to cut to when all microphones are silent |
| Switch holdoff | Minimum seconds between two camera switches |
| Silence delay | Seconds of silence before cutting to the no-audio camera |
| Gate threshold | Signal level in dBFS the mic must exceed to open |
| Attack | Seconds the signal must stay above threshold before the gate opens |
| Release | Seconds the gate stays open after the signal drops below threshold |

---

## Stream Deck integration via Bitfocus Companion

The switcher includes a built-in HTTP server that Bitfocus Companion can talk to directly, so you can turn auto-switching on and off from a Stream Deck button.

In the **Settings** tab, set the port (default `8765`) and click **Enable**. The server starts immediately and the setting is remembered on next launch.

### Setting up in Companion

Add a new connection using the **Generic HTTP** module. Set the base URL to `http://127.0.0.1:8765` (or the IP of the PC if Companion runs on a different machine). Then on a button, add a **Send HTTP POST request** action and set the URI to one of the following:

| URI | What it does |
|---|---|
| `/automation/toggle` | Flip automation on or off |
| `/automation/on` | Turn automation on |
| `/automation/off` | Turn automation off |

For a toggle button that also shows whether automation is currently active, add a **Background Image** feedback to the same button. Set the URL to `http://127.0.0.1:8765/status/image` with a refresh interval of around 1000 ms. The button will show green when automation is on and red when it is off.

The `/status` endpoint returns a JSON response (`{"automation_active": true/false}`) if you need to read the state from another system.

---

## License

MIT
