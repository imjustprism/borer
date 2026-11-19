#!/usr/bin/env python3
"""Measure GPUI frame pacing, Win32 input latency, startup, memory, and network.

Runs the release `borer-app` binary across every benchmark required by the app
spike:
1. First frame (`--first-frame`, 10 runs, median and max, bar <= 300 ms).
2. `notepad.exe` open to its function list (`--report-open`, 10 runs, median
   and max, bar <= 1000 ms).
3. Private-bytes delta (`--measure-memory` minus `--headless` on `notepad.exe`,
   bar <= 150 MB).
4. 100,000-row list scroll (`--measure --phase list`, 10 s, frame work/draw
   p99 <= 8.3 ms and present cadence within display refresh budget).
5. 1,000,000-line code scroll (`--measure --phase code`, 10 s, frame work/draw
   p99 <= 8.3 ms and present cadence within display refresh budget).
6. Real Win32 `SendInput` latency (`--measure --phase input`, 200 filter
   keystrokes at 20/s + 100 clicks on call tokens, bar <= 16 ms anchored at
   `SendInput` and including Windows input-queue delay).
7. Call tree expansions (`--measure --phase tree`, nodes of `notepad.exe`'s call
   tree opened one by one until 200 asked the engine). An expansion of a level the
   tree kept is UI work only and holds the 16 ms input-to-paint bar at p95; one that
   asks the engine waits for `call_children` on the background executor, engine
   work like a decompile, so it holds its own bar, p95 <= 50 ms with virtual calls
   off.
8. Action bars (`--measure --phase actions`): a fixed script of actions on
   `notepad.exe`, then on the large DLL of the list scroll, 50 runs each, timed from
   dispatch to the first presented change (ack) and to settled views (settle), and
   graph pan and zoom sweeps timed frame by frame. The bars are the harness's own
   table; this script prints the times and fails on every `MEASURE_MISS` it reports.
   A large DLL that is missing or too slow to analyze is printed as skipped.

During every measured run a background `iphlpapi` watcher polls IPv4/IPv6 TCP
and UDP owner-PID tables (`GetExtendedTcpTable` / `GetExtendedUdpTable`) and the
process table (`CreateToolhelp32Snapshot`) while confirming each phase's process
is observed alive, recording any socket opened and any child process started.
"""

from __future__ import annotations

import argparse
import collections
import contextlib
import ctypes
import ctypes.wintypes as wt
import json
import os
import re
import shutil
import socket
import statistics
import struct
import subprocess
import sys
import tempfile
import threading
import time
from collections.abc import Callable
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from harness.root import ROOT  # noqa: E402

SYSTEM_NOTEPAD = r"C:\Windows\System32\notepad.exe"

INPUT_MOUSE = 0
INPUT_KEYBOARD = 1
KEYEVENTF_KEYUP = 0x0002
MOUSEEVENTF_MOVE = 0x0001
MOUSEEVENTF_LEFTDOWN = 0x0002
MOUSEEVENTF_LEFTUP = 0x0004
MOUSEEVENTF_VIRTUALDESK = 0x4000
MOUSEEVENTF_ABSOLUTE = 0x8000
VK_BACK = 0x08
VK_CONTROL = 0x11
WM_KEYDOWN = 0x0100
WM_KEYUP = 0x0101
WM_MOUSEMOVE = 0x0200
WM_LBUTTONDOWN = 0x0201
WM_LBUTTONUP = 0x0202
MK_LBUTTON = 0x0001
MK_CONTROL = 0x0008
SM_XVIRTUALSCREEN = 76
SM_YVIRTUALSCREEN = 77
SM_CXVIRTUALSCREEN = 78
SM_CYVIRTUALSCREEN = 79
PROCESS_QUERY_LIMITED_INFORMATION = 0x1000
PROCESS_VM_READ = 0x0010


class MOUSEINPUT(ctypes.Structure):
    _fields_ = [
        ("dx", wt.LONG),
        ("dy", wt.LONG),
        ("mouseData", wt.DWORD),
        ("dwFlags", wt.DWORD),
        ("time", wt.DWORD),
        ("dwExtraInfo", ctypes.c_size_t),
    ]


class KEYBDINPUT(ctypes.Structure):
    _fields_ = [
        ("wVk", wt.WORD),
        ("wScan", wt.WORD),
        ("dwFlags", wt.DWORD),
        ("time", wt.DWORD),
        ("dwExtraInfo", ctypes.c_size_t),
    ]


class _INPUTUNION(ctypes.Union):
    _fields_ = [
        ("mi", MOUSEINPUT),
        ("ki", KEYBDINPUT),
    ]


class INPUT(ctypes.Structure):
    _anonymous_ = ("u",)
    _fields_ = [
        ("type", wt.DWORD),
        ("u", _INPUTUNION),
    ]


class PROCESS_MEMORY_COUNTERS_EX(ctypes.Structure):
    _fields_ = [
        ("cb", wt.DWORD),
        ("PageFaultCount", wt.DWORD),
        ("PeakWorkingSetSize", ctypes.c_size_t),
        ("WorkingSetSize", ctypes.c_size_t),
        ("QuotaPeakPagedPoolUsage", ctypes.c_size_t),
        ("QuotaPagedPoolUsage", ctypes.c_size_t),
        ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t),
        ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
        ("PagefileUsage", ctypes.c_size_t),
        ("PeakPagefileUsage", ctypes.c_size_t),
        ("PrivateUsage", ctypes.c_size_t),
    ]


def _enable_dpi_awareness() -> None:
    if sys.platform != "win32":
        return
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except Exception:
        with contextlib.suppress(Exception):
            ctypes.windll.user32.SetProcessDPIAware()


def read_private_bytes(pid: int) -> int:
    kernel32 = ctypes.windll.kernel32
    handle = kernel32.OpenProcess(
        PROCESS_QUERY_LIMITED_INFORMATION | PROCESS_VM_READ,
        False,
        pid,
    )
    if not handle:
        raise OSError(f"OpenProcess({pid}) failed")
    try:
        counters = PROCESS_MEMORY_COUNTERS_EX()
        counters.cb = ctypes.sizeof(PROCESS_MEMORY_COUNTERS_EX)
        ok = kernel32.K32GetProcessMemoryInfo(
            handle,
            ctypes.byref(counters),
            counters.cb,
        )
        if not ok:
            raise OSError(f"K32GetProcessMemoryInfo({pid}) failed")
        return int(counters.PrivateUsage)
    finally:
        kernel32.CloseHandle(handle)


def find_window_for_pid(pid: int, timeout_s: float = 10.0) -> int:
    user32 = ctypes.windll.user32
    deadline = time.perf_counter() + timeout_s
    enum_proc_type = ctypes.WINFUNCTYPE(wt.BOOL, wt.HWND, wt.LPARAM)
    candidates: list[tuple[int, int]] = []

    def callback(hwnd: int, _lparam: int) -> bool:
        if not user32.IsWindowVisible(hwnd):
            return True
        win_pid = wt.DWORD(0)
        user32.GetWindowThreadProcessId(hwnd, ctypes.byref(win_pid))
        if win_pid.value == pid:
            rect = wt.RECT()
            user32.GetClientRect(hwnd, ctypes.byref(rect))
            width = int(rect.right - rect.left)
            height = int(rect.bottom - rect.top)
            if width >= 400 and height >= 300:
                candidates.append((width * height, int(hwnd)))
        return True

    cb = enum_proc_type(callback)
    while time.perf_counter() < deadline:
        candidates.clear()
        user32.EnumWindows(cb, 0)
        if candidates:
            candidates.sort(reverse=True)
            return candidates[0][1]
        time.sleep(0.02)
    raise TimeoutError(f"no visible main HWND found for pid={pid}")


def focus_window(hwnd: int) -> None:
    user32 = ctypes.windll.user32
    user32.ShowWindow(wt.HWND(hwnd), 9)
    user32.BringWindowToTop(wt.HWND(hwnd))
    user32.SetForegroundWindow(wt.HWND(hwnd))


def ensure_foreground(hwnd: int, *, allow_fallback: bool) -> bool:
    user32 = ctypes.windll.user32
    user32.GetForegroundWindow.restype = wt.HWND
    if int(user32.GetForegroundWindow() or 0) == hwnd:
        return True
    focus_window(hwnd)
    fg = int(user32.GetForegroundWindow() or 0)
    if fg == hwnd:
        return True
    if allow_fallback and fg == 0:
        return False
    deadline = time.perf_counter() + 0.25
    while time.perf_counter() < deadline:
        focus_window(hwnd)
        if int(user32.GetForegroundWindow() or 0) == hwnd:
            return True
        time.sleep(0.01)
    fg = int(user32.GetForegroundWindow() or 0)
    if allow_fallback:
        return False
    raise RuntimeError(
        f"benchmark window {hwnd:#x} does not own foreground (foreground={fg:#x}); "
        "aborting before SendInput so events are never sent to another window"
    )


def _make_lparam(x: int, y: int) -> int:
    return (x & 0xFFFF) | ((y & 0xFFFF) << 16)


def _next_stdout_line(
    proc: subprocess.Popen[str],
    pending_lines: collections.deque[str],
) -> str:
    if pending_lines:
        return pending_lines.popleft()
    assert proc.stdout is not None
    return proc.stdout.readline()


class MarkCoordinator:
    """Coordinates numbered `MARK <id>` / `SENT <id> <delta_ns>` input timing lines."""

    def __init__(
        self,
        proc: subprocess.Popen[str],
        pending_lines: collections.deque[str],
    ) -> None:
        self._proc = proc
        self._pending_lines = pending_lines
        self._next_id = 0

    def arm(self) -> tuple[int, int] | None:
        assert self._proc.stdin is not None
        assert self._proc.stdout is not None
        self._next_id += 1
        mark_id = self._next_id
        expected = f"MARK_OK {mark_id}"
        try:
            self._proc.stdin.write(f"MARK {mark_id}\n")
            self._proc.stdin.flush()
        except OSError as exc:
            for rest in self._proc.stdout:
                self._pending_lines.append(rest)
            if any(item.lstrip().startswith("MEASURE_INPUT") for item in self._pending_lines):
                return None
            raise RuntimeError(f"benchmark process closed stdin before MARK_OK: {exc}") from exc
        while True:
            raw = self._proc.stdout.readline()
            if not raw:
                if any(item.lstrip().startswith("MEASURE_INPUT") for item in self._pending_lines):
                    return None
                raise RuntimeError("benchmark process closed stdout before MARK_OK")
            stripped = raw.strip()
            if stripped in ("MARK_OK", expected):
                return mark_id, time.perf_counter_ns()
            self._pending_lines.append(raw)

    def record_sent(self, armed: tuple[int, int] | None, sent_ns: int) -> None:
        if armed is None or self._proc.stdin is None:
            return
        mark_id, ack_ns = armed
        delta_ns = max(0, sent_ns - ack_ns)
        with contextlib.suppress(OSError):
            self._proc.stdin.write(f"SENT {mark_id} {delta_ns}\n")
            self._proc.stdin.flush()


def send_vk(
    hwnd: int,
    vk: int,
    *,
    marks: MarkCoordinator | None = None,
    allow_fallback: bool = False,
) -> str | None:
    user32 = ctypes.WinDLL("user32", use_last_error=True)
    scan = int(user32.MapVirtualKeyW(vk, 0)) & 0xFF
    armed: tuple[int, int] | None = None
    if ensure_foreground(hwnd, allow_fallback=allow_fallback):
        down = INPUT(type=INPUT_KEYBOARD)
        down.ki = KEYBDINPUT(wVk=vk, wScan=scan, dwFlags=0, time=0, dwExtraInfo=0)
        up = INPUT(type=INPUT_KEYBOARD)
        up.ki = KEYBDINPUT(wVk=vk, wScan=scan, dwFlags=KEYEVENTF_KEYUP, time=0, dwExtraInfo=0)
        arr = (INPUT * 2)(down, up)
        if marks is not None:
            armed = marks.arm()
            if armed is None:
                return None
        if ensure_foreground(hwnd, allow_fallback=allow_fallback):
            ctypes.set_last_error(0)
            sent_ns = time.perf_counter_ns()
            inserted = int(user32.SendInput(2, arr, ctypes.sizeof(INPUT)))
            if inserted == 2:
                if marks is not None:
                    marks.record_sent(armed, sent_ns)
                return "SendInput"
            if not allow_fallback:
                err = ctypes.get_last_error()
                raise RuntimeError(
                    f"SendInput(keyboard) inserted {inserted}/2 events (last_error={err}); "
                    "unlock the Windows desktop or pass --allow-postmessage-fallback to record "
                    "window-message fallback separately"
                )
    if marks is not None and armed is None:
        armed = marks.arm()
        if armed is None:
            return None
    lparam_down = 1 | (scan << 16)
    lparam_up = 1 | (scan << 16) | (1 << 30) | (1 << 31)
    sent_ns = time.perf_counter_ns()
    user32.PostMessageW(wt.HWND(hwnd), WM_KEYDOWN, wt.WPARAM(vk), wt.LPARAM(lparam_down))
    user32.PostMessageW(wt.HWND(hwnd), WM_KEYUP, wt.WPARAM(vk), wt.LPARAM(lparam_up))
    if marks is not None:
        marks.record_sent(armed, sent_ns)
    return "PostMessageW"


def send_ascii_char(
    hwnd: int,
    ch: str,
    *,
    marks: MarkCoordinator | None = None,
    allow_fallback: bool = False,
) -> str | None:
    user32 = ctypes.windll.user32
    mapped = int(user32.VkKeyScanW(ord(ch)))
    vk = mapped & 0xFF if mapped != -1 else ord(ch.upper())
    return send_vk(hwnd, vk, marks=marks, allow_fallback=allow_fallback)


def _control_key(up: bool) -> INPUT:
    key = INPUT(type=INPUT_KEYBOARD)
    flags = KEYEVENTF_KEYUP if up else 0
    key.ki = KEYBDINPUT(wVk=VK_CONTROL, wScan=0, dwFlags=flags, time=0, dwExtraInfo=0)
    return key


def _release_mouse_button(user32: Any, hwnd: int, lparam: wt.LPARAM) -> None:
    release = (INPUT * 2)()
    release[0].type = INPUT_MOUSE
    release[0].mi = MOUSEINPUT(
        dx=0,
        dy=0,
        mouseData=0,
        dwFlags=MOUSEEVENTF_LEFTUP,
        time=0,
        dwExtraInfo=0,
    )
    release[1] = _control_key(up=True)
    with contextlib.suppress(Exception):
        released = int(user32.SendInput(2, release, ctypes.sizeof(INPUT)))
        if released != 2:
            user32.PostMessageW(wt.HWND(hwnd), WM_LBUTTONUP, wt.WPARAM(0), lparam)


def send_client_click(
    hwnd: int,
    logical_x: float,
    logical_y: float,
    *,
    marks: MarkCoordinator | None = None,
    allow_fallback: bool = False,
) -> str | None:
    user32 = ctypes.WinDLL("user32", use_last_error=True)
    dpi = user32.GetDpiForWindow(wt.HWND(hwnd)) or 96
    scale = float(dpi) / 96.0
    px_x = round(logical_x * scale)
    px_y = round(logical_y * scale)
    pt = wt.POINT(px_x, px_y)
    user32.ClientToScreen(wt.HWND(hwnd), ctypes.byref(pt))

    vx = int(user32.GetSystemMetrics(SM_XVIRTUALSCREEN))
    vy = int(user32.GetSystemMetrics(SM_YVIRTUALSCREEN))
    vw = max(1, int(user32.GetSystemMetrics(SM_CXVIRTUALSCREEN)) - 1)
    vh = max(1, int(user32.GetSystemMetrics(SM_CYVIRTUALSCREEN)) - 1)
    abs_x = round((pt.x - vx) * 65535 / vw)
    abs_y = round((pt.y - vy) * 65535 / vh)
    vflags = MOUSEEVENTF_ABSOLUTE | MOUSEEVENTF_VIRTUALDESK
    lparam = wt.LPARAM(_make_lparam(px_x, px_y))

    armed_down: tuple[int, int] | None = None
    if ensure_foreground(hwnd, allow_fallback=allow_fallback):
        move_down = (INPUT * 3)()
        move_down[0] = _control_key(up=False)
        move_down[1].type = INPUT_MOUSE
        move_down[1].mi = MOUSEINPUT(
            dx=abs_x,
            dy=abs_y,
            mouseData=0,
            dwFlags=MOUSEEVENTF_MOVE | vflags,
            time=0,
            dwExtraInfo=0,
        )
        move_down[2].type = INPUT_MOUSE
        move_down[2].mi = MOUSEINPUT(
            dx=abs_x,
            dy=abs_y,
            mouseData=0,
            dwFlags=MOUSEEVENTF_LEFTDOWN | vflags,
            time=0,
            dwExtraInfo=0,
        )
        if marks is not None:
            armed_down = marks.arm()
            if armed_down is None:
                return None
        if ensure_foreground(hwnd, allow_fallback=allow_fallback):
            ctypes.set_last_error(0)
            sent_down_ns = time.perf_counter_ns()
            down_inserted = int(user32.SendInput(3, move_down, ctypes.sizeof(INPUT)))
            if down_inserted == 3:
                if marks is not None:
                    marks.record_sent(armed_down, sent_down_ns)
                up_sent = False
                try:
                    time.sleep(0.025)
                    armed_up = marks.arm() if marks is not None else None
                    if marks is not None and armed_up is None:
                        return None
                    ensure_foreground(hwnd, allow_fallback=False)
                    up = (INPUT * 2)()
                    up[0].type = INPUT_MOUSE
                    up[0].mi = MOUSEINPUT(
                        dx=abs_x,
                        dy=abs_y,
                        mouseData=0,
                        dwFlags=MOUSEEVENTF_LEFTUP | vflags,
                        time=0,
                        dwExtraInfo=0,
                    )
                    up[1] = _control_key(up=True)
                    ctypes.set_last_error(0)
                    sent_up_ns = time.perf_counter_ns()
                    up_inserted = int(user32.SendInput(2, up, ctypes.sizeof(INPUT)))
                    up_sent = up_inserted == 2
                    if not up_sent:
                        err = ctypes.get_last_error()
                        raise RuntimeError(
                            f"SendInput(mouse up) inserted {up_inserted}/2 events (last_error={err})"
                        )
                    if marks is not None:
                        marks.record_sent(armed_up, sent_up_ns)
                    return "SendInput"
                finally:
                    if not up_sent:
                        _release_mouse_button(user32, hwnd, lparam)
            if not allow_fallback:
                err = ctypes.get_last_error()
                raise RuntimeError(
                    f"SendInput(mouse down) inserted {down_inserted}/3 events (last_error={err}); "
                    "unlock the Windows desktop or pass --allow-postmessage-fallback to record "
                    "window-message fallback separately"
                )

    if marks is not None and armed_down is None:
        armed_down = marks.arm()
        if armed_down is None:
            return None
    sent_down_ns = time.perf_counter_ns()
    user32.PostMessageW(wt.HWND(hwnd), WM_MOUSEMOVE, wt.WPARAM(0), lparam)
    user32.PostMessageW(wt.HWND(hwnd), WM_LBUTTONDOWN, wt.WPARAM(MK_LBUTTON | MK_CONTROL), lparam)
    if marks is not None:
        marks.record_sent(armed_down, sent_down_ns)
    up_posted = False
    try:
        time.sleep(0.025)
        armed_up = marks.arm() if marks is not None else None
        if marks is not None and armed_up is None:
            return None
        sent_up_ns = time.perf_counter_ns()
        user32.PostMessageW(wt.HWND(hwnd), WM_LBUTTONUP, wt.WPARAM(MK_CONTROL), lparam)
        up_posted = True
        if marks is not None:
            marks.record_sent(armed_up, sent_up_ns)
        return "PostMessageW"
    finally:
        if not up_posted:
            with contextlib.suppress(Exception):
                user32.PostMessageW(wt.HWND(hwnd), WM_LBUTTONUP, wt.WPARAM(0), lparam)


_RUN_DIR_PREFIX = "borer-app-measure-"
"""Name prefix of the data directory each app run gets, so a sweep finds leftovers."""

_RUN_DIRS: list[Path] = []
"""Data directories of this script's app runs, removed once every run has ended."""


def _spawn_app(
    exe: Path,
    args: list[str],
    *,
    with_stdin: bool = False,
) -> tuple[subprocess.Popen[str], Callable[[], str]]:
    """Start the app over a fresh, randomly named, private data directory of its own."""
    data_dir = Path(tempfile.mkdtemp(prefix=_RUN_DIR_PREFIX))
    _RUN_DIRS.append(data_dir)
    return _spawn_bench_proc([str(exe), "--data-dir", str(data_dir), *args], with_stdin=with_stdin)


def _remove_run_dirs(dirs: list[Path]) -> str | None:
    """Remove the given run data directories; return what could not be removed, or None."""
    left: list[str] = []
    for data_dir in dirs:
        for attempt in range(20):
            try:
                shutil.rmtree(data_dir)
                break
            except FileNotFoundError:
                break
            except OSError as exc:
                if attempt == 19:
                    left.append(f"{data_dir}: {exc}")
                time.sleep(0.1)
    return "; ".join(left) or None


def _stale_run_dirs() -> list[Path]:
    """Return the run data directories earlier, killed or crashed measurements left."""
    return sorted(Path(tempfile.gettempdir()).glob(f"{_RUN_DIR_PREFIX}*"))


def _spawn_bench_proc(
    cmd: list[str],
    *,
    with_stdin: bool = False,
) -> tuple[subprocess.Popen[str], Callable[[], str]]:
    """Start `cmd` suspended; `NetWatcher.watch_while` joins it to its job, then resumes it."""
    proc = subprocess.Popen(
        cmd,
        stdin=subprocess.PIPE if with_stdin else None,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        encoding="utf-8",
        creationflags=_CREATE_SUSPENDED,
    )
    err_chunks: list[str] = []

    def _drain() -> None:
        if proc.stderr is None:
            return
        with contextlib.suppress(OSError, ValueError):
            for line in proc.stderr:
                err_chunks.append(line)

    err_thread = threading.Thread(target=_drain, daemon=True)
    err_thread.start()

    def get_stderr() -> str:
        err_thread.join(timeout=2.0)
        return "".join(err_chunks).strip()

    return proc, get_stderr


@contextlib.contextmanager
def _proc_watchdog(proc: subprocess.Popen[str], timeout_s: float, label: str) -> Any:
    timed_out = threading.Event()

    def _kill() -> None:
        timed_out.set()
        with contextlib.suppress(OSError):
            proc.kill()

    timer = threading.Timer(timeout_s, _kill)
    timer.daemon = True
    timer.start()
    try:
        yield timed_out
    except BaseException:
        if proc.poll() is None:
            with contextlib.suppress(OSError):
                proc.kill()
            with contextlib.suppress(OSError, subprocess.TimeoutExpired):
                proc.wait(timeout=5)
        raise
    finally:
        timer.cancel()
        if timed_out.is_set():
            with contextlib.suppress(OSError, subprocess.TimeoutExpired):
                proc.wait(timeout=5)
            raise TimeoutError(f"{label} timed out after {timeout_s}s")


_AF_INET = 2
_AF_INET6 = 23
_TCP_TABLE_OWNER_PID_ALL = 5
_UDP_TABLE_OWNER_PID = 1
_ERROR_INSUFFICIENT_BUFFER = 122


def _read_iphlpapi_table(fn: Any, af: int, table_class: int, label: str) -> bytes:
    size = wt.DWORD(65536)
    for _ in range(6):
        buf = ctypes.create_string_buffer(size.value)
        rc = int(fn(buf, ctypes.byref(size), False, af, table_class, 0))
        if rc == 0:
            return buf.raw[: size.value]
        if rc != _ERROR_INSUFFICIENT_BUFFER:
            raise OSError(f"{label}(af={af}) failed with Win32 error {rc}")
        size = wt.DWORD(max(size.value * 2, 65536))
    raise OSError(f"{label}(af={af}) exceeded buffer retries (needed {size.value} bytes)")


def _query_process_sockets(pid: int) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    iphlpapi = ctypes.windll.iphlpapi
    tcp: list[dict[str, Any]] = []
    udp: list[dict[str, Any]] = []

    raw_tcp4 = _read_iphlpapi_table(
        iphlpapi.GetExtendedTcpTable,
        _AF_INET,
        _TCP_TABLE_OWNER_PID_ALL,
        "GetExtendedTcpTable",
    )
    if len(raw_tcp4) >= 4:
        (n_tcp4,) = struct.unpack_from("<I", raw_tcp4, 0)
        for idx in range(n_tcp4):
            off = 4 + idx * 24
            if off + 24 > len(raw_tcp4):
                break
            state, laddr, lport, raddr, rport, owner = struct.unpack_from("<6I", raw_tcp4, off)
            if owner == pid:
                tcp.append(
                    {
                        "LocalAddress": socket.inet_ntop(
                            socket.AF_INET,
                            struct.pack("<I", laddr),
                        ),
                        "LocalPort": socket.ntohs(lport & 0xFFFF),
                        "RemoteAddress": socket.inet_ntop(
                            socket.AF_INET,
                            struct.pack("<I", raddr),
                        ),
                        "RemotePort": socket.ntohs(rport & 0xFFFF),
                        "State": int(state),
                    }
                )

    raw_tcp6 = _read_iphlpapi_table(
        iphlpapi.GetExtendedTcpTable,
        _AF_INET6,
        _TCP_TABLE_OWNER_PID_ALL,
        "GetExtendedTcpTable",
    )
    if len(raw_tcp6) >= 4:
        (n_tcp6,) = struct.unpack_from("<I", raw_tcp6, 0)
        for idx in range(n_tcp6):
            off = 4 + idx * 56
            if off + 56 > len(raw_tcp6):
                break
            laddr6, _ls, lport, raddr6, _rs, rport, state, owner = struct.unpack_from(
                "<16sII16sIIII",
                raw_tcp6,
                off,
            )
            if owner == pid:
                tcp.append(
                    {
                        "LocalAddress": socket.inet_ntop(socket.AF_INET6, laddr6),
                        "LocalPort": socket.ntohs(lport & 0xFFFF),
                        "RemoteAddress": socket.inet_ntop(socket.AF_INET6, raddr6),
                        "RemotePort": socket.ntohs(rport & 0xFFFF),
                        "State": int(state),
                    }
                )

    raw_udp4 = _read_iphlpapi_table(
        iphlpapi.GetExtendedUdpTable,
        _AF_INET,
        _UDP_TABLE_OWNER_PID,
        "GetExtendedUdpTable",
    )
    if len(raw_udp4) >= 4:
        (n_udp4,) = struct.unpack_from("<I", raw_udp4, 0)
        for idx in range(n_udp4):
            off = 4 + idx * 12
            if off + 12 > len(raw_udp4):
                break
            laddr, lport, owner = struct.unpack_from("<3I", raw_udp4, off)
            if owner == pid:
                udp.append(
                    {
                        "LocalAddress": socket.inet_ntop(
                            socket.AF_INET,
                            struct.pack("<I", laddr),
                        ),
                        "LocalPort": socket.ntohs(lport & 0xFFFF),
                    }
                )

    raw_udp6 = _read_iphlpapi_table(
        iphlpapi.GetExtendedUdpTable,
        _AF_INET6,
        _UDP_TABLE_OWNER_PID,
        "GetExtendedUdpTable",
    )
    if len(raw_udp6) >= 4:
        (n_udp6,) = struct.unpack_from("<I", raw_udp6, 0)
        for idx in range(n_udp6):
            off = 4 + idx * 28
            if off + 28 > len(raw_udp6):
                break
            laddr6, _ls, lport, owner = struct.unpack_from("<16sIII", raw_udp6, off)
            if owner == pid:
                udp.append(
                    {
                        "LocalAddress": socket.inet_ntop(socket.AF_INET6, laddr6),
                        "LocalPort": socket.ntohs(lport & 0xFFFF),
                    }
                )

    return tcp, udp


_TH32CS_SNAPPROCESS = 0x00000002
_INVALID_HANDLE_VALUE = ctypes.c_void_p(-1).value


class PROCESSENTRY32W(ctypes.Structure):
    _fields_ = [
        ("dwSize", wt.DWORD),
        ("cntUsage", wt.DWORD),
        ("th32ProcessID", wt.DWORD),
        ("th32DefaultHeapID", ctypes.c_size_t),
        ("th32ModuleID", wt.DWORD),
        ("cntThreads", wt.DWORD),
        ("th32ParentProcessID", wt.DWORD),
        ("pcPriClassBase", wt.LONG),
        ("dwFlags", wt.DWORD),
        ("szExeFile", wt.WCHAR * 260),
    ]


def _resume_process(pid: int) -> None:
    """Resume a process started suspended."""
    kernel32 = ctypes.windll.kernel32
    kernel32.OpenProcess.restype = ctypes.c_void_p
    handle = kernel32.OpenProcess(_PROCESS_SUSPEND_RESUME, False, pid)
    if not handle:
        raise OSError(f"OpenProcess({pid}) failed with Win32 error {ctypes.GetLastError()}")
    try:
        status = ctypes.windll.ntdll.NtResumeProcess(ctypes.c_void_p(handle))
        if status != 0:
            raise OSError(f"NtResumeProcess({pid}) failed with status {status:#x}")
    finally:
        kernel32.CloseHandle(ctypes.c_void_p(handle))


def _query_child_processes(pid: int) -> list[dict[str, Any]]:
    """Return every live process whose parent is `pid`, from a Toolhelp snapshot."""
    kernel32 = ctypes.windll.kernel32
    kernel32.CreateToolhelp32Snapshot.restype = ctypes.c_void_p
    snap = kernel32.CreateToolhelp32Snapshot(_TH32CS_SNAPPROCESS, 0)
    if snap is None or snap == _INVALID_HANDLE_VALUE:
        raise OSError(f"CreateToolhelp32Snapshot failed with Win32 error {ctypes.GetLastError()}")
    children: list[dict[str, Any]] = []
    try:
        entry = PROCESSENTRY32W()
        entry.dwSize = ctypes.sizeof(PROCESSENTRY32W)
        ok = kernel32.Process32FirstW(ctypes.c_void_p(snap), ctypes.byref(entry))
        while ok:
            if entry.th32ParentProcessID == pid and entry.th32ProcessID != pid:
                children.append({"pid": int(entry.th32ProcessID), "exe": entry.szExeFile})
            ok = kernel32.Process32NextW(ctypes.c_void_p(snap), ctypes.byref(entry))
    finally:
        kernel32.CloseHandle(ctypes.c_void_p(snap))
    return children


_CREATE_SUSPENDED = 0x00000004
_PROCESS_SUSPEND_RESUME = 0x0800
_PROCESS_SET_QUOTA = 0x0100
_PROCESS_TERMINATE = 0x0001
_JOB_OBJECT_BASIC_ACCOUNTING_INFORMATION = 1


class JOBOBJECT_BASIC_ACCOUNTING_INFORMATION(ctypes.Structure):
    _fields_ = [
        ("TotalUserTime", ctypes.c_int64),
        ("TotalKernelTime", ctypes.c_int64),
        ("ThisPeriodTotalUserTime", ctypes.c_int64),
        ("ThisPeriodTotalKernelTime", ctypes.c_int64),
        ("TotalPageFaultCount", wt.DWORD),
        ("TotalProcesses", wt.DWORD),
        ("ActiveProcesses", wt.DWORD),
        ("TotalTerminatedProcesses", wt.DWORD),
    ]


class ProcessJob:
    """A job object holding one spawned process and every process it starts.

    The job counts a child however briefly it lives, which polling the process table
    misses. The process joins while it is still suspended, before it runs at all. A
    program the app hands to the shell or to a COM broker (opening a URL, say) runs
    outside the job, as a child of that broker, and is not counted.
    """

    def __init__(self, pid: int) -> None:
        kernel32 = ctypes.windll.kernel32
        kernel32.CreateJobObjectW.restype = ctypes.c_void_p
        kernel32.OpenProcess.restype = ctypes.c_void_p
        self._handle = kernel32.CreateJobObjectW(None, None)
        if not self._handle:
            raise OSError(f"CreateJobObjectW failed with Win32 error {ctypes.GetLastError()}")
        proc = kernel32.OpenProcess(_PROCESS_SET_QUOTA | _PROCESS_TERMINATE, False, pid)
        if not proc:
            self.close()
            raise OSError(f"OpenProcess({pid}) failed with Win32 error {ctypes.GetLastError()}")
        try:
            if not kernel32.AssignProcessToJobObject(
                ctypes.c_void_p(self._handle), ctypes.c_void_p(proc)
            ):
                self.close()
                err = ctypes.GetLastError()
                raise OSError(f"AssignProcessToJobObject failed with Win32 error {err}")
        finally:
            kernel32.CloseHandle(ctypes.c_void_p(proc))

    def children(self) -> int:
        """Return how many processes besides the spawned one have run in the job."""
        info = JOBOBJECT_BASIC_ACCOUNTING_INFORMATION()
        ok = ctypes.windll.kernel32.QueryInformationJobObject(
            ctypes.c_void_p(self._handle),
            _JOB_OBJECT_BASIC_ACCOUNTING_INFORMATION,
            ctypes.byref(info),
            ctypes.sizeof(info),
            None,
        )
        if not ok:
            raise OSError(
                f"QueryInformationJobObject failed with Win32 error {ctypes.GetLastError()}"
            )
        return max(int(info.TotalProcesses) - 1, 0)

    def close(self) -> None:
        if self._handle:
            ctypes.windll.kernel32.CloseHandle(ctypes.c_void_p(self._handle))
            self._handle = None


class NetWatcher:
    """Sub-millisecond `iphlpapi` socket-table poller tracking live phase coverage.

    Each watched process also runs in its own job object, whose count of every process it
    started is the phase's child count; the process-table polls name the children seen.
    """

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._closed = threading.Event()
        self._live_phases: set[str] = set()
        self.events: list[dict[str, Any]] = []
        self.children: dict[tuple[int, str], dict[str, Any]] = {}
        self.child_counts: dict[str, int] = {}
        self._jobs: dict[str, ProcessJob] = {}
        self.polls = 0
        self.error: str | None = None
        self.unmonitored_phases: list[str] = []

    def _record_failure(self, phase: str, reason: str) -> None:
        if self.error is None:
            self.error = f"{phase}: {reason}"
        if phase not in self.unmonitored_phases:
            self.unmonitored_phases.append(phase)

    def poll_proc(self, proc: subprocess.Popen[str], phase: str) -> bool:
        if self._closed.is_set():
            return False
        with self._lock:
            if self._closed.is_set():
                return False
            if self.error is not None:
                if phase not in self.unmonitored_phases:
                    self.unmonitored_phases.append(phase)
                return False
            if proc.poll() is not None:
                return False
            try:
                tcp, udp = _query_process_sockets(proc.pid)
                children = _query_child_processes(proc.pid)
            except Exception as exc:
                self._record_failure(phase, f"socket or process query failed ({exc})")
                return False
            still_alive = proc.poll() is None
            self.polls += 1
            for conn in tcp:
                self.events.append({"phase": phase, "proto": "tcp", **conn})
            for ep in udp:
                self.events.append({"phase": phase, "proto": "udp", **ep})
            for child in children:
                self.children.setdefault((child["pid"], child["exe"]), {"phase": phase, **child})
            if still_alive:
                self._live_phases.add(phase)
            return still_alive

    def finish_phase(self, phase: str) -> None:
        with self._lock:
            if phase not in self._live_phases and phase not in self.unmonitored_phases:
                self.unmonitored_phases.append(phase)
            job = self._jobs.pop(phase, None)
            if job is not None:
                try:
                    count = job.children()
                except OSError as exc:
                    self._record_failure(phase, f"job query failed ({exc})")
                    count = 0
                finally:
                    job.close()
                if count:
                    self.child_counts[phase] = count

    def child_total(self) -> int:
        """Return the children of every finished phase, each counted once."""
        return max(sum(self.child_counts.values()), len(self.children))

    def watch_while(self, proc: subprocess.Popen[str], phase: str) -> threading.Thread:
        try:
            self._jobs[phase] = ProcessJob(proc.pid)
        except OSError as exc:
            self._record_failure(phase, f"job object setup failed ({exc})")
        finally:
            _resume_process(proc.pid)
        self.poll_proc(proc, phase)

        def runner() -> None:
            ticks = 0
            while proc.poll() is None and not self._closed.is_set():
                self.poll_proc(proc, phase)
                ticks += 1
                steps = 2 if ticks <= 6 else 10
                for _ in range(steps):
                    if proc.poll() is not None or self._closed.is_set():
                        return
                    time.sleep(0.05 if ticks <= 6 else 0.1)

        thread = threading.Thread(target=runner, daemon=True)
        thread.start()
        return thread

    def close(self) -> None:
        self._closed.set()


def child_count_self_test() -> str | None:
    """Return why the watcher miscounts a stand-in parent with one 10 ms child, or None.

    The parent starts `cmd.exe /c exit`, which is gone before most polls, then lives on
    for several poll cycles; the watcher must report exactly one child.
    """
    script = "import subprocess, time; subprocess.run(['cmd.exe', '/c', 'exit']); time.sleep(1.0)"
    watcher = NetWatcher()
    python = getattr(sys, "_base_executable", sys.executable)
    proc, get_stderr = _spawn_bench_proc([python, "-I", "-c", script])
    thread = watcher.watch_while(proc, "self-test")
    rc = proc.wait(timeout=30)
    thread.join(timeout=2)
    watcher.finish_phase("self-test")
    watcher.close()
    if rc != 0:
        return f"stand-in parent exited with code {rc}: {get_stderr()}"
    if watcher.error is not None:
        return watcher.error
    if watcher.child_total() != 1:
        return f"reported {watcher.child_total()} children, not 1 ({watcher.child_counts})"
    return None


def query_hardware() -> dict[str, Any]:
    ps = r"""
$cpu = (Get-CimInstance Win32_Processor | Select-Object -First 1).Name
$gpus = @(Get-CimInstance Win32_VideoController | ForEach-Object {
    @{ name = $_.Name; hz = $_.CurrentRefreshRate }
})
@{ cpu = $cpu; gpus = $gpus } | ConvertTo-Json -Compress
"""
    res = subprocess.run(
        ["powershell", "-NoProfile", "-NonInteractive", "-Command", ps],
        capture_output=True,
        text=True,
        check=True,
    )
    return json.loads(res.stdout.strip())


def parse_kv_line(line: str) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for key, raw_val in re.findall(r'(\w+)=(".*?"|\S+)', line):
        if raw_val.startswith('"') and raw_val.endswith('"'):
            out[key] = raw_val[1:-1]
            continue
        if raw_val in ("true", "false"):
            out[key] = raw_val == "true"
            continue
        try:
            out[key] = int(raw_val)
            continue
        except ValueError:
            pass
        try:
            out[key] = float(raw_val)
            continue
        except ValueError:
            out[key] = raw_val
    return out


def measure_timed_marker(
    exe: Path,
    args: list[str],
    marker: str,
    runs: int,
    watcher: NetWatcher,
    phase: str,
) -> dict[str, Any]:
    samples_ms: list[float] = []
    last_kv: dict[str, Any] = {}
    for i in range(runs):
        phase_id = f"{phase}-{i}"
        t0 = time.perf_counter()
        proc, get_stderr = _spawn_app(exe, args)
        watch_thread = watcher.watch_while(proc, phase_id)
        assert proc.stdout is not None
        matched = False
        rc = 0
        with _proc_watchdog(proc, 30.0, phase_id):
            for line in proc.stdout:
                if line.startswith(marker):
                    elapsed_ms = (time.perf_counter() - t0) * 1000.0
                    samples_ms.append(elapsed_ms)
                    last_kv = parse_kv_line(line)
                    matched = True
                    watcher.poll_proc(proc, phase_id)
                    break
            rc = proc.wait(timeout=30)
        watch_thread.join(timeout=2)
        watcher.finish_phase(phase_id)
        err = get_stderr()
        if not matched:
            raise RuntimeError(f"{phase} run {i} missed {marker} (rc={rc}): {err}")
        if rc != 0:
            raise RuntimeError(f"{phase} run {i} exited with code {rc}: {err}")
    return {
        "runs": runs,
        "samples_ms": [round(x, 2) for x in samples_ms],
        "median_ms": round(statistics.median(samples_ms), 2),
        "max_ms": round(max(samples_ms), 2),
        "meta": last_kv,
    }


def measure_memory_delta(exe: Path, binary: str, watcher: NetWatcher) -> dict[str, Any]:
    def sample_mode(flag: str, marker: str, label: str) -> tuple[int, dict[str, Any]]:
        proc, get_stderr = _spawn_app(exe, [flag, binary], with_stdin=True)
        watch_thread = watcher.watch_while(proc, label)
        assert proc.stdout is not None and proc.stdin is not None
        kv: dict[str, Any] = {}
        rc = 0
        with _proc_watchdog(proc, 30.0, label):
            for line in proc.stdout:
                if line.startswith(marker):
                    kv = parse_kv_line(line)
                    break
            if not kv:
                proc.kill()
                proc.wait(timeout=5)
                raise RuntimeError(f"{label} missed {marker}: {get_stderr()}")
            private_b = read_private_bytes(proc.pid)
            watcher.poll_proc(proc, label)
            proc.stdin.write("\n")
            proc.stdin.flush()
            rc = proc.wait(timeout=15)
        watch_thread.join(timeout=2)
        watcher.finish_phase(label)
        if rc != 0:
            raise RuntimeError(f"{label} exited with code {rc}: {get_stderr()}")
        return private_b, kv

    headless_b, headless_kv = sample_mode("--headless", "HEADLESS_READY", "headless")
    ui_b, ui_kv = sample_mode("--measure-memory", "MEMORY_READY", "measure-memory")
    delta_mb = (ui_b - headless_b) / (1024.0 * 1024.0)
    return {
        "headless_mb": round(headless_b / (1024.0 * 1024.0), 2),
        "ui_mb": round(ui_b / (1024.0 * 1024.0), 2),
        "delta_mb": round(delta_mb, 2),
        "headless_meta": headless_kv,
        "ui_meta": ui_kv,
    }


def measure_scroll_phase(
    exe: Path, kind: str, watcher: NetWatcher, marker: str = "MEASURE_SCROLL"
) -> dict[str, Any]:
    phase_id = f"scroll-{kind}"
    proc, get_stderr = _spawn_app(exe, ["--measure", "--phase", kind])
    watch_thread = watcher.watch_while(proc, phase_id)
    assert proc.stdout is not None
    kv: dict[str, Any] = {}
    rc = 0
    with _proc_watchdog(proc, 400.0, phase_id):
        for line in proc.stdout:
            print(f"  [{kind}] {line.rstrip()}", flush=True)
            if line.startswith(marker):
                kv = parse_kv_line(line)
        rc = proc.wait(timeout=400)
    watch_thread.join(timeout=2)
    watcher.finish_phase(phase_id)
    err = get_stderr()
    if not kv:
        raise RuntimeError(f"scroll {kind} failed (rc={rc}): {err}")
    if rc != 0:
        raise RuntimeError(f"scroll {kind} exited with code {rc}: {err}")
    return kv


def _stall_watchdog(proc: subprocess.Popen[str], idle_s: float, last: list[str]) -> threading.Event:
    """Kill `proc` once it prints nothing for `idle_s` seconds; `last` holds its latest line."""
    stalled = threading.Event()
    seen = [time.monotonic(), ""]

    def _poll() -> None:
        while proc.poll() is None:
            if last and last[-1] != seen[1]:
                seen[:] = [time.monotonic(), last[-1]]
            if time.monotonic() - seen[0] > idle_s:
                stalled.set()
                with contextlib.suppress(OSError):
                    proc.kill()
                return
            time.sleep(0.5)

    threading.Thread(target=_poll, daemon=True).start()
    return stalled


ACTIONS_IDLE_S = 60.0
"""Longest the actions phase may go without a line: each run of its script prints one."""


def measure_actions(exe: Path, watcher: NetWatcher) -> dict[str, Any]:
    """Run the actions phase, print its table, and return its rows, misses and skips.

    The app prints a `MEASURE_RUN` line as each run of the script starts; a phase that
    prints nothing for `ACTIONS_IDLE_S` is killed and fails naming the run it stalled in.
    """
    proc, get_stderr = _spawn_app(exe, ["--measure", "--phase", "actions"])
    watch_thread = watcher.watch_while(proc, "actions")
    assert proc.stdout is not None
    out: dict[str, Any] = {"actions": [], "frames": [], "misses": [], "skipped": [], "end": {}}
    rc = 0
    last: list[str] = []
    stalled = _stall_watchdog(proc, ACTIONS_IDLE_S, last)
    with _proc_watchdog(proc, 3600.0, "actions"):
        for line in proc.stdout:
            last.append(line.strip())
            del last[:-1]
            kv = parse_kv_line(line)
            for marker, key in (
                ("MEASURE_ACTION ", "actions"),
                ("MEASURE_FRAMES ", "frames"),
                ("MEASURE_MISS ", "misses"),
                ("MEASURE_ACTIONS_SKIPPED ", "skipped"),
            ):
                if line.startswith(marker):
                    out[key].append(kv)
            if line.startswith("MEASURE_ACTIONS "):
                out["end"] = kv
        rc = proc.wait(timeout=60)
    watch_thread.join(timeout=2)
    watcher.finish_phase("actions")
    if stalled.is_set():
        where = last[-1] if last else "before its first line"
        raise RuntimeError(
            f"actions phase stalled: no line for {ACTIONS_IDLE_S:.0f} s after {where!r}"
        )
    if not out["end"]:
        raise RuntimeError(f"actions phase missed MEASURE_ACTIONS (rc={rc}): {get_stderr()}")
    if rc != 0:
        raise RuntimeError(f"actions phase exited with code {rc}: {get_stderr()}")
    head = "bench    action    ack p50/p95/p99/max ms (n)        settle p50/p95/p99/max ms (n)"
    print(f"    {head}   still late skipped", flush=True)
    for row in out["actions"]:
        cells = [
            "/".join(
                f"{float(row.get(f'{part}_{q}_ms', 0)):.2f}" for q in ("p50", "p95", "p99", "max")
            )
            + f" ({row.get(f'{part}_samples', 0)})"
            for part in ("ack", "settle")
        ]
        print(
            f"    {row.get('bench'):<8} {row.get('action'):<9} {cells[0]:<33} {cells[1]:<33}"
            f" {row.get('still')} {row.get('late')} {row.get('skipped')}",
            flush=True,
        )
    for row in out["frames"]:
        print(
            f"    {row.get('bench'):<8} {row.get('sweep'):<9} frame draw p99 {row.get('p99_ms')} ms"
            f" max {row.get('max_ms')} ms ({row.get('samples')} frames)",
            flush=True,
        )
    for row in out["skipped"]:
        print(f"    [skip] {row.get('bench')}: {row.get('reason')}", flush=True)
    return out


def measure_folder_drop(exe: Path, watcher: NetWatcher) -> dict[str, Any]:
    """Drop a folder whose settings start a context server on the app and read back
    the project's folder count; the watcher's job counts any program the drop started."""
    with tempfile.TemporaryDirectory(prefix="borer-app-drop-") as tmp:
        settings = Path(tmp) / ".zed" / "settings.json"
        settings.parent.mkdir()
        server = {"context_servers": {"x": {"command": "cmd.exe", "args": ["/c", "exit"]}}}
        settings.write_text(json.dumps(server), encoding="utf-8")
        proc, get_stderr = _spawn_app(exe, ["--measure-drop", tmp])
        watch_thread = watcher.watch_while(proc, "drop")
        assert proc.stdout is not None
        kv: dict[str, Any] = {}
        rc = 0
        with _proc_watchdog(proc, 60.0, "drop"):
            for line in proc.stdout:
                if line.startswith("DROP_DONE"):
                    kv = parse_kv_line(line)
                    break
            rc = proc.wait(timeout=30)
        watch_thread.join(timeout=2)
        watcher.finish_phase("drop")
        if not kv:
            raise RuntimeError(f"drop phase missed DROP_DONE (rc={rc}): {get_stderr()}")
        if rc != 0:
            raise RuntimeError(f"drop phase exited with code {rc}: {get_stderr()}")
    return kv


def measure_input_latency(
    exe: Path,
    watcher: NetWatcher,
    *,
    allow_fallback: bool = False,
) -> dict[str, Any]:
    proc, get_stderr = _spawn_app(exe, ["--measure", "--phase", "input"], with_stdin=True)
    watch_thread = watcher.watch_while(proc, "input")
    hwnd: int | None = None
    kv: dict[str, Any] = {}
    deliveries: set[str] = set()
    pattern = ["m", "a", "i", "n"]
    pending_lines: collections.deque[str] = collections.deque()
    marks = MarkCoordinator(proc, pending_lines)

    rc = 0
    with _proc_watchdog(proc, 120.0, "input"):
        while True:
            raw = _next_stdout_line(proc, pending_lines)
            if not raw:
                break
            line = raw.strip()
            if not line.startswith("CALL_TARGET") or "clicks=0" in line or "clicks=99" in line:
                print(f"  [input] {line}", flush=True)
            if line.startswith("INPUT_FILTER_READY"):
                hwnd = find_window_for_pid(proc.pid)
                ensure_foreground(hwnd, allow_fallback=allow_fallback)
                time.sleep(0.1)
                for idx in range(200):
                    mod = idx % 8
                    if mod < 4:
                        sent = send_ascii_char(
                            hwnd,
                            pattern[mod],
                            marks=marks,
                            allow_fallback=allow_fallback,
                        )
                    else:
                        sent = send_vk(
                            hwnd,
                            VK_BACK,
                            marks=marks,
                            allow_fallback=allow_fallback,
                        )
                    if sent is not None:
                        deliveries.add(sent)
                    time.sleep(0.05)
            elif line.startswith("CALL_TARGET"):
                if any(
                    item.lstrip().startswith(("MEASURE_INPUT", "CALL_TARGET"))
                    for item in pending_lines
                ):
                    continue
                target = parse_kv_line(line)
                if hwnd is None:
                    hwnd = find_window_for_pid(proc.pid)
                sent = send_client_click(
                    hwnd,
                    float(target["x"]),
                    float(target["y"]),
                    marks=marks,
                    allow_fallback=allow_fallback,
                )
                if sent is not None:
                    deliveries.add(sent)
            elif line.startswith("MEASURE_INPUT"):
                kv = parse_kv_line(line)
                break
        rc = proc.wait(timeout=60)
    watch_thread.join(timeout=2)
    watcher.finish_phase("input")
    err = get_stderr()
    if not kv:
        raise RuntimeError(f"input latency phase failed (rc={rc}): {err}")
    if rc != 0:
        raise RuntimeError(f"input latency phase exited with code {rc}: {err}")
    delivery = "+".join(sorted(deliveries))
    kv["delivery"] = delivery
    kv["sendinput_verified"] = delivery == "SendInput"
    if not allow_fallback and not kv["sendinput_verified"]:
        raise RuntimeError(f"SendInput verification failed: observed delivery={delivery!r}")
    if int(kv.get("queue_samples", 0)) < 300:
        raise RuntimeError(
            f"input queue-delay samples incomplete: queue_samples={kv.get('queue_samples')}"
        )
    return kv


def default_release_exe() -> Path:
    outer = Path(os.environ.get("CARGO_TARGET_DIR") or (ROOT / "target"))
    direct = outer / "release" / "borer-app.exe"
    if direct.is_file():
        return direct
    nested = outer / "app" / "release" / "borer-app.exe"
    return nested


def _build_report(
    exe: Path,
    hw: dict[str, Any],
    first_frame: dict[str, Any],
    open_notepad: dict[str, Any],
    memory: dict[str, Any],
    list_scroll: dict[str, Any],
    code_scroll: dict[str, Any],
    input_lat: dict[str, Any],
    watcher: NetWatcher,
) -> dict[str, Any]:
    verified = bool(input_lat.get("sendinput_verified"))
    report: dict[str, Any] = {
        "exe": str(exe),
        "exe_bytes": exe.stat().st_size,
        "hardware": hw,
        "first_frame": first_frame,
        "open_notepad": open_notepad,
        "memory": memory,
        "list_scroll": list_scroll,
        "code_scroll": code_scroll,
        "input_latency": input_lat if verified else None,
        "network": {
            "sampling": "polled_active_endpoints",
            "polls": watcher.polls,
            "connections": watcher.events,
            "error": watcher.error,
            "unmonitored_phases": watcher.unmonitored_phases,
        },
        "child_processes": {
            "total": watcher.child_total(),
            "by_phase": watcher.child_counts,
            "seen": list(watcher.children.values()),
        },
    }
    if not verified:
        report["input_latency_fallback"] = input_lat
    return report


def _collect_bar_failures(
    first_frame: dict[str, Any],
    open_notepad: dict[str, Any],
    memory: dict[str, Any],
    list_scroll: dict[str, Any],
    code_scroll: dict[str, Any],
    input_lat: dict[str, Any],
    watcher: NetWatcher,
) -> list[str]:
    failures: list[str] = []
    if watcher.error is not None:
        failures.append(f"incomplete network monitoring ({watcher.error})")
    if watcher.unmonitored_phases:
        failures.append(f"unmonitored phases: {watcher.unmonitored_phases}")
    if watcher.events:
        failures.append(f"unexpected network sockets opened ({len(watcher.events)})")
    if watcher.child_total():
        failures.append(f"unexpected child processes started ({watcher.child_total()})")
    if float(first_frame.get("median_ms", 9999.0)) > 300.0:
        failures.append(
            f"first-frame median {first_frame.get('median_ms')} ms exceeds 300.0 ms bar"
        )
    if float(open_notepad.get("median_ms", 9999.0)) > 1000.0:
        failures.append(
            f"open-notepad median {open_notepad.get('median_ms')} ms exceeds 1000.0 ms bar"
        )
    if float(memory.get("delta_mb", 9999.0)) > 150.0:
        failures.append(f"memory delta {memory.get('delta_mb')} MB exceeds 150.0 MB bar")
    for label, phase in (("list-scroll", list_scroll), ("code-scroll", code_scroll)):
        if phase.get("painted") is not True:
            failures.append(f"{label} scrolled a view that was not painted")
        if int(phase.get("draw_n", 0)) <= 0:
            failures.append(f"{label} recorded zero draw samples (draw_n={phase.get('draw_n')})")
        if int(phase.get("present_n", 0)) <= 0:
            failures.append(
                f"{label} recorded zero present samples (present_n={phase.get('present_n')})"
            )
        if float(phase.get("draw_p99_ms", 9999.0)) > 8.3:
            failures.append(f"{label} draw p99 {phase.get('draw_p99_ms')} ms exceeds 8.3 ms bar")
        if int(phase.get("work_n", 0)) > 0 and float(phase.get("work_p99_ms", 9999.0)) > 8.3:
            failures.append(
                f"{label} frame work p99 {phase.get('work_p99_ms')} ms exceeds 8.3 ms bar"
            )
        refresh_ms = float(phase.get("refresh_ms", 0.0))
        present_bar_ms = round(max(8.3, refresh_ms * 1.25), 3) if refresh_ms > 0.0 else 8.3
        if float(phase.get("present_p99_ms", 9999.0)) > present_bar_ms:
            failures.append(
                f"{label} present interval p99 {phase.get('present_p99_ms')} ms exceeds "
                f"{present_bar_ms} ms cadence bar"
            )
        if int(phase.get("ui_engine_calls", 1)) != 0:
            failures.append(
                f"{label} recorded {phase.get('ui_engine_calls')} UI-thread engine calls"
            )
    if "not_measured" in input_lat:
        failures.append(f"input-to-paint not measured: {input_lat['not_measured']}")
        return failures
    if not input_lat.get("sendinput_verified"):
        failures.append(f"SendInput not verified (delivery={input_lat.get('delivery')!r})")
    if int(input_lat.get("samples", 0)) <= 0:
        failures.append(
            f"input phase recorded zero latency samples (samples={input_lat.get('samples')})"
        )
    if float(input_lat.get("p99_ms", 9999.0)) > 16.0:
        failures.append(f"input-to-paint p99 {input_lat.get('p99_ms')} ms exceeds 16.0 ms bar")
    if int(input_lat.get("ui_engine_calls", 1)) != 0:
        failures.append(
            f"input phase recorded {input_lat.get('ui_engine_calls')} UI-thread engine calls"
        )
    return failures


def main() -> int:
    if sys.platform != "win32":
        print("[skip] app_measure: Windows-only GPUI benchmark harness")
        return 0

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exe", type=Path, default=None, help="Path to release borer-app.exe")
    parser.add_argument("--json", type=Path, default=None, help="Optional JSON report path")
    parser.add_argument("--runs", type=int, default=10, help="Startup/open run count (default 10)")
    parser.add_argument(
        "--allow-postmessage-fallback",
        action="store_true",
        help="Record PostMessageW fallback separately if SendInput is blocked; still exits 1.",
    )
    args = parser.parse_args()

    selftest = child_count_self_test()
    if selftest is not None:
        print(f"ERROR: child-process watcher self-test: {selftest}", file=sys.stderr)
        return 1
    _enable_dpi_awareness()
    exe = (args.exe or default_release_exe()).resolve()
    if not exe.is_file():
        print(f"release binary not found at {exe}", file=sys.stderr)
        return 1

    hw = query_hardware()
    print(f"Hardware: CPU={hw['cpu']} GPUs={hw['gpus']}", flush=True)
    print(f"Binary:   {exe} ({exe.stat().st_size:,} bytes)", flush=True)

    stale = _remove_run_dirs(_stale_run_dirs())
    if stale is not None:
        print(f"ERROR: run data directories left by earlier measurements: {stale}", file=sys.stderr)
        return 1
    watcher = NetWatcher()
    try:
        print("==> 1/6 First frame (10 runs)...", flush=True)
        first_frame = measure_timed_marker(
            exe,
            ["--first-frame"],
            "FIRST_FRAME_READY",
            args.runs,
            watcher,
            "first-frame",
        )
        print(
            f"    median={first_frame['median_ms']} ms max={first_frame['max_ms']} ms", flush=True
        )

        print("==> 2/6 notepad.exe open to list (10 runs)...", flush=True)
        open_notepad = measure_timed_marker(
            exe,
            ["--report-open", SYSTEM_NOTEPAD],
            "OPEN_LIST_READY",
            args.runs,
            watcher,
            "open-notepad",
        )
        print(
            f"    median={open_notepad['median_ms']} ms max={open_notepad['max_ms']} ms",
            flush=True,
        )

        print("==> 3/6 Memory delta (--measure-memory minus --headless)...", flush=True)
        memory = measure_memory_delta(exe, SYSTEM_NOTEPAD, watcher)
        print(
            f"    headless={memory['headless_mb']} MB ui={memory['ui_mb']} MB "
            f"delta={memory['delta_mb']} MB",
            flush=True,
        )

        print("==> 4/6 100k-row list scroll (10 s)...", flush=True)
        list_scroll = measure_scroll_phase(exe, "list", watcher)

        print("==> 5/6 1M-line code scroll (10 s)...", flush=True)
        code_scroll = measure_scroll_phase(exe, "code", watcher)

        print("==> 6/6 Win32 SendInput latency (200 keys + 100 clicks)...", flush=True)
        try:
            input_lat = measure_input_latency(
                exe,
                watcher,
                allow_fallback=args.allow_postmessage_fallback,
            )
        except (RuntimeError, TimeoutError) as exc:
            input_lat = {"not_measured": str(exc)}
            print(f"    input: not measured: {exc}", flush=True)

        print("==> drop of a folder with a context server in its settings...", flush=True)
        folder_drop = measure_folder_drop(exe, watcher)
        print(f"    folders={folder_drop.get('folders')}", flush=True)

        print("==> call tree expansions (200 on notepad.exe)...", flush=True)
        call_tree = measure_scroll_phase(exe, "tree", watcher, marker="MEASURE_TREE")

        print("==> action bars (notepad.exe, then the large DLL)...", flush=True)
        actions = measure_actions(exe, watcher)
    finally:
        watcher.close()
        left = _remove_run_dirs(_RUN_DIRS)

    report = _build_report(
        exe,
        hw,
        first_frame,
        open_notepad,
        memory,
        list_scroll,
        code_scroll,
        input_lat,
        watcher,
    )
    report["folder_drop"] = folder_drop
    report["call_tree"] = call_tree
    report["actions"] = actions

    if args.json is not None:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    print("\n=== SUMMARY ===", flush=True)
    print(json.dumps(report, indent=2), flush=True)
    failures = _collect_bar_failures(
        first_frame,
        open_notepad,
        memory,
        list_scroll,
        code_scroll,
        input_lat,
        watcher,
    )
    for where in ("on_start", "on_tab"):
        if folder_drop.get(where) is not True:
            failures.append(f"the drop {where} did not reach a tab's drop handler")
    if int(call_tree.get("samples", 0)) < 200:
        failures.append(f"call tree timed {call_tree.get('samples')} of 200 expansions")
    if float(call_tree.get("p95_ms", 9999.0)) > 50.0:
        failures.append(f"call tree expand p95 {call_tree.get('p95_ms')} ms exceeds 50.0 ms bar")
    if int(call_tree.get("kept_samples", 0)) > 0 and float(call_tree.get("kept_p95_ms")) > 16.0:
        failures.append(
            f"call tree kept-level expand p95 {call_tree.get('kept_p95_ms')} ms exceeds 16.0 ms bar"
        )
    if int(call_tree.get("ui_engine_calls", 1)) != 0:
        failures.append(
            f"call tree phase recorded {call_tree.get('ui_engine_calls')} UI-thread engine calls"
        )
    for miss in actions["misses"]:
        failures.append(
            f"{miss.get('bench')} {miss.get('what')} {miss.get('held')} misses its bar: "
            + " ".join(f"{k}={v}" for k, v in miss.items() if k not in ("bench", "what", "held"))
        )
    if int(actions["end"].get("ui_engine_calls", 1)) != 0:
        failures.append(
            f"actions phase recorded {actions['end'].get('ui_engine_calls')} UI-thread engine calls"
        )
    if left is not None:
        failures.append(f"run data directories not removed: {left}")
    if folder_drop.get("folders") != 0:
        failures.append(
            f"a dropped folder joined the project (folders={folder_drop.get('folders')})"
        )
    if failures:
        for msg in failures:
            print(f"ERROR: {msg}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
