#!/usr/bin/env python3
"""W5.8 live gate: two authenticated TCP/Noise/yamux ping directions.

Docker builds the pinned Go peer. Both binaries then run on the Linux
host, so loopback addresses reach both peers. No mock result counts as
success. Timeouts and stdin EOF bound every child process lifetime.
"""
from __future__ import annotations

import argparse
import contextlib
import os
from pathlib import Path
import platform
import re
import selectors
import shutil
import signal
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent
GO_MODULE = ROOT / "scripts/ping-peer"
GO_VERSION = re.search(r"github\.com/libp2p/go-libp2p\s+(v[^\s]+)",
                       (GO_MODULE / "go.mod").read_text()).group(1)
GO_IMAGE = "golang:1.26-alpine"
READY_ADDRESS = re.compile(r"/ip4/127\.0\.0\.1/tcp/([0-9]+)(?:/p2p/([^/\s]+))?")
PING_RESULT = re.compile(r"PING OK rtt=[0-9]+ms")


def peer_address(line: str) -> str:
    """Read the literal readiness contract and pin the announced peer."""
    fields = line.split()
    if len(fields) != 3 or fields[0] != "ADDR":
        raise ValueError("invalid ADDR line")
    address, peer = fields[1:]
    parsed = READY_ADDRESS.fullmatch(address)
    if parsed is None or "/" in peer:
        raise ValueError("expected IPv4 loopback TCP with an optional peer suffix")
    port, suffix = parsed.groups()
    if not 0 < int(port) < 65536:
        raise ValueError("invalid bound port or peer")
    if suffix is not None:
        if suffix != peer:
            raise ValueError("address suffix disagrees with the announced peer")
        return address
    return address + "/p2p/" + peer


def readiness(process: subprocess.Popen, seconds: float = 15) -> str:
    """Wait for one bounded line without blocking on a partial line."""
    deadline = time.monotonic() + seconds
    data = bytearray()
    with selectors.DefaultSelector() as selector:
        selector.register(process.stdout, selectors.EVENT_READ)
        while time.monotonic() < deadline:
            for key, _ in selector.select(min(0.2, max(0, deadline - time.monotonic()))):
                chunk = os.read(key.fd, 4096)
                if not chunk:
                    raise RuntimeError(f"server ended before readiness (exit {process.poll()})")
                data.extend(chunk)
                if len(data) > 8192:
                    raise RuntimeError("server readiness exceeds 8192 bytes")
                if b"\n" in data:
                    return peer_address(bytes(data).split(b"\n", 1)[0].decode("utf-8"))
    raise TimeoutError("server did not announce its address")


def stop(process: subprocess.Popen) -> None:
    """Close stdin first, then terminate the process group if teardown stalls."""
    if process.stdin:
        try:
            process.stdin.close()
        except (BrokenPipeError, ValueError):
            pass
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            process.wait(timeout=2)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait(timeout=2)
    if process.stdout:
        process.stdout.close()


@contextlib.contextmanager
def server(command: list[str], log: Path):
    with log.open("wb") as errors:
        process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                   stderr=errors, start_new_session=True)
        try:
            yield process
        finally:
            stop(process)


def require_ping(command: list[str]) -> None:
    """Only a successful dial process with the expected result passes a leg."""
    result = subprocess.run(command, capture_output=True, text=True, timeout=40)
    if result.returncode != 0 or not any(PING_RESULT.fullmatch(line) for line in result.stdout.splitlines()):
        raise RuntimeError(f"ping failed: {result.stdout}\n{result.stderr}")
    print(result.stdout.strip(), flush=True)


def build_go(work: Path) -> Path:
    """The Docker toolchain builds for the Linux host with CGO disabled."""
    shutil.copyfile(ROOT / "scripts/pingd.go", work / "pingd.go")
    shutil.copyfile(GO_MODULE / "go.mod", work / "go.mod")
    shutil.copyfile(GO_MODULE / "go.sum", work / "go.sum")
    name = "leanp2p-ping-build-" + work.name
    command = ["docker", "run", "--rm", "--name", name, "-v", f"{work}:/work", "-w", "/work",
               "-e", "CGO_ENABLED=0", GO_IMAGE, "go", "build", "-mod=readonly", "-o", "pingd", "pingd.go"]
    try:
        subprocess.run(command, check=True, timeout=240)
    finally:
        subprocess.run(["docker", "rm", "-f", name], stdout=subprocess.DEVNULL,
                       stderr=subprocess.DEVNULL, timeout=15, check=False)
    return work / "pingd"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-bin", type=Path, default=ROOT / ".lake/build/bin/pingnode")
    args = parser.parse_args()
    if platform.system() != "Linux":
        parser.error("the live Docker-built Go peer requires a Linux host")
    if not args.lean_bin.is_file():
        parser.error("build pingnode first: lake build pingnode")
    with tempfile.TemporaryDirectory(prefix="leanp2p-ping-") as temporary:
        work = Path(temporary)
        try:
            with server([str(args.lean_bin.resolve()), "serve", "0"], work / "lean.err") as lean:
                # The default dependency mocks fail here, before Docker or a false PASS.
                lean_address = readiness(lean)
                if shutil.which("docker") is None:
                    raise RuntimeError("Docker is required to build the pinned Go peer")
                go = build_go(work)
                with server([str(go), "-mode", "serve", "-port", "0"], work / "go.err") as other:
                    go_address = readiness(other)
                    print("Lean dials Go (tcp + noise + yamux)", flush=True)
                    require_ping([str(args.lean_bin.resolve()), "dial", go_address])
                    print("Go dials Lean (tcp + noise + yamux)", flush=True)
                    require_ping([str(go), "-mode", "dial", "-addr", lean_address])
            if lean.returncode != 0 or other.returncode != 0:
                raise RuntimeError("a server failed during stdin-EOF shutdown")
        except (OSError, RuntimeError, ValueError, TimeoutError, subprocess.SubprocessError) as error:
            print(f"interop failed: {error}", file=os.sys.stderr)
            for name in ("lean.err", "go.err"):
                log = work / name
                if log.exists():
                    print(log.read_text(errors="replace")[-8192:], file=os.sys.stderr)
            return 1
    print(f"PASS: Lean <-> go-libp2p {GO_VERSION}, both directions", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
