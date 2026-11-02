#!/usr/bin/env python3
"""Rebuild the patched Snappy tree and compare it with the vendor tree.

The script reads the package that contains it. The caller's working
directory does not matter. It uses the standard library only, and it
does not use the network. A failing check exits nonzero.
"""

from __future__ import annotations

import hashlib
import os
import stat
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path
from typing import NoReturn


PACKAGE_ROOT = Path(__file__).resolve().parent.parent
REPOSITORY_ROOT = PACKAGE_ROOT.parents[2]
UPSTREAM = PACKAGE_ROOT / "upstream"
PRISTINE = UPSTREAM / "pristine"
VENDOR = PACKAGE_ROOT / "native" / "vendor" / "snappy"
PATCH = PACKAGE_ROOT / "patches" / "0001-block-only.patch"
TOML_PATH = UPSTREAM / "UPSTREAM.toml"
SUMS_PATH = UPSTREAM / "SHA256SUMS"

EXPECTED_REPOSITORY = "https://github.com/google/snappy"
EXPECTED_RELEASE = "1.3.1"
EXPECTED_COMMIT = "9c28114a38866f6deeaa826db918293bc28ae410"
EXPECTED_FILES = (
    "COPYING",
    "pristine/snappy.cc",
    "pristine/snappy.h",
    "pristine/snappy-internal.h",
    "pristine/snappy-sinksource.cc",
    "pristine/snappy-sinksource.h",
    "pristine/snappy-stubs-internal.h",
    "pristine/snappy-stubs-public.h.in",
)
PRISTINE_NAMES = tuple(
    rel.removeprefix("pristine/") for rel in EXPECTED_FILES if rel != "COPYING"
)
EXPECTED_TREE = tuple(sorted(PRISTINE_NAMES))
EXPECTED_METADATA_KEYS = frozenset({"repository", "release", "commit", "files"})


def fail(message: str) -> NoReturn:
    print(f"verify-upstream: {message}", file=sys.stderr)
    raise SystemExit(1)


def display(path: Path) -> str:
    try:
        return path.resolve().relative_to(PACKAGE_ROOT).as_posix()
    except ValueError:
        return path.name


def reject_rel_path(rel: str, label: str) -> None:
    if rel == "" or rel != rel.strip():
        fail(f"{label}: malformed path")
    if "\\" in rel or "\x00" in rel or "//" in rel or rel.endswith("/"):
        fail(f"{label}: malformed path {rel!r}")
    candidate = Path(rel)
    if candidate.is_absolute() or rel.startswith("/"):
        fail(f"{label}: absolute path {rel!r}")
    if candidate.parts != tuple(part for part in rel.split("/") if part != ""):
        fail(f"{label}: malformed path {rel!r}")
    if any(part in ("", ".", "..") for part in candidate.parts):
        fail(f"{label}: escaping path {rel!r}")


def read_regular(path: Path) -> bytes:
    try:
        info = os.lstat(path)
    except FileNotFoundError:
        fail(f"missing {display(path)}")
    except OSError as exc:
        fail(f"cannot read {display(path)}: {exc.strerror}")
    if stat.S_ISLNK(info.st_mode):
        fail(f"symlink {display(path)}")
    if not stat.S_ISREG(info.st_mode):
        fail(f"not a regular file: {display(path)}")
    flags = os.O_RDONLY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        fd = os.open(path, flags)
    except FileNotFoundError:
        fail(f"missing {display(path)}")
    except OSError as exc:
        fail(f"cannot read {display(path)}: {exc.strerror}")
    try:
        opened = os.fstat(fd)
        if not stat.S_ISREG(opened.st_mode):
            fail(f"not a regular file: {display(path)}")
        chunks = []
        while True:
            block = os.read(fd, 1024 * 1024)
            if not block:
                break
            chunks.append(block)
        return b"".join(chunks)
    finally:
        os.close(fd)


def text_of(path: Path) -> str:
    try:
        return read_regular(path).decode("utf-8")
    except UnicodeDecodeError:
        fail(f"{display(path)}: invalid UTF-8")


def parse_sums(text: str) -> dict[str, str]:
    found: dict[str, str] = {}
    if text == "":
        fail("SHA256SUMS: empty")
    if not text.endswith("\n"):
        fail("SHA256SUMS: missing final newline")
    for number, line in enumerate(text.splitlines(), 1):
        if line.strip() == "":
            fail(f"SHA256SUMS:{number}: blank line")
        digest, separator, rel = line.partition("  ")
        if separator != "  " or "  " in rel or rel == "":
            fail(f"SHA256SUMS:{number}: malformed line")
        if len(digest) != 64 or any(ch not in "0123456789abcdef" for ch in digest):
            fail(f"SHA256SUMS:{number}: malformed digest")
        reject_rel_path(rel, f"SHA256SUMS:{number}")
        if rel in found:
            fail(f"SHA256SUMS:{number}: duplicate path {rel}")
        found[rel] = digest
    return found


def listed_names(root: Path) -> list[str]:
    try:
        info = os.lstat(root)
    except FileNotFoundError:
        fail(f"missing {display(root)}")
    except OSError as exc:
        fail(f"cannot read {display(root)}: {exc.strerror}")
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISDIR(info.st_mode):
        fail(f"not a directory: {display(root)}")
    names: list[str] = []
    for dirpath, dirnames, filenames in os.walk(root, followlinks=False):
        current = Path(dirpath)
        for dirname in dirnames:
            entry = current / dirname
            info = os.lstat(entry)
            if stat.S_ISLNK(info.st_mode):
                fail(f"symlink {display(entry)}")
            if not stat.S_ISDIR(info.st_mode):
                fail(f"not a directory: {display(entry)}")
        for filename in filenames:
            entry = current / filename
            rel = entry.relative_to(root).as_posix()
            reject_rel_path(rel, display(root))
            read_regular(entry)
            names.append(rel)
        if dirnames:
            fail(f"unexpected directory under {display(root)}")
    return sorted(names)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def verify() -> None:
    try:
        metadata = tomllib.loads(text_of(TOML_PATH))
    except tomllib.TOMLDecodeError as exc:
        fail(f"UPSTREAM.toml: invalid TOML: {exc}")
    if set(metadata) != EXPECTED_METADATA_KEYS:
        missing = [
            key
            for key in ("repository", "release", "commit", "files")
            if key not in metadata
        ]
        unexpected = sorted(set(metadata) - EXPECTED_METADATA_KEYS)
        fail(f"UPSTREAM.toml: missing={missing}, unexpected={unexpected}")
    for key in ("repository", "release", "commit"):
        if type(metadata[key]) is not str:
            fail(f"UPSTREAM.toml: {key} must be a string")
    files = metadata["files"]
    if type(files) is not list or any(type(item) is not str for item in files):
        fail("UPSTREAM.toml: files must be a list of strings")
    if len(files) != len(set(files)):
        fail("UPSTREAM.toml: duplicate path")
    for rel in files:
        reject_rel_path(rel, "UPSTREAM.toml")
    if metadata["repository"] != EXPECTED_REPOSITORY:
        fail(f"repository is {metadata['repository']!r}")
    if metadata["release"] != EXPECTED_RELEASE:
        fail(f"release is {metadata['release']!r}")
    if metadata["commit"] != EXPECTED_COMMIT:
        fail(f"commit is {metadata['commit']!r}")
    if tuple(files) != EXPECTED_FILES:
        fail("UPSTREAM.toml file list does not match the pinned list")

    sums = parse_sums(text_of(SUMS_PATH))
    if set(sums) != set(EXPECTED_FILES):
        missing = sorted(set(EXPECTED_FILES) - set(sums))
        extra = sorted(set(sums) - set(EXPECTED_FILES))
        fail(f"SHA256SUMS coverage mismatch, missing={missing}, extra={extra}")

    pinned: dict[str, bytes] = {}
    for rel in EXPECTED_FILES:
        data = read_regular(UPSTREAM / rel)
        digest = sha256(data)
        if digest != sums[rel]:
            fail(f"hash mismatch for {rel}")
        pinned[rel] = data

    pristine_names = listed_names(PRISTINE)
    if pristine_names != list(EXPECTED_TREE):
        fail(f"pristine tree is {pristine_names}, want {list(EXPECTED_TREE)}")
    vendor_names = listed_names(VENDOR)
    if vendor_names != list(EXPECTED_TREE):
        fail(f"vendor tree is {vendor_names}, want {list(EXPECTED_TREE)}")

    patch = read_regular(PATCH)
    if patch == b"":
        fail("patch is empty")

    repository_root = REPOSITORY_ROOT.resolve()
    with tempfile.TemporaryDirectory(prefix="leanp2p-snappy-verify-") as directory:
        temp_dir = Path(directory)
        resolved_temp = temp_dir.resolve()
        if resolved_temp == repository_root or repository_root in resolved_temp.parents:
            fail("temporary directory is inside the repository")
        for name in PRISTINE_NAMES:
            target = temp_dir / name
            payload = pinned[f"pristine/{name}"]
            flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
            if hasattr(os, "O_NOFOLLOW"):
                flags |= os.O_NOFOLLOW
            try:
                fd = os.open(target, flags, 0o644)
            except OSError as exc:
                fail(f"cannot write {name}: {exc.strerror}")
            try:
                view = payload
                while view:
                    written = os.write(fd, view)
                    view = view[written:]
            finally:
                os.close(fd)
        try:
            applied = subprocess.run(
                ["git", "apply", "--whitespace=error-all", os.fspath(PATCH)],
                cwd=temp_dir,
                check=False,
                capture_output=True,
                text=True,
            )
        except FileNotFoundError:
            fail("git is not available")
        if applied.returncode != 0:
            detail = (applied.stderr or applied.stdout).strip()
            fail(f"git apply failed: {detail}")
        rebuilt = listed_names(temp_dir)
        if rebuilt != list(EXPECTED_TREE):
            fail(f"reconstructed tree is {rebuilt}, want {list(EXPECTED_TREE)}")
        for name in EXPECTED_TREE:
            got = read_regular(temp_dir / name)
            want = read_regular(VENDOR / name)
            if got != want:
                fail(
                    f"byte mismatch for {name}: "
                    f"reconstructed {len(got)} bytes, vendor {len(want)} bytes"
                )

    print(
        "verify-upstream: pin "
        f"{EXPECTED_REPOSITORY} {EXPECTED_RELEASE} {EXPECTED_COMMIT}"
    )
    print(f"verify-upstream: {len(EXPECTED_FILES)} sha256 digests match")
    print(f"verify-upstream: git apply produced {len(PRISTINE_NAMES)} files")
    print("verify-upstream: native/vendor/snappy matches byte for byte")


def main() -> None:
    try:
        verify()
    except UnicodeDecodeError:
        fail("input is not valid UTF-8")
    except FileNotFoundError:
        fail("a required file or git is missing")
    except OSError as exc:
        fail(f"filesystem error: {exc.strerror or exc}")


if __name__ == "__main__":
    main()
