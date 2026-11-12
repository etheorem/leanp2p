#!/usr/bin/env python3
"""Check the pinned ngtcp2 tree of net/quic.

The script reads the package that contains it. The caller's working
directory does not matter. It uses the standard library only.

Without arguments it checks the package offline: `UPSTREAM.toml` names
the pin and the file list, `SHA256SUMS` holds one digest for each listed
file in the same order, every digest matches, and `upstream/` holds the
listed files and no other.

With `--clone DIR` it also reads each listed file from the pinned commit
of the ngtcp2 clone at DIR (`git cat-file`, so the checkout state of the
clone does not matter) and requires a byte-for-byte match. That is the
import check: it shows that the committed bytes are upstream's bytes at
the pin.

A failing check exits nonzero.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import stat
import subprocess
import sys
import tomllib
from pathlib import Path
from typing import NoReturn


PACKAGE_ROOT = Path(__file__).resolve().parent.parent
UPSTREAM = PACKAGE_ROOT / "upstream"
TOML_PATH = UPSTREAM / "UPSTREAM.toml"
SUMS_PATH = UPSTREAM / "SHA256SUMS"
METADATA_KEYS = frozenset({"repository", "release", "commit", "files"})
# The two files of `upstream/` that describe the pin and are no part of it.
RECORD_FILES = frozenset({"UPSTREAM.toml", "SHA256SUMS"})


def fail(message: str) -> NoReturn:
    print(f"verify-upstream: {message}", file=sys.stderr)
    raise SystemExit(1)


def check_rel(rel: str, label: str) -> None:
    """Refuse a path that is empty, absolute, or leaves `upstream/`."""
    if rel == "" or rel != rel.strip() or "\\" in rel or "\x00" in rel:
        fail(f"{label}: malformed path {rel!r}")
    parts = rel.split("/")
    if rel.startswith("/") or any(part in ("", ".", "..") for part in parts):
        fail(f"{label}: escaping path {rel!r}")


def read_regular(path: Path) -> bytes:
    """The bytes of a regular file; a symlink or a missing file fails."""
    try:
        info = os.lstat(path)
    except FileNotFoundError:
        fail(f"missing {path.relative_to(PACKAGE_ROOT)}")
    if not stat.S_ISREG(info.st_mode):
        fail(f"not a regular file: {path.relative_to(PACKAGE_ROOT)}")
    return path.read_bytes()


def load_metadata() -> tuple[str, str, str, list[str]]:
    try:
        metadata = tomllib.loads(read_regular(TOML_PATH).decode("utf-8"))
    except (tomllib.TOMLDecodeError, UnicodeDecodeError) as exc:
        fail(f"UPSTREAM.toml: {exc}")
    if set(metadata) != METADATA_KEYS:
        fail(f"UPSTREAM.toml: keys are {sorted(metadata)}, want {sorted(METADATA_KEYS)}")
    for key in ("repository", "release", "commit"):
        if type(metadata[key]) is not str:
            fail(f"UPSTREAM.toml: {key} must be a string")
    commit = metadata["commit"]
    if len(commit) != 40 or any(ch not in "0123456789abcdef" for ch in commit):
        fail("UPSTREAM.toml: commit must be a full lowercase SHA-1")
    files = metadata["files"]
    if type(files) is not list or any(type(item) is not str for item in files):
        fail("UPSTREAM.toml: files must be a list of strings")
    if len(files) != len(set(files)):
        fail("UPSTREAM.toml: duplicate path")
    if files != sorted(files):
        fail("UPSTREAM.toml: files must be sorted")
    for rel in files:
        check_rel(rel, "UPSTREAM.toml")
        if rel in RECORD_FILES:
            fail(f"UPSTREAM.toml: the record file {rel} is in the list of pinned files")
    return metadata["repository"], metadata["release"], commit, files


def load_sums() -> list[tuple[str, str]]:
    text = read_regular(SUMS_PATH).decode("utf-8")
    if text == "" or not text.endswith("\n"):
        fail("SHA256SUMS: empty, or no final newline")
    entries: list[tuple[str, str]] = []
    for number, line in enumerate(text.splitlines(), 1):
        digest, separator, rel = line.partition("  ")
        if separator != "  " or len(digest) != 64 or any(
            ch not in "0123456789abcdef" for ch in digest
        ):
            fail(f"SHA256SUMS:{number}: malformed line")
        check_rel(rel, f"SHA256SUMS:{number}")
        entries.append((rel, digest))
    return entries


def tree_files() -> list[str]:
    """Every file under `upstream/` but the record files, sorted."""
    found: list[str] = []
    for dirpath, dirnames, filenames in os.walk(UPSTREAM, followlinks=False):
        current = Path(dirpath)
        for name in dirnames:
            if os.path.islink(current / name):
                fail(f"symlink {(current / name).relative_to(PACKAGE_ROOT)}")
        for name in filenames:
            rel = (current / name).relative_to(UPSTREAM).as_posix()
            if rel not in RECORD_FILES:
                found.append(rel)
    return sorted(found)


def clone_blob(clone: Path, commit: str, rel: str) -> bytes:
    """The bytes of `rel` at `commit` in the clone. The pinned tree keeps
    upstream's paths under `pristine/`; the license sits beside it."""
    upstream_path = rel.removeprefix("pristine/")
    try:
        result = subprocess.run(
            ["git", "-C", os.fspath(clone), "cat-file", "blob", f"{commit}:{upstream_path}"],
            check=False,
            capture_output=True,
        )
    except FileNotFoundError:
        fail("git is not available")
    if result.returncode != 0:
        fail(f"the clone has no {upstream_path} at {commit}")
    return result.stdout


def verify(clone: Path | None) -> None:
    repository, release, commit, files = load_metadata()

    sums = load_sums()
    if [rel for rel, _ in sums] != files:
        fail("SHA256SUMS does not list the files of UPSTREAM.toml, in order")
    for rel, digest in sums:
        if hashlib.sha256(read_regular(UPSTREAM / rel)).hexdigest() != digest:
            fail(f"hash mismatch for {rel}")

    present = tree_files()
    if present != files:
        missing = sorted(set(files) - set(present))
        extra = sorted(set(present) - set(files))
        fail(f"upstream/ tree mismatch, missing={missing}, extra={extra}")

    print(f"verify-upstream: pin {repository} {release} {commit}")
    print(f"verify-upstream: {len(files)} sha256 digests match, and no other file is present")

    if clone is not None:
        for rel in files:
            if clone_blob(clone, commit, rel) != read_regular(UPSTREAM / rel):
                fail(f"byte mismatch with the clone for {rel}")
        print(f"verify-upstream: {len(files)} files match the clone at {commit}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--clone", type=Path, help="an ngtcp2 clone that holds the pinned commit")
    args = parser.parse_args()
    verify(args.clone)


if __name__ == "__main__":
    main()
