#!/usr/bin/env python3
"""Audit the production Snappy objects and the two control surfaces.

The script reads the paths Lake passes to it. It uses nm -P -g, c++filt,
and the toolchain archiver. A failing check exits nonzero. The script
does not rebuild those files, and it does not search the tree for them.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass

POLICY = "phase-3b/1"

# Undefined C and platform symbols observed in the production objects.
# A symbol outside this set, and outside the Snappy classes and the Lean
# runtime set, is a failure.
C_RUNTIME = frozenset(
    {
        "abort",
        "bzero",
        "free",
        "malloc",
        "memcmp",
        "memcpy",
        "memmove",
        "__assert_rtn",
        "__stack_chk_fail",
        "__stack_chk_guard",
    }
)

# Exact Lean runtime symbols referenced by the compiled compression shim.
# `lean_alloc_object` allocates the output scalar array.
# `lean_inc_heartbeat` is the small-object heartbeat for the result pair.
# `lean_internal_panic` ends an internal invariant failure.
# `lean_internal_panic_out_of_memory` ends a failed scratch allocation
# and a failed checked size calculation in the Lean headers.
# `lean_notify_assert` is the header assertion path used by those helpers.
# `mi_malloc_small` allocates the result pair under the toolchain mimalloc.
LEAN_RUNTIME = frozenset(
    {
        "lean_alloc_object",
        "lean_inc_heartbeat",
        "lean_internal_panic",
        "lean_internal_panic_out_of_memory",
        "lean_notify_assert",
        "mi_malloc_small",
    }
)

NM_KINDS = frozenset("ABCDGINRSTUVWabcdginrstuvw")
MEMBER_HEADER = re.compile(r"^[A-Za-z0-9._+-]+\.o:$")
STD_NAME = re.compile(r"(^|[^A-Za-z0-9_])std::")
SNAPPY_NAME = re.compile(r"(^|[^A-Za-z0-9_])snappy::")
GLOBAL_ALLOC_DEMANGLED = re.compile(r"^operator (new|delete)(\[\])?\(")
GLOBAL_ALLOC_MANGLED = re.compile(r"^_Z(nw|na|dl|da)")
PRODUCTION_MEMBERS = (
    "snappy.block.o",
    "snappy-sinksource.block.o",
    "shim.o",
)
PRISTINE_MEMBERS = ("snappy.pristine.o", "snappy-sinksource.pristine.o")
PATCHED_MEMBERS = ("snappy.patched.o", "snappy-sinksource.patched.o")
SHIM_EXPORTS = (
    "leanp2p_snappy_compress",
    "leanp2p_snappy_decompress",
    "leanp2p_snappy_internal_panic",
)

REQUIRED_DEMANGLED = (
    "snappy::Sink::Append(char const*, unsigned long)",
    "snappy::Source::Available() const",
    "snappy::Source::Peek(unsigned long*)",
    "snappy::Source::Skip(unsigned long)",
    "snappy::Sink::operator delete(void*)",
    "snappy::Sink::operator delete(void*, unsigned long)",
    "snappy::Source::operator delete(void*)",
    "snappy::Source::operator delete(void*, unsigned long)",
    "snappy::ByteArraySource::operator delete(void*)",
    "snappy::ByteArraySource::operator delete(void*, unsigned long)",
    "snappy::UncheckedByteArraySink::operator delete(void*)",
    "snappy::UncheckedByteArraySink::operator delete(void*, unsigned long)",
)


@dataclass(frozen=True)
class Symbol:
    name: str
    kind: str


def fail(message: str) -> None:
    print(f"audit-native: {message}", file=sys.stderr)
    raise SystemExit(1)


def run_text(cmd: list[str], stdin: str | None = None) -> str:
    try:
        result = subprocess.run(
            cmd,
            input=stdin,
            text=True,
            capture_output=True,
            check=False,
        )
    except FileNotFoundError:
        fail(f"missing tool {cmd[0]}")
    if result.returncode != 0:
        detail = (result.stderr or result.stdout).strip()
        fail(f"{' '.join(cmd)} exited {result.returncode}: {detail}")
    return result.stdout


def parse_nm(text: str, archive: bool) -> list[Symbol]:
    symbols: list[Symbol] = []
    for line_number, raw_line in enumerate(text.splitlines(), start=1):
        line = raw_line.strip()
        if line == "":
            continue
        if MEMBER_HEADER.fullmatch(line):
            if not archive:
                fail(f"nm line {line_number} is an archive member label: {line}")
            continue
        fields = line.split()
        if len(fields) < 2 or fields[1] not in NM_KINDS:
            fail(f"nm line {line_number} is not a symbol: {raw_line}")
        name = fields[0]
        if name == "" or any(char.isspace() for char in name):
            fail(f"nm line {line_number} has a malformed name")
        symbols.append(Symbol(name, fields[1]))
    return symbols


def itanium(raw: str) -> str | None:
    if raw.startswith("__Z"):
        return raw[1:]
    if raw.startswith("_Z"):
        return raw
    return None


def demangle_all(names: list[str], cxxfilt: str) -> dict[str, str]:
    if not names:
        return {}
    stdout = run_text([cxxfilt], "\n".join(names) + "\n")
    lines = stdout.splitlines()
    if len(lines) != len(names):
        fail(
            f"c++filt returned {len(lines)} lines for {len(names)} symbols"
        )
    return dict(zip(names, lines, strict=True))


def forbidden_reason(raw: str, demangled: str) -> str | None:
    candidates = (raw, raw[1:] if raw.startswith("_") else raw)
    for candidate in candidates:
        if "__cxa_" in candidate:
            return "forbidden-cxa"
        if "__gxx_personality" in candidate:
            return "forbidden-personality"
    if STD_NAME.search(demangled):
        return "forbidden-std"
    if SNAPPY_NAME.search(demangled):
        return None
    if GLOBAL_ALLOC_DEMANGLED.match(demangled):
        if demangled.startswith("operator delete"):
            return "forbidden-global-delete"
        return "forbidden-global-new"
    mangled = itanium(raw)
    if mangled and GLOBAL_ALLOC_MANGLED.match(mangled):
        if mangled.startswith("_Zdl") or mangled.startswith("_Zda"):
            return "forbidden-global-delete"
        return "forbidden-global-new"
    return None


def stripped_name(raw: str) -> str:
    return raw[1:] if raw.startswith("_") else raw


def classify(raw: str, demangled: str) -> str:
    reason = forbidden_reason(raw, demangled)
    if reason:
        return reason
    stripped = stripped_name(raw)
    if raw in LEAN_RUNTIME or stripped in LEAN_RUNTIME:
        return "lean-runtime"
    if SNAPPY_NAME.search(demangled):
        return "snappy-cross"
    if raw in C_RUNTIME or stripped in C_RUNTIME:
        return "c-runtime"
    return "unfamiliar"


def load_symbols(path: str, nm: str, archive: bool) -> list[Symbol]:
    return parse_nm(run_text([nm, "-P", "-g", path]), archive)


def inventory(
    label: str, symbols: list[Symbol], demangled: dict[str, str]
) -> tuple[list[str], list[str]]:
    seen: set[str] = set()
    defined = {symbol.name for symbol in symbols if symbol.kind != "U"}
    lines = [f"undefined symbols for {label}"]
    failures: list[str] = []
    rows = []
    for symbol in symbols:
        if symbol.kind != "U" or symbol.name in seen:
            continue
        seen.add(symbol.name)
        rendered = demangled[symbol.name]
        kind = classify(symbol.name, rendered)
        if kind == "snappy-cross" and symbol.name in defined:
            kind = "snappy-resolved"
        rows.append((kind, symbol.name, rendered))
        if kind == "unfamiliar" or kind.startswith("forbidden-"):
            failures.append(f"{label}: {kind} {symbol.name} {rendered}")
    for kind, name, rendered in sorted(rows):
        lines.append(f"  {kind} {name} {rendered}")
    if not rows:
        lines.append("  none")
    return lines, failures


def require_guarded(
    label: str, symbols: list[Symbol], demangled: dict[str, str]
) -> tuple[list[str], list[str]]:
    by_demangled: dict[str, list[str]] = {}
    for symbol in symbols:
        if symbol.kind == "U":
            continue
        by_demangled.setdefault(demangled[symbol.name], []).append(symbol.name)
    lines = [f"guarded symbols in {label}"]
    failures: list[str] = []
    for required in REQUIRED_DEMANGLED:
        raw_names = sorted(set(by_demangled.get(required, [])))
        if raw_names:
            lines.append(f"  present {required}")
            for raw_name in raw_names:
                lines.append(f"    {raw_name}")
        else:
            lines.append(f"  missing {required}")
            failures.append(f"{label} does not define {required}")
    return lines, failures


def archive_members(
    label: str, path: str, ar: str, expected: tuple[str, ...]
) -> tuple[list[str], list[str]]:
    text = run_text([ar, "t", path])
    members = [line.strip() for line in text.splitlines() if line.strip()]
    lines = [f"{label} archive members", *[f"  {member}" for member in members]]
    failures: list[str] = []
    if members != list(expected):
        failures.append(
            f"{label} archive members differ: "
            f"found {members or ['none']}; expected {list(expected)}"
        )
    return lines, failures


def shim_defined_exports(symbols: list[Symbol]) -> tuple[list[str], list[str]]:
    defined = [symbol for symbol in symbols if symbol.kind != "U"]
    counts = Counter(stripped_name(symbol.name) for symbol in defined)
    lines = ["defined symbols in shim.o"]
    for symbol in sorted(defined, key=lambda item: (stripped_name(item.name), item.kind)):
        lines.append(f"  {symbol.kind} {stripped_name(symbol.name)}")
    expected = Counter(SHIM_EXPORTS)
    if counts == expected:
        return lines, []
    missing = sorted((expected - counts).elements())
    unexpected = sorted((counts - expected).elements())
    duplicate = sorted(name for name, count in counts.items() if count > 1)
    return lines, [
        "shim.o defined symbols differ: "
        f"missing {missing or 'none'}; "
        f"unexpected {unexpected or 'none'}; "
        f"duplicate {duplicate or 'none'}"
    ]


def require_panic(label: str, symbols: list[Symbol]) -> tuple[list[str], list[str]]:
    names = {stripped_name(symbol.name) for symbol in symbols if symbol.kind == "U"}
    lines = [f"internal panic symbol in {label}"]
    if "lean_internal_panic" in names:
        lines.append("  present lean_internal_panic")
        return lines, []
    lines.append("  missing lean_internal_panic")
    return lines, [f"{label} does not reference lean_internal_panic"]


def reject_forbidden_symbols(
    label: str, symbols: list[Symbol], demangled: dict[str, str]
) -> tuple[list[str], list[str]]:
    lines = [f"forbidden symbols in {label}"]
    failures: list[str] = []
    for symbol in symbols:
        rendered = demangled[symbol.name]
        reason = forbidden_reason(symbol.name, rendered)
        if reason:
            lines.append(f"  {reason} {symbol.name} {rendered}")
            failures.append(f"{label}: {reason} {symbol.name} {rendered}")
    if len(lines) == 1:
        lines.append("  none")
    return lines, failures


def defined_surface(symbols: list[Symbol]) -> Counter[tuple[str, str]]:
    return Counter(
        (symbol.name, symbol.kind) for symbol in symbols if symbol.kind != "U"
    )


def compare_surfaces(
    label: str,
    left: Counter[tuple[str, str]],
    right: Counter[tuple[str, str]],
) -> tuple[list[str], list[str]]:
    removed = left - right
    added = right - left
    lines = [
        f"symbol surface {label}",
        f"  left {sum(left.values())}",
        f"  right {sum(right.values())}",
    ]
    failures: list[str] = []
    if removed or added:
        lines.append("  removed")
        for (name, kind), count in sorted(removed.items()):
            lines.append(f"    {name} {kind} x{count}")
        lines.append("  added")
        for (name, kind), count in sorted(added.items()):
            lines.append(f"    {name} {kind} x{count}")
        failures.append(
            f"{label} symbol surfaces differ: "
            f"{sum(removed.values())} removed, {sum(added.values())} added"
        )
    else:
        lines.append("  equal")
    return lines, failures


def collect_demangled(groups: list[list[Symbol]], cxxfilt: str) -> dict[str, str]:
    names = sorted({symbol.name for group in groups for symbol in group})
    return demangle_all(names, cxxfilt)


def audit_paths(args: argparse.Namespace) -> None:
    if args.policy != POLICY:
        fail(f"audit policy {args.policy} does not match {POLICY}")
    roles = (
        ("snappy.block.o", args.production_core, False),
        ("snappy-sinksource.block.o", args.production_sink, False),
        ("shim.o", args.production_shim, False),
        ("libsnappy.a", args.production_archive, True),
        ("snappy.pristine.o", args.pristine_core, False),
        ("snappy-sinksource.pristine.o", args.pristine_sink, False),
        ("libsnappy_pristine.a", args.pristine_archive, True),
        ("snappy.patched.o", args.patched_core, False),
        ("snappy-sinksource.patched.o", args.patched_sink, False),
        ("libsnappy_patched.a", args.patched_archive, True),
    )
    loaded: dict[str, list[Symbol]] = {}
    for label, path, archive in roles:
        if path != label and not path.endswith("/" + label):
            fail(f"{path} does not end with {label}")
        loaded[label] = load_symbols(path, args.nm, archive)
    demangled = collect_demangled(list(loaded.values()), args.cxxfilt)
    report: list[str] = [
        f"policy {POLICY}",
        f"nm {args.nm}",
        f"c++filt {args.cxxfilt}",
        f"ar {args.ar}",
    ]
    failures: list[str] = []
    for label in (
        "snappy.block.o",
        "snappy-sinksource.block.o",
        "shim.o",
        "libsnappy.a",
    ):
        lines, found = inventory(label, loaded[label], demangled)
        report.extend(lines)
        failures.extend(found)
    for label in ("shim.o", "libsnappy.a"):
        lines, found = require_panic(label, loaded[label])
        report.extend(lines)
        failures.extend(found)
    lines, found = reject_forbidden_symbols("shim.o", loaded["shim.o"], demangled)
    report.extend(lines)
    failures.extend(found)
    lines, found = shim_defined_exports(loaded["shim.o"])
    report.extend(lines)
    failures.extend(found)
    for label in ("snappy-sinksource.block.o", "libsnappy.a"):
        lines, found = require_guarded(label, loaded[label], demangled)
        report.extend(lines)
        failures.extend(found)
    for label, path, expected in (
        ("production", args.production_archive, PRODUCTION_MEMBERS),
        ("pristine", args.pristine_archive, PRISTINE_MEMBERS),
        ("patched", args.patched_archive, PATCHED_MEMBERS),
    ):
        lines, found = archive_members(label, path, args.ar, expected)
        report.extend(lines)
        failures.extend(found)
    pairs = (
        ("pristine/patched snappy object", "snappy.pristine.o", "snappy.patched.o"),
        (
            "pristine/patched sink object",
            "snappy-sinksource.pristine.o",
            "snappy-sinksource.patched.o",
        ),
        (
            "pristine/patched archive",
            "libsnappy_pristine.a",
            "libsnappy_patched.a",
        ),
    )
    for label, left, right in pairs:
        lines, found = compare_surfaces(
            label, defined_surface(loaded[left]), defined_surface(loaded[right])
        )
        report.extend(lines)
        failures.extend(found)
    sys.stdout.write("\n".join(report) + "\n")
    if failures:
        print("\n".join(failures), file=sys.stderr)
        raise SystemExit(1)


def command_classify(args: argparse.Namespace) -> None:
    text = sys.stdin.read()
    symbols = parse_nm(text, archive=False)
    demangled = demangle_all(sorted({symbol.name for symbol in symbols}), args.cxxfilt)
    lines, failures = inventory("sample", symbols, demangled)
    sys.stdout.write("\n".join(lines) + "\n")
    if failures:
        print("\n".join(failures), file=sys.stderr)
        raise SystemExit(1)


def parse_surface_text(text: str) -> list[tuple[str, str]]:
    rows: list[tuple[str, str]] = []
    for line_number, raw_line in enumerate(text.splitlines(), start=1):
        line = raw_line.strip()
        if line == "":
            continue
        fields = line.split()
        if len(fields) != 2 or fields[1] not in NM_KINDS or fields[1] == "U":
            fail(f"surface line {line_number} is not a defined symbol: {raw_line}")
        rows.append((fields[0], fields[1]))
    return rows


def command_compare(args: argparse.Namespace) -> None:
    del args
    text = sys.stdin.read()
    parts = text.split("\n---\n", maxsplit=1)
    if len(parts) != 2:
        fail("compare text needs two surfaces separated by ---")
    lines, failures = compare_surfaces(
        "sample",
        Counter(parse_surface_text(parts[0])),
        Counter(parse_surface_text(parts[1])),
    )
    sys.stdout.write("\n".join(lines) + "\n")
    if failures:
        print("\n".join(failures), file=sys.stderr)
        raise SystemExit(1)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subcommands = parser.add_subparsers(dest="command", required=True)

    audit = subcommands.add_parser("audit")
    audit.add_argument("--policy", required=True)
    audit.add_argument("--nm", required=True)
    audit.add_argument("--cxxfilt", required=True)
    audit.add_argument("--ar", required=True)
    audit.add_argument("--production-core", required=True)
    audit.add_argument("--production-sink", required=True)
    audit.add_argument("--production-shim", required=True)
    audit.add_argument("--production-archive", required=True)
    audit.add_argument("--pristine-core", required=True)
    audit.add_argument("--pristine-sink", required=True)
    audit.add_argument("--pristine-archive", required=True)
    audit.add_argument("--patched-core", required=True)
    audit.add_argument("--patched-sink", required=True)
    audit.add_argument("--patched-archive", required=True)
    audit.set_defaults(func=audit_paths)

    classify = subcommands.add_parser("classify-text")
    classify.add_argument("--cxxfilt", required=True)
    classify.set_defaults(func=command_classify)

    compare = subcommands.add_parser("compare-text")
    compare.set_defaults(func=command_compare)
    return parser


def main() -> None:
    parser = build_parser()
    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
