#!/usr/bin/env python3
"""Linux x86-64 audit and paired sanitizer gates for the Snappy archive.

The script exits unless `uname` reports Linux and `x86_64`. It runs
`lake build snappyNative/snappyAudit` on the production objects. It
then links that archive into a shim workload and links a matched
runtime control with the same Lean linker. Host `c++` compiles the
instrumented units. Host `cc` from the same toolchain links them and
supplies the GCC AddressSanitizer runtime. The link receives the
toolchain library directories that the pinned `leanc` driver searches
implicitly. Lean's static `libc++` and `libc++abi` stay on that link
line. AddressSanitizer and
LeakSanitizer each run on that pair. A leak in either executable, a
sanitizer error, or a negative control that exits cleanly fails the
process. The control does not excuse a leak.

ASan gate environment:
  ASAN_OPTIONS=halt_on_error=1:abort_on_error=1:detect_leaks=0:allocator_may_return_null=0:strict_string_checks=1
  A nonzero status fails the gate.

LSan gate environment:
  ASAN_OPTIONS=halt_on_error=1:abort_on_error=0:detect_leaks=1:allocator_may_return_null=0
  LSAN_OPTIONS=exitcode=23:fast_unwind_on_malloc=0:malloc_context_size=20
  Both executables must exit 0. A LeakSanitizer report in either
  executable fails the gate. The deliberate leak probe is separate
  and must exit 23.
"""

from __future__ import annotations

import os
import re
import shlex
import subprocess
import sys
import tempfile
from pathlib import Path

ASAN_OPTIONS = (
    "halt_on_error=1:abort_on_error=1:detect_leaks=0:"
    "allocator_may_return_null=0:strict_string_checks=1"
)
LSAN_ASAN_OPTIONS = (
    "halt_on_error=1:abort_on_error=0:detect_leaks=1:"
    "allocator_may_return_null=0"
)
LSAN_OPTIONS = "exitcode=23:fast_unwind_on_malloc=0:malloc_context_size=20"
NEGATIVE_ASAN_OPTIONS = (
    "halt_on_error=1:abort_on_error=0:detect_leaks=0:"
    "allocator_may_return_null=0"
)
LSAN_EXIT = 23

LANGUAGE_FLAGS = [
    "-std=c++11",
    "-O2",
    "-Wall",
    "-Wextra",
    "-Werror",
    "-fno-exceptions",
    "-fno-rtti",
    "-fno-threadsafe-statics",
    "-ffunction-sections",
    "-fdata-sections",
]
PRODUCTION_FLAGS = LANGUAGE_FLAGS + [
    "-fPIC",
    "-DHAVE_CONFIG_H=1",
    "-DLEANP2P_SNAPPY_BLOCK_ONLY=1",
]
SANITIZE_FLAGS = [
    "-fsanitize=address",
    "-fno-omit-frame-pointer",
    "-fno-sanitize-recover=address",
    "-g",
]
ARCHIVE_MEMBERS = (
    "snappy.block.o",
    "snappy-sinksource.block.o",
    "shim.o",
)
CXX_FAMILIES = ("libstdc++", "libc++")
SANITIZER_LIBRARIES = ("libasan", "liblsan", "libubsan", "libtsan")

NEEDED_LIBRARY = re.compile(r"Shared library: \[([^\]]+)\]")


def fail(message: str) -> None:
    print(f"linux-hardening: {message}", file=sys.stderr)
    raise SystemExit(1)


def repo_root() -> Path:
    return Path(__file__).resolve().parents[4]


def run(
    cmd: list[str],
    *,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
    check: bool = True,
    quiet: bool = False,
) -> subprocess.CompletedProcess[str]:
    if not quiet:
        print("+ " + " ".join(cmd), flush=True)
    try:
        result = subprocess.run(
            cmd,
            cwd=cwd,
            env=env,
            text=True,
            capture_output=True,
            check=False,
        )
    except FileNotFoundError:
        fail(f"missing tool {cmd[0]}")
    if not quiet and result.stdout:
        print(result.stdout, end="" if result.stdout.endswith("\n") else "\n", flush=True)
    if not quiet and result.stderr:
        print(
            result.stderr,
            end="" if result.stderr.endswith("\n") else "\n",
            file=sys.stderr,
            flush=True,
        )
    if check and result.returncode != 0:
        fail(f"{cmd[0]} exited {result.returncode}")
    return result


def first_line(cmd: list[str]) -> str:
    result = run(cmd, check=False, quiet=True)
    text = (result.stdout or result.stderr).strip()
    if text == "":
        fail(f"{cmd[0]} returned an empty identity")
    return text.splitlines()[0]


def assert_platform() -> None:
    system = run(["uname", "-s"]).stdout.strip()
    machine = run(["uname", "-m"]).stdout.strip()
    print(f"uname -s {system}")
    print(f"uname -m {machine}")
    if system != "Linux":
        fail(f"uname -s is {system}")
    if machine != "x86_64":
        fail(f"uname -m is {machine}")


def print_identities(prefix: Path, leanc: Path, ar: Path) -> None:
    print(first_line(["uname", "-r"]))
    print(f"lean --version {first_line(['lean', '--version'])}")
    print(f"leanc --version {first_line([str(leanc), '--version'])}")
    assert_compiler_linker_pair()
    print(first_line(["nm", "--version"]))
    print(first_line([str(ar), "--version"]))
    print(first_line(["ld", "--version"]))
    print(first_line(["ldd", "--version"]))
    print(first_line(["readelf", "--version"]))
    print(first_line(["python3", "--version"]))
    print(f"lean-prefix {prefix}")
    print(f"ASAN_OPTIONS {ASAN_OPTIONS}")
    print(f"LSAN ASAN_OPTIONS {LSAN_ASAN_OPTIONS}")
    print(f"LSAN_OPTIONS {LSAN_OPTIONS}")
    asan_lib = run(["c++", "-print-file-name=libasan.so"], check=False).stdout.strip()
    print(f"libasan {asan_lib or 'unresolved'}")


def core_flags() -> list[str]:
    """Flags for upstream `snappy.cc`.

    GCC 15 diagnoses ignored alignment attributes on the upstream
    `std::pair<__m128i, __m128i>` construct. This list suppresses that
    diagnostic after `-Werror`. Every other warning remains an error.
    The sink, the shim, and the check drivers keep `PRODUCTION_FLAGS`
    or `LANGUAGE_FLAGS`.
    """
    flags: list[str] = []
    for flag in PRODUCTION_FLAGS:
        flags.append(flag)
        if flag == "-Werror":
            flags.append("-Wno-ignored-attributes")
    return flags


CXX_RUNTIME_LIBS = frozenset({"-lc++", "-lc++abi", "-lstdc++"})
STATIC_MODE = "-Wl,-Bstatic"
DYNAMIC_MODE = "-Wl,-Bdynamic"
SANITIZER_LINK = [
    "cc",
    "-fsanitize=address",
    "-fno-omit-frame-pointer",
    "-fno-sanitize-recover=address",
]


def driver_text(driver: str, *args: str) -> str:
    result = run([driver, *args], check=False)
    text = result.stdout.strip()
    if result.returncode != 0 or text == "":
        fail(f"{driver} {' '.join(args)} failed")
    return text.splitlines()[0]


def assert_compiler_linker_pair() -> None:
    """Require host `cc` and `c++` to share a target and sanitizer runtime."""
    print(f"c++ --version {driver_text('c++', '--version')}")
    cxx_target = driver_text("c++", "-dumpmachine")
    print(f"c++ -dumpmachine {cxx_target}")
    print(f"cc --version {driver_text('cc', '--version')}")
    cc_target = driver_text("cc", "-dumpmachine")
    print(f"cc -dumpmachine {cc_target}")
    if cc_target != cxx_target:
        fail(f"cc target {cc_target} differs from c++ target {cxx_target}")
    cxx_asan = run(["c++", "-print-file-name=libasan.so"], check=False).stdout.strip()
    cc_asan = run(["cc", "-print-file-name=libasan.so"], check=False).stdout.strip()
    print(f"c++ libasan {cxx_asan or 'unresolved'}")
    print(f"cc libasan {cc_asan or 'unresolved'}")
    cxx_found = "/" in cxx_asan
    cc_found = "/" in cc_asan
    if cxx_found != cc_found or (cxx_found and cxx_asan != cc_asan):
        fail("cc and c++ resolve different AddressSanitizer runtimes")


def validate_static_cxx_runtime(tokens: list[str]) -> None:
    """Allow a C++ runtime library only inside a closed static region."""
    static = False
    for token in tokens:
        if token == STATIC_MODE:
            if static:
                fail("leanc linker static mode is already active")
            static = True
            continue
        if token == DYNAMIC_MODE:
            if not static:
                fail("leanc linker dynamic mode is already active")
            static = False
            continue
        if token in CXX_RUNTIME_LIBS and not static:
            fail(f"leanc links {token} outside static mode")
    if static:
        fail("leanc linker static mode does not return to dynamic mode")


TOOLCHAIN_LIBRARY_NAMES = ("libc++.a", "libc++abi.a", "libuv.a", "libuv.so")


def driver_library_path(prefix: Path, name: str, printed: str) -> Path | None:
    """Accept a driver path that names an existing file inside the prefix."""
    text = printed.strip()
    if text == "" or text == name or "/" not in text:
        return None
    path = Path(text)
    if not path.is_absolute():
        path = prefix / path
    if not path.is_file():
        return None
    resolved = path.resolve()
    if not resolved.is_relative_to(prefix.resolve()):
        return None
    return resolved


def prefix_library_path(prefix: Path, name: str) -> Path | None:
    """Accept `<lean-prefix>/lib/<name>` when that file exists."""
    path = prefix / "lib" / name
    if not path.is_file():
        return None
    resolved = path.resolve()
    if not resolved.is_relative_to(prefix.resolve()):
        return None
    return resolved


def collect_toolchain_libraries(prefix: Path, printed: dict[str, str]) -> list[Path]:
    """Resolve the C++ runtime and libuv from driver output and prefix/lib."""
    found: list[Path] = []
    seen: set[Path] = set()
    for name in TOOLCHAIN_LIBRARY_NAMES:
        candidates = (
            driver_library_path(prefix, name, printed.get(name, "")),
            prefix_library_path(prefix, name),
        )
        for path in candidates:
            if path is not None and path not in seen:
                seen.add(path)
                found.append(path)
    names = {path.name for path in found}
    if "libc++.a" not in names:
        fail("the Lean toolchain has no libc++.a")
    if "libc++abi.a" not in names:
        fail("the Lean toolchain has no libc++abi.a")
    if "libuv.a" not in names and "libuv.so" not in names:
        fail("the Lean toolchain has no libuv.a or libuv.so")
    return found


def toolchain_search_directories(libraries: list[Path]) -> list[Path]:
    """Return unique parent directories in first-seen order."""
    directories: list[Path] = []
    seen: set[Path] = set()
    for library in libraries:
        parent = library.parent
        if parent not in seen:
            seen.add(parent)
            directories.append(parent)
    return directories


def toolchain_link_args(prefix: Path, leanc: Path) -> list[str]:
    """Discover Lean library directories and return explicit `-L` arguments."""
    printed: dict[str, str] = {}
    for name in TOOLCHAIN_LIBRARY_NAMES:
        result = run([str(leanc), f"-print-file-name={name}"], check=False)
        if result.returncode != 0:
            fail(f"leanc -print-file-name={name} exited {result.returncode}")
        printed[name] = result.stdout.strip()
    libraries = collect_toolchain_libraries(prefix, printed)
    for library in libraries:
        print(f"toolchain library {library.name} {library}")
    args: list[str] = []
    for directory in toolchain_search_directories(libraries):
        if not directory.is_dir():
            fail(f"Lean library search directory is absent: {directory}")
        print(f"toolchain search directory {directory}")
        args.extend(["-L", str(directory)])
    return args


def filtered_link_flags(leanc: Path) -> list[str]:
    text = run([str(leanc), "--print-ldflags"]).stdout.strip()
    if text == "":
        fail("leanc --print-ldflags returned an empty line")
    kept: list[str] = []
    tokens = shlex.split(text)
    index = 0
    while index < len(tokens):
        token = tokens[index]
        if token in {"-I", "-L", "-isystem"}:
            if index + 1 >= len(tokens):
                fail(f"leanc flag {token} has no argument")
            if token == "-L":
                kept.extend([token, tokens[index + 1]])
            index += 2
            continue
        if token.startswith("-l") or token.startswith("-Wl,") or token == "-pthread":
            kept.append(token)
        elif token.endswith(".a") or token.endswith(".so"):
            kept.append(token)
        index += 1
    if not kept:
        fail("leanc --print-ldflags produced no linker flags")
    validate_static_cxx_runtime(kept)
    print("sanitizer link flags")
    for token in kept:
        print(f"  {token}")
    return kept


def compile_sources(work: Path, prefix: Path, root: Path) -> dict[str, Path]:
    vendor = root / "packages" / "codec" / "snappy" / "native" / "vendor" / "snappy"
    include = root / "packages" / "codec" / "snappy" / "native" / "include"
    checks = root / "packages" / "codec" / "snappy" / "native" / "check"
    lean_include = prefix / "include"
    objects = {
        "core": work / "snappy.san.o",
        "sink": work / "snappy-sinksource.san.o",
        "shim": work / "shim.san.o",
        "workload": work / "shim-workload.o",
        "control": work / "runtime-control.o",
        "workload-plain": work / "shim-workload.plain.o",
        "control-plain": work / "runtime-control.plain.o",
    }
    run(
        ["c++", *core_flags(), *SANITIZE_FLAGS, "-I", str(vendor), "-I", str(include),
         "-c", str(vendor / "snappy.cc"), "-o", str(objects["core"])]
    )
    run(
        ["c++", *PRODUCTION_FLAGS, *SANITIZE_FLAGS, "-I", str(vendor), "-I", str(include),
         "-c", str(vendor / "snappy-sinksource.cc"), "-o", str(objects["sink"])]
    )
    run(
        ["c++", *PRODUCTION_FLAGS, *SANITIZE_FLAGS, "-I", str(vendor), "-I", str(include),
         "-I", str(lean_include), "-c",
         str(root / "packages" / "codec" / "snappy" / "native" / "shim.cpp"),
         "-o", str(objects["shim"])]
    )
    for name, source, sanitized in (
        ("workload", checks / "shim-workload.cpp", True),
        ("control", checks / "runtime-control.cpp", True),
        ("workload-plain", checks / "shim-workload.cpp", False),
        ("control-plain", checks / "runtime-control.cpp", False),
    ):
        flags = [*LANGUAGE_FLAGS]
        if sanitized:
            flags.extend(SANITIZE_FLAGS)
        run(
            ["c++", *flags, "-I", str(lean_include), "-c", str(source), "-o", str(objects[name])]
        )
    return objects


def link_sanitized(
    prefix: Path, leanc: Path, objects: dict[str, Path], work: Path
) -> tuple[Path, Path]:
    search = toolchain_link_args(prefix, leanc)
    flags = filtered_link_flags(leanc)
    snappy = work / "shim-workload-asan"
    control = work / "runtime-control-asan"
    common = SANITIZER_LINK
    run(
        [
            *common,
            "-o",
            str(snappy),
            str(objects["workload"]),
            str(objects["core"]),
            str(objects["sink"]),
            str(objects["shim"]),
            *search,
            *flags,
        ]
    )
    run(
        [
            *common,
            "-o",
            str(control),
            str(objects["control"]),
            *search,
            *flags,
        ]
    )
    return snappy, control


def link_plain(
    leanc: Path, objects: dict[str, Path], archive: Path, work: Path
) -> tuple[Path, Path]:
    snappy = work / "shim-workload"
    control = work / "runtime-control"
    run(
        [
            str(leanc),
            "-o",
            str(snappy),
            str(objects["workload-plain"]),
            str(archive),
            "-Wl,--gc-sections",
        ]
    )
    run(
        [
            str(leanc),
            "-o",
            str(control),
            str(objects["control-plain"]),
            "-Wl,--gc-sections",
        ]
    )
    return snappy, control


def require_archive(root: Path, ar: Path) -> Path:
    archive = (
        root
        / "packages"
        / "codec"
        / "snappy"
        / "native"
        / ".lake"
        / "build"
        / "snappy"
        / "block"
        / "libsnappy.a"
    )
    if not archive.is_file():
        fail(f"production archive is absent: {archive}")
    for member in ARCHIVE_MEMBERS:
        path = archive.parent / member
        if not path.is_file():
            fail(f"production object is absent: {path}")
    listed = run([str(ar), "t", str(archive)]).stdout.split()
    print("production archive members")
    for member in listed:
        print(f"  {member}")
    if tuple(listed) != ARCHIVE_MEMBERS:
        fail(f"archive members are {listed or ['none']}")
    report = (
        root
        / "packages"
        / "codec"
        / "snappy"
        / "native"
        / ".lake"
        / "build"
        / "check"
        / "audit.txt"
    )
    if not report.is_file():
        fail(f"audit report is absent: {report}")
    text = report.read_text()
    for label in (
        "undefined symbols for snappy.block.o",
        "undefined symbols for snappy-sinksource.block.o",
        "undefined symbols for shim.o",
        "undefined symbols for libsnappy.a",
        "production archive members",
    ):
        if label not in text:
            fail(f"audit report does not record {label}")
    print(f"audit report {report}")
    return archive


def basename_of(token: str) -> str:
    return Path(token).name


def ldd_names(path: Path) -> list[str]:
    result = run(["ldd", str(path)], check=False)
    if result.returncode != 0:
        fail(f"ldd exited {result.returncode} for {path.name}")
    names: list[str] = []
    for line_number, raw in enumerate(result.stdout.splitlines(), start=1):
        line = raw.strip()
        if line == "":
            continue
        if "not found" in line:
            fail(f"ldd line {line_number} of {path.name} is unresolved: {line}")
        if "=>" in line:
            left, right = line.split("=>", 1)
            library = left.strip().split()[0]
            if library == "":
                fail(f"ldd line {line_number} of {path.name} has no library: {line}")
            if right.strip().split()[0:1] == []:
                fail(f"ldd line {line_number} of {path.name} has no target: {line}")
            names.append(basename_of(library))
            continue
        token = line.split()[0]
        if token == "":
            fail(f"ldd line {line_number} of {path.name} is unparseable: {line}")
        names.append(basename_of(token))
    if not names:
        fail(f"ldd returned no libraries for {path.name}")
    return names


def needed_names(path: Path) -> list[str]:
    result = run(["readelf", "-d", str(path)], check=False)
    if result.returncode != 0:
        fail(f"readelf exited {result.returncode} for {path.name}")
    names = NEEDED_LIBRARY.findall(result.stdout)
    if not names:
        fail(f"readelf found no NEEDED entries in {path.name}")
    return names


def runtime_families(names: list[str]) -> set[str]:
    found: set[str] = set()
    for name in names:
        for family in CXX_FAMILIES:
            if family in name:
                found.add(family)
    return found


def assert_at_most_one_runtime(label: str, names: list[str]) -> set[str]:
    """Accept no C++ runtime, or one family. Reject both families."""
    found = runtime_families(names)
    shown = "none" if not found else ", ".join(sorted(found))
    print(f"{label} c++ runtime {shown}")
    if len(found) > 1:
        fail(f"{label} links libstdc++ and libc++")
    return found


def assert_same_runtime_families(
    snappy_names: list[str],
    control_names: list[str],
    prefix: str,
) -> None:
    """Require both executables to carry the same zero-or-one family set."""
    snappy = assert_at_most_one_runtime(f"{prefix} snappy", snappy_names)
    control = assert_at_most_one_runtime(f"{prefix} control", control_names)
    if snappy != control:
        fail(f"the {prefix} Snappy executable and the control use different C++ runtimes")


def compare_sanitized_dynamic(snappy: Path, control: Path) -> None:
    snappy_ldd = ldd_names(snappy)
    control_ldd = ldd_names(control)
    print("sanitized ldd snappy")
    for name in snappy_ldd:
        print(f"  {name}")
    print("sanitized ldd control")
    for name in control_ldd:
        print(f"  {name}")
    assert_same_runtime_families(snappy_ldd, control_ldd, "sanitized")
    if set(snappy_ldd) != set(control_ldd):
        fail("the sanitized dynamic libraries differ")
    for label, names in (("sanitized snappy", snappy_ldd), ("sanitized control", control_ldd)):
        if not any("libasan" in name for name in names):
            fail(f"{label} does not link the AddressSanitizer runtime")


def assert_no_sanitizer(label: str, names: list[str]) -> None:
    present = [name for name in names if any(kind in name for kind in SANITIZER_LIBRARIES)]
    if present:
        fail(f"{label} links a sanitizer runtime: {present}")


def compare_dynamic(snappy: Path, control: Path) -> None:
    snappy_ldd = ldd_names(snappy)
    control_ldd = ldd_names(control)
    snappy_needed = needed_names(snappy)
    control_needed = needed_names(control)
    print("unsanitized ldd snappy")
    for name in snappy_ldd:
        print(f"  {name}")
    print("unsanitized ldd control")
    for name in control_ldd:
        print(f"  {name}")
    extra = sorted(set(snappy_ldd) - set(control_ldd))
    if extra:
        fail(f"the Snappy executable adds dynamic libraries: {extra}")
    extra_needed = sorted(set(snappy_needed) - set(control_needed))
    if extra_needed:
        fail(f"the Snappy executable adds NEEDED entries: {extra_needed}")
    assert_same_runtime_families(snappy_ldd, control_ldd, "unsanitized")
    assert_no_sanitizer("snappy", snappy_ldd)
    assert_no_sanitizer("control", control_ldd)


def require_symbol(path: Path, symbol: str, present: bool) -> None:
    text = run(["nm", "-P", "-g", str(path)]).stdout
    found = any(line.split()[:1] == [symbol] for line in text.splitlines())
    if found != present:
        state = "present" if found else "absent"
        fail(f"{symbol} is {state} in {path.name}")


def plain_env() -> dict[str, str]:
    env = os.environ.copy()
    env.pop("ASAN_OPTIONS", None)
    env.pop("LSAN_OPTIONS", None)
    return env


def child_env(asan: str, lsan: str | None) -> dict[str, str]:
    env = plain_env()
    env["ASAN_OPTIONS"] = asan
    if lsan is not None:
        env["LSAN_OPTIONS"] = lsan
    return env


def run_gate(path: Path, asan: str, lsan: str | None) -> subprocess.CompletedProcess[str]:
    return run([str(path)], env=child_env(asan, lsan), check=False)


def assert_clean(label: str, result: subprocess.CompletedProcess[str]) -> None:
    combined = result.stdout + result.stderr
    if "ERROR: AddressSanitizer" in combined or "ERROR: LeakSanitizer" in combined:
        fail(f"{label} reported a sanitizer error")
    if result.returncode != 0:
        fail(f"{label} exited {result.returncode}")


def lsan_gate(snappy: Path, control: Path) -> None:
    for label, path in (("snappy", snappy), ("control", control)):
        result = run_gate(path, LSAN_ASAN_OPTIONS, LSAN_OPTIONS)
        combined = result.stdout + result.stderr
        if result.returncode != 0:
            fail(f"{label} leak gate exited {result.returncode}")
        if "LeakSanitizer" in combined or "detected memory leaks" in combined:
            fail(f"{label} reported a leak")
        if "ERROR: AddressSanitizer" in combined:
            fail(f"{label} hit an AddressSanitizer error during the leak gate")


def negative_controls(work: Path, root: Path) -> None:
    checks = root / "packages" / "codec" / "snappy" / "native" / "check"
    asan_exe = work / "asan-negative"
    lsan_exe = work / "lsan-negative"
    compile = ["c++", *LANGUAGE_FLAGS, *SANITIZE_FLAGS]
    link = SANITIZER_LINK
    # asan-negative.cpp frees a block and then reads it. GCC must not
    # reject that probe before AddressSanitizer runs it.
    # `-Wno-use-after-free` suppresses only that compiler warning, and
    # only for this disposable file. AddressSanitizer stays enabled.
    run(
        [
            *compile,
            "-Wno-use-after-free",
            "-c",
            str(checks / "asan-negative.cpp"),
            "-o",
            str(work / "asan-negative.o"),
        ]
    )
    run([*link, "-o", str(asan_exe), str(work / "asan-negative.o")])
    run([*compile, "-c", str(checks / "lsan-negative.cpp"), "-o", str(work / "lsan-negative.o")])
    run([*link, "-o", str(lsan_exe), str(work / "lsan-negative.o")])
    asan = run_gate(asan_exe, NEGATIVE_ASAN_OPTIONS, None)
    asan_text = asan.stdout + asan.stderr
    if (
        asan.returncode == 0
        or "ERROR: AddressSanitizer" not in asan_text
        or "heap-use-after-free" not in asan_text
    ):
        fail("the AddressSanitizer negative control was not detected")
    print("asan negative control detected")
    lsan = run_gate(lsan_exe, LSAN_ASAN_OPTIONS, LSAN_OPTIONS)
    lsan_text = lsan.stdout + lsan.stderr
    if (
        lsan.returncode != LSAN_EXIT
        or "LeakSanitizer" not in lsan_text
        or "detected memory leaks" not in lsan_text
    ):
        fail("the LeakSanitizer negative control was not detected")
    print("lsan negative control detected")


def prepared_temp(path: Path) -> None:
    temp_root = Path(tempfile.gettempdir()).resolve()
    resolved = path.resolve()
    if not resolved.is_relative_to(temp_root):
        fail(f"temporary directory is outside the system temp directory: {resolved}")
    if not resolved.is_dir():
        fail(f"temporary directory is absent: {resolved}")


def main() -> None:
    assert_platform()
    root = repo_root()
    prefix_text = run(["lean", "--print-prefix"]).stdout.strip()
    if prefix_text == "":
        fail("lean --print-prefix returned an empty path")
    prefix = Path(prefix_text)
    leanc = prefix / "bin" / "leanc"
    ar = prefix / "bin" / "llvm-ar"
    if not leanc.is_file():
        fail(f"leanc is absent: {leanc}")
    if not ar.is_file():
        fail(f"llvm-ar is absent: {ar}")
    print_identities(prefix, leanc, ar)
    run(["lake", "build", "snappyNative/snappyAudit"], cwd=root)
    archive = require_archive(root, ar)
    with tempfile.TemporaryDirectory(prefix="snappy-linux-") as raw_work:
        work = Path(raw_work)
        prepared_temp(work)
        objects = compile_sources(work, prefix, root)
        plain_snappy, plain_control = link_plain(leanc, objects, archive, work)
        require_symbol(plain_snappy, "leanp2p_snappy_compress", True)
        require_symbol(plain_control, "leanp2p_snappy_compress", False)
        compare_dynamic(plain_snappy, plain_control)
        assert_clean(
            "plain snappy",
            run([str(plain_snappy)], env=plain_env(), check=False),
        )
        assert_clean(
            "plain control",
            run([str(plain_control)], env=plain_env(), check=False),
        )
        san_snappy, san_control = link_sanitized(prefix, leanc, objects, work)
        require_symbol(san_snappy, "leanp2p_snappy_compress", True)
        require_symbol(san_control, "leanp2p_snappy_compress", False)
        compare_sanitized_dynamic(san_snappy, san_control)
        assert_clean("asan snappy", run_gate(san_snappy, ASAN_OPTIONS, None))
        assert_clean("asan control", run_gate(san_control, ASAN_OPTIONS, None))
        lsan_gate(san_snappy, san_control)
        negative_controls(work, root)
    print("linux-hardening: passed")


if __name__ == "__main__":
    main()
