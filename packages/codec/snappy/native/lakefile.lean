import Lake
open Lake DSL System

set_option autoImplicit false

/-!
The native helper builds three static Snappy archives.
It exposes no Lean library. The root `lakefile.toml` requires this
directory by a relative path. The Snappy library waits for the
production archive. The two control archives stay on explicit targets.

The helper compiles with the host C++ compiler. That compiler supplies
the standard-library headers for these translation units. The production
archive also contains `shim.o`. The two control archives stay the two
upstream objects. The boundary target compiles one driver and links
that object to each archive. The abort target calls each guarded
production body in its own process. The internal-panic target links one
child to the production archive and calls `leanp2p_snappy_internal_panic`.
The audit target reads the production objects, the production archive,
and the two control surfaces.
-/

/-- Which of the three matched archives a target builds. -/
private inductive ArchiveKind where
  | pristine
  | patched
  | block
  deriving DecidableEq

/-- Output directory name for one archive kind. -/
private def ArchiveKind.dirName : ArchiveKind → String
  | .pristine => "pristine"
  | .patched => "patched"
  | .block => "block"

/--
The host C++ compiler selected for every archive.
`machine` is the `-dumpmachine` target triple.
-/
private structure Cxx where
  command : String
  version : String
  machine : String

/--
Semantic flags shared by the three archives.
Snappy 1.3.1 selects C++11 when its CMake build leaves the standard
unset. `HAVE_CONFIG_H=1` selects `include/config.h`. The objects keep
the upstream assertions. `buildO` records this list as `traceArgs`.
-/
private def sharedCxxArgs : Array String := #[
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
  "-fPIC",
  "-DHAVE_CONFIG_H=1"
]

/-- Semantic flags for one archive kind. The block-only macro is the production difference. -/
private def traceCxxArgs (kind : ArchiveKind) : Array String := Id.run do
  let mut args := sharedCxxArgs
  if kind = .block then
    args := args.push "-DLEANP2P_SNAPPY_BLOCK_ONLY=1"
  return args

/--
Semantic flags for upstream `snappy.cc`.
GCC 15 warns that `std::pair<__m128i, __m128i>` drops the alignment
attribute on the template argument. `-Wno-error=ignored-attributes`
follows `-Werror` in this list only. The warning stays visible. Every
other warning remains an error. The sink unit, the shim, and the check
drivers keep `traceCxxArgs` or `driverTraceArgs`.
-/
private def coreTraceCxxArgs (kind : ArchiveKind) : Array String := Id.run do
  let mut args : Array String := #[]
  for flag in traceCxxArgs kind do
    args := args.push flag
    if flag == "-Werror" then
      args := args.push "-Wno-error=ignored-attributes"
  return args

/--
Absolute include paths for one archive.
`buildO` treats these as `weakArgs`, so the object trace follows the
header bytes rather than the path spelling.
-/
private def weakCxxArgs (srcDir includeDir : FilePath) : Array String := #[
  "-I", srcDir.toString,
  "-I", includeDir.toString
]

/-- Stdout and stderr from a compiler probe, with surrounding whitespace removed. -/
private def commandText (out : IO.Process.Output) : String :=
  let stdout := out.stdout.trimAscii.copy
  let stderr := out.stderr.trimAscii.copy
  if stderr.isEmpty then stdout
  else if stdout.isEmpty then stderr
  else s!"{stdout}\n{stderr}"

/--
Run one compiler command.
`none` means the command is absent from the process search path.
A command that starts and then fails is an error.
-/
private def tryCommand (cmd : String) (args : Array String) : LogIO (Option IO.Process.Output) := do
  match ← (IO.Process.output {cmd, args}).toBaseIO with
  | .error (.noFileOrDirectory ..) => return none
  | .error err =>
    error s!"The C++ compiler `{cmd}` failed to start: {err}"
  | .ok out =>
    if out.exitCode = 0 then
      return some out
    else
      error s!"The C++ compiler `{cmd}` rejected `{" ".intercalate args.toList}`.\n{commandText out}"

/--
Select `c++`, then `clang++`, then `g++`.
The result carries the command, its `--version` report, and its
`-dumpmachine` target. Compile jobs use this same command.
-/
private def selectCxx : LogIO Cxx := do
  for name in #["c++", "clang++", "g++"] do
    match ← tryCommand name #["--version"] with
    | none => continue
    | some verOut =>
      let version := commandText verOut
      if version.isEmpty then
        error s!"The C++ compiler `{name}` returned an empty `--version` report."
      let some machOut ← tryCommand name #["-dumpmachine"]
        | error s!"The C++ compiler `{name}` reported its version and returned no `-dumpmachine` target."
      let machine := machOut.stdout.trimAscii.copy
      if machine.isEmpty then
        error s!"The C++ compiler `{name}` returned an empty `-dumpmachine` target."
      return {command := name, version, machine}
  error "The process search path has no C++ compiler. The search tried c++, clang++, and g++."

/-- Headers included by `snappy.cc` from the selected source directory. -/
private def coreHeaders (srcDir : FilePath) : Array FilePath := #[
  srcDir / "snappy.h",
  srcDir / "snappy-internal.h",
  srcDir / "snappy-sinksource.h",
  srcDir / "snappy-stubs-internal.h"
]

/-- Build-support headers selected by `HAVE_CONFIG_H` and by `snappy.h`. -/
private def supportHeaders (includeDir : FilePath) : Array FilePath := #[
  includeDir / "config.h",
  includeDir / "snappy-stubs-public.h"
]

/--
Compile one translation unit.
The source job is an `inputTextFile`. `weakArgs` carry the include
paths, and `traceArgs` carry the semantic flags. `extraDepTrace`
records the project headers and the host compiler identity. `buildO`
adds the platform trace and the `traceArgs` trace.
-/
private def compileUnit
    (oFile src : FilePath) (headers : Array FilePath)
    (cxx : Cxx) (weakArgs traceArgs : Array String)
    : SpawnM (Job FilePath) := do
  let srcJob ← inputTextFile src
  buildO oFile srcJob weakArgs traceArgs cxx.command (extraDepTrace := do
    for header in headers do
      addTrace (← computeTrace (TextFilePath.mk header))
    addPureTrace cxx.command "cxx"
    addPureTrace cxx.version "cxx-version"
    addPureTrace cxx.machine "cxx-target"
    return BuildTrace.nil)

/--
Source directory for one archive kind.
`realPath` resolves the pristine directory, which sits beside this package.
-/
private def sourceDir (pkg : Package) (kind : ArchiveKind) : LogIO FilePath := do
  let raw :=
    match kind with
    | .pristine => pkg.dir / ".." / "upstream" / "pristine"
    | .patched | .block => pkg.dir / "vendor" / "snappy"
  IO.FS.realPath raw

/-- Archive file name for one archive kind. `libsnappy.a` is the production archive. -/
private def archiveName : ArchiveKind → String
  | .pristine => "libsnappy_pristine.a"
  | .patched => "libsnappy_patched.a"
  | .block => "libsnappy.a"

/--
Build the upstream objects and the static archive.
The control arrays are the core object, the sink object, and the archive.
The production array adds `shim.o` before the archive.
`buildStaticLib` archives the object jobs with the toolchain `ar`.
An object whose bytes stay the same leaves the archive current.
The audit fetches this same job.
-/
private def buildParts (pkg : Package) (kind : ArchiveKind) : FetchM (Job (Array FilePath)) := do
  let cxx ← selectCxx
  let srcDir ← sourceDir pkg kind
  let includeDir ← IO.FS.realPath (pkg.dir / "include")
  let outDir := (pkg.buildDir / "snappy" / kind.dirName).normalize
  let weakArgs := weakCxxArgs srcDir includeDir
  let traceArgs := traceCxxArgs kind
  let coreTraceArgs := coreTraceCxxArgs kind
  let stem := kind.dirName
  logVerbose s!"cxx: {cxx.command}"
  logVerbose s!"cxx-target: {cxx.machine}"
  logVerbose s!"cxx-version: {cxx.version}"
  let snappyO ← compileUnit
    (outDir / s!"snappy.{stem}.o")
    (srcDir / "snappy.cc")
    (coreHeaders srcDir ++ supportHeaders includeDir)
    cxx weakArgs coreTraceArgs
  let sinkO ← compileUnit
    (outDir / s!"snappy-sinksource.{stem}.o")
    (srcDir / "snappy-sinksource.cc")
    #[srcDir / "snappy-sinksource.h"]
    cxx weakArgs traceArgs
  let mut objects : Array (Job FilePath) := #[snappyO, sinkO]
  if kind = .block then
    let leanInc ← getLeanIncludeDir
    let shimWeak := weakArgs ++ #["-I", leanInc.toString]
    let shimO ← compileUnit
      (outDir / "shim.o")
      (pkg.dir / "shim.cpp")
      #[
        srcDir / "snappy.h",
        includeDir / "snappy-stubs-public.h",
        includeDir / "config.h",
        leanInc / "lean" / "lean.h"
      ]
      cxx shimWeak traceArgs
    objects := objects.push shimO
  let archive ← buildStaticLib (outDir / archiveName kind) objects
  return Job.collectArray (objects.push archive) s!"parts-{stem}"

/-- Return the archive from a parts job after checking the member names. -/
private def archiveFromParts (kind : ArchiveKind) (parts : Job (Array FilePath)) : SpawnM (Job FilePath) :=
  parts.mapM fun files => do
    let expected := if kind = .block then 4 else 3
    if files.size != expected then
      error s!"The {kind.dirName} parts job expected {expected} files. It received {files.size}."
    else
      let core := files[0]!
      let sink := files[1]!
      let archive := files[files.size - 1]!
      if core.fileName != some s!"snappy.{kind.dirName}.o" then
        error s!"The {kind.dirName} parts job expected snappy.{kind.dirName}.o. It received {core}."
      if sink.fileName != some s!"snappy-sinksource.{kind.dirName}.o" then
        error s!"The {kind.dirName} parts job expected snappy-sinksource.{kind.dirName}.o. It received {sink}."
      if kind = .block && files[2]!.fileName != some "shim.o" then
        error s!"The block parts job expected shim.o. It received {files[2]!}."
      if archive.fileName != some (archiveName kind) then
        error s!"The {kind.dirName} parts job expected {archiveName kind}. It received {archive}."
      return archive

package snappyNative

/--
Production objects and the production archive.
The array is `snappy.block.o`, `snappy-sinksource.block.o`, `shim.o`,
and `libsnappy.a`. The archive target and the audit target both fetch
this job.
-/
target snappyBlockParts pkg : Array FilePath :=
  buildParts pkg .block

/-- Pristine objects and the pristine archive. -/
target snappyPristineParts pkg : Array FilePath :=
  buildParts pkg .pristine

/-- Patched objects and the patched archive. The define stays off. -/
target snappyPatchedParts pkg : Array FilePath :=
  buildParts pkg .patched

/--
Production block-only archive.
The objects come from `vendor/snappy` with `LEANP2P_SNAPPY_BLOCK_ONLY=1`,
plus `shim.o`. The archive is `libsnappy.a`.
-/
@[default_target]
target snappy _pkg : FilePath := do
  archiveFromParts .block (← snappyBlockParts.fetch)

/-- Pristine control archive. The objects come from `upstream/pristine`. -/
target snappyPristine _pkg : FilePath := do
  archiveFromParts .pristine (← snappyPristineParts.fetch)

/-- Patched control archive. The objects come from `vendor/snappy` under the shared flags. -/
target snappyPatched _pkg : FilePath := do
  archiveFromParts .patched (← snappyPatchedParts.fetch)

/--
Build the pristine archive and the patched archive.
The production target stays `snappy`.
-/
target snappyControls : Array FilePath := do
  let pristine ← snappyPristine.fetch
  let patched ← snappyPatched.fetch
  return Job.collectArray #[pristine, patched]

/--
Build the pristine archive, the patched archive, and the production archive.
The array follows that order.
-/
target snappyArchives : Array FilePath := do
  let pristine ← snappyPristine.fetch
  let patched ← snappyPatched.fetch
  let prod ← snappy.fetch
  return Job.collectArray #[pristine, patched, prod]

/-- Semantic flags for the boundary driver. `buildO` records this list as `traceArgs`. -/
private def driverTraceArgs : Array String := #[
  "-std=c++11",
  "-O2",
  "-Wall",
  "-Wextra",
  "-Werror",
  "-fno-exceptions",
  "-fno-rtti",
  "-fno-threadsafe-statics",
  "-ffunction-sections",
  "-fdata-sections"
]

/--
Section garbage collection for the three check executables.
macOS uses `-dead_strip`. Linux uses `--gc-sections`.
-/
private def sectionGcArgs : Array String :=
  if System.Platform.isOSX then #["-Wl,-dead_strip"]
  else #["-Wl,--gc-sections"]

/-- Driver source. One compilation of this file feeds every check executable. -/
private def driverSrc (pkg : Package) : FilePath :=
  pkg.dir / "check" / "core.cpp"

/-- Transcript written by the check executable for one archive. -/
private def transcriptPath (pkg : Package) (kind : ArchiveKind) : FilePath :=
  pkg.buildDir / "check" / s!"{kind.dirName}.txt"

/-- Compile `check/core.cpp` once with the host C++ compiler. -/
private def buildDriver (pkg : Package) (cxx : Cxx) : FetchM (Job FilePath) := do
  let srcDir ← IO.FS.realPath (pkg.dir / "vendor" / "snappy")
  let includeDir ← IO.FS.realPath (pkg.dir / "include")
  let oFile := pkg.buildDir / "check" / "core.o"
  logVerbose s!"cxx: {cxx.command}"
  logVerbose s!"cxx-target: {cxx.machine}"
  logVerbose s!"cxx-version: {cxx.version}"
  compileUnit oFile (driverSrc pkg)
    #[srcDir / "snappy.h", includeDir / "snappy-stubs-public.h"]
    cxx (weakCxxArgs srcDir includeDir) driverTraceArgs

/--
The driver object.
A separate target keeps this compilation as one job. The three links
fetch that job.
-/
target snappyCheckObj pkg : FilePath := do
  buildDriver pkg (← selectCxx)

/--
Link one check executable to one archive.
The link arguments name the driver object and that archive directly.
`snappy.cc` and `snappy-sinksource.cc` stay inside the archive.
-/
private def buildCheckExe
    (pkg : Package) (kind : ArchiveKind) (cxx : Cxx)
    (driverO archive : Job FilePath) : SpawnM (Job FilePath) := do
  let exe := pkg.buildDir / "check" / s!"core-{kind.dirName}"
  (Job.collectArray #[driverO, archive] s!"check-{kind.dirName}").mapM fun files => do
    if files.size != 2 then
      error s!"The {kind.dirName} check link expected the driver and one archive."
    else
      let driver := files[0]!
      let lib := files[1]!
      if driver.extension != some "o" then
        error s!"The {kind.dirName} check link expected the driver object. It received {driver}."
      if lib.extension != some "a" || lib.fileName != some (archiveName kind) then
        error s!"The {kind.dirName} check link expected {archiveName kind}. It received {lib}."
      addPlatformTrace
      addPureTrace sectionGcArgs "link-args"
      addPureTrace cxx.command "cxx"
      addPureTrace cxx.version "cxx-version"
      addPureTrace cxx.machine "cxx-target"
      let art ← buildArtifactUnlessUpToDate exe (ext := "exe") (exe := true) do
        createParentDirs exe
        proc {
          cmd := cxx.command
          args := #["-o", exe.toString, driver.toString, lib.toString] ++ sectionGcArgs
        }
      return art.path

/--
Remove a text artifact whose bytes differ from the hash Lake saved.
`buildArtifactUnlessUpToDate` rebuilds a missing file. It keeps a file
that is still present, so a changed artifact is removed first.
`text := true` matches the artifact hash.
-/
private def dropChangedTextArtifact (out : FilePath) : JobM PUnit := do
  if !(← out.pathExists) then
    return
  let hashFile := FilePath.mk <| out.toString ++ ".hash"
  match ← Hash.load? hashFile with
  | none => removeFileIfExists out
  | some saved =>
    if (← computeFileHash out (text := true)) != saved then
      removeFileIfExists out

/--
Run one check executable.
The transcript is the artifact of this job, and the job waits for that
executable. The text cache stores a copy, so the local file is not a
hard link to the cache.
-/
private def runTranscript
    (pkg : Package) (kind : ArchiveKind) (exe : Job FilePath)
    : SpawnM (Job FilePath) := do
  let out := transcriptPath pkg kind
  exe.mapM fun exePath => do
    dropChangedTextArtifact out
    let art ← buildArtifactUnlessUpToDate out (ext := "txt") (text := true) do
      createParentDirs out
      proc {
        cmd := exePath.toString
        args := #[out.toString]
      }
    return art.path

/-- First index at which two transcripts differ, or the first index past the shorter one. -/
private def firstByteDiffFrom (a b : ByteArray) (i : Nat) : Option Nat :=
  if h : i < a.size then
    if h2 : i < b.size then
      if a[i] == b[i] then
        firstByteDiffFrom a b (i + 1)
      else
        some i
    else
      some i
  else if i < b.size then
    some i
  else
    none
termination_by a.size - i

/-- Two lowercase hex digits for one transcript byte. -/
private def hexByte (b : UInt8) : String :=
  let digits := #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
                  'a', 'b', 'c', 'd', 'e', 'f']
  let n := b.toNat
  s!"{digits[n / 16]!}{digits[n % 16]!}"

/-- Describe the first byte difference. `none` means the transcripts match. -/
private def describeDiff (left right : String) (a b : ByteArray) : Option String :=
  match firstByteDiffFrom a b 0 with
  | none => none
  | some i =>
    let leftByte :=
      if h : i < a.size then s!"The {left} byte is {hexByte a[i]}."
      else s!"The {left} transcript has {a.size} bytes."
    let rightByte :=
      if h : i < b.size then s!"The {right} byte is {hexByte b[i]}."
      else s!"The {right} transcript has {b.size} bytes."
    some s!"The {left} transcript and the {right} transcript differ at byte {i}. {leftByte} {rightByte}"

/-- Fail the build at the first transcript difference. -/
private def rejectDiff (left right : String) (a b : ByteArray) : JobM PUnit := do
  if let some msg := describeDiff left right a b then
    error msg

/--
Compare the three transcript jobs.
The paths come from those jobs. `match.stamp` records a comparison
that accepted those bytes.
-/
private def compareTranscripts
    (pkg : Package) (pristine patched prod : Job FilePath)
    : SpawnM (Job (Array FilePath)) := do
  let matchStamp := pkg.buildDir / "check" / "match.stamp"
  (Job.collectArray #[pristine, patched, prod] "transcripts").mapM fun paths => do
    if paths.size != 3 then
      error s!"The transcript comparison expected 3 files. It received {paths.size}."
    else
      let pristinePath := paths[0]!
      let patchedPath := paths[1]!
      let prodPath := paths[2]!
      discard <| buildArtifactUnlessUpToDate matchStamp (ext := "stamp") (text := true) do
        let pristineBytes ← IO.FS.readBinFile pristinePath
        let patchedBytes ← IO.FS.readBinFile patchedPath
        let prodBytes ← IO.FS.readBinFile prodPath
        rejectDiff "pristine" "patched" pristineBytes patchedBytes
        rejectDiff "pristine" "production" pristineBytes prodBytes
        rejectDiff "patched" "production" patchedBytes prodBytes
        createParentDirs matchStamp
        IO.FS.writeFile matchStamp "match\n"
      return paths

/--
Build the three archives and the three check executables.
Each executable writes its own transcript. The comparison waits for
those three transcript jobs.
`lake build snappyNative/snappyBoundary` runs this target from the
repository root. The production executable is the file this link job
produces.
-/
target snappyBoundary pkg : Array FilePath := do
  let cxx ← selectCxx
  let driver ← snappyCheckObj.fetch
  let pristineExe ← buildCheckExe pkg .pristine cxx driver (← snappyPristine.fetch)
  let patchedExe ← buildCheckExe pkg .patched cxx driver (← snappyPatched.fetch)
  let blockExe ← buildCheckExe pkg .block cxx driver (← snappy.fetch)
  let pristineTxt ← runTranscript pkg .pristine pristineExe
  let patchedTxt ← runTranscript pkg .patched patchedExe
  let blockTxt ← runTranscript pkg .block blockExe
  compareTranscripts pkg pristineTxt patchedTxt blockTxt

/--
Semantic flags for the abort driver.
They extend the boundary driver flags with the production define.
`buildO` records this list as `traceArgs`.
-/
private def abortTraceArgs : Array String :=
  driverTraceArgs.push "-DLEANP2P_SNAPPY_BLOCK_ONLY=1"

/-- Status produced by the driver's `SIGABRT` handler. -/
private def abortSentinel : UInt32 := 86

/-- One child process calls one guarded function. -/
private def abortModes : Array String := #[
  "sink-append",
  "source-available",
  "source-peek",
  "source-skip",
  "sink-delete",
  "sink-delete-sized",
  "source-delete",
  "source-delete-sized",
  "byte-array-source-delete",
  "byte-array-source-delete-sized",
  "unchecked-byte-array-sink-delete",
  "unchecked-byte-array-sink-delete-sized"
]

/-- Abort driver source. The boundary driver stays in `check/core.cpp`. -/
private def abortSrc (pkg : Package) : FilePath :=
  pkg.dir / "check" / "abort.cpp"

/-- Compile `check/abort.cpp` once against the production headers. -/
private def buildAbortObj (pkg : Package) (cxx : Cxx) : FetchM (Job FilePath) := do
  let srcDir ← IO.FS.realPath (pkg.dir / "vendor" / "snappy")
  let includeDir ← IO.FS.realPath (pkg.dir / "include")
  let oFile := pkg.buildDir / "check" / "abort.o"
  logVerbose s!"cxx: {cxx.command}"
  logVerbose s!"cxx-target: {cxx.machine}"
  logVerbose s!"cxx-version: {cxx.version}"
  compileUnit oFile (abortSrc pkg)
    #[srcDir / "snappy-sinksource.h"]
    cxx (weakCxxArgs srcDir includeDir) abortTraceArgs

/-- One named file from a parts array. -/
private def partFile (files : Array FilePath) (index : Nat) (expected : String) : JobM FilePath := do
  if files.size ≤ index then
    error s!"The parts array has no {expected}."
  else
    let file := files[index]!
    if file.fileName != some expected then
      error s!"The parts array expected {expected}. It received {file}."
    return file

/-- A core dump is `core` or `core.<pid>`. `core.o` is the boundary object. -/
private def isCoreDump (name : String) : Bool :=
  name == "core" ||
    (name.startsWith "core." && (name.drop 5).all Char.isDigit && !(name.drop 5).isEmpty)

/-- Remove a core dump left beside the abort executable, then fail. -/
private def rejectCoreFile (dir : FilePath) : JobM PUnit := do
  if !(← dir.pathExists) then
    return
  for entry in (← dir.readDir) do
    let name := entry.fileName
    if isCoreDump name then
      IO.FS.removeFile entry.path
      error s!"The abort driver left {entry.path}."

/--
Run every abort mode in its own process.
`workDir` is the executable directory. Each child starts there, and the
core-file check reads that same directory. The text artifact is written
only after every mode returns `abortSentinel`.
-/
private def runAbortMatrix (exe workDir artifact : FilePath) : JobM PUnit := do
  removeFileIfExists artifact
  let mut lines : Array String := #[]
  for mode in abortModes do
    let out ← IO.Process.output {
      cmd := exe.toString
      args := #[mode]
      cwd := some workDir
    }
    if out.exitCode != abortSentinel then
      error s!"Abort mode {mode} returned status {out.exitCode}. The SIGABRT sentinel is {abortSentinel}.\n{out.stdout}{out.stderr}"
    lines := lines.push s!"{mode} {abortSentinel}"
  rejectCoreFile workDir
  createParentDirs artifact
  IO.FS.writeFile artifact <| String.intercalate "\n" lines.toList ++ "\n"

/--
Link `check/abort.cpp` to the production archive and run the twelve modes.
The link names `abort.o` and `libsnappy.a` directly. This target returns
the text artifact, and the executable stays an input of that artifact.
`lake build snappyNative/snappyAbort` runs this target from the repository root.
-/
target snappyAbort pkg : FilePath := do
  let cxx ← selectCxx
  let obj ← buildAbortObj pkg cxx
  let archive ← (← snappyBlockParts.fetch).mapM fun files => partFile files 3 "libsnappy.a"
  let exe := pkg.buildDir / "check" / "abort"
  let artifact := pkg.buildDir / "check" / "abort.txt"
  (Job.collectArray #[obj, archive] "abort-link").mapM fun files => do
    if files.size != 2 then
      error s!"The abort link expected the driver and the production archive. It received {files.size}."
    else
      let driver := files[0]!
      let lib := files[1]!
      if driver.fileName != some "abort.o" then
        error s!"The abort link expected abort.o. It received {driver}."
      if lib.fileName != some "libsnappy.a" then
        error s!"The abort link expected libsnappy.a. It received {lib}."
      addPlatformTrace
      addPureTrace sectionGcArgs "link-args"
      addPureTrace cxx.command "cxx"
      addPureTrace cxx.version "cxx-version"
      addPureTrace cxx.machine "cxx-target"
      addPureTrace (" ".intercalate abortModes.toList) "abort-modes"
      addPureTrace (toString abortSentinel) "abort-sentinel"
      let linked ← buildArtifactUnlessUpToDate exe (ext := "exe") (exe := true) do
        createParentDirs exe
        proc {
          cmd := cxx.command
          args := #["-o", exe.toString, driver.toString, lib.toString] ++ sectionGcArgs
        }
      let exePath ← IO.FS.realPath linked.path
      let some parent := exePath.parent
        | error s!"The abort executable has no directory: {exePath}."
      let workDir ← IO.FS.realPath parent
      logVerbose s!"abort-workdir: {workDir}"
      dropChangedTextArtifact artifact
      let art ← buildArtifactUnlessUpToDate artifact (ext := "txt") (text := true) do
        runAbortMatrix exePath workDir artifact
      return art.path

/-- Policy string shared with `scripts/audit-native.py`. -/
private def auditPolicy : String := "phase-3b/1"

/-- Package audit script. It sits beside the offline verifier. -/
private def auditScript (pkg : Package) : FilePath :=
  pkg.dir / ".." / "scripts" / "audit-native.py"

/-- Stdout and stderr of a tool probe. A nonzero status is an error. -/
private def toolReport (cmd : String) (args : Array String) : LogIO String := do
  let out ← IO.Process.output {cmd, args}
  if out.exitCode != 0 then
    error s!"`{cmd}` failed.\n{commandText out}"
  let text := commandText out
  if text.isEmpty then
    error s!"`{cmd}` returned an empty report."
  return text

/--
Audit the production objects and archive, then compare the control surfaces.
The object paths come from the three parts targets, including `shim.o`.
The script does not search for a second copy.
`lake build snappyNative/snappyAudit` runs this target from the repository root.
-/
target snappyAudit pkg : FilePath := do
  let block ← snappyBlockParts.fetch
  let pristine ← snappyPristineParts.fetch
  let patched ← snappyPatchedParts.fetch
  let auditPy ← IO.FS.realPath (auditScript pkg)
  let nmVersion ← toolReport "nm" #["--version"]
  let filtVersion ← toolReport "c++filt" #["--version"]
  let ar ← getLeanAr
  let arVersion ← toolReport ar.toString #["--version"]
  let pyVersion ← toolReport "python3" #["--version"]
  let report := pkg.buildDir / "check" / "audit.txt"
  (Job.collectArray #[block, pristine, patched] "audit-parts").mapM fun groups => do
    if groups.size != 3 then
      error s!"The audit expected 3 part arrays. It received {groups.size}."
    else
      let prodCore ← partFile groups[0]! 0 "snappy.block.o"
      let prodSink ← partFile groups[0]! 1 "snappy-sinksource.block.o"
      let prodShim ← partFile groups[0]! 2 "shim.o"
      let prodArchive ← partFile groups[0]! 3 "libsnappy.a"
      let pristineCore ← partFile groups[1]! 0 "snappy.pristine.o"
      let pristineSink ← partFile groups[1]! 1 "snappy-sinksource.pristine.o"
      let pristineArchive ← partFile groups[1]! 2 "libsnappy_pristine.a"
      let patchedCore ← partFile groups[2]! 0 "snappy.patched.o"
      let patchedSink ← partFile groups[2]! 1 "snappy-sinksource.patched.o"
      let patchedArchive ← partFile groups[2]! 2 "libsnappy_patched.a"
      addPlatformTrace
      addPureTrace auditPolicy "audit-policy"
      addPureTrace "nm" "nm"
      addPureTrace nmVersion "nm-version"
      addPureTrace "c++filt" "cxxfilt"
      addPureTrace filtVersion "cxxfilt-version"
      addPureTrace ar.toString "ar"
      addPureTrace arVersion "ar-version"
      addPureTrace "python3" "python"
      addPureTrace pyVersion "python-version"
      addTrace (← computeTrace (TextFilePath.mk auditPy))
      dropChangedTextArtifact report
      let art ← buildArtifactUnlessUpToDate report (ext := "txt") (text := true) do
        let out ← IO.Process.output {
          cmd := "python3"
          args := #[
            auditPy.toString, "audit",
            "--policy", auditPolicy,
            "--nm", "nm",
            "--cxxfilt", "c++filt",
            "--ar", ar.toString,
            "--production-core", prodCore.toString,
            "--production-sink", prodSink.toString,
            "--production-shim", prodShim.toString,
            "--production-archive", prodArchive.toString,
            "--pristine-core", pristineCore.toString,
            "--pristine-sink", pristineSink.toString,
            "--pristine-archive", pristineArchive.toString,
            "--patched-core", patchedCore.toString,
            "--patched-sink", patchedSink.toString,
            "--patched-archive", patchedArchive.toString
          ]
        }
        if out.exitCode != 0 then
          error s!"The native audit failed with status {out.exitCode}.\n{out.stdout}{out.stderr}"
        if out.stdout.isEmpty then
          error "The native audit returned an empty report."
        createParentDirs report
        IO.FS.writeFile report out.stdout
      return art.path

/-- Source for the internal-panic child. -/
private def internalPanicSrc (pkg : Package) : FilePath :=
  pkg.dir / "check" / "internal-panic.cpp"

/-- Stderr of a successful call to `leanp2p_snappy_internal_panic(1)`. -/
private def internalPanicStderr : String :=
  "INTERNAL PANIC: snappy: compression returned an unexpected status\n"

/--
Link `check/internal-panic.cpp` to the production archive and call
`leanp2p_snappy_internal_panic`. The link names `internal-panic.o` and
`libsnappy.a` once. The child sets `LEAN_ABORT_ON_PANIC` itself.
This target returns the text artifact.
`lake build snappyNative/snappyInternalPanic` runs it from the repository root.
-/
target snappyInternalPanic pkg : FilePath := do
  let cxx ← selectCxx
  let leanInc ← getLeanIncludeDir
  let obj ← compileUnit
    (pkg.buildDir / "check" / "internal-panic.o")
    (internalPanicSrc pkg)
    #[leanInc / "lean" / "lean.h"]
    cxx #["-I", leanInc.toString] driverTraceArgs
  let archive ← (← snappyBlockParts.fetch).mapM fun files => partFile files 3 "libsnappy.a"
  let exe := pkg.buildDir / "check" / "internal-panic"
  let artifact := pkg.buildDir / "check" / "internal-panic.txt"
  let leanc := (← getLeanSysroot) / "bin" / "leanc"
  (Job.collectArray #[obj, archive] "internal-panic-link").mapM fun files => do
    if files.size != 2 then
      error s!"The internal-panic link expected the child and the production archive. It received {files.size}."
    else
      let driver := files[0]!
      let lib := files[1]!
      if driver.fileName != some "internal-panic.o" then
        error s!"The internal-panic link expected internal-panic.o. It received {driver}."
      if lib.fileName != some "libsnappy.a" then
        error s!"The internal-panic link expected libsnappy.a. It received {lib}."
      addPlatformTrace
      addPureTrace sectionGcArgs "link-args"
      addPureTrace leanc.toString "leanc"
      addPureTrace cxx.command "cxx"
      addPureTrace cxx.version "cxx-version"
      addPureTrace cxx.machine "cxx-target"
      addPureTrace (toString abortSentinel) "internal-panic-sentinel"
      addPureTrace internalPanicStderr "internal-panic-stderr"
      let linkArgs := #["-o", exe.toString, driver.toString, lib.toString] ++ sectionGcArgs
      logVerbose s!"internal-panic-link: {leanc} {" ".intercalate linkArgs.toList}"
      let linked ← buildArtifactUnlessUpToDate exe (ext := "exe") (exe := true) do
        createParentDirs exe
        proc {
          cmd := leanc.toString
          args := linkArgs
        }
      let exePath ← IO.FS.realPath linked.path
      let some parent := exePath.parent
        | error s!"The internal-panic executable has no directory: {exePath}."
      let workDir ← IO.FS.realPath parent
      removeFileIfExists artifact
      dropChangedTextArtifact artifact
      let art ← buildArtifactUnlessUpToDate artifact (ext := "txt") (text := true) do
        let out ← IO.Process.output {
          cmd := exePath.toString
          cwd := some workDir
        }
        let mut cores : Array String := #[]
        if (← workDir.pathExists) then
          for entry in (← workDir.readDir) do
            if isCoreDump entry.fileName then
              cores := cores.push entry.fileName
              IO.FS.removeFile entry.path
        let statusOk := out.exitCode == abortSentinel
        let stdoutOk := out.stdout == ""
        let stderrOk := out.stderr == internalPanicStderr
        if !statusOk || !stdoutOk || !stderrOk || !cores.isEmpty then
          error s!"The internal-panic child failed.\nstatus {out.exitCode}\nstdout [{out.stdout}]\nstderr [{out.stderr}]\ncore {cores}"
        createParentDirs artifact
        IO.FS.writeFile artifact <|
          s!"link {leanc} {" ".intercalate linkArgs.toList}\nstatus {abortSentinel}\nstderr:\n{internalPanicStderr}"
      return art.path

/--
Run the boundary check, the abort check, the internal-panic check, and
the audit. The targets share the production object jobs. This target
does not compile a second `snappy.cc` or `snappy-sinksource.cc`.
`lake build snappyNative/snappyValidation` runs it from the repository root.
-/
target snappyValidation pkg : FilePath := do
  let boundary ← (← snappyBoundary.fetch).mapM fun _ => pure "boundary"
  let abortTxt ← (← snappyAbort.fetch).mapM fun path => pure path.toString
  let panicTxt ← (← snappyInternalPanic.fetch).mapM fun path => pure path.toString
  let auditTxt ← (← snappyAudit.fetch).mapM fun path => pure path.toString
  let stamp := pkg.buildDir / "check" / "validation.stamp"
  (Job.collectArray #[boundary, abortTxt, panicTxt, auditTxt] "validation").mapM fun _ => do
    dropChangedTextArtifact stamp
    let art ← buildArtifactUnlessUpToDate stamp (ext := "stamp") (text := true) do
      createParentDirs stamp
      IO.FS.writeFile stamp "validation\n"
    return art.path
