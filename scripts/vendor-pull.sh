#!/usr/bin/env bash
# Recreate vendor/ from the pins in VECTORS.lock (VECTOR_TEST_PLAN.md, phase 0).
#
# Usage:
#   scripts/vendor-pull.sh            # (re)fetch every pinned copy into vendor/
#   scripts/vendor-pull.sh --verify   # diff existing copies against fresh clones
#                                     # of the pinned commits, change nothing
#
# To bump a pin: edit VECTORS.lock, run this script, re-run
# scripts/extract-vectors.py, and commit the refreshed JSON.
set -euo pipefail

cd "$(dirname "$0")/.."

python3 - VECTORS.lock "$1" <<'PY'
import os, subprocess, sys, tomllib, tempfile

lock, mode = sys.argv[1], sys.argv[2]
verify = mode == "--verify"
with open(lock, "rb") as f:
    entries = tomllib.load(f)["vendor"]

for e in entries:
    d, repo, commit = e["dir"], e["repo"], e["commit"]
    pin = os.path.join(d, ".pin")
    if verify:
        if not os.path.isdir(d):
            print("MISSING " + d)
            continue
        with open(pin) as f:
            if f.read().strip() != commit:
                print("PIN-MISMATCH " + d)
                continue
    tmp = tempfile.mkdtemp(prefix="vendor-" + os.path.basename(d) + "-")
    subprocess.run(["git", "clone", "--quiet", "--filter=blob:none", repo, tmp],
                   check=True)
    subprocess.run(["git", "-C", tmp, "checkout", "--quiet", commit], check=True)
    subprocess.run(["rm", "-rf", os.path.join(tmp, ".git")], check=True)
    with open(os.path.join(tmp, ".pin"), "w") as f:
        f.write(commit + "\n")
    if verify:
        r = subprocess.run(["diff", "-r", "--exclude=.pin", d, tmp])
        print(("OK  " if r.returncode == 0 else "BAD ") + d)
        subprocess.run(["rm", "-rf", tmp])
    else:
        if os.path.exists(d):
            subprocess.run(["rm", "-rf", d])
        subprocess.run(["mv", tmp, d])
        print("synced " + d + " @ " + commit[:12])
PY
