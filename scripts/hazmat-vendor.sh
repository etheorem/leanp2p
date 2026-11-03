#!/usr/bin/env bash
# Fetch the native sources of the etheorem hazmat pins (root
# ARCHITECTURE §4.6, PLAN W3.2; packages/crypto/backend/docs/PLAN.md,
# milestones for 1a).
#
# Lake clones each pinned family into `.lake/packages/<Family>`, a full
# checkout of the etheorem monorepo at the pinned rev. Two families
# build from sources that the monorepo's own `just` recipes fetch
# shallow into a gitignored `vendor/` tree, at the pins the recipes
# carry: libsecp256k1 for LeanHazmatSecp256k1 and keccak-tiny for
# LeanHazmatKeccak. LeanHazmatP256 needs no fetch. LeanHazmatSha256 is
# not pinned (see the root lakefile.toml).
# This script runs each recipe inside its own clone, so the pins stay
# the monorepo's. The recipes skip a fetch that is already at its pin,
# so a rerun is cheap. After the fetch, `lake build` stays offline.
#
# Order: `lake update` (or any build) clones the pins first; then this
# script; then `lake build`.
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"

for tool in just git; do
  if ! command -v "$tool" >/dev/null; then
    echo "hazmat-vendor: $tool is missing; install it and rerun" >&2
    exit 1
  fi
done

# family recipe
fetches=(
  "LeanHazmatSecp256k1 hazmat-secp256k1-vendor"
  "LeanHazmatKeccak hazmat-keccak-vendor"
)

for entry in "${fetches[@]}"; do
  read -r family recipe <<< "$entry"
  clone="$root/.lake/packages/$family"
  if [ ! -f "$clone/Justfile" ]; then
    echo "hazmat-vendor: $clone is not a monorepo clone; run \`lake update\` first" >&2
    exit 1
  fi
  just --justfile "$clone/Justfile" --working-directory "$clone" "$recipe"
done
