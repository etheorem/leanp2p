#!/usr/bin/env bash
# The W5.8 live gate. Python owns deadlines and process cleanup.
set -euo pipefail
root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
exec python3 "$root/scripts/ping-interop.py" "$@"
