#!/usr/bin/env bash
set -euo pipefail
audit_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
# Optionally reuse an existing Mathlib checkout at the pinned revision.
if [[ $# -gt 0 ]]; then
  cd -- "$1"
  expected_rev=56a005855ea17e0b0958f73ec801ae140b0a1679
  if [[ $(git rev-parse HEAD) != "$expected_rev" ]]; then
    echo "Expected Mathlib revision $expected_rev" >&2
    exit 1
  fi
  exec lake env lean "$audit_dir/Counterexample.lean"
fi
cd -- "$audit_dir"
exec lake build
