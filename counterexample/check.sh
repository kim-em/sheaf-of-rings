#!/usr/bin/env bash
# Build the Isabelle development against a stock Isabelle and a stock AFP.
#
#   ./counterexample/check.sh                 # AFP already registered as a component
#   AFP=/path/to/afp/thys ./counterexample/check.sh
#   ISABELLE=/path/to/Isabelle2026/bin/isabelle AFP=... ./counterexample/check.sh
set -euo pipefail
dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
isabelle_bin=${ISABELLE:-isabelle}
afp_args=()
if [[ -n "${AFP:-}" ]]; then
  afp_args=(-d "$AFP")
fi
audit=$(mktemp)
trap 'rm -f "$audit"' EXIT
SCHEMES_AUDIT_FILE=$audit "$isabelle_bin" build -v "${afp_args[@]}" -D "$dir"
cat "$audit"
