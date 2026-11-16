#!/usr/bin/env bash
# Apply repair.patch to a copy of the stock AFP entry Grothendieck_Schemes, rebuild the
# whole entry, and check that the repaired sheaf predicate gives gluing over families
# indexed by an arbitrary type.
#
#   AFP=/path/to/afp/thys ./repair/check.sh
set -euo pipefail
dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
isabelle_bin=${ISABELLE:-isabelle}
: "${AFP:?Set AFP to the thys directory of the AFP release}"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
entry=$work/Grothendieck_Schemes_Repaired
cp -r "$AFP/Grothendieck_Schemes" "$entry"
patch -d "$entry" -p1 < "$dir/repair.patch"
sed -i 's/^session "\{0,1\}Grothendieck_Schemes"\{0,1\} = /session Grothendieck_Schemes_Repaired = /' "$entry/ROOT"
grep -q '^session Grothendieck_Schemes_Repaired = ' "$entry/ROOT"
"$isabelle_bin" build -v -d "$AFP" -d "$entry" -D "$dir"
