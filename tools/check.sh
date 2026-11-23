#!/usr/bin/env bash
# The release's checks, as its CI runs them. From the repository's root:
#
#   tools/check.sh
#
# Builds the library and the executable, which must build with no warning (a new warning
# is then easy to see), then runs, stopping at the first failure:
#   1. the axiom audit (tools/check-axioms.lean);
#   2. the examples (tools/check-examples.py);
#   3. the Markdown blueprint's links and known defects (tools/check-blueprint-md.py);
#   4. one version and date (tools/check-version.py; the PDF is checked at export).
# Needs Lean (elan) and Python 3.8 or later. Fetches nothing.
set -euo pipefail
cd "$(dirname "$0")/.."
t0=$SECONDS
run() { printf '\n== %s\n' "$1"; shift; "$@"; }
build() {
  local log; log=$(mktemp)
  lake build 2>&1 | tee "$log"
  [ "${PIPESTATUS[0]}" = 0 ] || { rm -f "$log"; return 1; }
  if grep -q '^warning:' "$log"; then
    echo "FAIL the build printed $(grep -c '^warning:' "$log") warnings; it must print none" >&2
    rm -f "$log"; return 1
  fi
  rm -f "$log"
}
run "lake build, with no warning" build
run "the axiom audit" lake env lean --run tools/check-axioms.lean
run "the examples" python3 tools/check-examples.py
run "the Markdown blueprint" python3 tools/check-blueprint-md.py blueprint --lean-dir . \
  --also README.md examples/README.md --list-external
run "one version" python3 tools/check-version.py
printf '\nAll checks passed in %ds.\n' $((SECONDS - t0))
