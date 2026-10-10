#!/usr/bin/env bash
# Builds the linter and the fixtures, runs every check on the fixtures, and compares the
# (check, declaration) pairs with test/expected.tsv. Exits non-zero on any difference.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build lean-linter LeanLinterTest > /dev/null
actual=$(lake env .lake/build/bin/lean-linter LeanLinterTest 2> /dev/null | cut -f1,2 || true)
if diff <(echo "$actual") test/expected.tsv; then
  echo "ok: $(wc -l < test/expected.tsv | tr -d ' ') findings, as expected"
else
  echo "FAIL: findings differ from test/expected.tsv (< actual, > expected)" >&2
  exit 1
fi
