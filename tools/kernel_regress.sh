#!/bin/bash
# 213 Kernel regression: ensure all E213.Term.* theorems remain 0-axiom.
# Exit 0 = pure, exit 1 = regression detected.
set -euo pipefail

cd "$(dirname "$0")/../lean"

# Term ring targets (Raw representation + Tree internals + capstones if present).
# Cap_* targets were removed in a post-M14 cleanup; current Term/ has:
#   - 8 user-facing module files (Term, Compare, Pair, Rat, Decide, Sound,
#     Demo, MonomialAxioms)
#   - 5 Tree-internal files under Term/Internal/Tree/
#   - 2 umbrellas (API.lean, Tree.lean)
KERNEL_TARGETS=(
  E213.Term.API
  E213.Term.Term
  E213.Term.Compare
  E213.Term.Pair
  E213.Term.Rat
  E213.Term.Decide
  E213.Term.Sound
  E213.Term.Demo
  E213.Term.MonomialAxioms
  E213.Term.Tree
)

OUT=$(lake build --rehash "${KERNEL_TARGETS[@]}" 2>&1)

# Check for regression: any "Term.*depends on axioms" line is a regression.
# Use `if grep -q` form so a no-match (no regression) doesn't fire `set -e`.
if echo "$OUT" | grep -qE "info: .*Term.*depends on axioms"; then
  echo "❌ REGRESSION: kernel theorem with axiom dependency."
  echo ""
  echo "$OUT" | grep -E "info: .*Term.*depends on axioms"
  exit 1
fi

# Count PURE confirmations.  `grep -c` returns 1 if zero matches → `|| true`.
PURE=$(echo "$OUT" | grep -cE "info: .*Term.*does not depend on any axioms" || true)
echo "✅ Kernel pure: ${PURE} theorems verified 0-axiom across ${#KERNEL_TARGETS[@]} targets."
