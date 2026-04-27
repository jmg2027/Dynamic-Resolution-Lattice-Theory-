#!/bin/bash
# 213 Kernel regression: ensure all E213.Kernel.* theorems remain 0-axiom.
# Exit 0 = pure, exit 1 = regression detected.
set -euo pipefail

cd "$(dirname "$0")/../lean"

KERNEL_TARGETS=(
  E213.Kernel.Term
  E213.Kernel.Compare
  E213.Kernel.Pair
  E213.Kernel.Rat
  E213.Kernel.Decide
  E213.Kernel.Sound
  E213.Kernel.Demo
  E213.Kernel.Cap_PeriodicTable
  E213.Kernel.Cap_PhysicsBrackets
)

OUT=$(lake build --rehash "${KERNEL_TARGETS[@]}" 2>&1)
echo "$OUT" | grep -E "info: .*Kernel.*depends on axioms" && {
  echo ""
  echo "❌ REGRESSION: kernel theorem with axiom dependency."
  exit 1
}

PURE=$(echo "$OUT" | grep -cE "info: .*Kernel.*does not depend on any axioms" || true)
echo "✅ Kernel pure: ${PURE} theorems verified 0-axiom."
