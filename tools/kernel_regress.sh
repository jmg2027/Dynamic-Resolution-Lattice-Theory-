#!/bin/bash
# 213 Kernel regression: ensure all E213.Term.* theorems remain 0-axiom.
# Exit 0 = pure, exit 1 = regression detected.
set -euo pipefail

cd "$(dirname "$0")/../lean"

KERNEL_TARGETS=(
  E213.Term.Term
  E213.Term.Compare
  E213.Term.Pair
  E213.Term.Rat
  E213.Term.Decide
  E213.Term.Sound
  E213.Term.Demo
  E213.Term.Cap_PeriodicTable
  E213.Term.Cap_PhysicsBrackets
  E213.Term.Cap_PhysicsObservables
  E213.Term.Cap_PhysicsFalsifiers
  E213.Term.Cap_PhysicsAtomicIE
  E213.Term.Cap_AtomicComplexity
  E213.Term.Cap_MathArithmetic
)

OUT=$(lake build --rehash "${KERNEL_TARGETS[@]}" 2>&1)
echo "$OUT" | grep -E "info: .*Kernel.*depends on axioms" && {
  echo ""
  echo "❌ REGRESSION: kernel theorem with axiom dependency."
  exit 1
}

PURE=$(echo "$OUT" | grep -cE "info: .*Kernel.*does not depend on any axioms" || true)
echo "✅ Kernel pure: ${PURE} theorems verified 0-axiom."
