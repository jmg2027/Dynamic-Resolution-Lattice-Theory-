#!/bin/bash
# 213 full build — COMPREHENSIVE gate over every E213 module.
#
# `lake build E213` (the default target driven by `E213.lean`) only
# exercises the framework rings (Term / Theory / Lens / Meta +
# Pigeonhole) — fast, for iteration.  `lake build E213.Lib.Math
# E213.Lib.Physics` adds the two content-umbrella closures.  But neither
# is a complete gate: modules not transitively imported from those roots
# ("orphans") are never compiled, so latent breakage hides (see
# research-notes/G159).
#
# This script builds EVERY module under lean/E213, so no orphan escapes.
# Use it as the build gate after any refactor.
#
# Exit 0 = clean; non-zero = build failure (see output).

set -euo pipefail

cd "$(dirname "$0")/../lean"

echo "===> Building E213 (framework rings)..."
lake build E213

echo ""
echo "===> Building ALL E213 modules (comprehensive — no orphan escapes)..."
mods=$(find E213 -name '*.lean' | sed 's|\.lean$||; s|/|.|g')
lake build $mods

echo ""
echo "✓ Full build clean — all $(echo "$mods" | wc -l) modules."
