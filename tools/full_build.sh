#!/bin/bash
# 213 full build — framework rings + Lib content libraries.
#
# `lake build E213` (the default target driven by `E213.lean`)
# only exercises the framework rings (Term / Theory / Lens / Meta
# + Pigeonhole).  Lib/Math + Lib/Physics are excluded by design
# (large dependency closures, slow build) and consumers import the
# specific sub-modules they need.  This script does the explicit
# Lib build so refactor regressions are caught BEFORE they bite a
# downstream consumer.
#
# Use after any refactor touching Meta tactics, Real213, List213,
# or any framework symbol that Lib depends on transitively.
#
# Exit 0 = clean; non-zero = build failure (see output).

set -euo pipefail

cd "$(dirname "$0")/../lean"

echo "===> Building E213 (framework rings)..."
lake build E213

echo ""
echo "===> Building E213.Lib.Math + E213.Lib.Physics (content)..."
lake build E213.Lib.Math E213.Lib.Physics

echo ""
echo "✓ Full build clean (framework + Lib)."
