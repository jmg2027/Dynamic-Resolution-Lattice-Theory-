import E213.Math.Foundation
import E213.Math.CutOps
import E213.Math.Generic
import E213.Math.Continuity
import E213.Math.Cauchy
import E213.Math.Series
import E213.Math.Analysis

/-!
# E213.Math: 213-native real analysis library (root entry)

Library structure with namespace separation.

## Sub-modules

- **Foundation**: Real213 type-level (Phase A).
- **CutOps**: cut-level rational arithmetic (Sum/Mul/MaxMin/Inv/Pow/...).
- **Generic**: cutBinary universal kernel + CutBinaryOp.
- **Continuity**: locally-determined + categorical closure.
- **Cauchy**: completeness via direct construction.
- **Series**: partialSum + geometric/exp/trig/π specific series.
- **Analysis**: IVT bisection / differentiation / Riemann (scaffolded).

## Status

All build successfully, 0 sorry, ≤ propext + Quot.sound (Lean 4 core
only).

Research-stage modules (incomplete proofs or scaffolding) are also
imported — "library" status is stated explicitly in each doc-string.

Working evidence for user directives:
- "reals native to 213" → Real213 (Foundation)
- "213-style via Generic" → Generic + CutOps
- "make it a library" → this namespace structure
- "Real = Lens output" → AsLensOutput (Analysis)
- "transcendental Lens" → RecurrenceLens (Analysis)
-/
