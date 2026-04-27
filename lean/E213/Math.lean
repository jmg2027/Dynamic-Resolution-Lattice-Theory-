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

모두 build 성공, 0 sorry, ≤ propext + Quot.sound (Lean 4 core only).

연 구 단 계 (incomplete proofs 또 는 scaffolding) modules 도 import —
"library" status 는 doc-string 의 명 시.

User directives 의 working evidence:
- "213 만 의 실수" → Real213 (Foundation)
- "Generic 으 로 213 스럽 게" → Generic + CutOps
- "라 이 브 러 리 화" → 이 namespace structure
- "Real = Lens output" → AsLensOutput (Analysis)
- "transcendental Lens" → RecurrenceLens (Analysis)
-/
