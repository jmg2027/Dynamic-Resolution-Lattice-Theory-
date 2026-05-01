import E213.Physics.AlphaEM.Unified

set_option maxRecDepth 4096

/-!
# 1/α_em(IR) — bracket tightening at higher N

Strengthens AlphaEM137 from N=10 (width ~6) to higher N:

  N = 50:  bracket = [135.84, 137.04],  width 1.2
  N = 100: bracket = [136.43, 137.03+ε], width 0.6

The upper bracket converges to (10π² + 30 + 25/3) ≈ 137.029.
Observed 1/α_em ≈ 137.036 — the gap 0.007 is the α_GUT/(NS+1)
Dyson-tail term not in this five-term sum.
-/

namespace E213.Physics.AlphaEM137Tighter

open E213.Physics.AlphaEMUnified

/-- ★★★ 137 ∈ unified bracket at N=50 (width ~1.2). -/
theorem unified_137_in_at_50 :
    let lo := alpha_em_unified_lower 50
    let hi := alpha_em_unified_upper 50
    lo.1 < 137 * lo.2 ∧ 137 * hi.2 < hi.1 := by decide

/-- ★★★★ 137 ∈ unified bracket at N=100 (width ~0.6). -/
theorem unified_137_in_at_100 :
    let lo := alpha_em_unified_lower 100
    let hi := alpha_em_unified_upper 100
    lo.1 < 137 * lo.2 ∧ 137 * hi.2 < hi.1 := by decide

/-- 138 strictly excluded at N=100. -/
theorem upper_excludes_138_at_100 :
    let hi := alpha_em_unified_upper 100
    hi.1 < 138 * hi.2 := by decide

end E213.Physics.AlphaEM137Tighter
