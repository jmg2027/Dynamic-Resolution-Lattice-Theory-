import E213.Research.Trigintaduonion
import E213.Research.SedenionHeavy
import E213.Tactic.HurwitzRing

/-!
# Research: Trigintaduonion "heavy" identities

Testing `hurwitz_ring` at CD layer 4 (32-dim, 64 Int coords).
-/

namespace E213.Research.Trigintaduonion

open E213.Tactic

set_option maxHeartbeats 8000000 in
/-- Involutivity of conjugation at layer 4 — 1-var, 64 Int
    coords.  Stress test. -/
theorem conj_conj (u : Trigintaduonion) : conj (conj u) = u := by
  hurwitz_ring

end E213.Research.Trigintaduonion

namespace E213.Research.Trigintaduonion

open E213.Tactic

set_option maxHeartbeats 32000000 in
/-- Anti-distributivity at layer 4: `conj(u·v) = conj(v) · conj(u)`.
    128 Int vars, 2-factor polynomial.  Ambitious stress test. -/
theorem conj_mul_anti (u v : Trigintaduonion) :
    conj (u * v) = conj v * conj u := by
  hurwitz_ring

end E213.Research.Trigintaduonion
