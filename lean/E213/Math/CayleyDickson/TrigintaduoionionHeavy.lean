import E213.Math.CayleyDickson.Trigintaduonion
import E213.Math.CayleyDickson.SedenionHeavy
import E213.Math.Tactic.HurwitzRing

/-!
# Research: Trigintaduonion "heavy" identities

Testing `hurwitz_ring` at CD layer 4 (32-dim, 64 Int coords).
-/

namespace E213.Math.CayleyDickson.TrigintaduoionionHeavy


open E213.Math.CayleyDickson.ZI
open E213.Math.CayleyDickson.ZI.ZI
open E213.Tactic

set_option maxHeartbeats 8000000 in
/-- Involutivity of conjugation at layer 4 — 1-var, 64 Int
    coords.  Stress test. -/
theorem conj_conj (u : Trigintaduonion) : conj (conj u) = u := by
  hurwitz_ring

open E213.Tactic

set_option maxHeartbeats 32000000 in
/-- Anti-distributivity at layer 4: `conj(u·v) = conj(v) · conj(u)`.
    128 Int vars, 2-factor polynomial.  Ambitious stress test. -/
theorem conj_mul_anti (u v : Trigintaduonion) :
    conj (u * v) = conj v * conj u := by
  hurwitz_ring

end E213.Math.CayleyDickson.TrigintaduoionionHeavy

/-
**Trigintaduonion flexibility** `(a·b)·a = a·(b·a)` is a
128-Int-var 3-factor polynomial identity.  Attempted with
`set_option maxHeartbeats 128000000` but ~12 minutes of CPU
did not complete — at or past the `hurwitz_ring` + omega
practical ceiling.  Classically flexibility holds at all CD
layers (consequence of CD structure); obstruction here is
tactic cost, not truth.  Deferred.
-/
