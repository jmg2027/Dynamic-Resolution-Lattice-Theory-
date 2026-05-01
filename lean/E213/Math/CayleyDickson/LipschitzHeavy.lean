import E213.Math.CayleyDickson.CDDouble
import E213.Math.IntHelpers
import E213.Tactic.HurwitzRing

/-!
# Research: Lipschitz "heavy" identities via `hurwitz_ring`

Identities too large for `quad_norm` alone, closed by the
new `hurwitz_ring` tactic which descends through
`Lipschitz.ext` and `ZI.ext` before invoking the polynomial
AC-normalisation + `omega`.
-/

namespace E213.Math.CayleyDickson.LipschitzHeavy

open E213.Tactic

/-- **Universal associativity** of Lipschitz multiplication.
    `(u·v)·w = u·(v·w)` — a 12-variable Int polynomial
    identity.  Closed by `hurwitz_ring`. -/
theorem mul_assoc (u v w : Lipschitz) :
    (u * v) * w = u * (v * w) := by hurwitz_ring

end E213.Math.CayleyDickson.LipschitzHeavy

namespace E213.Math.CayleyDickson.LipschitzHeavy

open E213.Tactic E213.Math.CayleyDickson.ZI

/-- **Hurwitz norm-multiplicativity** at Lipschitz level:
    `|u·v|² = |u|² · |v|²`.  8-variable Int polynomial
    identity with ~100 monomials per side.  Closed by
    `hurwitz_ring`. -/
theorem normSq_mul (u v : Lipschitz) :
    normSq (u * v) = normSq u * normSq v := by
  show (u * v).re.normSq + (u * v).im.normSq
     = (u.re.normSq + u.im.normSq) * (v.re.normSq + v.im.normSq)
  unfold ZI.normSq
  hurwitz_ring

end E213.Math.CayleyDickson.LipschitzHeavy

namespace E213.Math.CayleyDickson.LipschitzHeavy

open E213.Tactic E213.Math.CayleyDickson.ZI

/-- `Lipschitz.normSq u = 0 ↔ u = 0`.  Sum of 4 integer
    squares = 0 iff each square = 0. -/
theorem normSq_eq_zero_iff (u : Lipschitz) : normSq u = 0 ↔ u = 0 := by
  constructor
  · intro h
    show u = ⟨0, 0⟩
    apply ext
    · show u.re = (0 : ZI)
      apply ZI.ext
      · show u.re.re = 0
        have : u.re.re * u.re.re + u.re.im * u.re.im +
                (u.im.re * u.im.re + u.im.im * u.im.im) = 0 := h
        have h1 : 0 ≤ u.re.re * u.re.re := IntHelpers.mul_self_nonneg _
        have h2 : 0 ≤ u.re.im * u.re.im := IntHelpers.mul_self_nonneg _
        have h3 : 0 ≤ u.im.re * u.im.re := IntHelpers.mul_self_nonneg _
        have h4 : 0 ≤ u.im.im * u.im.im := IntHelpers.mul_self_nonneg _
        have hsq : u.re.re * u.re.re = 0 := by omega
        rcases Int.mul_eq_zero.mp hsq with h | h <;> exact h
      · show u.re.im = 0
        have : u.re.re * u.re.re + u.re.im * u.re.im +
                (u.im.re * u.im.re + u.im.im * u.im.im) = 0 := h
        have h1 : 0 ≤ u.re.re * u.re.re := IntHelpers.mul_self_nonneg _
        have h2 : 0 ≤ u.re.im * u.re.im := IntHelpers.mul_self_nonneg _
        have h3 : 0 ≤ u.im.re * u.im.re := IntHelpers.mul_self_nonneg _
        have h4 : 0 ≤ u.im.im * u.im.im := IntHelpers.mul_self_nonneg _
        have hsq : u.re.im * u.re.im = 0 := by omega
        rcases Int.mul_eq_zero.mp hsq with h | h <;> exact h
    · show u.im = (0 : ZI)
      apply ZI.ext
      · show u.im.re = 0
        have : u.re.re * u.re.re + u.re.im * u.re.im +
                (u.im.re * u.im.re + u.im.im * u.im.im) = 0 := h
        have h1 : 0 ≤ u.re.re * u.re.re := IntHelpers.mul_self_nonneg _
        have h2 : 0 ≤ u.re.im * u.re.im := IntHelpers.mul_self_nonneg _
        have h3 : 0 ≤ u.im.re * u.im.re := IntHelpers.mul_self_nonneg _
        have h4 : 0 ≤ u.im.im * u.im.im := IntHelpers.mul_self_nonneg _
        have hsq : u.im.re * u.im.re = 0 := by omega
        rcases Int.mul_eq_zero.mp hsq with h | h <;> exact h
      · show u.im.im = 0
        have : u.re.re * u.re.re + u.re.im * u.re.im +
                (u.im.re * u.im.re + u.im.im * u.im.im) = 0 := h
        have h1 : 0 ≤ u.re.re * u.re.re := IntHelpers.mul_self_nonneg _
        have h2 : 0 ≤ u.re.im * u.re.im := IntHelpers.mul_self_nonneg _
        have h3 : 0 ≤ u.im.re * u.im.re := IntHelpers.mul_self_nonneg _
        have h4 : 0 ≤ u.im.im * u.im.im := IntHelpers.mul_self_nonneg _
        have hsq : u.im.im * u.im.im = 0 := by omega
        rcases Int.mul_eq_zero.mp hsq with h | h <;> exact h
  · rintro rfl; rfl

end E213.Math.CayleyDickson.LipschitzHeavy

namespace E213.Math.CayleyDickson.LipschitzHeavy

open E213.Math.CayleyDickson.ZI

/-- **R3 at Lipschitz (= integer quaternions)**: no zero
    divisors.  Classical consequence of norm multiplicativity
    (Lipschitz integers are a subring of the quaternion
    division algebra).

    Proof: if `u·v = 0`, then `|uv|² = 0`, and by
    `normSq_mul`, `|u|² · |v|² = 0`, so one of them is 0.
    Then `normSq_eq_zero_iff` gives `u = 0` or `v = 0`. -/
theorem no_zero_div (u v : Lipschitz) :
    u * v = 0 → u = 0 ∨ v = 0 := by
  intro huv
  have hnorm : normSq (u * v) = 0 := by rw [huv]; rfl
  rw [normSq_mul] at hnorm
  rcases Int.mul_eq_zero.mp hnorm with h | h
  · left; exact (normSq_eq_zero_iff u).mp h
  · right; exact (normSq_eq_zero_iff v).mp h

end E213.Math.CayleyDickson.LipschitzHeavy
