import E213.Lib.Math.Algebra.CayleyDickson.Tower.CDDouble
import E213.Lib.Math.Algebra.CayleyDickson.Lipschitz.LipschitzAlgebra213
import E213.Meta.Nat.IntHelpers
import E213.Meta.Algebra213.Core
import E213.Meta.Int213.Core

/-!
# Lipschitz "heavy" identities — ∅-axiom via Algebra213 typeclass

Replaces the previous `hurwitz_ring`-based proofs (which expanded to
12-variable Int polynomials and timed out at higher CD layers).  The
generic `IntegerNormed213.normSq_mul` theorem at the abstract layer
auto-derives Hurwitz norm-multiplicativity for any instance — here
applied to Lipschitz.

mul_assoc is now a one-line typeclass projection through
`Ring213.mul_assoc`.  normSq_mul through `IntegerNormed213.normSq_mul`.
no_zero_div uses `Int213.mul_eq_zero` (PURE) to avoid Lean-core
`Int.mul_eq_zero.mp` (propext).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Lipschitz.LipschitzHeavy


open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI.ZI
open E213.Lib.Math.Algebra.CayleyDickson.Tower.CDDouble
open E213.Lib.Math.Algebra.CayleyDickson.Tower.CDDouble.Lipschitz
open E213.Meta.Algebra213

/-- ★ **Universal associativity** of Lipschitz multiplication.
    `(u·v)·w = u·(v·w)`.  ∅-axiom — typeclass projection through
    `Ring213.mul_assoc`, derived in `LipschitzAlgebra213` from ZI
    ring axioms (no Int polynomial expansion). -/
theorem mul_assoc (u v w : Lipschitz) :
    (u * v) * w = u * (v * w) :=
  Ring213.mul_assoc u v w

/-- ★ **Hurwitz norm-multiplicativity** at Lipschitz level:
    `|u·v|² = |u|² · |v|²`.  ∅-axiom — typeclass projection through
    `IntegerNormed213.normSq_mul`, the generic Hurwitz theorem proved
    once at the abstract layer using only ring algebra. -/
theorem normSq_mul (u v : Lipschitz) :
    normSq (u * v) = normSq u * normSq v :=
  IntegerNormed213.normSq_mul u v

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI

/-- `Lipschitz.normSq u = 0 ↔ u = 0`.  Sum of 4 integer
    squares = 0 iff each square = 0.

    ∅-axiom: cascade of `Int213.add_eq_zero_of_nonneg` (sum of
    nonnegatives = 0 → both = 0) + `IntHelpers.mul_self_eq_zero`. -/
theorem normSq_eq_zero_iff (u : Lipschitz) : normSq u = 0 ↔ u = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h_eq : u.re.normSq + u.im.normSq = 0 := h
    have h1 : 0 ≤ u.re.normSq := ZI.normSq_nonneg u.re
    have h2 : 0 ≤ u.im.normSq := ZI.normSq_nonneg u.im
    obtain ⟨hre, him⟩ :=
      E213.Meta.Int213.add_eq_zero_of_nonneg h1 h2 h_eq
    apply Lipschitz.ext
    · exact (ZI.normSq_eq_zero_iff u.re).mp hre
    · exact (ZI.normSq_eq_zero_iff u.im).mp him
  · rintro rfl; rfl

/-- ★ **R3 at Lipschitz** (= integer quaternions): no zero divisors.

    ∅-axiom: `normSq_mul` + `Int213.mul_eq_zero` (forward direction
    only, no Iff projection) + `normSq_eq_zero_iff`. -/
theorem no_zero_div (u v : Lipschitz) :
    u * v = 0 → u = 0 ∨ v = 0 := by
  intro huv
  have hnorm : normSq (u * v) = 0 := by rw [huv]; rfl
  rw [normSq_mul] at hnorm
  rcases E213.Meta.Int213.mul_eq_zero hnorm with h | h
  · left; exact (normSq_eq_zero_iff u).mp h
  · right; exact (normSq_eq_zero_iff v).mp h

end E213.Lib.Math.Algebra.CayleyDickson.Lipschitz.LipschitzHeavy
