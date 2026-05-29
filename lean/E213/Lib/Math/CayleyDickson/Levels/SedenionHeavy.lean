import E213.Lib.Math.CayleyDickson.Levels.Sedenion
import E213.Lib.Math.CayleyDickson.Lipschitz.LipschitzAlgebra213
import E213.Meta.Nat.IntHelpers
import E213.Lib.Math.CayleyDickson.Levels.CayleyHeavy
import E213.Lib.Math.Tactic.HurwitzRing
import E213.Meta.Algebra213.Core
import E213.Meta.Algebra213.AlternativeNormed

/-!
# Sedenion "heavy" identities

`conj_conj` migrated to ∅-axiom via Ring213.neg_neg cascade.
`flexible` / `conj_mul_anti` still use hurwitz_ring (DIRTY) — would
need Cayley alternative ring algebra to avoid Int polynomial.
-/

namespace E213.Lib.Math.CayleyDickson.Levels.SedenionHeavy


open E213.Lib.Math.CayleyDickson.Integer.ZI
open E213.Lib.Math.CayleyDickson.Integer.ZI.ZI
open E213.Lib.Math.CayleyDickson.Levels.Sedenion
open E213.Lib.Math.CayleyDickson.Levels.Sedenion.Sedenion
open E213.Lib.Math.CayleyDickson.Levels.CayleyHeavy
open E213.Meta.Algebra213
open E213.Tactic E213.Lib.Math.CayleyDickson.Levels.Cayley E213.Lib.Math.CayleyDickson.Tower.CDDouble.Lipschitz

/-- ∅-axiom Cayley `neg_neg` via Lipschitz Ring213 projection. -/
private theorem cayley_neg_neg (u : E213.Lib.Math.CayleyDickson.Levels.Cayley.Cayley) :
    -(-u) = u := by
  apply E213.Lib.Math.CayleyDickson.Levels.Cayley.Cayley.ext
  · show -(-u.re) = u.re; exact Ring213.neg_neg u.re
  · show -(-u.im) = u.im; exact Ring213.neg_neg u.im

/-- ★ ∅-axiom Sedenion conjugation involutive via Cayley cascade. -/
theorem conj_conj (u : Sedenion) : conj (conj u) = u := by
  apply Sedenion.ext
  · show u.re.conj.conj = u.re
    exact E213.Lib.Math.CayleyDickson.Levels.Cayley.conj_conj u.re
  · show -(-u.im) = u.im
    exact cayley_neg_neg u.im

open E213.Tactic

set_option maxHeartbeats 8000000 in
/-- **Sedenion flexibility** — DIRTY (32 Int vars). -/
theorem flexible (a b : Sedenion) : (a * b) * a = a * (b * a) := by
  hurwitz_ring

/-- **Sedenion anti-distributivity of conj**: `conj(u·v) = conj v·conj u`.
    Strict ∅-axiom — componentwise over the Cayley base using the
    generic `NonAssocStarRing213` / `NonAssocRing213` algebra (the proof
    needs no base associativity), replacing the 32-Int-var `hurwitz_ring`
    brute force. -/
theorem conj_mul_anti (u v : Sedenion) :
    conj (u * v) = conj v * conj u := by
  have cm : ∀ a b : Cayley, Cayley.conj (a * b) = Cayley.conj b * Cayley.conj a :=
    fun a b => NonAssocStarRing213.conj_mul a b
  have ca : ∀ a b : Cayley, Cayley.conj (a + b) = Cayley.conj a + Cayley.conj b :=
    fun a b => NonAssocStarRing213.conj_add a b
  have cc : ∀ a : Cayley, Cayley.conj (Cayley.conj a) = a :=
    fun a => NonAssocStarRing213.conj_conj a
  have cn : ∀ a : Cayley, Cayley.conj (-a) = -(Cayley.conj a) :=
    fun a => NonAssocStarRing213.conj_neg a
  have nm : ∀ a b : Cayley, (-a) * b = -(a * b) :=
    fun a b => NonAssocRing213.neg_mul a b
  have mn : ∀ a b : Cayley, a * (-b) = -(a * b) :=
    fun a b => NonAssocRing213.mul_neg a b
  have nn : ∀ a : Cayley, -(-a) = a := fun a => NonAssocRing213.neg_neg a
  have na : ∀ a b : Cayley, -(a + b) = -a + -b :=
    fun a b => NonAssocRing213.neg_add a b
  have ac : ∀ a b : Cayley, a + b = b + a := fun a b => NonAssocRing213.add_comm a b
  apply Sedenion.ext
  · show Cayley.conj (u.re * v.re + -(v.im.conj * u.im))
       = v.re.conj * u.re.conj + -((-u.im).conj * -v.im)
    rw [ca (u.re * v.re) (-(v.im.conj * u.im)), cm u.re v.re]
    have h_left : Cayley.conj (-(v.im.conj * u.im)) = -(u.im.conj * v.im) := by
      rw [cn (v.im.conj * u.im), cm (v.im.conj) u.im, cc v.im]
    have h_right : -((-u.im).conj * -v.im) = -(u.im.conj * v.im) := by
      rw [cn u.im, nm (u.im.conj) (-v.im), nn, mn (u.im.conj) v.im]
    rw [h_left, h_right]
  · show -(v.im * u.re + u.im * v.re.conj)
       = (-u.im) * v.re.conj + (-v.im) * (u.re.conj).conj
    rw [cc u.re, nm u.im (v.re.conj), nm v.im u.re,
        na (v.im * u.re) (u.im * v.re.conj),
        ac (-(v.im * u.re)) (-(u.im * v.re.conj))]

open E213.Lib.Math.CayleyDickson.Levels.Cayley E213.Lib.Math.CayleyDickson.Tower.CDDouble.Lipschitz

def normSq (u : Sedenion) : Int :=
  E213.Lib.Math.CayleyDickson.Levels.CayleyHeavy.normSq u.re
    + E213.Lib.Math.CayleyDickson.Levels.CayleyHeavy.normSq u.im

theorem normSq_zd_left_ne_zero : normSq zd_left ≠ 0 := by decide
theorem normSq_zd_right_ne_zero : normSq zd_right ≠ 0 := by decide

theorem normSq_zero : normSq (0 : Sedenion) = 0 := by
  show E213.Lib.Math.CayleyDickson.Levels.CayleyHeavy.normSq (0 : Cayley)
       + E213.Lib.Math.CayleyDickson.Levels.CayleyHeavy.normSq (0 : Cayley) = 0
  decide

/-- Norm multiplicativity FAILS at Sedenion (witnesses zero divisors). -/
theorem normSq_mul_fails :
    ∃ u v : Sedenion, normSq (u * v) ≠ normSq u * normSq v := by
  refine ⟨zd_left, zd_right, ?_⟩
  rw [zd_product_zero, normSq_zero]
  decide

end E213.Lib.Math.CayleyDickson.Levels.SedenionHeavy
