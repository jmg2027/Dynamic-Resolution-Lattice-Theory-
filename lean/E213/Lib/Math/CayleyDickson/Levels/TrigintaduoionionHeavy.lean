import E213.Lib.Math.CayleyDickson.Levels.Trigintaduonion
import E213.Lib.Math.CayleyDickson.Levels.SedenionHeavy
import E213.Lib.Math.CayleyDickson.Levels.SedenionAlgebra213
import E213.Lib.Math.CayleyDickson.Lipschitz.LipschitzAlgebra213
import E213.Meta.Algebra213.Core
import E213.Meta.Algebra213.AlternativeNormed

/-!
# Trigintaduonion "heavy" identities

`conj_conj` migrated to ∅-axiom via Ring213.neg_neg cascade
(Lipschitz Ring213 instance + componentwise structural
recursion through Cayley → Sedenion → Trigintaduonion).

`conj_mul_anti` is now **strict ∅-axiom**: the componentwise
structural proof over the `NonAssocStarRing213 Sedenion` base
(`SedenionAlgebra213`) — verbatim analog of
`SedenionHeavy.conj_mul_anti` one layer up — replacing the
128-Int-var `hurwitz_ring` brute force.
-/

namespace E213.Lib.Math.CayleyDickson.Levels.TrigintaduoionionHeavy


open E213.Lib.Math.CayleyDickson.Integer.ZI
open E213.Lib.Math.CayleyDickson.Integer.ZI.ZI
open E213.Lib.Math.CayleyDickson.Levels.Trigintaduonion
open E213.Lib.Math.CayleyDickson.Levels.Trigintaduonion.Trigintaduonion
open E213.Lib.Math.CayleyDickson.Levels.Sedenion
open E213.Lib.Math.CayleyDickson.Levels.Sedenion.Sedenion
open E213.Lib.Math.CayleyDickson.Levels.Cayley
open E213.Lib.Math.CayleyDickson.Tower.CDDouble
open E213.Lib.Math.CayleyDickson.Tower.CDDouble.Lipschitz
open E213.Meta.Algebra213
open E213.Tactic

/-- ∅-axiom Cayley `neg_neg` via Lipschitz Ring213. -/
private theorem cayley_neg_neg (u : E213.Lib.Math.CayleyDickson.Levels.Cayley.Cayley) :
    -(-u) = u := by
  apply E213.Lib.Math.CayleyDickson.Levels.Cayley.Cayley.ext
  · show -(-u.re) = u.re; exact Ring213.neg_neg u.re
  · show -(-u.im) = u.im; exact Ring213.neg_neg u.im

/-- ∅-axiom Sedenion `neg_neg` via Cayley. -/
private theorem sedenion_neg_neg
    (u : E213.Lib.Math.CayleyDickson.Levels.Sedenion.Sedenion) :
    -(-u) = u := by
  apply E213.Lib.Math.CayleyDickson.Levels.Sedenion.Sedenion.ext
  · show -(-u.re) = u.re; exact cayley_neg_neg u.re
  · show -(-u.im) = u.im; exact cayley_neg_neg u.im

/-- ★ ∅-axiom Trigintaduonion conjugation involutive via Sedenion cascade. -/
theorem conj_conj (u : Trigintaduonion) : conj (conj u) = u := by
  apply Trigintaduonion.ext
  · show u.re.conj.conj = u.re
    exact E213.Lib.Math.CayleyDickson.Levels.SedenionHeavy.conj_conj u.re
  · show -(-u.im) = u.im
    exact sedenion_neg_neg u.im

/-- **Trigintaduonion anti-distributivity of conj**:
    `conj(u·v) = conj v·conj u`.  Strict ∅-axiom — componentwise
    over the `Sedenion` base using the generic
    `NonAssocStarRing213` / `NonAssocRing213` algebra (no base
    associativity needed), the verbatim analog of
    `SedenionHeavy.conj_mul_anti`, replacing the 128-Int-var
    `hurwitz_ring` brute force. -/
theorem conj_mul_anti (u v : Trigintaduonion) :
    conj (u * v) = conj v * conj u := by
  have cm : ∀ a b : Sedenion, Sedenion.conj (a * b) = Sedenion.conj b * Sedenion.conj a :=
    fun a b => NonAssocStarRing213.conj_mul a b
  have ca : ∀ a b : Sedenion, Sedenion.conj (a + b) = Sedenion.conj a + Sedenion.conj b :=
    fun a b => NonAssocStarRing213.conj_add a b
  have cc : ∀ a : Sedenion, Sedenion.conj (Sedenion.conj a) = a :=
    fun a => NonAssocStarRing213.conj_conj a
  have cn : ∀ a : Sedenion, Sedenion.conj (-a) = -(Sedenion.conj a) :=
    fun a => NonAssocStarRing213.conj_neg a
  have nm : ∀ a b : Sedenion, (-a) * b = -(a * b) :=
    fun a b => NonAssocRing213.neg_mul a b
  have mn : ∀ a b : Sedenion, a * (-b) = -(a * b) :=
    fun a b => NonAssocRing213.mul_neg a b
  have nn : ∀ a : Sedenion, -(-a) = a := fun a => NonAssocRing213.neg_neg a
  have na : ∀ a b : Sedenion, -(a + b) = -a + -b :=
    fun a b => NonAssocRing213.neg_add a b
  have ac : ∀ a b : Sedenion, a + b = b + a := fun a b => NonAssocRing213.add_comm a b
  apply Trigintaduonion.ext
  · show Sedenion.conj (u.re * v.re + -(v.im.conj * u.im))
       = v.re.conj * u.re.conj + -((-u.im).conj * -v.im)
    rw [ca (u.re * v.re) (-(v.im.conj * u.im)), cm u.re v.re]
    have h_left : Sedenion.conj (-(v.im.conj * u.im)) = -(u.im.conj * v.im) := by
      rw [cn (v.im.conj * u.im), cm (v.im.conj) u.im, cc v.im]
    have h_right : -((-u.im).conj * -v.im) = -(u.im.conj * v.im) := by
      rw [cn u.im, nm (u.im.conj) (-v.im), nn, mn (u.im.conj) v.im]
    rw [h_left, h_right]
  · show -(v.im * u.re + u.im * v.re.conj)
       = (-u.im) * v.re.conj + (-v.im) * (u.re.conj).conj
    rw [cc u.re, nm u.im (v.re.conj), nm v.im u.re,
        na (v.im * u.re) (u.im * v.re.conj),
        ac (-(v.im * u.re)) (-(u.im * v.re.conj))]

end E213.Lib.Math.CayleyDickson.Levels.TrigintaduoionionHeavy
