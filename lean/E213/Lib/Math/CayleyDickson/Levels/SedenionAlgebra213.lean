import E213.Lib.Math.CayleyDickson.Levels.SedenionHeavy
import E213.Lib.Math.CayleyDickson.Levels.CayleyAlgebra213
import E213.Meta.Algebra213.Core
import E213.Meta.Algebra213.AlternativeNormed

/-!
# `Sedenion` (= CD-double of `Cayley`) NonAssocStarRing213 bridge

Sedenion (CD layer 3, 16-dim) sits one doubling above Cayley.  Its
base — `Cayley` — is already *non-associative* (alternative), so the
parametric `instNonAssocStarRing213CDDoubleStar [StarRing213 α]` of
`Meta/Algebra213/CDDoubleStar` cannot fire (it needs base
associativity, which Cayley lacks).  We therefore register
`NonAssocRing213 Sedenion` + `NonAssocStarRing213 Sedenion` by the
**manual componentwise route**, mirroring the `CayleyAlgebra213`
bridge but stated directly on the concrete `Sedenion` structure over
the `NonAssocStarRing213 Cayley` / `NonAssocRing213 Cayley` base.

The two anti-distributive star fields reuse the already-PURE
structural results in `SedenionHeavy`:
  * `conj_conj`     := `SedenionHeavy.conj_conj`
  * `conj_mul`      := `SedenionHeavy.conj_mul_anti`

Only the two distributive laws (`add_mul`, `mul_add`) carry the
genuine Cayley-Dickson content; both reduce — exactly as in the
generic `CDDoubleStar.add_mul'` / `mul_add'` — to base
`NonAssocRing213` add/distribute + the `add_4_swap_mid` reshuffle, no
multiplicative associativity required.

Once registered, `NonAssocStarRing213 Sedenion` unlocks the structural
(∅-axiom) `Trigintaduonion` anti-distributivity proof, replacing the
128-Int-var `hurwitz_ring` brute force — see
`TrigintaduoionionHeavy.conj_mul_anti`.
-/

namespace E213.Lib.Math.CayleyDickson.Levels.Sedenion

open E213.Meta.Algebra213
open E213.Lib.Math.CayleyDickson.Levels.Cayley

/-! ## §1 — Componentwise additive axioms (`NonAssocRing213 Cayley` base) -/

private theorem sed_add_assoc (u v w : Sedenion) : u + v + w = u + (v + w) := by
  apply Sedenion.ext
  · exact NonAssocRing213.add_assoc u.re v.re w.re
  · exact NonAssocRing213.add_assoc u.im v.im w.im

private theorem sed_add_comm (u v : Sedenion) : u + v = v + u := by
  apply Sedenion.ext
  · exact NonAssocRing213.add_comm u.re v.re
  · exact NonAssocRing213.add_comm u.im v.im

private theorem sed_add_zero (u : Sedenion) : u + 0 = u := by
  apply Sedenion.ext
  · exact NonAssocRing213.add_zero u.re
  · exact NonAssocRing213.add_zero u.im

private theorem sed_add_left_neg (u : Sedenion) : -u + u = 0 := by
  apply Sedenion.ext
  · exact NonAssocRing213.add_left_neg u.re
  · exact NonAssocRing213.add_left_neg u.im

/-! ## §2 — Distributive laws (CD content; no base associativity) -/

private theorem sed_add_mul (u v w : Sedenion) :
    (u + v) * w = u * w + v * w := by
  apply Sedenion.ext
  · show (u.re + v.re) * w.re + -(w.im.conj * (u.im + v.im))
       = (u.re * w.re + -(w.im.conj * u.im))
         + (v.re * w.re + -(w.im.conj * v.im))
    rw [NonAssocRing213.add_mul u.re v.re w.re,
        NonAssocRing213.mul_add w.im.conj u.im v.im,
        NonAssocRing213.neg_add (w.im.conj * u.im) (w.im.conj * v.im)]
    exact NonAssocRing213.add_4_swap_mid _ _ _ _
  · show w.im * (u.re + v.re) + (u.im + v.im) * w.re.conj
       = (w.im * u.re + u.im * w.re.conj)
         + (w.im * v.re + v.im * w.re.conj)
    rw [NonAssocRing213.mul_add w.im u.re v.re,
        NonAssocRing213.add_mul u.im v.im w.re.conj]
    exact NonAssocRing213.add_4_swap_mid _ _ _ _

private theorem sed_mul_add (u v w : Sedenion) :
    u * (v + w) = u * v + u * w := by
  apply Sedenion.ext
  · show u.re * (v.re + w.re) + -((v.im + w.im).conj * u.im)
       = (u.re * v.re + -(v.im.conj * u.im))
         + (u.re * w.re + -(w.im.conj * u.im))
    have hca : (v.im + w.im).conj = v.im.conj + w.im.conj :=
      NonAssocStarRing213.conj_add v.im w.im
    rw [hca, NonAssocRing213.mul_add u.re v.re w.re,
        NonAssocRing213.add_mul v.im.conj w.im.conj u.im,
        NonAssocRing213.neg_add (v.im.conj * u.im) (w.im.conj * u.im)]
    exact NonAssocRing213.add_4_swap_mid _ _ _ _
  · show (v.im + w.im) * u.re + u.im * (v.re + w.re).conj
       = (v.im * u.re + u.im * v.re.conj)
         + (w.im * u.re + u.im * w.re.conj)
    have hcb : (v.re + w.re).conj = v.re.conj + w.re.conj :=
      NonAssocStarRing213.conj_add v.re w.re
    rw [hcb, NonAssocRing213.add_mul v.im w.im u.re,
        NonAssocRing213.mul_add u.im v.re.conj w.re.conj]
    exact NonAssocRing213.add_4_swap_mid _ _ _ _

/-! ## §3 — Star anti-involution field (`conj_add` componentwise) -/

private theorem sed_conj_add (u v : Sedenion) :
    Sedenion.conj (u + v) = Sedenion.conj u + Sedenion.conj v := by
  apply Sedenion.ext
  · show (u.re + v.re).conj = u.re.conj + v.re.conj
    exact NonAssocStarRing213.conj_add u.re v.re
  · show -(u.im + v.im) = -u.im + -v.im
    exact NonAssocRing213.neg_add u.im v.im

/-! ## §4 — Instances -/

instance : NonAssocRing213 Sedenion where
  add_assoc    := sed_add_assoc
  add_comm     := sed_add_comm
  add_zero     := sed_add_zero
  add_left_neg := sed_add_left_neg
  add_mul      := sed_add_mul
  mul_add      := sed_mul_add

instance : NonAssocStarRing213 Sedenion where
  conj      := Sedenion.conj
  conj_conj := SedenionHeavy.conj_conj
  conj_add  := sed_conj_add
  conj_mul  := SedenionHeavy.conj_mul_anti

end E213.Lib.Math.CayleyDickson.Levels.Sedenion
