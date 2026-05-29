import E213.Meta.Algebra213.CDDoubleMoufang

/-!
# Octonion-analog alternativity for `CDDouble` of an associative base

Companion to `CDDoubleMoufang`.  For `CDDouble α` over a
`[TraceNormed213 α]` (hence associative) base, the algebra is
**alternative**: left/right alternative + flexible.  Only `cd_alt_left`
needs the hard component computation; `cd_alt_right` follows by the
`conj` anti-automorphism (involution), and `cd_flexible` by the standard
linearization (associator alternating in the first two arguments).

Each reduction uses the same two scalars as the Moufang norm proof:
`self_mul_conj`/`conj_mul_self` (norm central) and the trace polarization
`self_add_conj` (`a + conj a` central), plus base associativity.
-/

namespace E213.Meta.Algebra213

open Ring213 StarRing213 IntegerNormed213 TraceNormed213

variable {α : Type} [TraceNormed213 α]

/-- **Left alternativity** for `CDDouble α` (associative base):
    `(u·u)·v = u·(u·v)`. -/
theorem cd_alt_left (u v : CDDouble α) :
    (u * u) * v = u * (u * v) := by
  apply CDDouble.ext
  · show (u.re * u.re + -(conj u.im * u.im)) * v.re
         + -(conj v.im * (u.im * u.re + u.im * conj u.re))
       = u.re * (u.re * v.re + -(conj v.im * u.im))
         + -(conj (v.im * u.re + u.im * conj v.re) * u.im)
    have hN : -((conj u.im * u.im) * v.re) = -((v.re * conj u.im) * u.im) := by
      rw [conj_mul_self u.im, Ring213.mul_assoc v.re (conj u.im) u.im,
          conj_mul_self u.im, ofInt_central (normSq u.im) v.re]
    have hpair :
        -(conj v.im * (u.im * u.re)) + -(conj v.im * (u.im * conj u.re))
          = -(u.re * (conj v.im * u.im)) + -((conj u.re * conj v.im) * u.im) := by
      have hL : -(conj v.im * (u.im * u.re)) + -(conj v.im * (u.im * conj u.re))
              = -((ofInt (trace u.re) * conj v.im) * u.im) := by
        rw [← Ring213.neg_add,
            ← Ring213.mul_add (conj v.im) (u.im * u.re) (u.im * conj u.re),
            ← Ring213.mul_add u.im u.re (conj u.re), self_add_conj u.re,
            ← ofInt_central (trace u.re) u.im,
            ← Ring213.mul_assoc (conj v.im) (ofInt (trace u.re)) u.im,
            ← ofInt_central (trace u.re) (conj v.im)]
      have hR : -(u.re * (conj v.im * u.im)) + -((conj u.re * conj v.im) * u.im)
              = -((ofInt (trace u.re) * conj v.im) * u.im) := by
        rw [← Ring213.mul_assoc u.re (conj v.im) u.im, ← Ring213.neg_add,
            ← Ring213.add_mul (u.re * conj v.im) (conj u.re * conj v.im) u.im,
            ← Ring213.add_mul u.re (conj u.re) (conj v.im), self_add_conj u.re]
      rw [hL, hR]
    rw [Ring213.add_mul (u.re * u.re) (-(conj u.im * u.im)) v.re,
        Ring213.neg_mul (conj u.im * u.im) v.re,
        Ring213.mul_add (conj v.im) (u.im * u.re) (u.im * conj u.re),
        Ring213.neg_add (conj v.im * (u.im * u.re)) (conj v.im * (u.im * conj u.re)),
        Ring213.mul_add u.re (u.re * v.re) (-(conj v.im * u.im)),
        Ring213.mul_neg u.re (conj v.im * u.im),
        StarRing213.conj_add (v.im * u.re) (u.im * conj v.re),
        StarRing213.conj_mul v.im u.re,
        StarRing213.conj_mul u.im (conj v.re), StarRing213.conj_conj v.re,
        Ring213.add_mul (conj u.re * conj v.im) (v.re * conj u.im) u.im,
        Ring213.neg_add ((conj u.re * conj v.im) * u.im) ((v.re * conj u.im) * u.im),
        Ring213.mul_assoc u.re u.re v.re, hN, hpair,
        Ring213.add_4_swap_mid (u.re * (u.re * v.re)) (-((v.re * conj u.im) * u.im))
          (-(u.re * (conj v.im * u.im))) (-((conj u.re * conj v.im) * u.im)),
        Ring213.add_comm (-((v.re * conj u.im) * u.im)) (-((conj u.re * conj v.im) * u.im))]
  · show v.im * (u.re * u.re + -(conj u.im * u.im))
         + (u.im * u.re + u.im * conj u.re) * conj v.re
       = (v.im * u.re + u.im * conj v.re) * u.re
         + u.im * conj (u.re * v.re + -(conj v.im * u.im))
    have bcn : ∀ x : α, conj (-x) = -(conj x) :=
      fun x => NonAssocStarRing213.conj_neg x
    have hN_im : -(v.im * (conj u.im * u.im)) = -(u.im * (conj u.im * v.im)) := by
      rw [conj_mul_self u.im, ← Ring213.mul_assoc u.im (conj u.im) v.im,
          self_mul_conj u.im, ofInt_central (normSq u.im) v.im]
    have hpair_im :
        (u.im * u.re) * conj v.re + (u.im * conj u.re) * conj v.re
          = (u.im * conj v.re) * u.re + u.im * (conj v.re * conj u.re) := by
      have hL : (u.im * u.re) * conj v.re + (u.im * conj u.re) * conj v.re
              = (u.im * ofInt (trace u.re)) * conj v.re := by
        rw [← Ring213.add_mul (u.im * u.re) (u.im * conj u.re) (conj v.re),
            ← Ring213.mul_add u.im u.re (conj u.re), self_add_conj u.re]
      have hR : (u.im * conj v.re) * u.re + u.im * (conj v.re * conj u.re)
              = (u.im * ofInt (trace u.re)) * conj v.re := by
        rw [Ring213.mul_assoc u.im (conj v.re) u.re,
            ← Ring213.mul_add u.im (conj v.re * u.re) (conj v.re * conj u.re),
            ← Ring213.mul_add (conj v.re) u.re (conj u.re), self_add_conj u.re,
            ← ofInt_central (trace u.re) (conj v.re),
            ← Ring213.mul_assoc u.im (ofInt (trace u.re)) (conj v.re)]
      rw [hL, hR]
    rw [Ring213.mul_add v.im (u.re * u.re) (-(conj u.im * u.im)),
        Ring213.mul_neg v.im (conj u.im * u.im),
        Ring213.add_mul (u.im * u.re) (u.im * conj u.re) (conj v.re),
        Ring213.add_mul (v.im * u.re) (u.im * conj v.re) u.re,
        StarRing213.conj_add (u.re * v.re) (-(conj v.im * u.im)),
        StarRing213.conj_mul u.re v.re, bcn (conj v.im * u.im),
        StarRing213.conj_mul (conj v.im) u.im, StarRing213.conj_conj v.im,
        Ring213.mul_add u.im (conj v.re * conj u.re) (-(conj u.im * v.im)),
        Ring213.mul_neg u.im (conj u.im * v.im),
        ← Ring213.mul_assoc v.im u.re u.re, hN_im, hpair_im,
        Ring213.add_4_swap_mid (v.im * u.re * u.re) (-(u.im * (conj u.im * v.im)))
          (u.im * conj v.re * u.re) (u.im * (conj v.re * conj u.re)),
        Ring213.add_comm (-(u.im * (conj u.im * v.im)))
          (u.im * (conj v.re * conj u.re))]

/-- **Right alternativity** for `CDDouble α`: `x·(y·y) = (x·y)·y`.
    Follows from `cd_alt_left` by applying the `conj` anti-automorphism
    (`conj((u·u)·v)` reverses to the right-alternative shape) and
    `conj_conj`. -/
theorem cd_alt_right (x y : CDDouble α) : x * (y * y) = (x * y) * y := by
  have h := congrArg CDDouble.conj
    (cd_alt_left (CDDouble.conj y) (CDDouble.conj x))
  rw [cd_conj_mul, cd_conj_mul, cd_conj_mul, cd_conj_mul] at h
  have ccx : CDDouble.conj (CDDouble.conj x) = x := NonAssocStarRing213.conj_conj x
  have ccy : CDDouble.conj (CDDouble.conj y) = y := NonAssocStarRing213.conj_conj y
  rw [ccx, ccy] at h
  exact h

end E213.Meta.Algebra213
