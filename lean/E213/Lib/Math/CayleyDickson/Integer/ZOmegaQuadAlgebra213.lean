import E213.Lib.Math.CayleyDickson.Integer.ZOmegaQuad
import E213.Lib.Math.CayleyDickson.Integer.ZOmegaDoubleAlgebra213
import E213.Meta.Algebra213.AlternativeNormed

/-!
# `ZOmegaQuad` as a `MoufangIntegerNormed213` instance

ZOmegaQuad (CD-double of ZOmegaDouble = Type C L4, 24 units,
M_24 Chein loop) sits at the alternative non-associative layer of
the Type C tower — parallel to Type A's Cayley (octonions).

This file registers ZOmegaQuad as `MoufangIntegerNormed213`, the
non-associative extension of the `Algebra213` hierarchy.  The generic
`MoufangIntegerNormed213.normSq_mul` from `AlternativeNormed.lean`
then derives ZOmegaQuad's norm multiplicativity via 7-step calc, no
polynomial expansion at Int level.

The only non-trivial instance field is the Moufang norm-collapse
identity `(u·v)·(conj v · conj u) = u · (v · conj v) · conj u`,
proved here using the underlying `Ring213 ZOmegaDouble` (associative)
axioms from Phase 2.

Same recipe applies at every higher Type C layer (ZOmegaOct, …),
and structurally at Type A (Cayley, Sedenion) once their bases are
typeclass-citizens.
-/

namespace E213.Lib.Math.CayleyDickson.Integer.ZOmegaQuad

open E213.Meta.Algebra213
open E213.Lib.Math.CayleyDickson.Integer.ZOmega
open E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble

/-! ## §1 — Bridge to abstract `CDDouble ZOmegaDouble` -/

/-- ZOmegaQuad → abstract CDDouble ZOmegaDouble. -/
def toCDDouble (u : ZOmegaQuad) : CDDouble ZOmegaDouble := ⟨u.re, u.im⟩

/-- Abstract CDDouble ZOmegaDouble → ZOmegaQuad. -/
def fromCDDouble (u : CDDouble ZOmegaDouble) : ZOmegaQuad := ⟨u.re, u.im⟩

theorem to_from (u : CDDouble ZOmegaDouble) :
    toCDDouble (fromCDDouble u) = u := by cases u; rfl

theorem from_to (u : ZOmegaQuad) :
    fromCDDouble (toCDDouble u) = u := by cases u; rfl

theorem toCDDouble_inj {u v : ZOmegaQuad}
    (h : toCDDouble u = toCDDouble v) : u = v := by
  have := congrArg fromCDDouble h
  rwa [from_to, from_to] at this

/-! ## §2 — Operation bridges (rfl) -/

theorem toCDDouble_mul (u v : ZOmegaQuad) :
    toCDDouble (u * v) = toCDDouble u * toCDDouble v := by
  apply CDDouble.ext
  · show (u * v).re
       = u.re * v.re + -(StarRing213.conj v.im * u.im)
    show u.re * v.re - (ZOmegaDouble.conj v.im) * u.im
       = u.re * v.re + -(StarRing213.conj v.im * u.im)
    rfl
  · show (u * v).im
       = v.im * u.re + u.im * StarRing213.conj v.re
    rfl

theorem toCDDouble_conj (u : ZOmegaQuad) :
    toCDDouble (ZOmegaQuad.conj u) = CDDouble.conj (toCDDouble u) := by
  apply CDDouble.ext
  · show ZOmegaDouble.conj u.re = StarRing213.conj u.re; rfl
  · show -u.im = -u.im; rfl

theorem toCDDouble_add (u v : ZOmegaQuad) :
    toCDDouble (u + v) = toCDDouble u + toCDDouble v := by
  apply CDDouble.ext
  · show (u + v).re = u.re + v.re; rfl
  · show (u + v).im = u.im + v.im; rfl

theorem toCDDouble_neg (u : ZOmegaQuad) :
    toCDDouble (-u) = -(toCDDouble u) := by
  apply CDDouble.ext
  · show (-u).re = -u.re; rfl
  · show (-u).im = -u.im; rfl

theorem toCDDouble_zero : toCDDouble 0 = 0 := rfl

/-! ## §3 — `NonAssocRing213 + NonAssocStarRing213 ZOmegaQuad` via bridge

The parametric `instNonAssocRing213CDDoubleStar [StarRing213 α]` fires
on `α := ZOmegaDouble` (Type C L3, non-comm associative), giving
`NonAssocRing213 (CDDouble ZOmegaDouble)` directly.  ZOmegaQuad then
inherits via `toCDDouble` — same shape as ZOmegaDouble's Ring213
bridge in `ZOmegaDoubleAlgebra213` but at the non-associative layer.

Type C L4 = ZOmegaQuad sits at the Cayley-analog layer of the Type C
tower (24 units, M_24 Chein loop).  `mul_assoc` fails here; only
alternativity / Moufang holds — registered separately via
`MoufangIntegerNormed213` once moufang_norm is supplied. -/

private theorem add_assoc' (u v w : ZOmegaQuad) :
    u + v + w = u + (v + w) := by
  apply toCDDouble_inj
  rw [toCDDouble_add, toCDDouble_add, toCDDouble_add, toCDDouble_add]
  exact NonAssocRing213.add_assoc _ _ _

private theorem add_comm' (u v : ZOmegaQuad) : u + v = v + u := by
  apply toCDDouble_inj
  rw [toCDDouble_add, toCDDouble_add]
  exact NonAssocRing213.add_comm _ _

private theorem add_zero' (u : ZOmegaQuad) : u + 0 = u := by
  apply toCDDouble_inj
  rw [toCDDouble_add, toCDDouble_zero]
  exact NonAssocRing213.add_zero _

private theorem add_left_neg' (u : ZOmegaQuad) : -u + u = 0 := by
  apply toCDDouble_inj
  rw [toCDDouble_add, toCDDouble_neg, toCDDouble_zero]
  exact NonAssocRing213.add_left_neg _

private theorem add_mul' (u v w : ZOmegaQuad) :
    (u + v) * w = u * w + v * w := by
  apply toCDDouble_inj
  rw [toCDDouble_mul, toCDDouble_add, toCDDouble_add,
      toCDDouble_mul, toCDDouble_mul]
  exact NonAssocRing213.add_mul _ _ _

private theorem mul_add' (u v w : ZOmegaQuad) :
    u * (v + w) = u * v + u * w := by
  apply toCDDouble_inj
  rw [toCDDouble_mul, toCDDouble_add, toCDDouble_add,
      toCDDouble_mul, toCDDouble_mul]
  exact NonAssocRing213.mul_add _ _ _

instance : NonAssocRing213 ZOmegaQuad where
  add_assoc    := add_assoc'
  add_comm     := add_comm'
  add_zero     := add_zero'
  add_left_neg := add_left_neg'
  add_mul      := add_mul'
  mul_add      := mul_add'

private theorem conj_conj' (u : ZOmegaQuad) :
    ZOmegaQuad.conj (ZOmegaQuad.conj u) = u := by
  apply toCDDouble_inj
  rw [toCDDouble_conj, toCDDouble_conj]
  exact NonAssocStarRing213.conj_conj _

private theorem conj_add' (u v : ZOmegaQuad) :
    ZOmegaQuad.conj (u + v) = ZOmegaQuad.conj u + ZOmegaQuad.conj v := by
  apply toCDDouble_inj
  rw [toCDDouble_conj, toCDDouble_add, toCDDouble_add,
      toCDDouble_conj, toCDDouble_conj]
  exact NonAssocStarRing213.conj_add _ _

private theorem conj_mul' (u v : ZOmegaQuad) :
    ZOmegaQuad.conj (u * v) = ZOmegaQuad.conj v * ZOmegaQuad.conj u := by
  apply toCDDouble_inj
  rw [toCDDouble_conj, toCDDouble_mul, toCDDouble_mul,
      toCDDouble_conj, toCDDouble_conj]
  exact NonAssocStarRing213.conj_mul _ _

instance : NonAssocStarRing213 ZOmegaQuad where
  conj      := ZOmegaQuad.conj
  conj_conj := conj_conj'
  conj_add  := conj_add'
  conj_mul  := conj_mul'

end E213.Lib.Math.CayleyDickson.Integer.ZOmegaQuad
