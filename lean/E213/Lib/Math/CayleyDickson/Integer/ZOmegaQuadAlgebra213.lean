import E213.Lib.Math.CayleyDickson.Integer.ZOmegaQuad
import E213.Lib.Math.CayleyDickson.Integer.ZOmegaDoubleAlgebra213
import E213.Meta.Algebra213.AlternativeNormed
import E213.Meta.Algebra213.CDDoubleMoufang

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

/-! ## §4 — `MoufangIntegerNormed213 ZOmegaQuad` via the polarization bridge

ZOmegaQuad = CDDouble ZOmegaDouble doubles the **non-commutative**
associative base ZOmegaDouble, so the Moufang norm-collapse is the
genuine degree-4 Hurwitz identity (no `mul_assoc` shortcut).  We supply
the polarization condition `TraceNormed213 ZOmegaDouble` (the Eisenstein
trace `2·re − im` on the inner ZOmega real-axis), which makes the
abstract `instMoufangIntegerNormed213CDDouble` fire on
`CDDouble ZOmegaDouble`.  The concrete instance then bridges through
`toCDDouble`, exactly as the Phase-3 IntegerNormed213 bridge did. -/

/-- Eisenstein-trace polarization on ZOmegaDouble: `a + conj a` lands in
    the central `ofInt` image. -/
instance : TraceNormed213 ZOmegaDouble where
  trace a := a.re.re + (a.re.re - a.re.im)
  self_add_conj a := by
    apply ZOmegaDouble.ext
    · apply ZOmega.ZOmega.ext
      · rfl
      · exact E213.Meta.Int213.add_neg_cancel a.re.im
    · apply ZOmega.ZOmega.ext
      · exact E213.Meta.Int213.add_neg_cancel a.im.re
      · exact E213.Meta.Int213.add_neg_cancel a.im.im

/-- Real-axis integer embed for ZOmegaQuad. -/
def ofInt (n : Int) : ZOmegaQuad := ⟨ZOmegaDouble.ofInt n, 0⟩

theorem toCDDouble_ofInt (n : Int) :
    toCDDouble (ofInt n) = cdm_ofInt n := by
  apply CDDouble.ext
  · show ZOmegaDouble.ofInt n = IntegerNormed213.ofInt n; rfl
  · show (0 : ZOmegaDouble) = 0; rfl

private theorem zoq_self_mul_conj (u : ZOmegaQuad) :
    u * ZOmegaQuad.conj u = ofInt (ZOmegaQuad.normSq u) := by
  apply toCDDouble_inj
  rw [toCDDouble_mul, toCDDouble_conj, toCDDouble_ofInt]
  exact cd_self_mul_conj (toCDDouble u)

private theorem zoq_ofInt_mul (a b : Int) :
    ofInt a * ofInt b = ofInt (a * b) := by
  apply toCDDouble_inj
  rw [toCDDouble_mul, toCDDouble_ofInt, toCDDouble_ofInt, toCDDouble_ofInt]
  exact cd_ofInt_mul a b

private theorem zoq_ofInt_central (z : Int) (u : ZOmegaQuad) :
    ofInt z * u = u * ofInt z := by
  apply toCDDouble_inj
  rw [toCDDouble_mul, toCDDouble_mul, toCDDouble_ofInt]
  exact cd_ofInt_central z (toCDDouble u)

private theorem zoq_ofInt_inj {a b : Int}
    (h : (ofInt a : ZOmegaQuad) = ofInt b) : a = b := by
  apply @cd_ofInt_inj ZOmegaDouble _ a b
  rw [← toCDDouble_ofInt, ← toCDDouble_ofInt, h]

private theorem zoq_moufang_norm (u v : ZOmegaQuad) :
    (u * v) * (ZOmegaQuad.conj v * ZOmegaQuad.conj u)
      = u * (v * ZOmegaQuad.conj v) * ZOmegaQuad.conj u := by
  apply toCDDouble_inj
  repeat rw [toCDDouble_mul]
  repeat rw [toCDDouble_conj]
  exact cd_moufang_norm (toCDDouble u) (toCDDouble v)

private theorem zoq_ofInt_paren_central (z : Int) (u : ZOmegaQuad) :
    u * ofInt z * ZOmegaQuad.conj u = ofInt z * (u * ZOmegaQuad.conj u) := by
  apply toCDDouble_inj
  repeat rw [toCDDouble_mul]
  repeat rw [toCDDouble_conj]
  repeat rw [toCDDouble_ofInt]
  exact cd_ofInt_paren_central z (toCDDouble u)

/-- ★ MoufangIntegerNormed213 ZOmegaQuad — Type C L4 (24 units, M_24
    Chein loop).  The first genuinely non-associative Type C layer; the
    Moufang norm-collapse is the polarization-cancelled Hurwitz identity
    bridged from `cd_moufang_norm`. -/
instance : MoufangIntegerNormed213 ZOmegaQuad where
  ofInt               := ofInt
  normSq              := ZOmegaQuad.normSq
  self_mul_conj       := zoq_self_mul_conj
  ofInt_mul           := zoq_ofInt_mul
  ofInt_central       := zoq_ofInt_central
  ofInt_inj           := zoq_ofInt_inj
  moufang_norm        := zoq_moufang_norm
  ofInt_paren_central := zoq_ofInt_paren_central

/-- ★ Witness: ZOmegaQuad's norm multiplicativity via the generic
    `MoufangIntegerNormed213.normSq_mul` — the non-associative Type C
    Hurwitz composition, polarization-derived, strict ∅-axiom. -/
theorem normSq_mul (u v : ZOmegaQuad) :
    ZOmegaQuad.normSq (u * v) = ZOmegaQuad.normSq u * ZOmegaQuad.normSq v :=
  MoufangIntegerNormed213.normSq_mul u v

end E213.Lib.Math.CayleyDickson.Integer.ZOmegaQuad
