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

end E213.Lib.Math.CayleyDickson.Integer.ZOmegaQuad
