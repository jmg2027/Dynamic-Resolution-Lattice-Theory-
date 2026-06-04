import E213.Lib.Math.Algebra.CayleyDickson.Levels.Cayley
import E213.Lib.Math.Algebra.CayleyDickson.Lipschitz.LipschitzAlgebra213
import E213.Meta.Algebra213.CDDoubleStar

/-!
# `Cayley` (= CDDouble Lipschitz) NonAssocStarRing213 bridge

Cayley (Type A L3, integer octonions, 240 unit octonions in `O_int`)
sits at the alternative non-associative layer of the Type A tower —
parallel to Type C's ZOmegaQuad and Type B's L4T.

Lipschitz (Type A L2, quaternion analog) has Ring213 + StarRing213
(non-commutative associative) from `LipschitzAlgebra213` (PURE).  The
parametric `instNonAssocStarRing213CDDoubleStar [StarRing213 α]` from
`Meta/Algebra213/CDDoubleStar` then fires on α := Lipschitz, giving
`NonAssocRing213 (CDDouble Lipschitz)` and
`NonAssocStarRing213 (CDDouble Lipschitz)`.

Cayley bridges through `toCDDouble : Cayley → CDDouble Lipschitz` —
same recipe as ZOmegaQuad's bridge in `ZOmegaQuadAlgebra213` (Phase 4+)
and L4T's bridge in `ZSqrtMinus2Algebra213` §6.

`mul_assoc` fails here (Cayley is alternative, not associative).  The
full `MoufangIntegerNormed213 Cayley` instance is registered in
`CayleyMoufang.lean`: the moufang_norm input is the degree-4 Hurwitz
identity, proved structurally (not by `hurwitz_ring` brute force) via
the polarization condition `TraceNormed213 Lipschitz` and the abstract
`CDDoubleMoufang` framework — same recipe as ZOmegaQuad and L4T.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Levels.Cayley

open E213.Meta.Algebra213
open E213.Lib.Math.Algebra.CayleyDickson.Tower.CDDouble
open E213.Lib.Math.Algebra.CayleyDickson.Tower.CDDouble.Lipschitz

/-! ## §1 — Bridge to abstract `CDDouble Lipschitz` -/

/-- Cayley → abstract CDDouble Lipschitz. -/
def toCDDouble (u : Cayley) : CDDouble Lipschitz := ⟨u.re, u.im⟩

/-- Abstract CDDouble Lipschitz → Cayley. -/
def fromCDDouble (u : CDDouble Lipschitz) : Cayley := ⟨u.re, u.im⟩

theorem to_from (u : CDDouble Lipschitz) :
    toCDDouble (fromCDDouble u) = u := by cases u; rfl

theorem from_to (u : Cayley) :
    fromCDDouble (toCDDouble u) = u := by cases u; rfl

theorem toCDDouble_inj {u v : Cayley}
    (h : toCDDouble u = toCDDouble v) : u = v := by
  have := congrArg fromCDDouble h
  rwa [from_to, from_to] at this

/-! ## §2 — Operation bridges (rfl) -/

theorem toCDDouble_mul (u v : Cayley) :
    toCDDouble (u * v) = toCDDouble u * toCDDouble v := by
  apply CDDouble.ext
  · show (u * v).re
       = u.re * v.re + -(StarRing213.conj v.im * u.im)
    show u.re * v.re - (Lipschitz.conj v.im) * u.im
       = u.re * v.re + -(StarRing213.conj v.im * u.im)
    rfl
  · show (u * v).im
       = v.im * u.re + u.im * StarRing213.conj v.re
    rfl

theorem toCDDouble_conj (u : Cayley) :
    toCDDouble (Cayley.conj u) = CDDouble.conj (toCDDouble u) := by
  apply CDDouble.ext
  · show Lipschitz.conj u.re = StarRing213.conj u.re; rfl
  · show -u.im = -u.im; rfl

theorem toCDDouble_add (u v : Cayley) :
    toCDDouble (u + v) = toCDDouble u + toCDDouble v := by
  apply CDDouble.ext
  · show (u + v).re = u.re + v.re; rfl
  · show (u + v).im = u.im + v.im; rfl

theorem toCDDouble_neg (u : Cayley) :
    toCDDouble (-u) = -(toCDDouble u) := by
  apply CDDouble.ext
  · show (-u).re = -u.re; rfl
  · show (-u).im = -u.im; rfl

theorem toCDDouble_zero : toCDDouble 0 = 0 := rfl

/-! ## §3 — NonAssocRing213 + NonAssocStarRing213 Cayley via bridge -/

private theorem add_assoc' (u v w : Cayley) :
    u + v + w = u + (v + w) := by
  apply toCDDouble_inj
  rw [toCDDouble_add, toCDDouble_add, toCDDouble_add, toCDDouble_add]
  exact NonAssocRing213.add_assoc _ _ _

private theorem add_comm' (u v : Cayley) : u + v = v + u := by
  apply toCDDouble_inj
  rw [toCDDouble_add, toCDDouble_add]
  exact NonAssocRing213.add_comm _ _

private theorem add_zero' (u : Cayley) : u + 0 = u := by
  apply toCDDouble_inj
  rw [toCDDouble_add, toCDDouble_zero]
  exact NonAssocRing213.add_zero _

private theorem add_left_neg' (u : Cayley) : -u + u = 0 := by
  apply toCDDouble_inj
  rw [toCDDouble_add, toCDDouble_neg, toCDDouble_zero]
  exact NonAssocRing213.add_left_neg _

private theorem add_mul' (u v w : Cayley) :
    (u + v) * w = u * w + v * w := by
  apply toCDDouble_inj
  rw [toCDDouble_mul, toCDDouble_add, toCDDouble_add,
      toCDDouble_mul, toCDDouble_mul]
  exact NonAssocRing213.add_mul _ _ _

private theorem mul_add' (u v w : Cayley) :
    u * (v + w) = u * v + u * w := by
  apply toCDDouble_inj
  rw [toCDDouble_mul, toCDDouble_add, toCDDouble_add,
      toCDDouble_mul, toCDDouble_mul]
  exact NonAssocRing213.mul_add _ _ _

instance : NonAssocRing213 Cayley where
  add_assoc    := add_assoc'
  add_comm     := add_comm'
  add_zero     := add_zero'
  add_left_neg := add_left_neg'
  add_mul      := add_mul'
  mul_add      := mul_add'

private theorem conj_conj' (u : Cayley) :
    Cayley.conj (Cayley.conj u) = u := by
  apply toCDDouble_inj
  rw [toCDDouble_conj, toCDDouble_conj]
  exact NonAssocStarRing213.conj_conj _

private theorem conj_add' (u v : Cayley) :
    Cayley.conj (u + v) = Cayley.conj u + Cayley.conj v := by
  apply toCDDouble_inj
  rw [toCDDouble_conj, toCDDouble_add, toCDDouble_add,
      toCDDouble_conj, toCDDouble_conj]
  exact NonAssocStarRing213.conj_add _ _

private theorem conj_mul' (u v : Cayley) :
    Cayley.conj (u * v) = Cayley.conj v * Cayley.conj u := by
  apply toCDDouble_inj
  rw [toCDDouble_conj, toCDDouble_mul, toCDDouble_mul,
      toCDDouble_conj, toCDDouble_conj]
  exact NonAssocStarRing213.conj_mul _ _

instance : NonAssocStarRing213 Cayley where
  conj      := Cayley.conj
  conj_conj := conj_conj'
  conj_add  := conj_add'
  conj_mul  := conj_mul'

end E213.Lib.Math.Algebra.CayleyDickson.Levels.Cayley
