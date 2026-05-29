import E213.Lib.Math.CayleyDickson.Integer.ZSqrtMinus2Tower
import E213.Lib.Math.CayleyDickson.Integer.ZSqrtAlgebra213
import E213.Meta.Algebra213.CDDoubleStar

/-!
# `L3T` (= CDDouble ZSqrt[-2]) Algebra213 bridge

L3T (Type B L3 carrier from `ZSqrtMinus2Tower`) is structurally the
abstract `CDDouble (ZSqrt 2)`.  This file installs the bridge — same
recipe as `ZOmegaDoubleAlgebra213` (Phase 2 commit `38e17ad`) but
applied at the Type B base tower.

Bridge `toCDDouble : L3T → CDDouble (ZSqrt 2)` + inverse + mul/conj/
add/neg/zero compatibility (all `rfl`) transfers the abstract
`Ring213 (CDDouble (ZSqrt 2))` + `StarRing213 (CDDouble (ZSqrt 2))`
instances (auto-synthesised via `instRing213CDDouble` from
`CDDoubleStar` once `CommStarRing213 (ZSqrt 2)` is registered)
onto the concrete `L3T` type — no per-axiom hand-proof.

Same recipe extends to L4T = CDDouble L3T, etc. (Type B downstream).
-/

namespace E213.Lib.Math.CayleyDickson.ZSqrtMinus2

open E213.Meta.Algebra213
open E213.Lib.Math.CayleyDickson.Integer.ZSqrt

/-! ## §1 — Bridge to abstract `CDDouble Z2` -/

/-- L3T → abstract CDDouble Z2 (where Z2 = ZSqrt 2). -/
def toCDDouble (u : L3T) : CDDouble Z2 := ⟨u.re, u.im⟩

/-- Abstract CDDouble Z2 → L3T. -/
def fromCDDouble (u : CDDouble Z2) : L3T := ⟨u.re, u.im⟩

theorem to_from (u : CDDouble Z2) : toCDDouble (fromCDDouble u) = u := by
  cases u; rfl

theorem from_to (u : L3T) : fromCDDouble (toCDDouble u) = u := by
  cases u; rfl

theorem toCDDouble_inj {u v : L3T}
    (h : toCDDouble u = toCDDouble v) : u = v := by
  have := congrArg fromCDDouble h
  rwa [from_to, from_to] at this

/-! ## §2 — Operation bridges (rfl) -/

theorem toCDDouble_mul (u v : L3T) :
    toCDDouble (u * v) = toCDDouble u * toCDDouble v := by
  apply CDDouble.ext
  · show (u * v).re
       = u.re * v.re + -(StarRing213.conj v.im * u.im)
    show u.re * v.re - (ZSqrt.conj v.im) * u.im
       = u.re * v.re + -(StarRing213.conj v.im * u.im)
    rfl
  · show (u * v).im
       = v.im * u.re + u.im * StarRing213.conj v.re
    rfl

theorem toCDDouble_conj (u : L3T) :
    toCDDouble (L3T.conj u) = CDDouble.conj (toCDDouble u) := by
  apply CDDouble.ext
  · show ZSqrt.conj u.re = StarRing213.conj u.re; rfl
  · show -u.im = -u.im; rfl

theorem toCDDouble_add (u v : L3T) :
    toCDDouble (u + v) = toCDDouble u + toCDDouble v := by
  apply CDDouble.ext
  · show (u + v).re = u.re + v.re; rfl
  · show (u + v).im = u.im + v.im; rfl

theorem toCDDouble_neg (u : L3T) :
    toCDDouble (-u) = -(toCDDouble u) := by
  apply CDDouble.ext
  · show (-u).re = -u.re; rfl
  · show (-u).im = -u.im; rfl

theorem toCDDouble_zero : toCDDouble 0 = 0 := rfl

/-! ## §3 — Ring213 + StarRing213 instances via bridge -/

private theorem add_assoc' (u v w : L3T) : u + v + w = u + (v + w) := by
  apply toCDDouble_inj
  rw [toCDDouble_add, toCDDouble_add, toCDDouble_add, toCDDouble_add]
  exact Ring213.add_assoc _ _ _

private theorem add_comm' (u v : L3T) : u + v = v + u := by
  apply toCDDouble_inj
  rw [toCDDouble_add, toCDDouble_add]
  exact Ring213.add_comm _ _

private theorem add_zero' (u : L3T) : u + 0 = u := by
  apply toCDDouble_inj
  rw [toCDDouble_add, toCDDouble_zero]
  exact Ring213.add_zero _

private theorem add_left_neg' (u : L3T) : -u + u = 0 := by
  apply toCDDouble_inj
  rw [toCDDouble_add, toCDDouble_neg, toCDDouble_zero]
  exact Ring213.add_left_neg _

private theorem mul_assoc' (u v w : L3T) : (u * v) * w = u * (v * w) := by
  apply toCDDouble_inj
  rw [toCDDouble_mul, toCDDouble_mul, toCDDouble_mul, toCDDouble_mul]
  exact Ring213.mul_assoc _ _ _

private theorem add_mul' (u v w : L3T) : (u + v) * w = u * w + v * w := by
  apply toCDDouble_inj
  rw [toCDDouble_mul, toCDDouble_add, toCDDouble_add,
      toCDDouble_mul, toCDDouble_mul]
  exact Ring213.add_mul _ _ _

private theorem mul_add' (u v w : L3T) : u * (v + w) = u * v + u * w := by
  apply toCDDouble_inj
  rw [toCDDouble_mul, toCDDouble_add, toCDDouble_add,
      toCDDouble_mul, toCDDouble_mul]
  exact Ring213.mul_add _ _ _

private theorem conj_add' (u v : L3T) :
    L3T.conj (u + v) = L3T.conj u + L3T.conj v := by
  apply toCDDouble_inj
  rw [toCDDouble_conj, toCDDouble_add, toCDDouble_add,
      toCDDouble_conj, toCDDouble_conj]
  exact StarRing213.conj_add _ _

private theorem conj_mul' (u v : L3T) :
    L3T.conj (u * v) = L3T.conj v * L3T.conj u := by
  apply toCDDouble_inj
  rw [toCDDouble_conj, toCDDouble_mul, toCDDouble_mul,
      toCDDouble_conj, toCDDouble_conj]
  exact StarRing213.conj_mul _ _

private theorem conj_conj' (u : L3T) : L3T.conj (L3T.conj u) = u := by
  apply toCDDouble_inj
  rw [toCDDouble_conj, toCDDouble_conj]
  exact StarRing213.conj_conj _

/-- ★ L3T `Ring213` instance — all 7 axioms via abstract CDDouble
    bridge.  No polynomial proof at this layer. -/
instance : Ring213 L3T where
  add_assoc    := add_assoc'
  add_comm     := add_comm'
  add_zero     := add_zero'
  add_left_neg := add_left_neg'
  mul_assoc    := mul_assoc'
  add_mul      := add_mul'
  mul_add      := mul_add'

/-- ★ L3T `StarRing213` instance. -/
instance : StarRing213 L3T where
  conj      := L3T.conj
  conj_conj := conj_conj'
  conj_add  := conj_add'
  conj_mul  := conj_mul'

end E213.Lib.Math.CayleyDickson.ZSqrtMinus2
