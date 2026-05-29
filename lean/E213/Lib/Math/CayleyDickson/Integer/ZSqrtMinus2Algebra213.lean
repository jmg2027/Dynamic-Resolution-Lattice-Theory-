import E213.Lib.Math.CayleyDickson.Integer.ZSqrtMinus2Tower
import E213.Lib.Math.CayleyDickson.Integer.ZSqrtAlgebra213
import E213.Meta.Algebra213.CDDoubleStar
import E213.Meta.Algebra213.AlternativeNormed

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

/-! ## §4 — IntegerNormed213 (Type B downstream completion) -/

/-- Componentwise extensionality for L3T (not auto-generated). -/
theorem L3T_ext {u v : L3T} (hr : u.re = v.re) (hi : u.im = v.im) :
    u = v := by cases u; cases v; congr

/-- `ofInt n = ⟨(ZSqrt 2).ofInt n, 0⟩` along the real axis. -/
def ofInt (n : Int) : L3T :=
  ⟨E213.Lib.Math.CayleyDickson.Integer.ZSqrt.ofInt 2 n, 0⟩

private theorem ofInt_inj' {a b : Int} (h : ofInt a = ofInt b) : a = b := by
  have h_re : (ofInt a).re = (ofInt b).re := congrArg L3T.re h
  -- (ofInt a).re = ZSqrt.ofInt 2 a definitionally; need typeclass form
  exact @IntegerNormed213.ofInt_inj (ZSqrt 2) _ a b
    (by unfold ofInt at h_re; exact h_re)

/-- ZSqrt 2's ofInt is conj-fixed (real-axis is fixed by ZSqrt.conj). -/
private theorem zsqrt_ofInt_conj_self (n : Int) :
    ZSqrt.conj (E213.Lib.Math.CayleyDickson.Integer.ZSqrt.ofInt 2 n) = E213.Lib.Math.CayleyDickson.Integer.ZSqrt.ofInt 2 n := by
  apply ZSqrt.ext
  · show n = n; rfl
  · show -(0 : Int) = 0; rfl

private theorem ofInt_add' (a b : Int) :
    ofInt a + ofInt b = ofInt (a + b) := by
  apply L3T_ext
  · unfold ofInt
    change (E213.Lib.Math.CayleyDickson.Integer.ZSqrt.ofInt 2 a
          + E213.Lib.Math.CayleyDickson.Integer.ZSqrt.ofInt 2 b
          = E213.Lib.Math.CayleyDickson.Integer.ZSqrt.ofInt 2 (a + b))
    exact @IntegerNormed213.ofInt_add (ZSqrt 2) _ a b
  · unfold ofInt
    show (0 : Z2) + 0 = 0
    apply ZSqrt.ext
    · show (0 : Int) + 0 = 0; rfl
    · show (0 : Int) + 0 = 0; rfl

/-- ★ Bridge-based `ofInt_mul`: derive from abstract
    `IntegerNormed213 (CDDouble Z2)` via `toCDDouble`.  Replaces a
    ~25-line proof with a 5-line bridge projection. -/
private theorem ofInt_mul' (a b : Int) :
    ofInt a * ofInt b = ofInt (a * b) := by
  apply toCDDouble_inj
  rw [toCDDouble_mul]
  show toCDDouble (ofInt a) * toCDDouble (ofInt b) = toCDDouble (ofInt (a * b))
  exact @IntegerNormed213.ofInt_mul (CDDouble Z2) _ a b

/-- ★ Bridge-based `ofInt_central`: derive from abstract
    `IntegerNormed213 (CDDouble Z2)` via `toCDDouble`.  Replaces a
    ~28-line proof with a 5-line bridge projection. -/
private theorem ofInt_central' (z : Int) (a : L3T) :
    ofInt z * a = a * ofInt z := by
  apply toCDDouble_inj
  rw [toCDDouble_mul, toCDDouble_mul]
  show toCDDouble (ofInt z) * toCDDouble a = toCDDouble a * toCDDouble (ofInt z)
  exact @IntegerNormed213.ofInt_central (CDDouble Z2) _ z (toCDDouble a)

/-- ZSqrt 2's `conj(-a) = -conj a`. -/
private theorem zsqrt_conj_neg (a : Z2) : ZSqrt.conj (-a) = -ZSqrt.conj a := by
  apply ZSqrt.ext
  · show -a.re = -a.re; rfl
  · show -(-a.im) = -(-a.im); rfl

/-- ★ Bridge-based `self_mul_conj`: derive from abstract
    `IntegerNormed213 (CDDouble Z2)` via `toCDDouble`.  Replaces a
    ~30-line hand-written proof with a 5-line bridge projection. -/
private theorem self_mul_conj' (u : L3T) :
    u * L3T.conj u = ofInt u.normSq := by
  apply toCDDouble_inj
  rw [toCDDouble_mul, toCDDouble_conj]
  show toCDDouble u * CDDouble.conj (toCDDouble u)
     = toCDDouble (ofInt u.normSq)
  exact @IntegerNormed213.self_mul_conj (CDDouble Z2) _ (toCDDouble u)

/-- `ZSqrt.normSq (-x) = ZSqrt.normSq x` for any D — direct via
    `(-y)·(-y) = y·y` componentwise. -/
private theorem zsqrt_normSq_neg (x : Z2) : ZSqrt.normSq (-x) = ZSqrt.normSq x := by
  show (-x.re) * (-x.re) + 2 * ((-x.im) * (-x.im))
     = x.re * x.re + 2 * (x.im * x.im)
  rw [E213.Meta.Int213.neg_mul x.re (-x.re),
      E213.Meta.Int213.mul_neg x.re x.re, Int.neg_neg,
      E213.Meta.Int213.neg_mul x.im (-x.im),
      E213.Meta.Int213.mul_neg x.im x.im, Int.neg_neg]

/-- `ZSqrt.normSq (conj x) = ZSqrt.normSq x` for Z2 — direct via
    `(-y)·(-y) = y·y` componentwise (mirrors `zsqrt_normSq_neg`). -/
private theorem zsqrt_normSq_conj (x : Z2) :
    ZSqrt.normSq (ZSqrt.conj x) = ZSqrt.normSq x := by
  show x.re * x.re + 2 * ((-x.im) * (-x.im))
     = x.re * x.re + 2 * (x.im * x.im)
  rw [E213.Meta.Int213.neg_mul x.im (-x.im),
      E213.Meta.Int213.mul_neg x.im x.im, Int.neg_neg]

/-- `normSq (conj u) = normSq u` for L3T.  Componentwise via Z2's
    `zsqrt_normSq_conj` + `zsqrt_normSq_neg`. -/
private theorem normSq_conj' (u : L3T) : L3T.normSq (L3T.conj u) = L3T.normSq u := by
  show ZSqrt.normSq (ZSqrt.conj u.re) + ZSqrt.normSq (-u.im)
     = ZSqrt.normSq u.re + ZSqrt.normSq u.im
  rw [zsqrt_normSq_conj u.re, zsqrt_normSq_neg u.im]

/-- `conj (ofInt z) = ofInt z` for L3T.  conj ⟨ZSqrt.ofInt 2 z, 0⟩
    = ⟨ZSqrt.conj (ZSqrt.ofInt 2 z), -0⟩ = ⟨ZSqrt.ofInt 2 z, 0⟩. -/
private theorem ofInt_conj' (z : Int) : L3T.conj (ofInt z) = ofInt z := by
  apply L3T_ext
  · exact @IntegerNormed213.ofInt_conj Z2 _ z
  · show -(0 : Z2) = 0
    apply ZSqrt.ext
    · show -(0 : Int) = 0; exact Int.neg_zero
    · show -(0 : Int) = 0; exact Int.neg_zero

instance : IntegerNormed213 L3T where
  ofInt         := ofInt
  normSq        := L3T.normSq
  self_mul_conj := self_mul_conj'
  ofInt_mul     := ofInt_mul'
  ofInt_add     := ofInt_add'
  ofInt_central := ofInt_central'
  ofInt_inj     := ofInt_inj'
  normSq_conj   := normSq_conj'
  ofInt_conj    := ofInt_conj'

/-- ★ Concrete witness: L3T's `normSq_mul` derived via the generic
    `IntegerNormed213.normSq_mul` typeclass projection — no
    polynomial expansion at Int level. -/
theorem normSq_mul (u v : L3T) :
    L3T.normSq (u * v) = L3T.normSq u * L3T.normSq v :=
  IntegerNormed213.normSq_mul u v

/-! ## §5 — MoufangIntegerNormed213 (associative quaternion-analog) -/

private theorem l3t_moufang_norm (u v : L3T) :
    (u * v) * (L3T.conj v * L3T.conj u)
      = u * (v * L3T.conj v) * L3T.conj u := by
  rw [← Ring213.mul_assoc (u * v) (L3T.conj v) (L3T.conj u),
      Ring213.mul_assoc u v (L3T.conj v)]

private theorem l3t_ofInt_paren_central (z : Int) (u : L3T) :
    u * ofInt z * L3T.conj u = ofInt z * (u * L3T.conj u) := by
  rw [show u * ofInt z = ofInt z * u from
        (@IntegerNormed213.ofInt_central L3T _ z u).symm,
      Ring213.mul_assoc (ofInt z) u (L3T.conj u)]

/-- ★ MoufangIntegerNormed213 L3T — Type B L3 associative
    quaternion-analog (parallel to Lipschitz Type A L2 + ZOmegaDouble
    Type C L3).  Moufang trivial via mul_assoc. -/
instance : MoufangIntegerNormed213 L3T where
  ofInt               := ofInt
  normSq              := L3T.normSq
  self_mul_conj       := self_mul_conj'
  ofInt_mul           := ofInt_mul'
  ofInt_central       := ofInt_central'
  ofInt_inj           := ofInt_inj'
  moufang_norm        := l3t_moufang_norm
  ofInt_paren_central := l3t_ofInt_paren_central

/-- ★ Generic `MoufangIntegerNormed213.normSq_mul` on L3T —
    alternative path to the IntegerNormed213-based derivation. -/
theorem moufang_normSq_mul (u v : L3T) :
    L3T.normSq (u * v) = L3T.normSq u * L3T.normSq v :=
  MoufangIntegerNormed213.normSq_mul u v

/-! ## §6 — L4T NonAssocRing213 + NonAssocStarRing213 via bridge

L4T = CDDouble L3T is the Type B L4 carrier (alternative non-associative
layer of the Type B tower).  Since L3T has `Ring213` + `StarRing213`
(non-comm associative) from §3, the parametric
`instNonAssocStarRing213CDDoubleStar [StarRing213 L3T]` from
`CDDoubleStar` fires, giving `NonAssocRing213 (CDDouble L3T)` and
`NonAssocStarRing213 (CDDouble L3T)`.  L4T then bridges through
`toCDDouble : L4T → CDDouble L3T` — same recipe as ZOmegaQuad.

`mul_assoc` fails at this layer (Cayley analog); only alternativity
holds.  Full `MoufangIntegerNormed213` requires moufang_norm input
(deferred — same Hurwitz polynomial obstruction as Cayley/ZOmegaQuad). -/

namespace L4T

/-- L4T → abstract CDDouble L3T. -/
def toCDDouble (u : L4T) : CDDouble L3T := ⟨u.re, u.im⟩

/-- Abstract CDDouble L3T → L4T. -/
def fromCDDouble (u : CDDouble L3T) : L4T := ⟨u.re, u.im⟩

theorem to_from (u : CDDouble L3T) :
    toCDDouble (fromCDDouble u) = u := by cases u; rfl

theorem from_to (u : L4T) :
    fromCDDouble (toCDDouble u) = u := by cases u; rfl

theorem toCDDouble_inj {u v : L4T}
    (h : toCDDouble u = toCDDouble v) : u = v := by
  have := congrArg fromCDDouble h
  rwa [from_to, from_to] at this

theorem toCDDouble_mul (u v : L4T) :
    toCDDouble (u * v) = toCDDouble u * toCDDouble v := by
  apply CDDouble.ext
  · show (u * v).re
       = u.re * v.re + -(StarRing213.conj v.im * u.im)
    show u.re * v.re - (L3T.conj v.im) * u.im
       = u.re * v.re + -(StarRing213.conj v.im * u.im)
    rfl
  · show (u * v).im
       = v.im * u.re + u.im * StarRing213.conj v.re
    rfl

theorem toCDDouble_conj (u : L4T) :
    toCDDouble (L4T.conj u) = CDDouble.conj (toCDDouble u) := by
  apply CDDouble.ext
  · show L3T.conj u.re = StarRing213.conj u.re; rfl
  · show -u.im = -u.im; rfl

theorem toCDDouble_add (u v : L4T) :
    toCDDouble (u + v) = toCDDouble u + toCDDouble v := by
  apply CDDouble.ext
  · show (u + v).re = u.re + v.re; rfl
  · show (u + v).im = u.im + v.im; rfl

theorem toCDDouble_neg (u : L4T) :
    toCDDouble (-u) = -(toCDDouble u) := by
  apply CDDouble.ext
  · show (-u).re = -u.re; rfl
  · show (-u).im = -u.im; rfl

theorem toCDDouble_zero : toCDDouble 0 = 0 := rfl

private theorem add_assoc' (u v w : L4T) :
    u + v + w = u + (v + w) := by
  apply toCDDouble_inj
  rw [toCDDouble_add, toCDDouble_add, toCDDouble_add, toCDDouble_add]
  exact NonAssocRing213.add_assoc _ _ _

private theorem add_comm' (u v : L4T) : u + v = v + u := by
  apply toCDDouble_inj
  rw [toCDDouble_add, toCDDouble_add]
  exact NonAssocRing213.add_comm _ _

private theorem add_zero' (u : L4T) : u + 0 = u := by
  apply toCDDouble_inj
  rw [toCDDouble_add, toCDDouble_zero]
  exact NonAssocRing213.add_zero _

private theorem add_left_neg' (u : L4T) : -u + u = 0 := by
  apply toCDDouble_inj
  rw [toCDDouble_add, toCDDouble_neg, toCDDouble_zero]
  exact NonAssocRing213.add_left_neg _

private theorem add_mul' (u v w : L4T) :
    (u + v) * w = u * w + v * w := by
  apply toCDDouble_inj
  rw [toCDDouble_mul, toCDDouble_add, toCDDouble_add,
      toCDDouble_mul, toCDDouble_mul]
  exact NonAssocRing213.add_mul _ _ _

private theorem mul_add' (u v w : L4T) :
    u * (v + w) = u * v + u * w := by
  apply toCDDouble_inj
  rw [toCDDouble_mul, toCDDouble_add, toCDDouble_add,
      toCDDouble_mul, toCDDouble_mul]
  exact NonAssocRing213.mul_add _ _ _

instance : NonAssocRing213 L4T where
  add_assoc    := add_assoc'
  add_comm     := add_comm'
  add_zero     := add_zero'
  add_left_neg := add_left_neg'
  add_mul      := add_mul'
  mul_add      := mul_add'

private theorem conj_conj' (u : L4T) :
    L4T.conj (L4T.conj u) = u := by
  apply toCDDouble_inj
  rw [toCDDouble_conj, toCDDouble_conj]
  exact NonAssocStarRing213.conj_conj _

private theorem conj_add' (u v : L4T) :
    L4T.conj (u + v) = L4T.conj u + L4T.conj v := by
  apply toCDDouble_inj
  rw [toCDDouble_conj, toCDDouble_add, toCDDouble_add,
      toCDDouble_conj, toCDDouble_conj]
  exact NonAssocStarRing213.conj_add _ _

private theorem conj_mul' (u v : L4T) :
    L4T.conj (u * v) = L4T.conj v * L4T.conj u := by
  apply toCDDouble_inj
  rw [toCDDouble_conj, toCDDouble_mul, toCDDouble_mul,
      toCDDouble_conj, toCDDouble_conj]
  exact NonAssocStarRing213.conj_mul _ _

instance : NonAssocStarRing213 L4T where
  conj      := L4T.conj
  conj_conj := conj_conj'
  conj_add  := conj_add'
  conj_mul  := conj_mul'

end L4T

end E213.Lib.Math.CayleyDickson.ZSqrtMinus2
