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

private theorem ofInt_mul' (a b : Int) :
    ofInt a * ofInt b = ofInt (a * b) := by
  apply L3T_ext
  · -- .re of ofInt a * ofInt b
    unfold ofInt
    change (E213.Lib.Math.CayleyDickson.Integer.ZSqrt.ofInt 2 a
            * E213.Lib.Math.CayleyDickson.Integer.ZSqrt.ofInt 2 b
            - (0 : Z2).conj * 0
          = E213.Lib.Math.CayleyDickson.Integer.ZSqrt.ofInt 2 (a * b))
    have h_conj_zero : ZSqrt.conj (0 : Z2) = 0 := by
      apply ZSqrt.ext
      · show (0 : Int) = 0; rfl
      · show -(0 : Int) = 0; rfl
    have h_neg_zero : -(0 : Z2) = 0 := by
      apply ZSqrt.ext
      · show -(0 : Int) = 0; rfl
      · show -(0 : Int) = 0; rfl
    rw [show ((0 : Z2).conj : Z2) = 0 from h_conj_zero,
        Ring213.zero_mul,
        show ∀ x : Z2, x - 0 = x from fun x => by
          show x + -0 = x
          rw [h_neg_zero, Ring213.add_zero]]
    exact @IntegerNormed213.ofInt_mul Z2 _ a b
  · -- .im: 0 * (ofInt a).re + 0 * (ofInt b).re.conj = 0
    change ((ofInt a).mul (ofInt b)).im = 0
    show (0 : Z2) * (ofInt a).re + 0 * (ofInt b).re.conj = 0
    rw [Ring213.zero_mul, Ring213.zero_mul, Ring213.add_zero]

private theorem ofInt_central' (z : Int) (a : L3T) :
    ofInt z * a = a * ofInt z := by
  apply L3T_ext
  · change ((ofInt z).mul a).re = (a.mul (ofInt z)).re
    show (ofInt z).re * a.re - a.im.conj * (ofInt z).im
       = a.re * (ofInt z).re - (ofInt z).im.conj * a.im
    have h_im_zero : (ofInt z).im = 0 := rfl
    have h_re_eq : (ofInt z).re
                = E213.Lib.Math.CayleyDickson.Integer.ZSqrt.ofInt 2 z := rfl
    have h_conj_zero : ZSqrt.conj (0 : Z2) = 0 := by
      apply ZSqrt.ext
      · show (0 : Int) = 0; rfl
      · show -(0 : Int) = 0; rfl
    rw [h_im_zero, h_re_eq, Ring213.mul_zero, h_conj_zero,
        Ring213.zero_mul]
    -- Goal: ofInt 2 z * a.re - 0 = a.re * ofInt 2 z - 0
    congr 1
    exact @CommRing213.mul_comm Z2 _
      (E213.Lib.Math.CayleyDickson.Integer.ZSqrt.ofInt 2 z) a.re
  · change ((ofInt z).mul a).im = (a.mul (ofInt z)).im
    show a.im * (ofInt z).re + (ofInt z).im * a.re.conj
       = (ofInt z).im * a.re + a.im * (ofInt z).re.conj
    have h_im_zero : (ofInt z).im = 0 := rfl
    have h_re_eq : (ofInt z).re
                = E213.Lib.Math.CayleyDickson.Integer.ZSqrt.ofInt 2 z := rfl
    rw [h_im_zero, h_re_eq,
        Ring213.zero_mul, Ring213.zero_mul,
        Ring213.add_zero, Ring213.zero_add,
        zsqrt_ofInt_conj_self z]

/-- ZSqrt 2's `conj(-a) = -conj a`. -/
private theorem zsqrt_conj_neg (a : Z2) : ZSqrt.conj (-a) = -ZSqrt.conj a := by
  apply ZSqrt.ext
  · show -a.re = -a.re; rfl
  · show -(-a.im) = -(-a.im); rfl

/-- `u * L3T.conj u = ofInt (L3T.normSq u)`. -/
private theorem self_mul_conj' (u : L3T) :
    u * L3T.conj u = ofInt u.normSq := by
  apply L3T_ext
  · change (u.mul (L3T.conj u)).re = (ofInt u.normSq).re
    show u.re * ZSqrt.conj u.re - ZSqrt.conj (-u.im) * u.im
       = E213.Lib.Math.CayleyDickson.Integer.ZSqrt.ofInt 2 u.normSq
    have h_self_re : u.re * ZSqrt.conj u.re
                   = E213.Lib.Math.CayleyDickson.Integer.ZSqrt.ofInt 2 u.re.normSq :=
      @IntegerNormed213.self_mul_conj Z2 _ u.re
    have h_self_im : u.im * ZSqrt.conj u.im
                   = E213.Lib.Math.CayleyDickson.Integer.ZSqrt.ofInt 2 u.im.normSq :=
      @IntegerNormed213.self_mul_conj Z2 _ u.im
    have h_comm_im : ZSqrt.conj u.im * u.im = u.im * ZSqrt.conj u.im :=
      @CommRing213.mul_comm Z2 _ (ZSqrt.conj u.im) u.im
    rw [zsqrt_conj_neg u.im, Ring213.neg_mul]
    -- Goal: u.re * conj u.re - -(conj u.im * u.im) = ofInt(N u.re + N u.im)
    show u.re * ZSqrt.conj u.re + -(-(ZSqrt.conj u.im * u.im))
       = E213.Lib.Math.CayleyDickson.Integer.ZSqrt.ofInt 2 u.normSq
    rw [Ring213.neg_neg, h_self_re, h_comm_im, h_self_im]
    show E213.Lib.Math.CayleyDickson.Integer.ZSqrt.ofInt 2 u.re.normSq
       + E213.Lib.Math.CayleyDickson.Integer.ZSqrt.ofInt 2 u.im.normSq
       = E213.Lib.Math.CayleyDickson.Integer.ZSqrt.ofInt 2 (u.re.normSq + u.im.normSq)
    exact @IntegerNormed213.ofInt_add Z2 _ _ _
  · change (u.mul (L3T.conj u)).im = (ofInt u.normSq).im
    show (-u.im) * u.re + u.im * ZSqrt.conj (ZSqrt.conj u.re) = 0
    rw [show ZSqrt.conj (ZSqrt.conj u.re) = u.re from
          @StarRing213.conj_conj Z2 _ u.re,
        Ring213.neg_mul,
        @CommRing213.mul_comm Z2 _ u.im u.re]
    -- Goal: -(u.re * u.im) + u.re * u.im = 0
    exact Ring213.add_left_neg _

/-- ★ L3T `IntegerNormed213` instance.  Completes Type B downstream
    Phase 3 equivalent.  Generic `IntegerNormed213.normSq_mul` then
    derives L3T's norm-multiplicativity via typeclass projection. -/
instance : IntegerNormed213 L3T where
  ofInt         := ofInt
  normSq        := L3T.normSq
  self_mul_conj := self_mul_conj'
  ofInt_mul     := ofInt_mul'
  ofInt_add     := ofInt_add'
  ofInt_central := ofInt_central'
  ofInt_inj     := ofInt_inj'

/-- ★ Concrete witness: L3T's `normSq_mul` derived via the generic
    `IntegerNormed213.normSq_mul` typeclass projection — no
    polynomial expansion at Int level. -/
theorem normSq_mul (u v : L3T) :
    L3T.normSq (u * v) = L3T.normSq u * L3T.normSq v :=
  IntegerNormed213.normSq_mul u v

end E213.Lib.Math.CayleyDickson.ZSqrtMinus2
