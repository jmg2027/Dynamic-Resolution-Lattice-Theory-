import E213.Lib.Math.Algebra.CayleyDickson.Tower.CDDouble
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZIAlgebra213
import E213.Meta.Algebra213.Core
import E213.Meta.Algebra213.CDDoubleStar
import E213.Meta.Int213.Core

/-!
# `Lipschitz` as an `IntegerNormed213` instance

Hierarchical-modular CD layer 1.  Ring axioms reduce to ZI's PURE
ring axioms — no Int polynomial expansion at this layer.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Tower.CDDouble.Lipschitz

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI.ZI
open E213.Meta.Algebra213

/-- `ofInt n = ⟨ZI.ofInt n, 0⟩`. -/
def ofInt (n : Int) : Lipschitz := ⟨ZI.ofInt n, 0⟩

/-! ## Bridge to abstract `CDDouble ZI` (enables abstract Hurwitz extension). -/

/-- Lipschitz → abstract CDDouble ZI. -/
def toCDDouble (u : Lipschitz) : CDDouble ZI := ⟨u.re, u.im⟩

/-- Abstract CDDouble ZI → Lipschitz. -/
def fromCDDouble (u : CDDouble ZI) : Lipschitz := ⟨u.re, u.im⟩

theorem to_from (u : CDDouble ZI) : toCDDouble (fromCDDouble u) = u := by
  cases u; rfl

theorem from_to (u : Lipschitz) : fromCDDouble (toCDDouble u) = u := by
  cases u; rfl

theorem toCDDouble_inj {u v : Lipschitz}
    (h : toCDDouble u = toCDDouble v) : u = v := by
  have := congrArg fromCDDouble h
  rwa [from_to, from_to] at this

theorem toCDDouble_mul (u v : Lipschitz) :
    toCDDouble (u * v) = toCDDouble u * toCDDouble v := by
  apply CDDouble.ext
  · show (u * v).re = u.re * v.re + -(StarRing213.conj v.im * u.im)
    show u.re * v.re - ZI.conj v.im * u.im
       = u.re * v.re + -(StarRing213.conj v.im * u.im)
    rfl
  · show (u * v).im = v.im * u.re + u.im * StarRing213.conj v.re
    rfl

theorem toCDDouble_conj (u : Lipschitz) :
    toCDDouble (Lipschitz.conj u) = CDDouble.conj (toCDDouble u) := by
  apply CDDouble.ext
  · show ZI.conj u.re = StarRing213.conj u.re; rfl
  · show -u.im = -u.im; rfl

private theorem add_assoc' (u v w : Lipschitz) : u + v + w = u + (v + w) := by
  apply ext
  · exact Ring213.add_assoc u.re v.re w.re
  · exact Ring213.add_assoc u.im v.im w.im

private theorem add_comm' (u v : Lipschitz) : u + v = v + u := by
  apply ext
  · exact Ring213.add_comm u.re v.re
  · exact Ring213.add_comm u.im v.im

private theorem add_zero' (u : Lipschitz) : u + 0 = u := by
  apply ext
  · exact Ring213.add_zero u.re
  · exact Ring213.add_zero u.im

private theorem add_left_neg' (u : Lipschitz) : -u + u = 0 := by
  apply ext
  · exact Ring213.add_left_neg u.re
  · exact Ring213.add_left_neg u.im

/-- ∅-axiom: `conj` distributes over `+`.  Componentwise via ZI's
    `conj_add` and `Ring213.neg_add` (negation distributes over `+` is
    derived from `add_left_neg + add_assoc + add_comm`, but we use the
    componentwise approach here). -/
private theorem conj_add' (u v : Lipschitz) :
    conj (u + v) = conj u + conj v := by
  apply ext
  · -- (u + v).re.conj = u.re.conj + v.re.conj
    exact ZI.conj_add u.re v.re
  · -- -(u + v).im = -u.im + -v.im
    show -(u.im + v.im) = -u.im + -v.im
    -- For any Ring213 R, -(a + b) = -a + -b is provable from add_left_neg
    -- We'll rely on Lean unfolding componentwise using ZI's negation rules.
    -- Use: x + (-x) = 0 ↔ -(a+b) = -a + -b via uniqueness of inverse.
    -- ZI.neg_add (we have it via Int213.neg_add componentwise)
    apply ZI.ext
    · show -(u.im.re + v.im.re) = -u.im.re + -v.im.re
      exact E213.Meta.Int213.neg_add _ _
    · show -(u.im.im + v.im.im) = -u.im.im + -v.im.im
      exact E213.Meta.Int213.neg_add _ _


/-- ∅-axiom: `(u + v) * w = u * w + v * w` componentwise via ZI add_mul. -/
private theorem add_mul' (u v w : Lipschitz) : (u + v) * w = u * w + v * w := by
  apply ext
  · -- ((u+v)*w).re = (u+v).re * w.re - w.im.conj * (u+v).im
    --             = (u.re + v.re) * w.re - w.im.conj * (u.im + v.im)
    show (u.re + v.re) * w.re - w.im.conj * (u.im + v.im)
       = (u.re * w.re - w.im.conj * u.im) + (v.re * w.re - w.im.conj * v.im)
    rw [Ring213.add_mul u.re v.re w.re, Ring213.mul_add w.im.conj u.im v.im]
    -- Goal: u.re*w.re + v.re*w.re - (w.im.conj*u.im + w.im.conj*v.im)
    --     = (u.re*w.re - w.im.conj*u.im) + (v.re*w.re - w.im.conj*v.im)
    -- Convert subs to add+neg, distribute neg, reorder.
    show (u.re * w.re + v.re * w.re) + (-(w.im.conj * u.im + w.im.conj * v.im))
       = (u.re * w.re + (-(w.im.conj * u.im))) + (v.re * w.re + (-(w.im.conj * v.im)))
    -- Distribute the outer negation
    rw [show (-(w.im.conj * u.im + w.im.conj * v.im) : ZI)
            = (-(w.im.conj * u.im)) + (-(w.im.conj * v.im))
        from by
          apply ZI.ext
          · exact E213.Meta.Int213.neg_add _ _
          · exact E213.Meta.Int213.neg_add _ _]
    exact Ring213.add_4_swap_mid _ _ _ _
  · -- ((u+v)*w).im = (u+v).im * w.re.conj + w.im * (u+v).re ...
    -- Wait: Lipschitz.mul.im = v.im * u.re + u.im * v.re.conj
    -- So ((u+v)*w).im = w.im * (u+v).re + (u+v).im * w.re.conj
    --                = w.im * (u.re + v.re) + (u.im + v.im) * w.re.conj
    show w.im * (u.re + v.re) + (u.im + v.im) * w.re.conj
       = (w.im * u.re + u.im * w.re.conj) + (w.im * v.re + v.im * w.re.conj)
    rw [Ring213.mul_add w.im u.re v.re, Ring213.add_mul u.im v.im w.re.conj]
    -- Goal: w.im*u.re + w.im*v.re + (u.im*w.re.conj + v.im*w.re.conj)
    --     = w.im*u.re + u.im*w.re.conj + (w.im*v.re + v.im*w.re.conj)
    exact Ring213.add_4_swap_mid _ _ _ _


/-- ∅-axiom Lipschitz `mul_add`: `u * (v + w) = u * v + u * w`. -/
private theorem mul_add' (u v w : Lipschitz) : u * (v + w) = u * v + u * w := by
  apply ext
  · -- (u * (v + w)).re = u.re * (v + w).re - (v + w).im.conj * u.im
    --                 = u.re * (v.re + w.re) - (v.im + w.im).conj * u.im
    show u.re * (v.re + w.re) - (v.im + w.im).conj * u.im
       = (u.re * v.re - v.im.conj * u.im) + (u.re * w.re - w.im.conj * u.im)
    -- Distribute conj over +
    rw [conj_add (v.im) (w.im)]
    -- Goal: u.re * (v.re + w.re) - (v.im.conj + w.im.conj) * u.im = ...
    rw [Ring213.mul_add u.re v.re w.re, Ring213.add_mul v.im.conj w.im.conj u.im]
    show (u.re * v.re + u.re * w.re) + (-(v.im.conj * u.im + w.im.conj * u.im))
       = (u.re * v.re + (-(v.im.conj * u.im))) + (u.re * w.re + (-(w.im.conj * u.im)))
    rw [show (-(v.im.conj * u.im + w.im.conj * u.im) : ZI)
            = (-(v.im.conj * u.im)) + (-(w.im.conj * u.im))
        from by
          apply ZI.ext
          · exact E213.Meta.Int213.neg_add _ _
          · exact E213.Meta.Int213.neg_add _ _]
    exact Ring213.add_4_swap_mid _ _ _ _
  · -- (u * (v + w)).im = (v + w).im * u.re + u.im * (v + w).re.conj
    show (v.im + w.im) * u.re + u.im * (v.re + w.re).conj
       = (v.im * u.re + u.im * v.re.conj) + (w.im * u.re + u.im * w.re.conj)
    rw [conj_add v.re w.re,
        Ring213.add_mul v.im w.im u.re, Ring213.mul_add u.im v.re.conj w.re.conj]
    -- Goal: v.im*u.re + w.im*u.re + (u.im*v.re.conj + u.im*w.re.conj)
    --     = (v.im*u.re + u.im*v.re.conj) + (w.im*u.re + u.im*w.re.conj)
    exact Ring213.add_4_swap_mid _ _ _ _


/-- Helper: `ZI.conj 0 = 0`. -/
private theorem conj_zero_zi : ZI.conj (0 : ZI) = 0 := by
  apply ZI.ext
  · show (0 : Int) = 0; rfl
  · show -(0 : Int) = 0; exact Int.neg_zero

/-- Helper: `ZI.conj (ZI.ofInt z) = ZI.ofInt z` (real elements are
    fixed by conjugation). -/
private theorem conj_ofInt_zi (z : Int) :
    ZI.conj (ZI.ofInt z) = ZI.ofInt z := by
  apply ZI.ext
  · show z = z; rfl
  · show -(0 : Int) = 0; exact Int.neg_zero

/-- ★ Bridge-based `ofInt_mul`: derive from abstract
    `IntegerNormed213 (CDDouble ZI)` via `toCDDouble`.  Replaces a
    ~18-line proof with a 5-line bridge projection. -/
private theorem ofInt_mul' (a b : Int) :
    ofInt a * ofInt b = ofInt (a * b) := by
  apply toCDDouble_inj
  rw [toCDDouble_mul]
  show toCDDouble (ofInt a) * toCDDouble (ofInt b) = toCDDouble (ofInt (a * b))
  exact @IntegerNormed213.ofInt_mul (CDDouble ZI) _ a b

/-- ∅-axiom: `ofInt_inj`. -/
private theorem ofInt_inj' {a b : Int} (h : ofInt a = ofInt b) : a = b := by
  have h_re : ZI.ofInt a = ZI.ofInt b := congrArg Lipschitz.re h
  have h_int : a = b := congrArg ZI.re h_re
  exact h_int


/-- ★ Bridge-based Lipschitz `self_mul_conj`: derive from abstract
    `IntegerNormed213 (CDDouble ZI)` via `toCDDouble`.  Replaces a
    ~35-line hand-written proof with a 5-line bridge projection. -/
private theorem self_mul_conj' (z : Lipschitz) :
    z * conj z = ofInt (Lipschitz.normSq z) := by
  apply toCDDouble_inj
  rw [toCDDouble_mul, toCDDouble_conj]
  show toCDDouble z * CDDouble.conj (toCDDouble z)
     = toCDDouble (ofInt (Lipschitz.normSq z))
  exact @IntegerNormed213.self_mul_conj (CDDouble ZI) _ (toCDDouble z)


/-- ★ Bridge-based `ofInt_central`: derive from abstract
    `IntegerNormed213 (CDDouble ZI)` via `toCDDouble`.  Replaces a
    ~22-line proof with a 5-line bridge projection. -/
private theorem ofInt_central' (z : Int) (a : Lipschitz) :
    ofInt z * a = a * ofInt z := by
  apply toCDDouble_inj
  rw [toCDDouble_mul, toCDDouble_mul]
  show toCDDouble (ofInt z) * toCDDouble a = toCDDouble a * toCDDouble (ofInt z)
  exact @IntegerNormed213.ofInt_central (CDDouble ZI) _ z (toCDDouble a)


/-- Generic Ring213 4-term cycle helper: `A + B + C + D = A + C + D + B`. -/
private theorem add_4_cycle {α : Type} [Ring213 α] (A B C D : α) :
    A + B + C + D = A + C + D + B := by
  rw [Ring213.add_right_comm A B C, Ring213.add_right_comm (A + C) B D]

/-- ★ ∅-axiom Lipschitz `mul_assoc.re`.  No Int polynomial — uses
    ZI ring axioms (mul_assoc, mul_comm, add_mul, mul_add, neg_mul,
    mul_neg, neg_add, add_4_cycle) only. -/
private theorem mul_assoc_re' (u v w : Lipschitz) :
    ((u * v) * w).re = (u * (v * w)).re := by
  show (u.re * v.re + -(v.im.conj * u.im)) * w.re
       + -(w.im.conj * (v.im * u.re + u.im * v.re.conj))
     = u.re * (v.re * w.re + -(w.im.conj * v.im))
       + -((w.im * v.re + v.im * w.re.conj).conj * u.im)
  rw [ZI.conj_add (w.im * v.re) (v.im * w.re.conj),
      ZI.conj_mul w.im v.re, ZI.conj_mul v.im w.re.conj, ZI.conj_conj w.re]
  rw [@Ring213.add_mul ZI _ (u.re * v.re) (-(v.im.conj * u.im)) w.re,
      @Ring213.mul_add ZI _ w.im.conj (v.im * u.re) (u.im * v.re.conj),
      @Ring213.mul_add ZI _ u.re (v.re * w.re) (-(w.im.conj * v.im)),
      @Ring213.add_mul ZI _ (w.im.conj * v.re.conj) (v.im.conj * w.re) u.im]
  rw [@Ring213.neg_add ZI _ (w.im.conj * (v.im * u.re)) (w.im.conj * (u.im * v.re.conj)),
      @Ring213.neg_add ZI _ (w.im.conj * v.re.conj * u.im) (v.im.conj * w.re * u.im)]
  rw [@Ring213.neg_mul ZI _ (v.im.conj * u.im) w.re,
      @Ring213.mul_neg ZI _ u.re (w.im.conj * v.im)]
  rw [@Ring213.mul_assoc ZI _ u.re v.re w.re]
  rw [show v.im.conj * u.im * w.re = v.im.conj * w.re * u.im
      from by rw [@Ring213.mul_assoc ZI _ v.im.conj u.im w.re,
                  @CommRing213.mul_comm ZI _ u.im w.re,
                  ← @Ring213.mul_assoc ZI _ v.im.conj w.re u.im]]
  rw [show w.im.conj * (v.im * u.re) = u.re * (w.im.conj * v.im)
      from by rw [← @Ring213.mul_assoc ZI _ w.im.conj v.im u.re,
                  @CommRing213.mul_comm ZI _ (w.im.conj * v.im) u.re]]
  rw [show w.im.conj * (u.im * v.re.conj) = w.im.conj * v.re.conj * u.im
      from by rw [@CommRing213.mul_comm ZI _ u.im v.re.conj,
                  ← @Ring213.mul_assoc ZI _ w.im.conj v.re.conj u.im]]
  rw [← @Ring213.add_assoc ZI _ (u.re * (v.re * w.re) + -(v.im.conj * w.re * u.im))
        (-(u.re * (w.im.conj * v.im))) (-(w.im.conj * v.re.conj * u.im))]
  rw [← @Ring213.add_assoc ZI _ (u.re * (v.re * w.re) + -(u.re * (w.im.conj * v.im)))
        (-(w.im.conj * v.re.conj * u.im)) (-(v.im.conj * w.re * u.im))]
  exact add_4_cycle _ _ _ _


/-- ★ ∅-axiom Lipschitz `mul_assoc.im`.  Same pattern as .re. -/
private theorem mul_assoc_im' (u v w : Lipschitz) :
    ((u * v) * w).im = (u * (v * w)).im := by
  show w.im * (u.re * v.re + -(v.im.conj * u.im))
       + (v.im * u.re + u.im * v.re.conj) * w.re.conj
     = (w.im * v.re + v.im * w.re.conj) * u.re
       + u.im * (v.re * w.re + -(w.im.conj * v.im)).conj
  rw [ZI.conj_add (v.re * w.re) (-(w.im.conj * v.im)),
      ZI.conj_mul v.re w.re, ZI.conj_neg (w.im.conj * v.im),
      ZI.conj_mul w.im.conj v.im, ZI.conj_conj w.im]
  rw [@Ring213.mul_add ZI _ w.im (u.re * v.re) (-(v.im.conj * u.im)),
      @Ring213.add_mul ZI _ (v.im * u.re) (u.im * v.re.conj) w.re.conj,
      @Ring213.add_mul ZI _ (w.im * v.re) (v.im * w.re.conj) u.re,
      @Ring213.mul_add ZI _ u.im (v.re.conj * w.re.conj) (-(w.im * v.im.conj))]
  rw [@Ring213.mul_neg ZI _ w.im (v.im.conj * u.im),
      @Ring213.mul_neg ZI _ u.im (w.im * v.im.conj)]
  rw [show w.im * (u.re * v.re) = w.im * v.re * u.re
      from by rw [@CommRing213.mul_comm ZI _ u.re v.re,
                  ← @Ring213.mul_assoc ZI _ w.im v.re u.re]]
  rw [show w.im * (v.im.conj * u.im) = u.im * (w.im * v.im.conj)
      from by rw [← @Ring213.mul_assoc ZI _ w.im v.im.conj u.im,
                  @CommRing213.mul_comm ZI _ (w.im * v.im.conj) u.im]]
  rw [show v.im * u.re * w.re.conj = v.im * w.re.conj * u.re
      from by rw [@Ring213.mul_assoc ZI _ v.im u.re w.re.conj,
                  @CommRing213.mul_comm ZI _ u.re w.re.conj,
                  ← @Ring213.mul_assoc ZI _ v.im w.re.conj u.re]]
  rw [@Ring213.mul_assoc ZI _ u.im v.re.conj w.re.conj]
  rw [← @Ring213.add_assoc ZI _ (w.im * v.re * u.re + -(u.im * (w.im * v.im.conj)))
        (v.im * w.re.conj * u.re) (u.im * (v.re.conj * w.re.conj))]
  rw [@add_4_cycle ZI _ (w.im * v.re * u.re) (-(u.im * (w.im * v.im.conj)))
        (v.im * w.re.conj * u.re) (u.im * (v.re.conj * w.re.conj))]
  rw [@Ring213.add_assoc ZI _ (w.im * v.re * u.re + v.im * w.re.conj * u.re)
        (u.im * (v.re.conj * w.re.conj)) (-(u.im * (w.im * v.im.conj)))]

/-- ★★★★★★★ ∅-axiom Lipschitz `mul_assoc`. -/
private theorem mul_assoc' (u v w : Lipschitz) :
    (u * v) * w = u * (v * w) := by
  apply ext
  · exact mul_assoc_re' u v w
  · exact mul_assoc_im' u v w


/-- ★ Lipschitz `Ring213` instance — all axioms PURE via ZI projections. -/
instance : Ring213 Lipschitz where
  add_assoc    := add_assoc'
  add_comm     := add_comm'
  add_zero     := add_zero'
  add_left_neg := add_left_neg'
  mul_assoc    := mul_assoc'
  add_mul      := add_mul'
  mul_add      := mul_add'

/-- ★ Lipschitz `StarRing213` instance.  NOT a CommRing213 — Lipschitz
    multiplication is non-commutative.  Conjugation is anti-distributive. -/
instance : StarRing213 Lipschitz where
  conj      := conj
  conj_conj := conj_conj
  conj_add  := conj_add'
  conj_mul  := conj_mul_anti

/-- `ZI.normSq (-x) = ZI.normSq x` — ZI norm is neg-invariant.
    Direct via `(-y)·(-y) = y·y` componentwise. -/
private theorem zi_normSq_neg (x : ZI) : ZI.normSq (-x) = ZI.normSq x := by
  show (-x.re) * (-x.re) + (-x.im) * (-x.im) = x.re * x.re + x.im * x.im
  rw [E213.Meta.Int213.neg_mul x.re (-x.re),
      E213.Meta.Int213.mul_neg x.re x.re, Int.neg_neg,
      E213.Meta.Int213.neg_mul x.im (-x.im),
      E213.Meta.Int213.mul_neg x.im x.im, Int.neg_neg]

/-- `ZI.normSq (conj x) = ZI.normSq x` — same pattern as
    `zi_normSq_neg`.  Componentwise direct expansion. -/
private theorem zi_normSq_conj (x : ZI) : ZI.normSq (ZI.conj x) = ZI.normSq x := by
  show x.re * x.re + (-x.im) * (-x.im) = x.re * x.re + x.im * x.im
  rw [E213.Meta.Int213.neg_mul x.im (-x.im),
      E213.Meta.Int213.mul_neg x.im x.im, Int.neg_neg]

/-- `normSq (conj u) = normSq u` for Lipschitz.  Componentwise via
    ZI's `zi_normSq_conj` (the underlying re component) + `zi_normSq_neg`
    (the underlying im is negated). -/
private theorem normSq_conj' (u : Lipschitz) :
    normSq (Lipschitz.conj u) = normSq u := by
  show (u.re.conj).normSq + (-u.im).normSq = u.re.normSq + u.im.normSq
  rw [zi_normSq_conj u.re, zi_normSq_neg u.im]

/-- ★ Lipschitz `IntegerNormed213` instance.  All fields PURE via
    ZI ring axioms — no Int polynomial expansion at this layer. -/
instance : IntegerNormed213 Lipschitz where
  ofInt         := ofInt
  normSq        := normSq
  self_mul_conj := self_mul_conj'
  ofInt_mul     := ofInt_mul'
  normSq_conj   := normSq_conj'
  ofInt_add     := by
    intro a b
    apply ext
    · show ZI.ofInt a + ZI.ofInt b = ZI.ofInt (a + b)
      exact @IntegerNormed213.ofInt_add ZI _ a b
    · show (0 : ZI) + 0 = 0
      apply ZI.ext
      · show (0 : Int) + 0 = 0; rfl
      · show (0 : Int) + 0 = 0; rfl
  ofInt_central := ofInt_central'
  ofInt_inj     := ofInt_inj'
  ofInt_conj    := by
    intro z
    apply ext
    · show ZI.conj (ZI.ofInt z) = ZI.ofInt z
      exact @IntegerNormed213.ofInt_conj ZI _ z
    · show -(0 : ZI) = 0
      apply ZI.ext
      · show -(0 : Int) = 0; exact Int.neg_zero
      · show -(0 : Int) = 0; exact Int.neg_zero

/-- Quaternion-trace polarization on Lipschitz: `a + conj a` lands in
    the central `ofInt` image (`2·re` on the inner ZI real axis).  This
    is the `TraceNormed213` companion of `self_mul_conj`, supplying the
    polarization condition the Cayley (octonion) Moufang norm-collapse
    needs — see `Meta/Algebra213/CDDoubleMoufang.lean`. -/
instance : TraceNormed213 Lipschitz where
  trace a := a.re.re + a.re.re
  self_add_conj a := by
    apply ext
    · apply ZI.ext
      · rfl
      · exact E213.Meta.Int213.add_neg_cancel a.re.im
    · apply ZI.ext
      · exact E213.Meta.Int213.add_neg_cancel a.im.re
      · exact E213.Meta.Int213.add_neg_cancel a.im.im

end E213.Lib.Math.Algebra.CayleyDickson.Tower.CDDouble.Lipschitz
