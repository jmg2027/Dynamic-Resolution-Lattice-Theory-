import E213.Lib.Math.CayleyDickson.CDDouble
import E213.Lib.Math.CayleyDickson.ZIAlgebra213
import E213.Theory.Internal.Algebra213
import E213.Theory.Internal.Int213

/-!
# `Lipschitz` as an `IntegerNormed213` instance

Hierarchical-modular CD layer 1.  Ring axioms reduce to ZI's PURE
ring axioms — no Int polynomial expansion at this layer.
-/

namespace E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz

open E213.Lib.Math.CayleyDickson.ZI
open E213.Lib.Math.CayleyDickson.ZI.ZI
open E213.Theory.Internal.Algebra213

/-- `ofInt n = ⟨ZI.ofInt n, 0⟩`. -/
def ofInt (n : Int) : Lipschitz := ⟨ZI.ZI.ofInt n, 0⟩

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
    exact ZI.ZI.conj_add u.re v.re
  · -- -(u + v).im = -u.im + -v.im
    show -(u.im + v.im) = -u.im + -v.im
    -- For any Ring213 R, -(a + b) = -a + -b is provable from add_left_neg
    -- We'll rely on Lean unfolding componentwise using ZI's negation rules.
    -- Use: x + (-x) = 0 ↔ -(a+b) = -a + -b via uniqueness of inverse.
    -- ZI.neg_add (we have it via Int213.neg_add componentwise)
    apply ZI.ZI.ext
    · show -(u.im.re + v.im.re) = -u.im.re + -v.im.re
      exact E213.Theory.Internal.Int213.neg_add _ _
    · show -(u.im.im + v.im.im) = -u.im.im + -v.im.im
      exact E213.Theory.Internal.Int213.neg_add _ _

end E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz

namespace E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz

open E213.Lib.Math.CayleyDickson.ZI
open E213.Lib.Math.CayleyDickson.ZI.ZI
open E213.Theory.Internal.Algebra213

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
          apply ZI.ZI.ext
          · exact E213.Theory.Internal.Int213.neg_add _ _
          · exact E213.Theory.Internal.Int213.neg_add _ _]
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

end E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz

namespace E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz

open E213.Lib.Math.CayleyDickson.ZI
open E213.Lib.Math.CayleyDickson.ZI.ZI
open E213.Theory.Internal.Algebra213

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
          apply ZI.ZI.ext
          · exact E213.Theory.Internal.Int213.neg_add _ _
          · exact E213.Theory.Internal.Int213.neg_add _ _]
    exact Ring213.add_4_swap_mid _ _ _ _
  · -- (u * (v + w)).im = (v + w).im * u.re + u.im * (v + w).re.conj
    show (v.im + w.im) * u.re + u.im * (v.re + w.re).conj
       = (v.im * u.re + u.im * v.re.conj) + (w.im * u.re + u.im * w.re.conj)
    rw [conj_add v.re w.re,
        Ring213.add_mul v.im w.im u.re, Ring213.mul_add u.im v.re.conj w.re.conj]
    -- Goal: v.im*u.re + w.im*u.re + (u.im*v.re.conj + u.im*w.re.conj)
    --     = (v.im*u.re + u.im*v.re.conj) + (w.im*u.re + u.im*w.re.conj)
    exact Ring213.add_4_swap_mid _ _ _ _

end E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz

namespace E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz

open E213.Lib.Math.CayleyDickson.ZI
open E213.Lib.Math.CayleyDickson.ZI.ZI
open E213.Theory.Internal.Algebra213

/-- Helper: `ZI.conj 0 = 0`. -/
private theorem conj_zero_zi : ZI.conj (0 : ZI) = 0 := by
  apply ZI.ZI.ext
  · show (0 : Int) = 0; rfl
  · show -(0 : Int) = 0; exact Int.neg_zero

/-- Helper: `ZI.conj (ZI.ofInt z) = ZI.ofInt z` (real elements are
    fixed by conjugation). -/
private theorem conj_ofInt_zi (z : Int) :
    ZI.conj (ZI.ZI.ofInt z) = ZI.ZI.ofInt z := by
  apply ZI.ZI.ext
  · show z = z; rfl
  · show -(0 : Int) = 0; exact Int.neg_zero

/-- ∅-axiom: `ofInt a * ofInt b = ofInt (a * b)` for Lipschitz. -/
private theorem ofInt_mul' (a b : Int) :
    ofInt a * ofInt b = ofInt (a * b) := by
  apply ext
  · show ZI.ZI.ofInt a * ZI.ZI.ofInt b - ZI.conj 0 * 0 = ZI.ZI.ofInt (a * b)
    rw [conj_zero_zi, Ring213.zero_mul]
    -- Goal: ZI.ofInt a * ZI.ofInt b - 0 = ZI.ofInt (a * b)
    rw [show ((ZI.ZI.ofInt a * ZI.ZI.ofInt b - 0 : ZI))
            = ZI.ZI.ofInt a * ZI.ZI.ofInt b
        from by
          show ZI.ZI.ofInt a * ZI.ZI.ofInt b + (-0 : ZI) = _
          rw [show (-0 : ZI) = 0 from by
                apply ZI.ZI.ext
                · show -(0 : Int) = 0; exact Int.neg_zero
                · show -(0 : Int) = 0; exact Int.neg_zero]
          exact Ring213.add_zero _]
    exact IntegerNormed213.ofInt_mul a b
  · show 0 * ZI.ZI.ofInt a + 0 * (ZI.ZI.ofInt b).conj = 0
    rw [conj_ofInt_zi b, Ring213.zero_mul, Ring213.zero_mul, Ring213.add_zero]

/-- ∅-axiom: `ofInt_inj`. -/
private theorem ofInt_inj' {a b : Int} (h : ofInt a = ofInt b) : a = b := by
  have h_re : ZI.ZI.ofInt a = ZI.ZI.ofInt b := congrArg Lipschitz.re h
  have h_int : a = b := congrArg ZI.re h_re
  exact h_int

end E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz

namespace E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz

open E213.Lib.Math.CayleyDickson.ZI
open E213.Lib.Math.CayleyDickson.ZI.ZI
open E213.Theory.Internal.Algebra213

/-- ★ ∅-axiom Lipschitz `self_mul_conj`: `z * conj z = ofInt z.normSq`.
    Uses ZI's `IntegerNormed213.self_mul_conj` recursively + ZI mul_comm
    (since ZI is commutative).  No Int polynomial expansion. -/
private theorem self_mul_conj' (z : Lipschitz) :
    z * conj z = ofInt (Lipschitz.normSq z) := by
  apply ext
  · -- re: z.re * z.re.conj - (-z.im).conj * z.im
    show z.re * z.re.conj - (-z.im).conj * z.im
       = ZI.ZI.ofInt (z.re.normSq + z.im.normSq)
    -- conj_neg: (-z.im).conj = -(z.im.conj)
    rw [ZI.ZI.conj_neg z.im]
    -- (-z.im.conj) * z.im = -(z.im.conj * z.im)  [Ring213.neg_mul at ZI level]
    rw [Ring213.neg_mul z.im.conj z.im]
    -- a - (-b) = a + b via sub_eq_add_neg + neg_neg
    show z.re * z.re.conj + (-(-(z.im.conj * z.im)))
       = ZI.ZI.ofInt (z.re.normSq + z.im.normSq)
    rw [Ring213.neg_neg (z.im.conj * z.im)]
    -- Goal: z.re * z.re.conj + z.im.conj * z.im = ofInt (...)
    -- ZI.conj is the concrete .conj here, but typeclass uses StarRing213.conj.
    -- They coincide via the instance.  Convert via `have`:
    have hre : z.re * z.re.conj = ZI.ZI.ofInt z.re.normSq :=
      @IntegerNormed213.self_mul_conj ZI _ z.re
    have him : z.im * z.im.conj = ZI.ZI.ofInt z.im.normSq :=
      @IntegerNormed213.self_mul_conj ZI _ z.im
    have hmc : z.im.conj * z.im = z.im * z.im.conj :=
      @CommRing213.mul_comm ZI _ z.im.conj z.im
    rw [hre, hmc, him]
    exact @IntegerNormed213.ofInt_add ZI _ z.re.normSq z.im.normSq
  · -- im: -z.im * z.re + z.im * z.re.conj.conj
    show -z.im * z.re + z.im * z.re.conj.conj = 0
    rw [ZI.ZI.conj_conj z.re]
    -- Goal: -z.im * z.re + z.im * z.re = 0
    rw [Ring213.neg_mul z.im z.re]
    -- Goal: -(z.im * z.re) + z.im * z.re = 0
    exact Ring213.add_left_neg _

end E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz

namespace E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz

open E213.Lib.Math.CayleyDickson.ZI
open E213.Lib.Math.CayleyDickson.ZI.ZI
open E213.Theory.Internal.Algebra213

/-- ∅-axiom Lipschitz `ofInt_central`: ofInt z commutes with all a. -/
private theorem ofInt_central' (z : Int) (a : Lipschitz) :
    ofInt z * a = a * ofInt z := by
  apply ext
  · -- LHS .re: (ZI.ofInt z) * a.re - a.im.conj * 0
    -- RHS .re: a.re * (ZI.ofInt z) - (ZI.conj 0) * a.im
    show ZI.ZI.ofInt z * a.re - a.im.conj * 0
       = a.re * ZI.ZI.ofInt z - ZI.conj 0 * a.im
    rw [conj_zero_zi]
    rw [Ring213.mul_zero (a.im.conj : ZI), Ring213.zero_mul (a.im : ZI)]
    -- Goal: ZI.ofInt z * a.re - 0 = a.re * ZI.ofInt z - 0
    show ZI.ZI.ofInt z * a.re + (-(0 : ZI))
       = a.re * ZI.ZI.ofInt z + (-(0 : ZI))
    rw [show (-(0 : ZI)) = 0 from by
          apply ZI.ZI.ext
          · show -(0 : Int) = 0; exact Int.neg_zero
          · show -(0 : Int) = 0; exact Int.neg_zero,
        Ring213.add_zero, Ring213.add_zero]
    exact @CommRing213.mul_comm ZI _ _ _
  · -- LHS .im: a.im * (ZI.ofInt z) + 0 * a.re.conj
    -- RHS .im: 0 * a.re + a.im * (ZI.ofInt z).conj
    show a.im * ZI.ZI.ofInt z + 0 * a.re.conj
       = 0 * a.re + a.im * (ZI.ZI.ofInt z).conj
    rw [conj_ofInt_zi z, Ring213.zero_mul, Ring213.zero_mul,
        Ring213.add_zero, Ring213.zero_add]

end E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz
