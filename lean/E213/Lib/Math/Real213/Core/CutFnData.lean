import E213.Lib.Math.Real213.Bisection.CutContinuity
import E213.Lib.Math.Real213.Bisection.CutBisection
import E213.Lib.Math.Real213.Mul.CutMulDetermined
import E213.Lib.Math.Real213.Mul.CutMulOuterReduce
import E213.Lib.Math.Real213.Mul.CutPow
import E213.Meta.Nat.Max213

import E213.Lib.Math.Real213.Mul.CutMul
import E213.Lib.Math.Real213.Sum.CutSumTest
/-!
# CutFnData: data-bearing local determinedness

*Data* form of `isLocallyDetermined` — cut function counterpart of
Bishop modulus.  The existence-only form requires Classical.choose during
composition.  The data form allows axiom-free composition.

## Definition

```
structure LocallyDeterminedData (f : CutFunction) where
  N : Nat → Nat → Nat
  prop : f's value at (m, k) determined by cx at ≤ N m k.
```
-/

namespace E213.Lib.Math.Real213.Core.CutFnData

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Bisection.CutContinuity (constCutFn)

/-- **LocallyDeterminedData**: explicit modulus carried as data. -/
structure LocallyDeterminedData (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) where
  N : Nat → Nat → Nat
  prop : ∀ m k, ∀ cx cy : Nat → Nat → Bool,
    (∀ m' k', m' ≤ N m k → k' ≤ N m k → cx m' k' = cy m' k') →
    f cx m k = f cy m k

/-- LocallyDeterminedData for identity.  ∅-axiom:
    `Max213.le_max_left/right` (Lean-core variants leak propext). -/
def idLDD : LocallyDeterminedData id where
  N := fun m k => max m k
  prop := by
    intro m k cx cy h
    exact h m k (E213.Meta.Nat.Max213.le_max_left _ _)
                (E213.Meta.Nat.Max213.le_max_right _ _)

/-- LocallyDeterminedData for const. -/
def constLDD (c : Nat → Nat → Bool) : LocallyDeterminedData (constCutFn c) where
  N := fun _ _ => 0
  prop := fun _ _ _ _ _ => rfl

open E213.Theory E213.Lens

/-- Max over j ∈ [0, K] of f i j. -/
def maxRangeRow (f : Nat → Nat → Nat) (i : Nat) : Nat → Nat
  | 0 => f i 0
  | k+1 => max (f i (k+1)) (maxRangeRow f i k)

/-- Max over (i, j) ∈ [0, M] × [0, K]. -/
def maxRange (f : Nat → Nat → Nat) (M K : Nat) : Nat :=
  match M with
  | 0 => maxRangeRow f 0 K
  | M+1 => max (maxRangeRow f (M+1) K) (maxRange f M K)

/-- Upper bound property of maxRangeRow. -/
theorem maxRangeRow_ge (f : Nat → Nat → Nat) (i K j : Nat) (hj : j ≤ K) :
    f i j ≤ maxRangeRow f i K := by
  induction K with
  | zero =>
    have : j = 0 := Nat.le_zero.mp hj
    subst this
    exact Nat.le_refl _
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hj with heq | hlt
    · subst heq
      show f i (k+1) ≤ max (f i (k+1)) (maxRangeRow f i k)
      exact E213.Meta.Nat.Max213.le_max_left _ _
    · have hjk : j ≤ k := Nat.lt_succ_iff.mp hlt
      show f i j ≤ max (f i (k+1)) (maxRangeRow f i k)
      exact Nat.le_trans (ih hjk) (E213.Meta.Nat.Max213.le_max_right _ _)

/-- Upper bound property of maxRange. -/
theorem maxRange_ge (f : Nat → Nat → Nat) (M K i j : Nat)
    (hi : i ≤ M) (hj : j ≤ K) : f i j ≤ maxRange f M K := by
  induction M with
  | zero =>
    have : i = 0 := Nat.le_zero.mp hi
    subst this
    show f 0 j ≤ maxRangeRow f 0 K
    exact maxRangeRow_ge f 0 K j hj
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hi with heq | hlt
    · subst heq
      show f (k+1) j ≤ max (maxRangeRow f (k+1) K) (maxRange f k K)
      exact Nat.le_trans (maxRangeRow_ge f (k+1) K j hj) (E213.Meta.Nat.Max213.le_max_left _ _)
    · have hik : i ≤ k := Nat.lt_succ_iff.mp hlt
      show f i j ≤ max (maxRangeRow f (k+1) K) (maxRange f k K)
      exact Nat.le_trans (ih hik) (E213.Meta.Nat.Max213.le_max_right _ _)

open E213.Theory E213.Lens

/-- **LDD composition closure**: f ∘ g is LDD if both f and g are LDD. -/
def composeLDD {f g : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (lf : LocallyDeterminedData f) (lg : LocallyDeterminedData g) :
    LocallyDeterminedData (f ∘ g) where
  N := fun m k => maxRange lg.N (lf.N m k) (lf.N m k)
  prop := by
    intro m k cx cy hagree
    show f (g cx) m k = f (g cy) m k
    apply lf.prop
    intro m' k' hm' hk'
    apply lg.prop
    intro m'' k'' hm'' hk''
    apply hagree
    · exact Nat.le_trans hm''
        (maxRange_ge lg.N (lf.N m k) (lf.N m k) m' k' hm' hk')
    · exact Nat.le_trans hk''
        (maxRange_ge lg.N (lf.N m k) (lf.N m k) m' k' hm' hk')

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Bisection.CutBisection (cutHalf)

/-- LocallyDeterminedData for cutHalf. -/
def cutHalfLDD : LocallyDeterminedData cutHalf where
  N := fun m k => max (2*m) k
  prop := by
    intro m k cx cy h
    show cx (2*m) k = cy (2*m) k
    exact h (2*m) k (E213.Meta.Nat.Max213.le_max_left _ _) (E213.Meta.Nat.Max213.le_max_right _ _)

open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Mul.CutMulDetermined (cutMulOuter_congr)
open E213.Lib.Math.Real213.Mul.CutMul (cutMul cutMulOuter)
open E213.Lib.Math.Real213.Mul.CutPow (cutScale)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)

/-- LocallyDeterminedData for cutScale a b (via cutMul_locallyDetermined).
    G110 FLUX-1 template (upstream variant). -/
def cutScaleLDD (a b : Nat) : LocallyDeterminedData (cutScale a b) where
  N := fun m k => (m + 1) * (k + 1)
  prop := by
    intro m k cx cy h
    show cutMul (constCut a b) cx m k = cutMul (constCut a b) cy m k
    show cutMulOuter (constCut a b) cx k m ((m+1)*(k+1)) ((m+1)*(k+1))
        = cutMulOuter (constCut a b) cy k m ((m+1)*(k+1)) ((m+1)*(k+1))
    have hk_le : k ≤ (m + 1) * (k + 1) :=
      Nat.le_trans (Nat.le_succ k)
        (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))
    exact E213.Lib.Math.Real213.Mul.CutMulOuterReduce.cutMulOuter_reduce_at
      (constCut a b) cx (constCut a b) cy m k ((m+1)*(k+1))
      (fun _ _ => rfl) (fun m' hm' => h m' k hm' hk_le)

/-- ★ Generic LDD branch helper (G107 §4 L4).  Extracts the recurring
    `apply sf.prop; intro m'' k'' hm'' hk''; apply hagree; <chain>` block
    from binary LDD proofs (addLDD, mulLDD).  PURE.

    Given: agreement `hagree` of `cx` and `cy` up to bound `M`,
    a `LocallyDeterminedData` `sf`, search bounds `S R`, and a
    `side_chain` proof that `maxRange sf.N S R ≤ M`.  Concludes
    `f cx m' R = f cy m' R` for any `m' ≤ maxRange sf.N S R`. -/
theorem ldd_branch_via_maxRange
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (sf : LocallyDeterminedData f) (cx cy : Nat → Nat → Bool) (M : Nat)
    (hagree : ∀ m' k', m' ≤ M → k' ≤ M → cx m' k' = cy m' k')
    (S R : Nat) (side_chain : maxRange sf.N S R ≤ M)
    (m' : Nat) (hm' : m' ≤ S) :
    f cx m' R = f cy m' R := by
  apply sf.prop
  intro m'' k'' hm'' hk''
  apply hagree
  · exact Nat.le_trans hm''
      (Nat.le_trans (maxRange_ge sf.N S R m' R hm' (Nat.le_refl _)) side_chain)
  · exact Nat.le_trans hk''
      (Nat.le_trans (maxRange_ge sf.N S R m' R hm' (Nat.le_refl _)) side_chain)

end E213.Lib.Math.Real213.Core.CutFnData
