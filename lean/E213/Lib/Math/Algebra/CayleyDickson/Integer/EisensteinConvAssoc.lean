import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvAssocIndex
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussShift

/-!
# Convolution is associative — `(f ⋆ g) ⋆ h = f ⋆ (g ⋆ h)` (∅-axiom, Phase A3 / route b)

In the group ring `R[C_p]`, convolution is associative (coefficientwise, for `k < p`):

  `((f ⋆ g) ⋆ h)(k) = (f ⋆ (g ⋆ h))(k)`   (`conv_assoc`).

Distribute the inner sum (`sum_mul_right`), swap the order of summation (`sum_swap`), then reindex the
inner `j`-sum by `j = (l+i)%p` (`rangeList_add_lperm`): the `g`-index collapses (`add_shift_index`) and
the `h`-index re-associates (`conv_assoc_index`).  With commutativity (`conv_comm`) this lets
`(g·ḡ)² = (g·g)·(ḡ·ḡ)`, the reassociation behind `N(J)=p`.  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvAssoc

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing (conv)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum
  (sumRange sum_congr sum_mul_left sum_mul_right sum_swap)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinListSum
  (listSum listSum_congr listSum_map listSum_lperm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeSum
  (sumRange_eq_listSum rangeList_add_lperm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussShift (add_shift_index)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvAssocIndex (conv_assoc_index)
open E213.Lib.Math.Combinatorics.RangeList (rangeList mem_rangeList)
open E213.Meta.Algebra213.Ring213 (mul_assoc)

/-- The inner `j`-sum reindexes to `f i · (g ⋆ h)((k+p−i)%p)` (`i < p`, `k < p`). -/
private theorem assoc_inner (p : Nat) (f g h : Nat → ZOmega) {i k : Nat} (hp : 0 < p)
    (hi : i < p) :
    sumRange (fun j => f i * g ((j + p - i) % p) * h ((k + p - j) % p)) p
      = f i * conv p g h ((k + p - i) % p) := by
  -- reassociate the product, pull `f i` out
  rw [sum_congr p (fun j _ => mul_assoc (f i) (g ((j + p - i) % p)) (h ((k + p - j) % p))),
      sum_mul_left (f i) (fun j => g ((j + p - i) % p) * h ((k + p - j) % p)) p]
  congr 1
  -- reindex the remaining sum `j = (l+i)%p`
  show sumRange (fun j => g ((j + p - i) % p) * h ((k + p - j) % p)) p
     = sumRange (fun l => g l * h (((k + p - i) % p + p - l) % p)) p
  rw [sumRange_eq_listSum, listSum_lperm _ (rangeList_add_lperm hp (Nat.le_of_lt hi)),
      listSum_map (fun j => g ((j + p - i) % p) * h ((k + p - j) % p)) (fun l => (l + i) % p)
        (rangeList p),
      ← sumRange_eq_listSum]
  refine sum_congr p (fun l hl => ?_)
  show g (((l + i) % p + p - i) % p) * h ((k + p - (l + i) % p) % p)
     = g l * h (((k + p - i) % p + p - l) % p)
  rw [add_shift_index hp (Nat.le_of_lt hi) hl, conv_assoc_index hp hi hl]

/-- ★★★★★ **Convolution is associative** — `((f ⋆ g) ⋆ h)(k) = (f ⋆ (g ⋆ h))(k)` for `k < p`.
    Distribute + `sum_swap` + reindex (`add_shift_index`, `conv_assoc_index`).  ∅-axiom. -/
theorem conv_assoc (p : Nat) (f g h : Nat → ZOmega) {k : Nat} (hk : k < p) :
    conv p (fun j => conv p f g j) h k = conv p f (fun j => conv p g h j) k := by
  have hp : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  show sumRange (fun j => (sumRange (fun i => f i * g ((j + p - i) % p)) p) * h ((k + p - j) % p)) p
     = sumRange (fun i => f i * conv p g h ((k + p - i) % p)) p
  rw [sum_congr p (fun j _ =>
        (sum_mul_right (h ((k + p - j) % p)) (fun i => f i * g ((j + p - i) % p)) p).symm),
      sum_swap (fun i j => f i * g ((j + p - i) % p) * h ((k + p - j) % p)) p p]
  exact sum_congr p (fun i hi => assoc_inner p f g h hp hi)

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvAssoc
