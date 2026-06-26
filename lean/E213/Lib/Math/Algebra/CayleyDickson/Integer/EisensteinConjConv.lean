import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvComm
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSum
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussOffDiag
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNorm
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmegaDomain

/-!
# The conjugate convolution `ḡ ⋆ ḡ = conj(g ⋆ g)∘(−·)` (∅-axiom, Phase A3 / route b)

`conj g` is a ring homomorphism with the index reflection `(conj g)_k = conj(g_{−k})`, so

  `(ḡ ⋆ ḡ)(k) = conj((g ⋆ g)((p−k)%p))`   (`gbgb_eq_conj_gg`),

where `ḡ = gaussConj` (the coefficient function of `conj g(χ)`).  Distribute `conj` over the
convolution (`conj_mul` + `conj_sumRange`) and reflect the summation index `i ↦ (p−i)%p`
(`rangeList_refl_lperm`); the inner indices collapse by `conv_diag_index` / `conv_offdiag_index` and
modular subtraction is commutative.  With `g⋆g = J·g(χ²)` this gives `ḡ⋆ḡ = J̄·conj g(χ²)`, the
conjugate Gauss–Jacobi relation feeding `(g·g)·(ḡ·ḡ) = |J|²·Y` and the norm law `N(J)=p`.  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConjConv

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (conj conj_mul)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing (conv)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSum (gauss gaussConj conv_diag_index)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussOffDiag (conv_offdiag_index)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNorm (conj_add conj_zero)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum (sumRange sumRange_succ sum_congr)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinListSum (listSum listSum_lperm listSum_map)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeSum (sumRange_eq_listSum)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvComm (rangeList_refl_lperm)
open E213.Meta.Nat.AddMod213 (mod_add_mod)
open E213.Tactic.NatHelper (add_sub_assoc)

/-- `conj (Σ_{i<n} f i) = Σ_{i<n} conj (f i)` — `conj` distributes over a finite sum. -/
theorem conj_sumRange (f : Nat → ZOmega) : ∀ n, conj (sumRange f n) = sumRange (fun i => conj (f i)) n
  | 0 => conj_zero
  | n + 1 => by
      show conj (sumRange f n + f n) = sumRange (fun i => conj (f i)) n + conj (f n)
      rw [conj_add, conj_sumRange f n]

/-- The conjugate-convolution reflection index — `(p−(k+p−(0+p−i)%p)%p)%p = ((p−k)%p+p−i)%p` for
    `i, k < p`: both `≡ −i−k`.  `conv_offdiag_index` + commutativity of modular subtraction.  ∅-axiom. -/
theorem conj_conv_index {p k i : Nat} (hp0 : 0 < p) (hk : k < p) (hi : i < p) :
    (p - (k + p - (0 + p - i) % p) % p) % p = ((p - k) % p + p - i) % p := by
  rw [conv_offdiag_index hk (Nat.mod_lt _ hp0), Nat.zero_add,
      add_sub_assoc ((p - i) % p) (Nat.le_of_lt hk), mod_add_mod hp0 (p - i) (p - k),
      add_sub_assoc ((p - k) % p) (Nat.le_of_lt hi), mod_add_mod hp0 (p - k) (p - i),
      Nat.add_comm (p - i) (p - k)]

/-- ★★★★★ **The conjugate convolution** — `(ḡ⋆ḡ)(k) = conj((g⋆g)((p−k)%p))` for `k < p`.
    `conj` is a ring hom (`conj_mul`/`conj_sumRange`) with index reflection.  ∅-axiom. -/
theorem gbgb_eq_conj_gg {p m x k : Nat} (hk : k < p) :
    conv p (gaussConj p m x) (gaussConj p m x) k
      = conj (conv p (gauss p m x) (gauss p m x) ((p - k) % p)) := by
  have hp0 : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  show sumRange (fun i => conj (gauss p m x ((p - i) % p))
                          * conj (gauss p m x ((p - (k + p - i) % p) % p))) p
     = conj (sumRange (fun j => gauss p m x j * gauss p m x (((p - k) % p + p - j) % p)) p)
  -- combine the per-term conjugates, then pull `conj` out of the whole sum
  rw [sum_congr p (fun i _ =>
        (conj_mul (gauss p m x ((p - i) % p)) (gauss p m x ((p - (k + p - i) % p) % p))).symm),
      ← conj_sumRange]
  congr 1
  -- reflect i ↦ (0+p−i)%p so the first factor's index collapses to i
  show sumRange (fun i => gauss p m x ((p - i) % p)
                          * gauss p m x ((p - (k + p - i) % p) % p)) p
     = sumRange (fun j => gauss p m x j * gauss p m x (((p - k) % p + p - j) % p)) p
  rw [sumRange_eq_listSum, listSum_lperm _ (rangeList_refl_lperm hp0 hp0),
      listSum_map (fun i => gauss p m x ((p - i) % p) * gauss p m x ((p - (k + p - i) % p) % p))
        (fun i => (0 + p - i) % p) (E213.Lib.Math.Combinatorics.RangeList.rangeList p),
      ← sumRange_eq_listSum]
  refine sum_congr p (fun i hi => ?_)
  show gauss p m x ((p - (0 + p - i) % p) % p)
        * gauss p m x ((p - (k + p - (0 + p - i) % p) % p) % p)
     = gauss p m x i * gauss p m x (((p - k) % p + p - i) % p)
  rw [conv_diag_index hi, conj_conv_index hp0 hk hi]

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConjConv
