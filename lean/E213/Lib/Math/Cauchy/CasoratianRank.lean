import E213.Lib.Math.Cauchy.CFiniteHadamard
import E213.Lib.Math.Linalg213.RowDependence

/-!
# CasoratianRank — C-finite ⟹ the Casoratian (Hankel) determinant vanishes

The forward half of **Casoratian rank = orbit dimension**: a sequence satisfying a monic order-`k`
shift recurrence has its `(k+1)×(k+1)` Casoratian (Hankel) determinant `det [s(n+i+j)]` identically
`0` — because the bottom row is exactly the recurrence combination of the upper rows
(`RowDependence.det_row_combo_zero`).  So the Casoratian rank of a C-finite sequence is `≤ k`, the
recurrence order.  All ∅-axiom.
-/

namespace E213.Lib.Math.Cauchy.CasoratianRank

open E213.Lib.Math.Linalg213.Permutation (sumZ iota)
open E213.Lib.Math.Linalg213.PermClosure (map_eq_of_mem)
open E213.Lib.Math.Linalg213.DetN (det)
open E213.Lib.Math.Linalg213.RowDependence (det_row_combo_zero)
open E213.Lib.Math.Cauchy.CFiniteRing (ShiftRecZ)
open E213.Lib.Math.Cauchy.CFiniteHadamard (shiftSum_eq_sumZ)

/-- ★★ **C-finite ⟹ the Casoratian determinant vanishes.**  For `s` satisfying the monic order-`k`
    shift recurrence `s(n+k) = Σ_{a<k} bₐ·s(n+a)`, the `(k+1)×(k+1)` Hankel/Casoratian determinant
    `det [s(n+i+j)]_{i,j≤k}` is `0` — the bottom row is the recurrence combination of the rest. -/
theorem casoratian_det_zero {k : Nat} {b s : Nat → Int} (h : ShiftRecZ k b s) (n : Nat) :
    det (k + 1) (fun i j => s (n + i + j)) = 0 := by
  refine det_row_combo_zero (k + 1) k (Nat.lt_succ_self k) k b (fun a => a)
    (fun i j => s (n + i + j)) (fun a ha => Nat.lt_succ_of_lt ha) (fun a ha => Nat.ne_of_lt ha)
    (fun bb => ?_)
  show s (n + k + bb) = sumZ ((iota k).map (fun a => b a * s (n + a + bb)))
  rw [Nat.add_right_comm n k bb, h (n + bb), shiftSum_eq_sumZ b s (n + bb) k]
  apply congrArg sumZ
  apply map_eq_of_mem
  intro a _
  show b a * s (n + bb + a) = b a * s (n + a + bb)
  rw [Nat.add_right_comm n bb a]

/-- ★ **Specialization to `CFiniteZ`**: every C-finite sequence has a vanishing Casoratian
    determinant at some order (its recurrence order). -/
theorem casoratian_det_zero_of_cfiniteZ {s : Nat → Int}
    (hs : E213.Lib.Math.Cauchy.OrbitDimension.CFiniteZ s) :
    ∃ (k : Nat), ∀ (n : Nat), det (k + 1) (fun i j => s (n + i + j)) = 0 := by
  obtain ⟨k, b, hk⟩ := E213.Lib.Math.Cauchy.CFiniteRing.shiftRec_of_cfiniteZ hs
  exact ⟨k, fun n => casoratian_det_zero hk n⟩

end E213.Lib.Math.Cauchy.CasoratianRank
