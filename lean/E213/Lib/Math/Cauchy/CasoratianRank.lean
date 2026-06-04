import E213.Lib.Math.Cauchy.CFiniteHadamard
import E213.Lib.Math.Linalg213.RowDependence
import E213.Lib.Math.Linalg213.FibCassiniDet

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
open E213.Lib.Math.Cauchy.OrbitDimension (fibZ)
open E213.Lib.Math.Linalg213.DetN (altSign)
open E213.Lib.Math.Linalg213.FibCassiniDet (fibCas_det_eq_unit)

/-- The Casoratian's bottom row `s(n+k+b)` is the recurrence combination `Σ_{a<k} bₐ·s(n+a+b)`. -/
theorem casoratian_row {k : Nat} {b s : Nat → Int} (h : ShiftRecZ k b s) (n bb : Nat) :
    s (n + k + bb) = sumZ ((iota k).map (fun a => b a * s (n + a + bb))) := by
  rw [Nat.add_right_comm n k bb, h (n + bb), shiftSum_eq_sumZ b s (n + bb) k]
  apply congrArg sumZ
  apply map_eq_of_mem
  intro a _
  show b a * s (n + bb + a) = b a * s (n + a + bb)
  rw [Nat.add_right_comm n bb a]

/-- ★★ **C-finite ⟹ every larger Casoratian determinant vanishes.**  For `s` satisfying a monic
    order-`k` shift recurrence and any `m ≥ k`, the `(m+1)×(m+1)` Hankel/Casoratian determinant
    `det [s(n+i+j)]_{i,j≤m} = 0` — row `k` is the recurrence combination of the rows below it.  So the
    **Casoratian rank is `≤ k`**, the recurrence order. -/
theorem casoratian_det_zero_ge {k : Nat} {b s : Nat → Int} (h : ShiftRecZ k b s) {m : Nat}
    (hm : k ≤ m) (n : Nat) : det (m + 1) (fun i j => s (n + i + j)) = 0 :=
  det_row_combo_zero (m + 1) k (Nat.lt_succ_of_le hm) k b (fun a => a) (fun i j => s (n + i + j))
    (fun a ha => Nat.lt_succ_of_le (Nat.le_trans (Nat.le_of_lt ha) hm))
    (fun a ha => Nat.ne_of_lt ha) (fun bb => casoratian_row h n bb)

/-- ★★ **C-finite ⟹ the `(k+1)×(k+1)` Casoratian determinant vanishes** (the marquee case). -/
theorem casoratian_det_zero {k : Nat} {b s : Nat → Int} (h : ShiftRecZ k b s) (n : Nat) :
    det (k + 1) (fun i j => s (n + i + j)) = 0 :=
  casoratian_det_zero_ge h (Nat.le_refl k) n

/-- ★ **Specialization to `CFiniteZ`**: every C-finite sequence has a vanishing Casoratian
    determinant at some order (its recurrence order). -/
theorem casoratian_det_zero_of_cfiniteZ {s : Nat → Int}
    (hs : E213.Lib.Math.Cauchy.OrbitDimension.CFiniteZ s) :
    ∃ (k : Nat), ∀ (n : Nat), det (k + 1) (fun i j => s (n + i + j)) = 0 := by
  obtain ⟨k, b, hk⟩ := E213.Lib.Math.Cauchy.CFiniteRing.shiftRec_of_cfiniteZ hs
  exact ⟨k, fun n => casoratian_det_zero hk n⟩

/-! ## §2 — the Fibonacci witness: Casoratian rank = orbit dimension = 2 -/

/-- Fibonacci's monic order-2 shift recurrence `f(n+2) = f(n+1) + f(n)`. -/
theorem fib_shiftRec : ShiftRecZ 2 (fun _ => 1) fibZ := fun n => by
  show fibZ (n + 2) = (0 + 1 * fibZ (n + 0)) + 1 * fibZ (n + 1)
  rw [Nat.add_zero, E213.Meta.Int213.zero_add, Int.one_mul, Int.one_mul]
  show fibZ (n + 1) + fibZ n = fibZ n + fibZ (n + 1)
  exact E213.Meta.Int213.add_comm _ _

/-- ★ **Fibonacci has Casoratian rank exactly 2 = its orbit dimension.**  The `3×3` Casoratian
    determinant vanishes (order-2 recurrence ⟹ row 2 is redundant), while the `2×2` is the
    conserved unit `(−1)ⁿ⁺¹ ≠ 0` (`FibCassiniDet`).  So the orbit dimension `2` is read off as the
    largest non-vanishing Casoratian — the determinant tower validated against the orbit ladder. -/
theorem fib_casoratian_rank (n : Nat) :
    det 3 (fun i j => fibZ (n + i + j)) = 0
      ∧ det 2 (fun i j => fibZ (n + i + j)) = altSign (n + 1) :=
  ⟨casoratian_det_zero fib_shiftRec n, fibCas_det_eq_unit n⟩

end E213.Lib.Math.Cauchy.CasoratianRank
