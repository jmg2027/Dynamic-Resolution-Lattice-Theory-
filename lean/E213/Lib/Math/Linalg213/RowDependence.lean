import E213.Lib.Math.Linalg213.CayleyHamilton
import E213.Lib.Math.PolyZ

/-!
# Linalg213 — row dependence ⟹ `det = 0`

The determinant payoff feeding the **Casoratian rank = orbit dimension** bridge: a matrix with one
row equal to a `ℤ`-linear combination of its *other* rows has `det = 0`.  Built from row
multilinearity (`det_setRow_add`/`_smul`) + the alternating property (`det_rows_eq_ne`).

All ∅-axiom.
-/

namespace E213.Lib.Math.Linalg213.RowDependence

open E213.Lib.Math.Linalg213.Permutation (sumZ iota)
open E213.Lib.Math.Linalg213.PermClosure
  (setRow setRow_at setRow_off map_eq_of_mem lt_of_mem_iota leibDet_zero_row)
open E213.Lib.Math.Linalg213.DetN (det det_congr)
open E213.Lib.Math.Linalg213.Laplace
  (det_setRow_add det_setRow_smul det_rows_eq_ne leibDet_eq_det sumZ_append map_append')
open E213.Lib.Math.Linalg213.CayleyHamilton (sumZ_singleton sumZ_map_zero mul_zero')

/-- Peel the top index of a `sumZ` over `iota (K+1)`. -/
theorem sumZ_iota_succ (g : Nat → Int) (K : Nat) :
    sumZ ((iota (K + 1)).map g) = sumZ ((iota K).map g) + g K := by
  rw [show iota (K + 1) = iota K ++ [K] from rfl, map_append', sumZ_append,
      show ([K] : List Nat).map g = [g K] from rfl, sumZ_singleton]

/-- A zero row ⟹ `det = 0`. -/
theorem det_zero_row (n i : Nat) (hi : i < n) (M : Nat → Nat → Int) (hz : ∀ c, M i c = 0) :
    det n M = 0 := by
  rw [← leibDet_eq_det]
  exact leibDet_zero_row n i hi M hz

/-- `setRow` respects pointwise equality of the inserted row. -/
theorem setRow_eq (i : Nat) (r r' : Nat → Int) (M : Nat → Nat → Int) (h : ∀ b, r b = r' b)
    (a b : Nat) : setRow i r M a b = setRow i r' M a b := by
  show (if a = i then r b else M a b) = (if a = i then r' b else M a b)
  by_cases hai : a = i
  · rw [if_pos hai, if_pos hai]; exact h b
  · rw [if_neg hai, if_neg hai]

/-- **Multilinearity over a finite combination**: the determinant with row `i` set to the
    combination `Σ_{a<K} c a · rows a` expands `ℤ`-linearly over the `K` summands. -/
theorem det_setRow_sumZ (n i : Nat) (hi : i < n) (rows : Nat → Nat → Int) (c : Nat → Int)
    (M : Nat → Nat → Int) : ∀ (K : Nat),
    det n (setRow i (fun j => sumZ ((iota K).map (fun a => c a * rows a j))) M)
      = sumZ ((iota K).map (fun a => c a * det n (setRow i (rows a) M)))
  | 0     => (det_zero_row n i hi _ (fun cc => (setRow_at i _ M cc).trans rfl)).trans rfl
  | K + 1 => by
    rw [det_congr n (setRow_eq i
          (fun j => sumZ ((iota (K + 1)).map (fun a => c a * rows a j)))
          (fun j => sumZ ((iota K).map (fun a => c a * rows a j)) + c K * rows K j) M
          (fun b => sumZ_iota_succ (fun a => c a * rows a b) K)),
        det_setRow_add n i hi (fun j => sumZ ((iota K).map (fun a => c a * rows a j)))
          (fun j => c K * rows K j) M,
        det_setRow_sumZ n i hi rows c M K,
        det_setRow_smul n i hi (c K) (rows K) M,
        sumZ_iota_succ (fun a => c a * det n (setRow i (rows a) M)) K]

/-- ★★ **Row dependence ⟹ `det = 0`**: if row `i` is a `ℤ`-combination `Σ_{a<K} c a · M(idx a)`
    of other rows (`idx a ≠ i`, `idx a < n`), the determinant vanishes. -/
theorem det_row_combo_zero (n i : Nat) (hi : i < n) (K : Nat) (c : Nat → Int) (idx : Nat → Nat)
    (M : Nat → Nat → Int) (hidx_lt : ∀ a, a < K → idx a < n) (hidx_ne : ∀ a, idx a ≠ i)
    (hrow : ∀ b, M i b = sumZ ((iota K).map (fun a => c a * M (idx a) b))) :
    det n M = 0 := by
  rw [det_congr n (fun a b =>
        (show M a b = setRow i (fun j => sumZ ((iota K).map (fun a' => c a' * M (idx a') j))) M a b from by
          by_cases hai : a = i
          · rw [hai, setRow_at]; exact hrow b
          · rw [setRow_off i _ M hai])),
      det_setRow_sumZ n i hi (fun a => M (idx a)) c M K,
      map_eq_of_mem (fun a => c a * det n (setRow i (M (idx a)) M)) (fun _ => 0)
        (fun a ha => by
          show c a * det n (setRow i (M (idx a)) M) = 0
          rw [det_rows_eq_ne (setRow i (M (idx a)) M) n i (idx a) (fun h => hidx_ne a h.symm) hi
                (hidx_lt a (lt_of_mem_iota ha))
                (fun cc => by rw [setRow_at, setRow_off i (M (idx a)) M (hidx_ne a)]),
              mul_zero']),
      sumZ_map_zero]

end E213.Lib.Math.Linalg213.RowDependence
