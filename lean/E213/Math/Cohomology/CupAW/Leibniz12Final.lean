import E213.Math.Cohomology.CupAW.LeibnizAlgLift
import E213.Math.Cohomology.Universal.Core.Prop51

/-!
# Universal Cup AW Leibniz at (5, 1, 2) — closed via algebraic lift

Closes ∀ α β Leibniz at (5, 1, 2) through the bilinearity lens:

  - α-pattern × basis Leibniz (3200-case decide)
  - case-split on β k (per-component): zero or basis branches
  - structural XOR rearrangement (combine_10, 0-axiom)

Total decide work: 3200 cases, vs the 327k blow-up of direct.
-/

namespace E213.Math.Cohomology.CupAW.Leibniz12Final

open E213.Physics.Simplex (binom)
open E213.Math.Cohomology.Universal.Core.Prop51 (pattern pattern_eq)
open E213.Math.Cohomology.CupAW.BasisLeibniz (basis)
open E213.Math.Cohomology.Cochain5_2Decomp (bz5_2)

/-- α-pattern × basis level Leibniz at (5, 1, 2): 3200-case decide. -/
theorem leibniz_α_basis_pattern :
    ∀ a0 a1 a2 a3 a4 : Bool, ∀ k : Fin 10, ∀ i : Fin (binom 5 3),
      delta (cupAW 5 1 2 (pattern a0 a1 a2 a3 a4) (basis 5 2 k)) i
        = xor (cupAW 5 2 2 (delta (pattern a0 a1 a2 a3 a4))
                (basis 5 2 k) i)
              (cupAW 5 1 3 (pattern a0 a1 a2 a3 a4)
                (delta (basis 5 2 k)) i) := by
  decide

/-- Universal α with β = basis. -/
theorem leibniz_α_basis (α : Cochain 5 1) (k : Fin 10)
    (i : Fin (binom 5 3)) :
    delta (cupAW 5 1 2 α (basis 5 2 k)) i
      = xor (cupAW 5 2 2 (delta α) (basis 5 2 k) i)
            (cupAW 5 1 3 α (delta (basis 5 2 k)) i) := by
  rw [pattern_eq α]
  exact leibniz_α_basis_pattern _ _ _ _ _ k i

/-- Per-component Leibniz: case-split on β k. -/
theorem h_components (α : Cochain 5 1) (β : Cochain 5 2)
    (i : Fin (binom 5 3)) (k : Fin 10) :
    delta (cupAW 5 1 2 α (bz5_2 β k)) i
      = xor (cupAW 5 2 2 (delta α) (bz5_2 β k) i)
            (cupAW 5 1 3 α (delta (bz5_2 β k)) i) := by
  cases hβ : β k
  · have h_eq : bz5_2 β k = Cochain.zero 5 2 := by
      funext j
      show ((k.val == j.val) && β k) = false
      rw [hβ]
      show ((k.val == j.val) && false) = false
      cases (k.val == j.val) <;> rfl
    rw [h_eq]
    rw [show cupAW 5 1 2 α (Cochain.zero 5 2) = Cochain.zero 5 2 from
          funext fun _ => cupAW_zero_right _ _ _ _ _,
        show delta (Cochain.zero 5 2) = Cochain.zero 5 3 from
          funext fun _ => delta_zero _ _ _,
        show cupAW 5 2 2 (delta α) (Cochain.zero 5 2)
              = Cochain.zero 5 3 from
          funext fun _ => cupAW_zero_right _ _ _ _ _,
        show cupAW 5 1 3 α (Cochain.zero 5 3) = Cochain.zero 5 3 from
          funext fun _ => cupAW_zero_right _ _ _ _ _]
    show false = xor false false
    rfl
  · have h_eq : bz5_2 β k = basis 5 2 k := by
      funext j
      show ((k.val == j.val) && β k) = basis 5 2 k j
      rw [hβ]
      show ((k.val == j.val) && true) = (k.val == j.val)
      cases (k.val == j.val) <;> rfl
    rw [h_eq]
    exact leibniz_α_basis α k i

/-- ★★★★★ Universal Cup AW Leibniz at (5, 1, 2) — algebraic lift CLOSED. -/
theorem leibniz_universal_5_1_2
    (α : Cochain 5 1) (β : Cochain 5 2) (i : Fin (binom 5 3)) :
    delta (cupAW 5 1 2 α β) i
      = xor (cupAW 5 2 2 (delta α) β i)
            (cupAW 5 1 3 α (delta β) i) :=
  CupAWLeibnizAlgLift.leibniz_via_β_decomp_lens α β i (h_components α β i)

end E213.Math.Cohomology.CupAW.Leibniz12Final
