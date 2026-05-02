import E213.Math.Cohomology.CupAW.BasisLeibniz

/-!
# Cochain 5 1 — basis decomposition (right-nested, AND-form)

Mirror of `Cochain5_2Decomp` for Cochain 5 1.  AND-form for
definitional reduction; right-nested for consistency with
`combine_5`.

  bz5_1_r β k j := (k.val == j.val) && β k
-/

namespace E213.Math.Cohomology.Cochain.V5_1DecompR

open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.CupAW.BasisLeibniz (basis)

/-- AND-form conditional basis-or-zero at (5, 1). -/
def bz5_1 (β : Cochain 5 1) (k : Fin 5) : Cochain 5 1 := fun j =>
  (k.val == j.val) && β k

/-- Right-nested 5-term XOR decomposition. -/
def decomp_5_1 (β : Cochain 5 1) : Cochain 5 1 :=
  Cochain.add (bz5_1 β ⟨0, by decide⟩)
    (Cochain.add (bz5_1 β ⟨1, by decide⟩)
      (Cochain.add (bz5_1 β ⟨2, by decide⟩)
        (Cochain.add (bz5_1 β ⟨3, by decide⟩)
          (bz5_1 β ⟨4, by decide⟩))))

/-- Per-j decomposition step. -/
private theorem decomp_step (β : Cochain 5 1) (j : Fin 5) :
    decomp_5_1 β j = β j := by
  match j with
  | ⟨0, _⟩ => simp only [decomp_5_1, bz5_1, Cochain.add]
              cases (β ⟨0, by decide⟩) <;> rfl
  | ⟨1, _⟩ => simp only [decomp_5_1, bz5_1, Cochain.add]
              cases (β ⟨1, by decide⟩) <;> rfl
  | ⟨2, _⟩ => simp only [decomp_5_1, bz5_1, Cochain.add]
              cases (β ⟨2, by decide⟩) <;> rfl
  | ⟨3, _⟩ => simp only [decomp_5_1, bz5_1, Cochain.add]
              cases (β ⟨3, by decide⟩) <;> rfl
  | ⟨4, _⟩ => simp only [decomp_5_1, bz5_1, Cochain.add]
              cases (β ⟨4, by decide⟩) <;> rfl

/-- Decomposition is identity on Cochain 5 1. -/
theorem decomp_5_1_eq (β : Cochain 5 1) : decomp_5_1 β = β := by
  funext j; exact decomp_step β j

end E213.Math.Cohomology.Cochain.V5_1DecompR
