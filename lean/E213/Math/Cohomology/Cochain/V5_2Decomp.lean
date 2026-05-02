import E213.Math.Cohomology.Cochain.V5Decomp

/-!
# Cochain 5 2 — basis decomposition (10-term, definitional reduction)

bz5_2 β k j := (k.val == j.val) && β k

  - on-diagonal (k = j): true && β j  = β j (definitional)
  - off-diagonal (k ≠ j): false && β k = false (definitional)

So the XOR sum reduces definitionally per j; only one `cases`
on (β j) needed to close.
-/

namespace E213.Math.Cohomology.Cochain.V5_2Decomp

open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.CupAW.BasisLeibniz (basis)

/-- Conditional basis-or-zero at (5, 2), AND-form (definitional). -/
def bz5_2 (β : Cochain 5 2) (k : Fin 10) : Cochain 5 2 := fun j =>
  (k.val == j.val) && β k

/-- Decomposition of Cochain 5 2 as XOR of 10 conditional basis cochains. -/
def decomp_5_2 (β : Cochain 5 2) : Cochain 5 2 :=
  Cochain.add (bz5_2 β ⟨0, by decide⟩)
    (Cochain.add (bz5_2 β ⟨1, by decide⟩)
      (Cochain.add (bz5_2 β ⟨2, by decide⟩)
        (Cochain.add (bz5_2 β ⟨3, by decide⟩)
          (Cochain.add (bz5_2 β ⟨4, by decide⟩)
            (Cochain.add (bz5_2 β ⟨5, by decide⟩)
              (Cochain.add (bz5_2 β ⟨6, by decide⟩)
                (Cochain.add (bz5_2 β ⟨7, by decide⟩)
                  (Cochain.add (bz5_2 β ⟨8, by decide⟩)
                    (bz5_2 β ⟨9, by decide⟩)))))))))

/-- Per-j proof: simp + cases on the diagonal value. -/
private theorem decomp_step (β : Cochain 5 2) (j : Fin 10) :
    decomp_5_2 β j = β j := by
  match j with
  | ⟨0, _⟩ => simp only [decomp_5_2, bz5_2, Cochain.add]
              cases (β ⟨0, by decide⟩) <;> rfl
  | ⟨1, _⟩ => simp only [decomp_5_2, bz5_2, Cochain.add]
              cases (β ⟨1, by decide⟩) <;> rfl
  | ⟨2, _⟩ => simp only [decomp_5_2, bz5_2, Cochain.add]
              cases (β ⟨2, by decide⟩) <;> rfl
  | ⟨3, _⟩ => simp only [decomp_5_2, bz5_2, Cochain.add]
              cases (β ⟨3, by decide⟩) <;> rfl
  | ⟨4, _⟩ => simp only [decomp_5_2, bz5_2, Cochain.add]
              cases (β ⟨4, by decide⟩) <;> rfl
  | ⟨5, _⟩ => simp only [decomp_5_2, bz5_2, Cochain.add]
              cases (β ⟨5, by decide⟩) <;> rfl
  | ⟨6, _⟩ => simp only [decomp_5_2, bz5_2, Cochain.add]
              cases (β ⟨6, by decide⟩) <;> rfl
  | ⟨7, _⟩ => simp only [decomp_5_2, bz5_2, Cochain.add]
              cases (β ⟨7, by decide⟩) <;> rfl
  | ⟨8, _⟩ => simp only [decomp_5_2, bz5_2, Cochain.add]
              cases (β ⟨8, by decide⟩) <;> rfl
  | ⟨9, _⟩ => simp only [decomp_5_2, bz5_2, Cochain.add]
              cases (β ⟨9, by decide⟩) <;> rfl

/-- Decomposition is identity on Cochain 5 2. -/
theorem decomp_5_2_eq (β : Cochain 5 2) : decomp_5_2 β = β := by
  funext j; exact decomp_step β j

end E213.Math.Cohomology.Cochain.V5_2Decomp
