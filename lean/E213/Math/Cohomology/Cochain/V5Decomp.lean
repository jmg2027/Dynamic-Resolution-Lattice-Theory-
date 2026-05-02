import E213.Math.Cohomology.CupAW.BasisLeibniz

/-!
# Cochain 5 1 / Cochain 5 2 — basis decomposition

σ : Cochain 5 1 = (σ 0)? e_0 : 0 + ... + (σ 4)? e_4 : 0
σ : Cochain 5 2 = (σ 0)? f_0 : 0 + ... + (σ 9)? f_9 : 0

Pointwise verified by funext + match j + cases on each (σ ⟨k, _⟩).
-/

namespace E213.Math.Cohomology.Cochain.V5Decomp

open E213.Math.Cohomology.CupAW.BasisLeibniz (basis)
open E213.Math.Cohomology.Cochain.Core (Cochain)

/-- Conditional basis or zero. -/
def bz5_1 (α : Cochain 5 1) (k : Fin 5) : Cochain 5 1 :=
  if α k then basis 5 1 k else Cochain.zero 5 1

/-- Decomposition of Cochain 5 1 as XOR of 5 conditional basis cochains. -/
def decomp_5_1 (α : Cochain 5 1) : Cochain 5 1 :=
  Cochain.add
    (Cochain.add
      (Cochain.add
        (Cochain.add
          (bz5_1 α ⟨0, by decide⟩)
          (bz5_1 α ⟨1, by decide⟩))
        (bz5_1 α ⟨2, by decide⟩))
      (bz5_1 α ⟨3, by decide⟩))
    (bz5_1 α ⟨4, by decide⟩)

/-- Decomposition is identity on Cochain 5 1. -/
theorem decomp_5_1_eq (α : Cochain 5 1) : decomp_5_1 α = α := by
  funext j
  match j with
  | ⟨0, _⟩ =>
    show (decomp_5_1 α) ⟨0, _⟩ = α ⟨0, _⟩
    unfold decomp_5_1 bz5_1 basis Cochain.add Cochain.zero
    cases (α ⟨0, by decide⟩) <;> cases (α ⟨1, by decide⟩) <;>
      cases (α ⟨2, by decide⟩) <;> cases (α ⟨3, by decide⟩) <;>
      cases (α ⟨4, by decide⟩) <;> rfl
  | ⟨1, _⟩ =>
    show (decomp_5_1 α) ⟨1, _⟩ = α ⟨1, _⟩
    unfold decomp_5_1 bz5_1 basis Cochain.add Cochain.zero
    cases (α ⟨0, by decide⟩) <;> cases (α ⟨1, by decide⟩) <;>
      cases (α ⟨2, by decide⟩) <;> cases (α ⟨3, by decide⟩) <;>
      cases (α ⟨4, by decide⟩) <;> rfl
  | ⟨2, _⟩ =>
    show (decomp_5_1 α) ⟨2, _⟩ = α ⟨2, _⟩
    unfold decomp_5_1 bz5_1 basis Cochain.add Cochain.zero
    cases (α ⟨0, by decide⟩) <;> cases (α ⟨1, by decide⟩) <;>
      cases (α ⟨2, by decide⟩) <;> cases (α ⟨3, by decide⟩) <;>
      cases (α ⟨4, by decide⟩) <;> rfl
  | ⟨3, _⟩ =>
    show (decomp_5_1 α) ⟨3, _⟩ = α ⟨3, _⟩
    unfold decomp_5_1 bz5_1 basis Cochain.add Cochain.zero
    cases (α ⟨0, by decide⟩) <;> cases (α ⟨1, by decide⟩) <;>
      cases (α ⟨2, by decide⟩) <;> cases (α ⟨3, by decide⟩) <;>
      cases (α ⟨4, by decide⟩) <;> rfl
  | ⟨4, _⟩ =>
    show (decomp_5_1 α) ⟨4, _⟩ = α ⟨4, _⟩
    unfold decomp_5_1 bz5_1 basis Cochain.add Cochain.zero
    cases (α ⟨0, by decide⟩) <;> cases (α ⟨1, by decide⟩) <;>
      cases (α ⟨2, by decide⟩) <;> cases (α ⟨3, by decide⟩) <;>
      cases (α ⟨4, by decide⟩) <;> rfl

end E213.Math.Cohomology.Cochain.V5Decomp
