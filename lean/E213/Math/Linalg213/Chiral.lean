import E213.Math.Linalg213.Span

/-!
# 213 Linear Algebra — chirality bigrading (Phase L4)

Paper 1's chiral decomposition ℂ⁵ = ℂ² ⊕ ℂ³ in 213-internal form.
Vec 5 = Vec_S ⊕ Vec_T where Vec_S = Fin 3 → Nat (NS=3 spatial),
Vec_T = Fin 2 → Nat (NT=2 temporal).  Indices {0,1,2} S-type,
{3,4} T-type.  Atomic split: NS+NT=d=5.
-/

namespace E213.Math.Linalg213

open E213.Physics.Simplex (NS NT)

/-- Spatial part. -/
def VecS : Type := Fin 3 → Nat

/-- Temporal part. -/
def VecT : Type := Fin 2 → Nat

/-- Project Vec 5 onto spatial part. -/
def projS (v : Vec 5) : VecS := fun i => v ⟨i.val, by omega⟩

/-- Project Vec 5 onto temporal part. -/
def projT (v : Vec 5) : VecT := fun i => v ⟨3 + i.val, by omega⟩

/-- Combine S-part and T-part back into Vec 5. -/
def combine (s : VecS) (t : VecT) : Vec 5 :=
  fun k =>
    if h : k.val < 3 then s ⟨k.val, h⟩
    else t ⟨k.val - 3, by have := k.isLt; omega⟩

/-- projS e0_5 = (1, 0, 0). -/
theorem projS_e0_5 :
    projS e0_5 ⟨0, by decide⟩ = 1
    ∧ projS e0_5 ⟨1, by decide⟩ = 0
    ∧ projS e0_5 ⟨2, by decide⟩ = 0 := by decide

/-- projT e0_5 = (0, 0). -/
theorem projT_e0_5 :
    projT e0_5 ⟨0, by decide⟩ = 0
    ∧ projT e0_5 ⟨1, by decide⟩ = 0 := by decide

/-- projS e3_5 = (0, 0, 0) — e_3 fully T-type. -/
theorem projS_e3_5 :
    projS e3_5 ⟨0, by decide⟩ = 0
    ∧ projS e3_5 ⟨1, by decide⟩ = 0
    ∧ projS e3_5 ⟨2, by decide⟩ = 0 := by decide

/-- projT e3_5 = (1, 0). -/
theorem projT_e3_5 :
    projT e3_5 ⟨0, by decide⟩ = 1
    ∧ projT e3_5 ⟨1, by decide⟩ = 0 := by decide

/-- projT e4_5 = (0, 1). -/
theorem projT_e4_5 :
    projT e4_5 ⟨0, by decide⟩ = 0
    ∧ projT e4_5 ⟨1, by decide⟩ = 1 := by decide

/-- ★ Chiral round-trip pointwise: combine (projS v) (projT v) k
    equals v k at every k.  Proves Vec 5 = VecS ⊕ VecT
    (paper 1 chiral split at vector level). -/
theorem combine_proj_eq (v : Vec 5) (k : Fin 5) :
    combine (projS v) (projT v) k = v k := by
  match k with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl

/-- ★ Phase L4 capstone. -/
theorem phase_L4_capstone :
    NS = 3 ∧ NT = 2 ∧ NS + NT = 5
    ∧ (∀ v : Vec 5, ∀ k : Fin 5,
         combine (projS v) (projT v) k = v k) :=
  ⟨by decide, by decide, by decide, combine_proj_eq⟩

end E213.Math.Linalg213
