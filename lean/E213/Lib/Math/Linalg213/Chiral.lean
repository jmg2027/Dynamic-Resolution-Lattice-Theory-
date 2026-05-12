import E213.Lib.Math.Linalg213.Span
import E213.Term.Tactic.Nat213

/-!
# 213 Linear Algebra — chirality bigrading (4)

Paper 1's chiral decomposition ℂ⁵ = ℂ² ⊕ ℂ³ in 213-internal form.
Vec 5 = Vec_S ⊕ Vec_T where Vec_S = Fin 3 → Nat (NS=3 spatial),
Vec_T = Fin 2 → Nat (NT=2 temporal).  Indices {0,1,2} S-type,
{3,4} T-type.  Atomic split: NS+NT=d=5.
-/

namespace E213.Lib.Math.Linalg213.Chiral

open E213.Lib.Physics.Simplex.Counts (NS NT)
open E213.Lib.Math.Linalg213.Vector
open E213.Lib.Math.Linalg213.Span

/-- Spatial part. -/
def VecS : Type := Fin 3 → Nat

/-- Temporal part. -/
def VecT : Type := Fin 2 → Nat

/-- Project Vec 5 onto spatial part. -/
def projS (v : Vec 5) : VecS := fun i =>
  v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (by decide : 3 ≤ 5)⟩

/-- Project Vec 5 onto temporal part. -/
def projT (v : Vec 5) : VecT := fun i =>
  v ⟨3 + i.val, by
    have h1 : i.val < 2 := i.isLt
    have h2 : 3 + i.val < 3 + 2 := Nat.add_lt_add_left h1 3
    exact h2⟩

/-- Combine S-part and T-part back into Vec 5. -/
def combine (s : VecS) (t : VecT) : Vec 5 :=
  fun k =>
    if h : k.val < 3 then s ⟨k.val, h⟩
    else t ⟨k.val - 3, by
      have hkLt : k.val < 5 := k.isLt
      have hge : 3 ≤ k.val := Nat.le_of_not_lt h
      have hadd_eq : k.val - 3 + 3 = k.val :=
        E213.Tactic.Nat213.sub_add_cancel hge
      have hadd_lt : k.val - 3 + 3 < 2 + 3 := hadd_eq ▸ hkLt
      exact Nat.lt_of_add_lt_add_right hadd_lt⟩

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
    (paper 1 chiral split at vector level).  PURE via cases_lt_five
    + subst (Fin pattern match would leak Quot.sound). -/
theorem combine_proj_eq (v : Vec 5) (k : Fin 5) :
    combine (projS v) (projT v) k = v k := by
  obtain ⟨n, hn⟩ := k
  show combine (projS v) (projT v) ⟨n, hn⟩ = v ⟨n, hn⟩
  rcases E213.Tactic.Nat213.cases_lt_five hn
    with h | h | h | h | h <;> subst h <;> rfl

/-- ★ 4 capstone. -/
theorem phase_L4_capstone :
    NS = 3 ∧ NT = 2 ∧ NS + NT = 5
    ∧ (∀ v : Vec 5, ∀ k : Fin 5,
         combine (projS v) (projT v) k = v k) :=
  ⟨by decide, by decide, by decide, combine_proj_eq⟩

end E213.Lib.Math.Linalg213.Chiral
