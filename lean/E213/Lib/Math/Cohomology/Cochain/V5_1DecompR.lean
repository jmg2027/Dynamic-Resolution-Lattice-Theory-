import E213.Lib.Math.Cohomology.CupAW.BasisLeibniz
import E213.Meta.Tactic.NatHelper

import E213.Lib.Math.Cohomology.Cochain.Core
/-!
# Cochain 5 1 — basis decomposition (right-nested, AND-form)

Mirror of `Cochain5_2Decomp` for Cochain 5 1.  AND-form for
definitional reduction; right-nested for consistency with
`combine_5`.

  bz5_1_r β k j := (k.val == j.val) && β k
-/

namespace E213.Lib.Math.Cohomology.Cochain.V5_1DecompR

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.BasisLeibniz (basis)

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

/-- Per-index helpers (PUBLIC PURE).  Single literal `k`, see
    V5_2Decomp.decomp_step_at_* for design rationale. -/
theorem decomp_step_at_0 (β : Cochain 5 1) :
    decomp_5_1 β ⟨0, by decide⟩ = β ⟨0, by decide⟩ := by
  show xor (β ⟨0, by decide⟩) false = β ⟨0, by decide⟩
  cases (β ⟨0, by decide⟩) <;> rfl

theorem decomp_step_at_1 (β : Cochain 5 1) :
    decomp_5_1 β ⟨1, by decide⟩ = β ⟨1, by decide⟩ := by
  show xor false (xor (β ⟨1, by decide⟩) false) = β ⟨1, by decide⟩
  cases (β ⟨1, by decide⟩) <;> rfl

theorem decomp_step_at_2 (β : Cochain 5 1) :
    decomp_5_1 β ⟨2, by decide⟩ = β ⟨2, by decide⟩ := by
  show xor false (xor false (xor (β ⟨2, by decide⟩) false))
       = β ⟨2, by decide⟩
  cases (β ⟨2, by decide⟩) <;> rfl

theorem decomp_step_at_3 (β : Cochain 5 1) :
    decomp_5_1 β ⟨3, by decide⟩ = β ⟨3, by decide⟩ := by
  show xor false (xor false (xor false (xor (β ⟨3, by decide⟩) false)))
       = β ⟨3, by decide⟩
  cases (β ⟨3, by decide⟩) <;> rfl

theorem decomp_step_at_4 (β : Cochain 5 1) :
    decomp_5_1 β ⟨4, by decide⟩ = β ⟨4, by decide⟩ := by
  show xor false (xor false (xor false (xor false (β ⟨4, by decide⟩))))
       = β ⟨4, by decide⟩
  cases (β ⟨4, by decide⟩) <;> rfl

/-! Note: the funext-based `decomp_5_1_eq : decomp_5_1 β = β` was
    removed (LeibnizAlgLift21 now uses the per-index `decomp_step_at_*`
    PURE helpers above). -/

end E213.Lib.Math.Cohomology.Cochain.V5_1DecompR
