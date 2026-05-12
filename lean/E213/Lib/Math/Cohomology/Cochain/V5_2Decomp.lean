import E213.Lib.Math.Cohomology.Cochain.V5Decomp
import E213.Meta.Tactic.Nat213

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.CupAW.BasisLeibniz
/-!
# Cochain 5 2 — basis decomposition (10-term, definitional reduction)

bz5_2 β k j := (k.val == j.val) && β k

  - on-diagonal (k = j): true && β j  = β j (definitional)
  - off-diagonal (k ≠ j): false && β k = false (definitional)

So the XOR sum reduces definitionally per j; only one `cases`
on (β j) needed to close.
-/

namespace E213.Lib.Math.Cohomology.Cochain.V5_2Decomp

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.BasisLeibniz (basis)

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

/-- Per-index helpers (PUBLIC PURE).  Single literal `k`, see
    `decomp_step_at_k_block` files for k=0..9. -/
theorem decomp_step_at_0 (β : Cochain 5 2) :
    decomp_5_2 β ⟨0, by decide⟩ = β ⟨0, by decide⟩ := by
  show xor (β ⟨0, by decide⟩) false = β ⟨0, by decide⟩
  cases (β ⟨0, by decide⟩) <;> rfl

theorem decomp_step_at_1 (β : Cochain 5 2) :
    decomp_5_2 β ⟨1, by decide⟩ = β ⟨1, by decide⟩ := by
  show xor false (xor (β ⟨1, by decide⟩) false) = β ⟨1, by decide⟩
  cases (β ⟨1, by decide⟩) <;> rfl

theorem decomp_step_at_2 (β : Cochain 5 2) :
    decomp_5_2 β ⟨2, by decide⟩ = β ⟨2, by decide⟩ := by
  show xor false (xor false (xor (β ⟨2, by decide⟩) false))
       = β ⟨2, by decide⟩
  cases (β ⟨2, by decide⟩) <;> rfl

theorem decomp_step_at_3 (β : Cochain 5 2) :
    decomp_5_2 β ⟨3, by decide⟩ = β ⟨3, by decide⟩ := by
  show xor false (xor false (xor false (xor (β ⟨3, by decide⟩) false)))
       = β ⟨3, by decide⟩
  cases (β ⟨3, by decide⟩) <;> rfl

theorem decomp_step_at_4 (β : Cochain 5 2) :
    decomp_5_2 β ⟨4, by decide⟩ = β ⟨4, by decide⟩ := by
  show xor false (xor false (xor false (xor false (xor (β ⟨4, by decide⟩) false))))
       = β ⟨4, by decide⟩
  cases (β ⟨4, by decide⟩) <;> rfl

theorem decomp_step_at_5 (β : Cochain 5 2) :
    decomp_5_2 β ⟨5, by decide⟩ = β ⟨5, by decide⟩ := by
  show xor false (xor false (xor false (xor false
       (xor false (xor (β ⟨5, by decide⟩) false)))))
       = β ⟨5, by decide⟩
  cases (β ⟨5, by decide⟩) <;> rfl

theorem decomp_step_at_6 (β : Cochain 5 2) :
    decomp_5_2 β ⟨6, by decide⟩ = β ⟨6, by decide⟩ := by
  show xor false (xor false (xor false (xor false
       (xor false (xor false (xor (β ⟨6, by decide⟩) false))))))
       = β ⟨6, by decide⟩
  cases (β ⟨6, by decide⟩) <;> rfl

theorem decomp_step_at_7 (β : Cochain 5 2) :
    decomp_5_2 β ⟨7, by decide⟩ = β ⟨7, by decide⟩ := by
  show xor false (xor false (xor false (xor false (xor false
       (xor false (xor false (xor (β ⟨7, by decide⟩) false)))))))
       = β ⟨7, by decide⟩
  cases (β ⟨7, by decide⟩) <;> rfl

theorem decomp_step_at_8 (β : Cochain 5 2) :
    decomp_5_2 β ⟨8, by decide⟩ = β ⟨8, by decide⟩ := by
  show xor false (xor false (xor false (xor false (xor false
       (xor false (xor false (xor false (xor (β ⟨8, by decide⟩) false))))))))
       = β ⟨8, by decide⟩
  cases (β ⟨8, by decide⟩) <;> rfl

theorem decomp_step_at_9 (β : Cochain 5 2) :
    decomp_5_2 β ⟨9, by decide⟩ = β ⟨9, by decide⟩ := by
  show xor false (xor false (xor false (xor false (xor false
       (xor false (xor false (xor false (xor false (β ⟨9, by decide⟩)))))))))
       = β ⟨9, by decide⟩
  cases (β ⟨9, by decide⟩) <;> rfl

/-! Note: the funext-based `decomp_5_2_eq : decomp_5_2 β = β` was
    removed (it had no remaining consumers — all LeibnizAlgLift*
    refactors now go through the per-index `decomp_step_at_*` PURE
    helpers above).  Eliminating it removed the file's last DIRTY
    entry (Quot.sound via funext, Cat 1 inherent). -/

end E213.Lib.Math.Cohomology.Cochain.V5_2Decomp
