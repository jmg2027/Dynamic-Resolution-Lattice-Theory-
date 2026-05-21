import E213.Lib.Math.Cohomology.CupAW.BasisLeibniz

import E213.Lib.Math.Cohomology.Cochain.Core
/-!
# Cochain 5 1 / Cochain 5 2 — basis decomposition

σ : Cochain 5 1 = (σ 0)? e_0 : 0 + ... + (σ 4)? e_4 : 0
σ : Cochain 5 2 = (σ 0)? f_0 : 0 + ... + (σ 9)? f_9 : 0

Pointwise verified by funext + match j + cases on each (σ ⟨k, _⟩).
-/

namespace E213.Lib.Math.Cohomology.Cochain.V5Decomp

open E213.Lib.Math.Cohomology.CupAW.BasisLeibniz (basis)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)

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

/-! This file provides the bz5_1 / decomp_5_1 definitions.
    See `V5_1DecompR.lean` for the AND-form variant with PURE
    per-index `decomp_step_at_*` helpers. -/

end E213.Lib.Math.Cohomology.Cochain.V5Decomp
