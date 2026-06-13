import E213.Lib.Math.NumberSystems.Real213.Completability.CompletabilityGrade
import E213.Lib.Math.Analysis.Cauchy.DepthCeilingResidue

/-!
# HeightTowerResidue — the height tower has no top; its diagonal is the residue

`CompletabilityGrade` made the completability height a genuine `ω`-coordinate: every step
up the exponential tower `expTower q (·)` breaks `CrossDetSmall` (`height_is_omega_coordinate`).
This file caps that axis: the height tower has **no top**, and naming "all heights at
once" diagonalizes to the **residue** — the same Cantor self-cover as
`DepthCeilingResidue` (`diag_not_in_seq`, `cantor_general`).

  * ★★ `height_tower_no_top` — `diag (expTower q)` (the height-tower diagonal,
    `n ↦ expTower q n n + 1`) is **not** any level `expTower q r`: referencing the whole
    tower produces a growth outside every finite height — the `ε₀`-style object beyond
    the finite `ω`-tower.
  * ★★★ `height_tower_residue` — bundles the open-endedness with its meaning: (i) every
    height step up overtakes (no level is final), (ii) the diagonal escapes every level
    (no top), (iii) that diagonalization **is** the pointing residue (`cantor_general` at
    the count scale).

So the completability height axis runs from the det-one **floor** (`DepthFloorDetOne`,
the trivially-free bottom) with **no top**: its ceiling is the residue.  Bottom (floor)
and top (residue) close into one self-cover loop — the refined real engine has no
exterior (`seed/AXIOM/05_no_exterior.md`); the height tower's `ε₀` cap is the residue
read at the scale of divergence-complexity.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Completability.HeightTowerResidue

open E213.Lib.Math.NumberSystems.Real213.CrossDet.CrossDetOvertake (CrossDetSmall)
open E213.Lib.Math.Analysis.Cauchy.DepthOmegaTower (expTower)
open E213.Lib.Math.Analysis.Cauchy.DepthCeilingResidue (diag diag_not_in_seq ceiling_reference_leaves_residue)
open E213.Lib.Math.NumberSystems.Real213.Completability.CompletabilityGrade (height_is_omega_coordinate)

/-- ★★ **The height tower has no top.**  The diagonal of the exponential height tower,
    `diag (expTower q) n = expTower q n n + 1`, is not any level `expTower q r` — naming
    the whole tower produces a growth outside every finite height.  The `ε₀`-style object
    above the finite `ω`-tower. -/
theorem height_tower_no_top (q : Nat) : ∀ r, diag (expTower q) ≠ expTower q r :=
  diag_not_in_seq (expTower q)

/-- ★★★ **The height tower's ceiling is the residue.**  (i) Every step up the exponential
    tower overtakes (`height_is_omega_coordinate`) — no completability level is final;
    (ii) the diagonal escapes every level (`height_tower_no_top`) — no top; (iii) that
    diagonalization is the pointing/Cantor residue (`ceiling_reference_leaves_residue` at
    the count scale).  So the refined engine's height axis is open-ended and capped by the
    residue — bottom (the det-one floor) and top (this residue) close into one self-cover
    loop with no exterior. -/
theorem height_tower_residue (q : Nat) (hq : 2 ≤ q) :
    (∀ r, ¬ CrossDetSmall (expTower q (r + 2)) (expTower q (r + 1)))
    ∧ (∀ r, diag (expTower q) ≠ expTower q r)
    ∧ (¬ ∃ g : Nat → (Nat → Bool), Function.Surjective g) :=
  ⟨height_is_omega_coordinate q hq, diag_not_in_seq (expTower q),
   ceiling_reference_leaves_residue⟩

end E213.Lib.Math.NumberSystems.Real213.Completability.HeightTowerResidue
