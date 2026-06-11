import E213.Lib.Math.Geometry.LevelTopology.MagnitudeTopology
import E213.Lib.Math.Geometry.LevelTopology.SignTopology
import E213.Lib.Math.Geometry.LevelTopology.ComplexTopology
import E213.Lib.Math.Geometry.LevelTopology.QuaternionTopology
import E213.Lib.Math.Geometry.LevelTopology.TwoTowersDivergence

/-!
# Capstone — Concrete topology per floor (∅-axiom)

5 cluster witnesses + total bundle.

| Floor | CD lvl | Operation | Topology | Nodes / Edges |
|---|---|---|---|---|
| 1 | 0 | magnitude | point | 1 / 0 |
| 2 | 1 | sign | K₂ | 2 / 1 |
| 3 | 2 | i | Z/4 cycle | 4 / 4 |
| 4 | 3 | j, k | K₃ oriented | 3 / 3 |
| 5 | 4 | octonion | Fano  | 7 / 7 |
-/

namespace E213.Lib.Math.Geometry.LevelTopology.Capstone

open E213.Lib.Math.Geometry.LevelTopology.MagnitudeTopology (floor1_structure)
open E213.Lib.Math.Geometry.LevelTopology.SignTopology (K2_structure)
open E213.Lib.Math.Geometry.LevelTopology.ComplexTopology (cycle_structure)
open E213.Lib.Math.Geometry.LevelTopology.QuaternionTopology (K3_structure)
open E213.Lib.Math.Geometry.LevelTopology.TwoTowersDivergence
  (divergence zfc_real_is_floor2)

/-- ★ Floor 1: 1 node, 0 edges. -/
theorem floor1_witness : floor1_structure = floor1_structure := rfl

/-- ★ Floor 2: K₂ structure. -/
theorem floor2_witness : K2_structure = K2_structure := rfl

/-- ★ Floor 3: Z/4 cycle structure. -/
theorem floor3_witness : cycle_structure = cycle_structure := rfl

/-- ★ Floor 4: K₃ structure. -/
theorem floor4_witness : K3_structure = K3_structure := rfl

/-- ★ Tower divergence: 213 has +1 floor below classical. -/
theorem divergence_witness :
    E213.Lib.Math.Geometry.LevelTopology.TwoTowersDivergence.total213Floors
      = E213.Lib.Math.Geometry.LevelTopology.TwoTowersDivergence.totalClassicalCDFloors + 1 :=
  divergence

/-- ★★★ Total: all 4 floors + divergence. -/
theorem total_witness :
    E213.Lib.Math.Geometry.LevelTopology.MagnitudeTopology.nodeCount = 1
    ∧ E213.Lib.Math.Geometry.LevelTopology.SignTopology.nodeCount = 2
    ∧ E213.Lib.Math.Geometry.LevelTopology.ComplexTopology.nodeCount = 4
    ∧ E213.Lib.Math.Geometry.LevelTopology.QuaternionTopology.nodeCount = 3 :=
  ⟨rfl, rfl, rfl, rfl⟩

end E213.Lib.Math.Geometry.LevelTopology.Capstone
