import E213.Lib.Math.Cohomology.Bipartite.V32Betti
import E213.Lib.Physics.Couplings.PhotonKernel
import E213.Lib.Physics.AlphaEM.Bare

import E213.Lib.Physics.Simplex.Counts
/-!
# Diamond Crystal — geometric formalization

The "diamond crystal" interpretation of the universe: N points
all directly connected via G_{ij}.  Gram matrix has rank ≤ 5
(atomicity-forced), so geometric image lies in ℂ⁵.  Any 5 points
form a chiral 4-simplex (K_{3,2}); other N−5 are linear
combinations projected onto its skeleton.

## Skeleton

  K_{3,2}^{(2)} bipartite multigraph
  5 vertices = 3 S (equatorial) + 2 T (polar)
  6 spokes (S-T) × c=2 multiplicity = 12 edges
  0 same-type edges (no S-S, no T-T)

## Visual

  T_0 (north pole)
  /|\\
  S_0–S_1–S_2  (equator, NO inter-S edges)
  \\|/
  T_1 (south pole)
  (each spoke doubled, c=2)

## Cohomology

  b_0 = 1 (connected), b_1 = 8 (= NS²−1 = 1/α_3)

See `books/physics/diamond.md` for narrative + figures.
-/

namespace E213.Lib.Math.Cohomology.DiamondShape

open E213.Lib.Physics.Simplex.Counts

/-- 5 vertices = NS + NT. -/
theorem total_vertices : NS + NT = 5 := by decide

/-- 3 equatorial pillars. -/
theorem spatial_pillars : NS = 3 := by decide

/-- 2 polar axes. -/
theorem temporal_axes : NT = 2 := by decide

/-- Bipartite spokes NS·NT = 6. -/
theorem bipartite_spokes : NS * NT = 6 := by decide

/-- c = 2 multiplicity. -/
theorem lattice_cycle : E213.Lib.Physics.AlphaEM.Prefactors.c_lat = 2 := by decide

/-- Total edges = c·NS·NT = 12. -/
theorem total_edges :
    E213.Lib.Physics.AlphaEM.Prefactors.c_lat * NS * NT = 12 := by decide

/-- Cycle dim b_1 = 8 = NS²−1 = 1/α_3. -/
theorem diamond_b1 :
    E213.Lib.Physics.Couplings.PhotonKernel.b_1 = 8
    ∧ (8 : Nat) = NS * NS - 1 :=
  ⟨E213.Lib.Physics.Couplings.PhotonKernel.b_1_eq_8, by decide⟩

/-- ★★★ DIAMOND CRYSTAL CAPSTONE ★★★ -/
theorem diamond_crystal_structure :
    NS + NT = 5
    ∧ NS = 3 ∧ NT = 2
    ∧ NS * NT = 6
    ∧ E213.Lib.Physics.AlphaEM.Prefactors.c_lat = 2
    ∧ E213.Lib.Physics.AlphaEM.Prefactors.c_lat * NS * NT = 12
    ∧ E213.Lib.Physics.Couplings.PhotonKernel.b_1 = 8
    ∧ (8 : Nat) = NS * NS - 1 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide,
          by decide, ?_, by decide⟩
  exact E213.Lib.Physics.Couplings.PhotonKernel.b_1_eq_8

end E213.Lib.Math.Cohomology.DiamondShape
