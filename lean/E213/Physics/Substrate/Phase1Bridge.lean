import E213.Physics.Substrate.Edges
import E213.Physics.Substrate.Force
import E213.Physics.Couplings.PhotonKernel
import E213.Physics.Simplex.Counts

/-!
# Phase 2 → Phase 1 Bridge — axiom-level = numeric track

**Layer: App** (cross-track consistency verification).

Phase 2 (Edges, Force): axiom-level arithmetic
  - num_directed_edges = c_lattice · NS_atomic · 2 = 12
  - cycle_space dim = 12 - 5 + 1 = 8 = NS_atomic² - 1

Phase 1 (PhotonKernel, SimplexCounts): precision quantity derivation
  - num_edges = c_lat · NS · NT = 12
  - b_1 = num_edges - num_vertices + 1 = 8 = NS² - 1 (= 1/α_3)

★ *Literally the same arithmetic* in both tracks ★ — formal proof in this file.
-/

namespace E213.Physics.Phase2.Phase1Bridge

open E213.Physics.Phase2.Edges
open E213.Physics.Simplex

/-- NS_atomic (Phase 2) = NS (Phase 1).  Both are 3. -/
theorem NS_match : NS_atomic = E213.Physics.Simplex.NS := by decide

/-- c_lattice (Phase 2) = 2 = Phase 1 c_lat value. -/
theorem c_match : c_lattice = 2 := by decide

/-- num_directed_edges (Phase 2) = num_edges (Phase 1) = 12. -/
theorem edges_match :
    num_directed_edges = E213.Physics.PhotonKernel.num_edges := by
  decide

/-- Phase 2 cycle space dim = Phase 1 b_1. -/
theorem cycle_space_match :
    num_directed_edges - 5 + 1 = E213.Physics.PhotonKernel.b_1 := by
  decide

/-- Phase 2 NS² - 1 = Phase 1 photon kernel. -/
theorem photon_kernel_match :
    NS_atomic * NS_atomic - 1 = E213.Physics.PhotonKernel.b_1 := by
  decide

/-- Atomicity-locked identity holds in Phase 2 quantities. -/
theorem atomicity_locked_in_phase2 :
    c_lattice * NS_atomic * 2 - (NS_atomic + 2) + 1
    = NS_atomic * NS_atomic - 1 := by decide

/-- ★ Bridge synthesis — Phase 1 ↔ Phase 2 arithmetic identical ★ -/
theorem bridge_capstone :
    (NS_atomic = E213.Physics.Simplex.NS)
    ∧ (c_lattice = 2)
    ∧ (num_directed_edges = E213.Physics.PhotonKernel.num_edges)
    ∧ (num_directed_edges = 12)
    ∧ (num_directed_edges - 5 + 1 = E213.Physics.PhotonKernel.b_1)
    ∧ (NS_atomic * NS_atomic - 1 = 8) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end E213.Physics.Phase2.Phase1Bridge
