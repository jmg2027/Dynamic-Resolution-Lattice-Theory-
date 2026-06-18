import E213.Lib.Physics.AtomicBase.Edges
import E213.Lib.Physics.AtomicBase.Force
import E213.Lib.Physics.Couplings.PhotonKernel
import E213.Lib.Physics.Simplex.Counts

/-!
# Phase 2 → Phase 1 Bridge — axiom-level = numeric track

**Layer: App** (cross-track consistency verification).

Phase 2 (Edges, Force): axiom-level arithmetic
  - num_directed_edges = NT · NS_atomic · NT = 12
  - cycle_space dim = 12 - 5 + 1 = 8 = NS_atomic² - 1

Phase 1 (PhotonKernel, SimplexCounts): precision quantity derivation
  - num_edges = NS · NT · NT = 12
  - b_1 = num_edges - num_vertices + 1 = 8 = NS² - 1 (= 1/α_3)

★ *Literally the same arithmetic* in both tracks ★ — formal proof in this file.
-/

namespace E213.Lib.Physics.AtomicBase.Phase1Bridge

open E213.Lib.Physics.AtomicBase.Edges
open E213.Lib.Physics.Simplex.Counts

/-- ★ Phase 1 ↔ Phase 2 bridge — axiom-level = numeric track ★

  Both tracks compute the same atomicity-locked quantities:
  NS_atomic = NS = 3, NT = 2, num_directed_edges = 12,
  cycle space dim = 8 = NS² − 1 = photon kernel b_1.

  Bundles all six bridge identities and the atomicity-locked
  algebraic identity NT·NS·NT − (NS+NT) + 1 = NS² − 1. -/
theorem bridge_capstone :
    NS_atomic = E213.Lib.Physics.Simplex.Counts.NS
    ∧ NT = 2
    ∧ num_directed_edges = E213.Lib.Physics.Couplings.PhotonKernel.num_edges
    ∧ num_directed_edges = 12
    ∧ num_directed_edges - 5 + 1 = E213.Lib.Physics.Couplings.PhotonKernel.b_1
    ∧ NS_atomic * NS_atomic - 1 = E213.Lib.Physics.Couplings.PhotonKernel.b_1
    ∧ NS_atomic * NS_atomic - 1 = 8
    -- Atomicity-locked algebraic identity
    ∧ NT * NS_atomic * NT - (NS_atomic + NT) + 1
        = NS_atomic * NS_atomic - 1 := by decide

end E213.Lib.Physics.AtomicBase.Phase1Bridge
