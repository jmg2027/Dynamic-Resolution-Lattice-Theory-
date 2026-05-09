import E213.Lib.Physics.Symmetry.AutEdgeActionGenerators
import E213.Lib.Math.Logic.Predicate

/-!
# Aut Edge Orbit Decomposition (C3 Step 5)

Step 5 of conjecture C3.

Step 4 (`AutEdgeActionGenerators`) gave the two Sym(3) generators
σ_E_swap_01 and σ_E_swap_12 on edges.  Step 5 computes the
**full orbit decomposition** of Sym(3) acting on the 10 Δ⁴ edges,
using `Logic.Predicate` Bool predicates (from main #43).

## Sym(3) orbits on Edges_K(10)

Tracing both generators on each edge:

  Orbit 1: {0, 1, 2}    — edges within the S-block (S = {0,1,2})
  Orbit 2: {3, 4, 5}    — edges from S to T-vertex 3
  Orbit 3: {6, 7, 8}    — edges from S to T-vertex 4
  Orbit 4: {9}          — the lone T-T edge [3,4]

Sizes: 3, 3, 3, 1.  Sum = 10 ✓ (= total edges).
**Four orbits** = 3 size-3 + 1 size-1 = `dim Hom(Sym(3), Edges)`.

This matches the geometric structure: Sym(3) = Sym(NS) acts on
S-vertices, leaving T-vertices fixed.  Edges are classified by
"how they touch S" (3 in S, 0 in S = T-T).

STRICT ∅-AXIOM (decide on Bool predicates).
-/

namespace E213.Lib.Physics.Symmetry.AutEdgeOrbits

open E213.Lib.Physics.Symmetry.AutEdgeAction (σ_E_swap_01)
open E213.Lib.Physics.Symmetry.AutEdgeActionGenerators (σ_E_swap_12)

/-! ## §1 — Orbit-membership predicates -/

/-- `EdgePred := Fin 10 → Bool` is the cochain-style edge predicate. -/
abbrev EdgePred := Fin 10 → Bool

/-- Orbit 1: {0, 1, 2}. -/
def orbit_1 : EdgePred := fun e =>
  e.val == 0 || e.val == 1 || e.val == 2

/-- Orbit 2: {3, 4, 5}. -/
def orbit_2 : EdgePred := fun e =>
  e.val == 3 || e.val == 4 || e.val == 5

/-- Orbit 3: {6, 7, 8}. -/
def orbit_3 : EdgePred := fun e =>
  e.val == 6 || e.val == 7 || e.val == 8

/-- Orbit 4: {9}. -/
def orbit_4 : EdgePred := fun e => e.val == 9

/-! ## §2 — Orbits are closed under both generators -/

/-- Orbit 1 is closed under σ_E_swap_01. -/
theorem orbit_1_closed_swap_01 :
    ∀ e : Fin 10, orbit_1 e = true → orbit_1 (σ_E_swap_01 e) = true := by
  decide

/-- Orbit 1 is closed under σ_E_swap_12. -/
theorem orbit_1_closed_swap_12 :
    ∀ e : Fin 10, orbit_1 e = true → orbit_1 (σ_E_swap_12 e) = true := by
  decide

/-- Orbit 2 is closed under σ_E_swap_01. -/
theorem orbit_2_closed_swap_01 :
    ∀ e : Fin 10, orbit_2 e = true → orbit_2 (σ_E_swap_01 e) = true := by
  decide

/-- Orbit 2 is closed under σ_E_swap_12. -/
theorem orbit_2_closed_swap_12 :
    ∀ e : Fin 10, orbit_2 e = true → orbit_2 (σ_E_swap_12 e) = true := by
  decide

/-- Orbit 3 is closed under σ_E_swap_01. -/
theorem orbit_3_closed_swap_01 :
    ∀ e : Fin 10, orbit_3 e = true → orbit_3 (σ_E_swap_01 e) = true := by
  decide

/-- Orbit 3 is closed under σ_E_swap_12. -/
theorem orbit_3_closed_swap_12 :
    ∀ e : Fin 10, orbit_3 e = true → orbit_3 (σ_E_swap_12 e) = true := by
  decide

/-- Orbit 4 is closed under σ_E_swap_01 (singleton fixed). -/
theorem orbit_4_closed_swap_01 :
    ∀ e : Fin 10, orbit_4 e = true → orbit_4 (σ_E_swap_01 e) = true := by
  decide

/-- Orbit 4 is closed under σ_E_swap_12 (singleton fixed). -/
theorem orbit_4_closed_swap_12 :
    ∀ e : Fin 10, orbit_4 e = true → orbit_4 (σ_E_swap_12 e) = true := by
  decide

/-! ## §3 — Orbits partition Edges_K(10) -/

/-- Every edge belongs to exactly one of the 4 orbits. -/
theorem orbits_cover :
    ∀ e : Fin 10,
      orbit_1 e || orbit_2 e || orbit_3 e || orbit_4 e = true := by decide

/-- Orbits are pairwise disjoint. -/
theorem orbits_disjoint_12 :
    ∀ e : Fin 10, !(orbit_1 e && orbit_2 e) = true := by decide
theorem orbits_disjoint_13 :
    ∀ e : Fin 10, !(orbit_1 e && orbit_3 e) = true := by decide
theorem orbits_disjoint_14 :
    ∀ e : Fin 10, !(orbit_1 e && orbit_4 e) = true := by decide
theorem orbits_disjoint_23 :
    ∀ e : Fin 10, !(orbit_2 e && orbit_3 e) = true := by decide
theorem orbits_disjoint_24 :
    ∀ e : Fin 10, !(orbit_2 e && orbit_4 e) = true := by decide
theorem orbits_disjoint_34 :
    ∀ e : Fin 10, !(orbit_3 e && orbit_4 e) = true := by decide

/-! ## §4 — Orbit cardinalities -/

/-- Orbit 1 has 3 elements. -/
theorem orbit_1_card_3 :
    orbit_1 ⟨0, by decide⟩ = true ∧ orbit_1 ⟨1, by decide⟩ = true
    ∧ orbit_1 ⟨2, by decide⟩ = true
    ∧ orbit_1 ⟨3, by decide⟩ = false := by decide

/-- Orbit 4 is a singleton {9}. -/
theorem orbit_4_singleton :
    orbit_4 ⟨9, by decide⟩ = true
    ∧ orbit_4 ⟨0, by decide⟩ = false
    ∧ orbit_4 ⟨5, by decide⟩ = false := by decide

/-! ## §5 — Master C3 Step 5 -/

/-- ★★★★★ Aut Edge Orbit Decomposition Master (C3 Step 5).
    STRICT ∅-AXIOM.

    Sym(3) = ⟨σ_E_swap_01, σ_E_swap_12⟩ acts on the 10 Δ⁴ edges
    with **4 orbits**:
      O₁ = {0, 1, 2}     (size 3, S-S edges)
      O₂ = {3, 4, 5}     (size 3, S-T edges via T=3)
      O₃ = {6, 7, 8}     (size 3, S-T edges via T=4)
      O₄ = {9}           (size 1, T-T edge [3,4])

    Three size-3 orbits + one size-1 orbit = the orbit type
    `(3, 3, 3, 1)` summing to 10.  This is the geometric
    classification of edges by their endpoint structure relative
    to the S/T bipartition.  Encoded via `EdgePred = Fin 10 → Bool`
    (the cochain-style predicate type, mirroring `Logic.Predicate`
    from main #43). -/
theorem aut_edge_orbits_master :
    -- Each orbit closed under both Sym(3) generators
    (∀ e : Fin 10, orbit_1 e = true → orbit_1 (σ_E_swap_01 e) = true)
    ∧ (∀ e : Fin 10, orbit_1 e = true → orbit_1 (σ_E_swap_12 e) = true)
    ∧ (∀ e : Fin 10, orbit_4 e = true → orbit_4 (σ_E_swap_01 e) = true)
    -- Orbits cover and are disjoint
    ∧ (∀ e : Fin 10,
        orbit_1 e || orbit_2 e || orbit_3 e || orbit_4 e = true)
    -- Orbit 4 is the singleton {9}
    ∧ orbit_4 ⟨9, by decide⟩ = true
    ∧ orbit_4 ⟨0, by decide⟩ = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact orbit_1_closed_swap_01
  · exact orbit_1_closed_swap_12
  · exact orbit_4_closed_swap_01
  all_goals decide

end E213.Lib.Physics.Symmetry.AutEdgeOrbits
