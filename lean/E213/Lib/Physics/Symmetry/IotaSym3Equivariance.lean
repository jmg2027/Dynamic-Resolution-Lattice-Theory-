import E213.Lib.Physics.Symmetry.IotaKToDelta4
import E213.Lib.Physics.Symmetry.Sym3OnKEdges
import E213.Lib.Physics.Symmetry.AutEdgeAction

/-!
# Sym(3)-equivariance of ι: K → Δ⁴ — Phase 8

Phase 8 of the **C3 chain** — proves the embedding ι_edge from
Phase 7 is **Sym(3)-equivariant**:

    ι_edge ∘ σ_K = σ_Δ⁴ ∘ ι_edge

for each transposition (σ_S01, σ_S12) of Sym(3).

This is the equivariance that makes the gluon octet identification
`coker ι* = H¹(K)` a **Sym(3)-equivariant** isomorphism — i.e., the
gluon octet inherits a Sym(3) representation structure from both
sides of the identification.

## Edge action correspondence

K_{3,2}^{(c=2)} S-S Δ⁴ vertex swap correspondence is direct
(K's 5 vertices = Δ⁴'s 5 vertices).  Under the vertex swap
S0 ↔ S1:
  · K edges 0–3 (S0 src) ↔ K edges 4–7 (S1 src)
  · Δ⁴ edges incident to vertex 0 ↔ Δ⁴ edges incident to vertex 1

AutEdgeAction.σ_E_swap_01 already encodes the Δ⁴ side.  We define
σ_E_Δ4_swap_12 for the S1 ↔ S2 generator.

All theorems below are **PURE** via `decide`.
-/

namespace E213.Lib.Physics.Symmetry.IotaSym3Equivariance

open E213.Lib.Physics.Symmetry.IotaKToDelta4 (ι_edge ι_pullback)
open E213.Lib.Physics.Symmetry.Sym3OnKEdges (σ_S01 σ_S12)
open E213.Lib.Physics.Symmetry.AutEdgeAction (σ_E_swap_01)

/-! ## §1.  σ_E_Δ4_swap_12: Δ⁴ vertex 1 ↔ 2 swap on edges

Edge effects of swapping vertices 1 and 2 on the 10 Δ⁴ edges
(colex enumeration):
  · [0,1] (edge 0) ↔ [0,2] (edge 1)   ⟹ swap (0, 1)
  · [1,2] (edge 2) fixed (both swapped)
  · [0,3] (edge 3) fixed (no 1 or 2)
  · [1,3] (edge 4) ↔ [2,3] (edge 5)   ⟹ swap (4, 5)
  · [0,4] (edge 6) fixed
  · [1,4] (edge 7) ↔ [2,4] (edge 8)   ⟹ swap (7, 8)
  · [3,4] (edge 9) fixed
-/

/-- Edge permutation induced by Δ⁴ vertex swap 1 ↔ 2.  Cycle
    structure (0 1)(4 5)(7 8) with fixed points {2, 3, 6, 9}. -/
def σ_E_Δ4_swap_12 (e : Fin 10) : Fin 10 :=
  match e.val with
  | 0 => ⟨1, by decide⟩
  | 1 => ⟨0, by decide⟩
  | 4 => ⟨5, by decide⟩
  | 5 => ⟨4, by decide⟩
  | 7 => ⟨8, by decide⟩
  | 8 => ⟨7, by decide⟩
  | _ => e

/-- σ_E_Δ4_swap_12 is involution. -/
theorem σ_E_Δ4_swap_12_involution :
    ∀ e : Fin 10, σ_E_Δ4_swap_12 (σ_E_Δ4_swap_12 e) = e := by decide

/-! ## §2.  Sym(3)-equivariance: ι_edge ∘ σ_K = σ_Δ⁴ ∘ ι_edge -/

/-- ★ Equivariance under the S0 ↔ S1 generator:
    `ι_edge (σ_S01 e) = σ_E_swap_01 (ι_edge e)` for all K edges e. -/
theorem ι_equivariance_S01 :
    ∀ e : Fin 12, ι_edge (σ_S01 e) = σ_E_swap_01 (ι_edge e) := by decide

/-- ★ Equivariance under the S1 ↔ S2 generator:
    `ι_edge (σ_S12 e) = σ_E_Δ4_swap_12 (ι_edge e)` for all K edges e. -/
theorem ι_equivariance_S12 :
    ∀ e : Fin 12, ι_edge (σ_S12 e) = σ_E_Δ4_swap_12 (ι_edge e) := by decide

/-! ## §3.  Cochain pullback equivariance

For α : Cochain 5 2 (= Δ⁴ edge cochain), the equivariance lifts to
the pullback:

  ι_pullback (σ_E_Δ4_swap_01 · α) = σ_act_E σ_S01 · (ι_pullback α)

This is the cochain-level expression of `ι_edge ∘ σ_S01 = σ_E_Δ4_swap_01 ∘ ι_edge`.
Pointwise form (no funext). -/

open E213.Lib.Physics.Symmetry.Sym3OnKEdges (σ_act_E)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)

/-- Pullback of the Δ⁴-edge action via σ_E_swap_01.  Equivalent
    pullback definition pre-composing with σ_E_swap_01. -/
def Δ4_act_E (σ_Δ : Fin 10 → Fin 10) (α : Cochain 5 2) : Cochain 5 2 :=
  fun e => α (σ_Δ e)

/-- ★ Cochain pullback equivariance under σ_S01.

    `ι_pullback (Δ4_act_E σ_E_swap_01 α) e = σ_act_E σ_S01 (ι_pullback α) e`

    pointwise on each K edge.  PURE. -/
theorem ι_pullback_equivariance_S01 (α : Cochain 5 2) (e : Fin 12) :
    ι_pullback (Δ4_act_E σ_E_swap_01 α) e
      = σ_act_E σ_S01 (ι_pullback α) e := by
  show α (σ_E_swap_01 (ι_edge e)) = α (ι_edge (σ_S01 e))
  rw [ι_equivariance_S01 e]

/-- ★ Cochain pullback equivariance under σ_S12. -/
theorem ι_pullback_equivariance_S12 (α : Cochain 5 2) (e : Fin 12) :
    ι_pullback (Δ4_act_E σ_E_Δ4_swap_12 α) e
      = σ_act_E σ_S12 (ι_pullback α) e := by
  show α (σ_E_Δ4_swap_12 (ι_edge e)) = α (ι_edge (σ_S12 e))
  rw [ι_equivariance_S12 e]

/-! ## §4.  Δ⁴ Sym(3) Cayley structure

Both Δ⁴ edge permutations are involutions; their composition is a
3-cycle on Δ⁴ edges. -/

/-- σ_E_Δ4_swap_01 ∘ σ_E_Δ4_swap_12 has order 3 — same Cayley as on K. -/
theorem Δ4_ρ_order_3 :
    ∀ e : Fin 10,
      σ_E_swap_01 (σ_E_Δ4_swap_12 (σ_E_swap_01 (σ_E_Δ4_swap_12 (σ_E_swap_01 (σ_E_Δ4_swap_12 e))))) = e := by decide

/-! ## §5.  Phase-8 capstone -/

/-- ★★ **Phase-8 capstone**: ι: K → Δ⁴ is **Sym(3)-equivariant**.

    Substantive content:
      (a) σ_E_Δ4_swap_12 — Δ⁴-edge permutation for the second
          transposition (vertex 1 ↔ 2); involution.
      (b) `★ ι_equivariance_S01` — edge-level commutation
          `ι_edge ∘ σ_S01 = σ_E_swap_01 ∘ ι_edge`.
      (c) `★ ι_equivariance_S12` — edge-level commutation for
          the second transposition.
      (d) Cochain pullback equivariance (pointwise):
          `ι_pullback ∘ Δ4_act = K_act ∘ ι_pullback` for both
          transposition generators.
      (e) Δ⁴ 3-cycle has order 3 (Cayley check at Δ⁴ side).

    Consequence: the gluon octet identification
    `coker ι* = H¹(K) ≃ (F_2)^8` (from Phase 7) is **Sym(3)-equivariant**
    — i.e., the gluon octet acquires a Sym(3) representation structure
    that lifts (via the Weyl-group embedding Sym(3) ⊂ SU(3)) to the
    full SU(3) adjoint structure on the QCD octet.

    PURE. -/
theorem IotaSym3Equivariance_capstone :
    -- Δ⁴ edge perm for second generator is involution
    (∀ e : Fin 10, σ_E_Δ4_swap_12 (σ_E_Δ4_swap_12 e) = e)
    -- Edge-level equivariance (both generators)
    ∧ (∀ e : Fin 12, ι_edge (σ_S01 e) = σ_E_swap_01 (ι_edge e))
    ∧ (∀ e : Fin 12, ι_edge (σ_S12 e) = σ_E_Δ4_swap_12 (ι_edge e))
    -- Cochain pullback equivariance (pointwise)
    ∧ (∀ α : Cochain 5 2, ∀ e : Fin 12,
         ι_pullback (Δ4_act_E σ_E_swap_01 α) e
           = σ_act_E σ_S01 (ι_pullback α) e)
    ∧ (∀ α : Cochain 5 2, ∀ e : Fin 12,
         ι_pullback (Δ4_act_E σ_E_Δ4_swap_12 α) e
           = σ_act_E σ_S12 (ι_pullback α) e)
    -- Δ⁴ 3-cycle Cayley
    ∧ (∀ e : Fin 10,
        σ_E_swap_01 (σ_E_Δ4_swap_12 (σ_E_swap_01
          (σ_E_Δ4_swap_12 (σ_E_swap_01 (σ_E_Δ4_swap_12 e))))) = e)
    := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact σ_E_Δ4_swap_12_involution
  · exact ι_equivariance_S01
  · exact ι_equivariance_S12
  · exact ι_pullback_equivariance_S01
  · exact ι_pullback_equivariance_S12
  · exact Δ4_ρ_order_3

end E213.Lib.Physics.Symmetry.IotaSym3Equivariance
