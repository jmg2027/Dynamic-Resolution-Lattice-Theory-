import E213.Lib.Physics.Symmetry.AutAction

/-!
# Aut(K) acting on edge cochains (C3 Step 3)

Step 3 of conjecture C3 per `research-notes/G35` §C3.

Extends the vertex action `aut_act` to edge cochains by lifting
the vertex permutation σ to an edge permutation σ_E (mapping
edge {a, b} → edge {σ a, σ b}).

For Δ⁴ with binom(5, 2) = 10 edges, the colex enumeration is:
  edge 0: [0, 1]    edge 5: [2, 3]
  edge 1: [0, 2]    edge 6: [0, 4]
  edge 2: [1, 2]    edge 7: [1, 4]
  edge 3: [0, 3]    edge 8: [2, 4]
  edge 4: [1, 3]    edge 9: [3, 4]

The transposition σ_swap_01 (swapping vertices 0 and 1) acts on
edges as a permutation: swaps which 0/1 endpoints, fixing edges
that contain both or neither.

  edge [0,1] = edge 0 → swap doesn't change the set ⟹ fixed
  edge [0,2] = edge 1 → [1,2] = edge 2  ⟹  swap (1, 2)
  edge [1,2] = edge 2 → [0,2] = edge 1  ⟹  swap (1, 2)
  edge [0,3] = edge 3 → [1,3] = edge 4  ⟹  swap (3, 4)
  edge [1,3] = edge 4 → [0,3] = edge 3  ⟹  swap (3, 4)
  edge [2,3] = edge 5 → fixed
  edge [0,4] = edge 6 → [1,4] = edge 7  ⟹  swap (6, 7)
  edge [1,4] = edge 7 → [0,4] = edge 6  ⟹  swap (6, 7)
  edge [2,4] = edge 8 → fixed
  edge [3,4] = edge 9 → fixed

Edge permutation cycle structure: (1 2)(3 4)(6 7) — three
transpositions + four fixed points (0, 5, 8, 9).

STRICT ∅-AXIOM (decide on edge permutation rules).
-/

namespace E213.Lib.Physics.Symmetry.AutEdgeAction

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)

/-! ## §1 — Edge permutation induced by σ_swap_01 -/

/-- Edge index permutation induced by σ_swap_01 (vertex swap 0 ↔ 1).
    Edges containing both 0 and 1, or neither, are fixed.  Edges
    containing exactly one of {0, 1} are swapped pairwise. -/
def σ_E_swap_01 (e : Fin 10) : Fin 10 :=
  match e.val with
  | 1 => ⟨2, by decide⟩
  | 2 => ⟨1, by decide⟩
  | 3 => ⟨4, by decide⟩
  | 4 => ⟨3, by decide⟩
  | 6 => ⟨7, by decide⟩
  | 7 => ⟨6, by decide⟩
  | _ => e

/-- Edge permutation is involutive: σ_E ∘ σ_E = id. -/
theorem σ_E_swap_01_involution :
    ∀ e : Fin 10, σ_E_swap_01 (σ_E_swap_01 e) = e := by decide

/-- Action on `Cochain 5 2` (edge cochains). -/
def aut_act_edge (σ_E : Fin 10 → Fin 10) (α : Cochain 5 2) : Cochain 5 2 :=
  fun e => α (σ_E e)

/-- Identity action on edges: σ_E = id ⟹ aut_act_edge id α = α. -/
theorem aut_act_edge_id (α : Cochain 5 2) : aut_act_edge id α = α := rfl

/-- Edge action involutive when σ_E is involutive (pointwise;
    funext would leak Quot.sound).  PURE. -/
theorem aut_act_edge_involution (α : Cochain 5 2) (e : Fin 10) :
    aut_act_edge σ_E_swap_01 (aut_act_edge σ_E_swap_01 α) e = α e := by
  show α (σ_E_swap_01 (σ_E_swap_01 e)) = α e
  rw [σ_E_swap_01_involution]

/-! ## §2 — Master C3 Step 3 -/

/-- ★★★★★ Aut Edge Action Master (C3 Step 3).
    STRICT ∅-AXIOM.

    Lifts the vertex transposition (0 ↔ 1) ∈ Sym(NS) to an edge
    permutation, with cycle structure (1 2)(3 4)(6 7) on the 10
    Δ⁴ edges.  Edge action is involutive. -/
theorem aut_edge_action_master :
    -- Edge permutation is involution
    (∀ e : Fin 10, σ_E_swap_01 (σ_E_swap_01 e) = e)
    -- Specific edge mappings
    ∧ σ_E_swap_01 ⟨0, by decide⟩ = ⟨0, by decide⟩  -- [0,1] fixed
    ∧ σ_E_swap_01 ⟨1, by decide⟩ = ⟨2, by decide⟩  -- [0,2] ↔ [1,2]
    ∧ σ_E_swap_01 ⟨2, by decide⟩ = ⟨1, by decide⟩
    ∧ σ_E_swap_01 ⟨3, by decide⟩ = ⟨4, by decide⟩  -- [0,3] ↔ [1,3]
    ∧ σ_E_swap_01 ⟨5, by decide⟩ = ⟨5, by decide⟩  -- [2,3] fixed
    ∧ σ_E_swap_01 ⟨9, by decide⟩ = ⟨9, by decide⟩  -- [3,4] fixed
    := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact σ_E_swap_01_involution
  all_goals decide

end E213.Lib.Physics.Symmetry.AutEdgeAction
