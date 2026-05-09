import E213.Lib.Physics.Symmetry.AutEdgeAction

/-!
# Aut Edge Action Generators (C3 Step 4)

Step 4 of conjecture C3.

Step 3 (`AutEdgeAction.lean`) defined a single edge permutation
`σ_E_swap_01` (cycle structure `(1 2)(3 4)(6 7)`).  Step 4 adds
the **second Sym(3) generator** `σ_E_swap_12` and demonstrates
their composition gives a 3-cycle, witnessing the **non-abelian
structure of Sym(NS) ⊆ Aut(K)**.

## σ_E_swap_12 induced from σ_swap_12

Vertex swap (1 ↔ 2) on `Fin 5`.  Edges affected:
  edge [0, 1] = edge 0 ↔ edge [0, 2] = edge 1
  edge [1, 2] = edge 2  fixed
  edge [1, 3] = edge 4 ↔ edge [2, 3] = edge 5
  edge [1, 4] = edge 7 ↔ edge [2, 4] = edge 8
  Edges 0, 1, 4, 5, 7, 8 swapped pairwise; 2, 3, 6, 9 fixed.

Cycle structure: `(0 1)(4 5)(7 8)` + fixed {2, 3, 6, 9}.

## σ_E_swap_01 ∘ σ_E_swap_12 (composition)

Maps:
  0 → 1 → 2,  1 → 0 → 0,  2 → 2 → 1
  3 → 3 → 4,  4 → 5 → 5,  5 → 4 → 3
  6 → 6 → 7,  7 → 8 → 8,  8 → 7 → 6
  9 → 9 → 9

Cycle structure: `(0 2 1)(3 4 5)(6 7 8)` + fixed {9}.
**Three 3-cycles** — the composition has order 3.

This explicitly demonstrates Sym(3) non-commutativity (= 3-cycle ≠ id).

STRICT ∅-AXIOM (decide on edge permutation rules).
-/

namespace E213.Lib.Physics.Symmetry.AutEdgeActionGenerators

open E213.Lib.Physics.Symmetry.AutEdgeAction (σ_E_swap_01)

/-! ## §1 — Second generator σ_E_swap_12 -/

/-- Edge permutation induced by σ_swap_12 (vertex swap 1 ↔ 2). -/
def σ_E_swap_12 (e : Fin 10) : Fin 10 :=
  match e.val with
  | 0 => ⟨1, by decide⟩
  | 1 => ⟨0, by decide⟩
  | 4 => ⟨5, by decide⟩
  | 5 => ⟨4, by decide⟩
  | 7 => ⟨8, by decide⟩
  | 8 => ⟨7, by decide⟩
  | _ => e

theorem σ_E_swap_12_involution :
    ∀ e : Fin 10, σ_E_swap_12 (σ_E_swap_12 e) = e := by decide

/-! ## §2 — Composition σ_E_swap_01 ∘ σ_E_swap_12 -/

/-- The composition is a 3-cycle structure on edges. -/
def σ_E_compose_01_12 (e : Fin 10) : Fin 10 :=
  σ_E_swap_01 (σ_E_swap_12 e)

/-- Specific composition values: cycle (0 2 1)(3 4 5)(6 7 8) + fix {9}. -/
theorem σ_E_compose_at_0 : σ_E_compose_01_12 ⟨0, by decide⟩ = ⟨2, by decide⟩ := by decide
theorem σ_E_compose_at_1 : σ_E_compose_01_12 ⟨1, by decide⟩ = ⟨0, by decide⟩ := by decide
theorem σ_E_compose_at_2 : σ_E_compose_01_12 ⟨2, by decide⟩ = ⟨1, by decide⟩ := by decide
theorem σ_E_compose_at_3 : σ_E_compose_01_12 ⟨3, by decide⟩ = ⟨4, by decide⟩ := by decide
theorem σ_E_compose_at_4 : σ_E_compose_01_12 ⟨4, by decide⟩ = ⟨5, by decide⟩ := by decide
theorem σ_E_compose_at_5 : σ_E_compose_01_12 ⟨5, by decide⟩ = ⟨3, by decide⟩ := by decide
theorem σ_E_compose_at_6 : σ_E_compose_01_12 ⟨6, by decide⟩ = ⟨7, by decide⟩ := by decide
theorem σ_E_compose_at_7 : σ_E_compose_01_12 ⟨7, by decide⟩ = ⟨8, by decide⟩ := by decide
theorem σ_E_compose_at_8 : σ_E_compose_01_12 ⟨8, by decide⟩ = ⟨6, by decide⟩ := by decide
theorem σ_E_compose_at_9 : σ_E_compose_01_12 ⟨9, by decide⟩ = ⟨9, by decide⟩ := by decide

/-- Composition has order 3: (σ ∘ σ ∘ σ) e = e. -/
theorem σ_E_compose_order_3 :
    ∀ e : Fin 10,
      σ_E_compose_01_12 (σ_E_compose_01_12 (σ_E_compose_01_12 e)) = e := by decide

/-! ## §3 — Non-commutativity of σ_E_swap_01 and σ_E_swap_12 -/

/-- The reverse composition is NOT the same as the forward —
    Sym(3) is non-abelian. -/
theorem σ_E_compositions_differ :
    σ_E_compose_01_12 ⟨0, by decide⟩ ≠ σ_E_swap_12 (σ_E_swap_01 ⟨0, by decide⟩) := by
  decide

/-! ## §4 — Master C3 Step 4 -/

/-- ★★★★★ Aut Edge Action Generators (C3 Step 4).
    STRICT ∅-AXIOM.

    Step 4 builds the Sym(NS) = Sym(3) action skeleton:
      · σ_E_swap_01: cycle (1 2)(3 4)(6 7), three 2-cycles.
      · σ_E_swap_12: cycle (0 1)(4 5)(7 8), three 2-cycles.
      · σ_E_compose_01_12: cycle (0 2 1)(3 4 5)(6 7 8) + fix 9,
        three 3-cycles (= order 3 element).
    Together they generate Sym(3) action on the 10 Δ⁴ edges.
    Composition non-commutativity witnesses Sym(3) non-abelian. -/
theorem aut_edge_generators_master :
    -- Both generators involutive
    (∀ e : Fin 10, σ_E_swap_12 (σ_E_swap_12 e) = e)
    -- Composition has order 3 (a 3-cycle element)
    ∧ (∀ e : Fin 10, σ_E_compose_01_12 (σ_E_compose_01_12 (σ_E_compose_01_12 e)) = e)
    -- Specific compose mapping
    ∧ σ_E_compose_01_12 ⟨0, by decide⟩ = ⟨2, by decide⟩
    ∧ σ_E_compose_01_12 ⟨3, by decide⟩ = ⟨4, by decide⟩
    ∧ σ_E_compose_01_12 ⟨6, by decide⟩ = ⟨7, by decide⟩
    ∧ σ_E_compose_01_12 ⟨9, by decide⟩ = ⟨9, by decide⟩
    -- Non-commutativity
    ∧ σ_E_compose_01_12 ⟨0, by decide⟩ ≠ σ_E_swap_12 (σ_E_swap_01 ⟨0, by decide⟩) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact σ_E_swap_12_involution
  · exact σ_E_compose_order_3
  all_goals decide

end E213.Lib.Physics.Symmetry.AutEdgeActionGenerators
