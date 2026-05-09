import E213.Lib.Physics.Symmetry.AutKChiral
import E213.Lib.Math.Cohomology.Cochain.Core

/-!
# Aut(K) acting on Cochain n k (C3 Step 2)

Step 2 of conjecture C3 (Aut(K) gauge group emergence) per
`research-notes/G35_chiral_cup_ring_catalog.md` §C3.

Encodes a sample group action of Aut(K_{3,2}^{(c=2)}) on
`Cochain 5 1` (vertex cochains).  Specifically: a single
permutation σ ∈ Sym(NS=3) acts on vertex indices, inducing a
linear map `Cochain 5 1 → Cochain 5 1`.

The full representation-theoretic decomposition (irreps of
Aut on `Cochain n k` for all k) is the open content of C3
Step 3+.  This file provides the action infrastructure.

STRICT ∅-AXIOM (decide on Bool/Fin equality).
-/

namespace E213.Lib.Physics.Symmetry.AutAction

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)

/-! ## §1 — Sample permutation σ = (S_0 S_1) ∈ Sym(3)

  The transposition swapping S-vertices 0 and 1 (fixing S-vertex 2,
  T-vertices 3 and 4). -/

/-- Sample transposition: swap indices 0 and 1, fix 2, 3, 4. -/
def σ_swap_01 (i : Fin 5) : Fin 5 :=
  if i.val = 0 then ⟨1, by decide⟩
  else if i.val = 1 then ⟨0, by decide⟩
  else i

/-- σ_swap_01 is its own inverse: σ ∘ σ = id. -/
theorem σ_swap_01_involution :
    ∀ i : Fin 5, σ_swap_01 (σ_swap_01 i) = i := by decide

/-! ## §2 — Action on Cochain 5 1 (vertex cochains) -/

/-- Aut action on vertex cochains: precompose with σ. -/
def aut_act (σ : Fin 5 → Fin 5) (α : Cochain 5 1) : Cochain 5 1 :=
  fun i => α (σ i)

/-- Identity action: σ = id ⟹ aut_act id α = α. -/
theorem aut_act_id (α : Cochain 5 1) : aut_act id α = α := rfl

/-- Action is involutive when σ is involutive. -/
theorem aut_act_involution (α : Cochain 5 1) :
    aut_act σ_swap_01 (aut_act σ_swap_01 α) = α := by
  funext i
  show α (σ_swap_01 (σ_swap_01 i)) = α i
  rw [σ_swap_01_involution]

end E213.Lib.Physics.Symmetry.AutAction
