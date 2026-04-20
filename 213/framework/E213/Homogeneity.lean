import E213.Clean213

/-!
# Swap automorphism on Raw

The two base tokens `a, b` can be exchanged; extended through the
`slash` operation recursively. At the canonical-form level, after
swapping children we must re-order them (implementation artifact of
the Lean encoding — see `Clean213.lean`).

This file defines swap at the `Tree` level with re-canonicalization,
then lifts to `Raw`.
-/

/-- Swap on the internal Tree.  After exchanging children by the
    recursive swap, re-order so the smaller child comes first. -/
def Tree.swap : Tree → Tree
  | .a         => .b
  | .b         => .a
  | .slash x y =>
      let x' := Tree.swap x
      let y' := Tree.swap y
      match Tree.cmp x' y' with
      | .lt => .slash x' y'
      | .gt => .slash y' x'
      | .eq => x'  -- unreachable on canonical inputs (distinct children)

theorem Tree.swap_a_b : Tree.swap .a = .b := rfl
theorem Tree.swap_b_a : Tree.swap .b = .a := rfl

/-- A Lens is *swap-invariant* iff its view agrees on `x` and
    the swapped Raw. Expressed at the Tree level for convenience. -/
def Lens.SwapInvariant {α : Type} (L : Lens α) : Prop :=
  ∀ t : Tree, L.viewTree (Tree.swap t) = L.viewTree t

/-- Swap-invariance forces the two base values to coincide:
    at the Lens layer, swap-invariance means "cannot tell `a` from
    `b`," which Lean-ly says `L.base_a = L.base_b`. -/
theorem Lens.swapInvariant_base_eq {α : Type} {L : Lens α}
    (h : L.SwapInvariant) : L.base_a = L.base_b := by
  have h0 := h .a
  simp [Lens.viewTree, Tree.swap] at h0
  exact h0.symm
