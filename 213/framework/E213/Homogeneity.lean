import E213.Clean213

/-!
# Homogeneity of Reachable + Aut-invariant Lens

We formalize the base swap automorphism `Raw.swap : Raw → Raw` and show:

1. `swap_swap` — swap is involutive (so bijective).
2. `Reachable.swap` — Reachable is preserved under swap.
3. `swap_invariant_const_obj` — a swap-invariant Lens has constant
   `objValue` on `Fin 2`.

This is the Raw-level incarnation of "every Reachable point has
isomorphic local structure" — at every base object, swap exchanges it
with the other; at every relation, swap acts recursively.
-/

/-- Flip the single base-object bit: `object 0 ↔ object 1`. -/
def flip213 (i : Fin 2) : Fin 2 := ⟨1 - i.val, by omega⟩

theorem flip213_flip213 (i : Fin 2) : flip213 (flip213 i) = i := by
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

/-- Swap automorphism: base objects exchanged; relation extended
    recursively. -/
def Raw.swap : Raw → Raw
  | .object i     => .object (flip213 i)
  | .relation x y => .relation (Raw.swap x) (Raw.swap y)

/-- Swap is involutive. -/
theorem Raw.swap_swap : ∀ x : Raw, (Raw.swap (Raw.swap x)) = x
  | .object i     => by simp [Raw.swap, flip213_flip213]
  | .relation x y => by
      simp [Raw.swap, Raw.swap_swap x, Raw.swap_swap y]

/-- Involutive ⟹ injective. -/
theorem Raw.swap_injective {x y : Raw}
    (h : Raw.swap x = Raw.swap y) : x = y := by
  have := congrArg Raw.swap h
  rw [Raw.swap_swap, Raw.swap_swap] at this
  exact this

/-- Reachable is preserved under swap (local structure isomorphism). -/
theorem Reachable.swap {x : Raw} (h : Reachable x) :
    Reachable (Raw.swap x) := by
  induction h with
  | base i =>
      show Reachable (Raw.swap (.object i))
      exact .base (flip213 i)
  | @step x y _ _ ihx ihy =>
      show Reachable (.relation (Raw.swap x) (Raw.swap y))
      exact .step ihx ihy

/-- A Lens is swap-invariant if its view agrees on x and swap(x). -/
def Lens.SwapInvariant {α : Type} (L : Lens α) : Prop :=
  ∀ x : Raw, L.view (Raw.swap x) = L.view x

/-- **Swap-invariance forces `objValue` to be constant on Fin 2.**
    This is the Raw-level Aut-invariant Lens theorem: the universal
    measure does not distinguish the two base objects. -/
theorem Lens.swapInvariant_const_obj {α : Type} {L : Lens α}
    (h : L.SwapInvariant) : L.objValue 0 = L.objValue 1 := by
  have h0 := h (.object 0)
  simp [Lens.view, Raw.swap, flip213] at h0
  exact h0.symm
