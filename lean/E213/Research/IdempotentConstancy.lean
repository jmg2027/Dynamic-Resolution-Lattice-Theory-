import E213.Math.Diagonal.Classification

/-!
# Research.IdempotentConstancy: Idempotent + swap-blind ⟹ constant

**Theorem**: if `L : Lens α` is Idempotent and has `base_a = base_b`
(swap-blind) and a symmetric combine, then `L.view` is constant
(= `L.base_a`).

## Significance

An idempotent combine means "merging something with itself leaves it
unchanged."  If the base is swap-blind, every leaf has the same value →
every fold value also has the same value (idempotent preserved).
View collapses.

This generalizes why boolAndLens and boolOrLens have the constant
`view r = true`.  A natural bridge between the Idempotent category
of Note 35 and the near-top (constant view Lens) of Note 37.
-/

namespace E213.Research.IdempotentConstancy

open E213.Firmware E213.Hypervisor E213.Math.DiagonalClassification

/-- **Idempotent + swap-blind base → constant view**. -/
theorem idempotent_swap_blind_const {α : Type} (L : Lens α)
    (hI : Idempotent L) (hbase : L.base_a = L.base_b)
    (hsym : ∀ u v : α, L.combine u v = L.combine v u) :
    ∀ r : Raw, L.view r = L.base_a := by
  intro r
  induction r using Raw.rec with
  | a => rfl
  | b => exact hbase.symm
  | slash x y h ihx ihy =>
      have hfs : L.view (Raw.slash x y h)
                   = L.combine (L.view x) (L.view y) :=
        Raw.fold_slash _ _ _ hsym x y h
      rw [hfs, ihx, ihy]
      exact hI L.base_a

end E213.Research.IdempotentConstancy
