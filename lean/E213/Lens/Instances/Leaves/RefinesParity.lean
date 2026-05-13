import E213.Lens.Instances.Parity
import E213.Lens.Lattice.Lattice
import E213.Meta.Nat.AddMod213

/-!
# LeavesRefinesParity: concrete witness for Q37.2

**Claim**: `Lens.leaves.refines parityLens`.

Reason: parity (xor fold) is determined by `% 2` of the leaves count.
Therefore if the leaves count is equal, parity is also equal → the
kernel of leaves ⊆ kernel of parity → leaves refines parity.

In the refines preorder from note 37: `Lens.leaves ⊑ parityLens`
(leaves is finer).
-/

namespace E213.Lens.Instances.Leaves.RefinesParity

open E213.Theory E213.Lens
open E213.Lens.Instances.Parity (parityLens)

/-- PURE Nat.mod-2 case-analysis (replaces Nat.mod_two_eq_zero_or_one). -/
private theorem mod_two_pure (a : Nat) : a % 2 = 0 ∨ a % 2 = 1 := by
  have h : a % 2 < 2 := Nat.mod_lt a (by decide)
  match heq : a % 2, h with
  | 0, _ => exact Or.inl rfl
  | 1, _ => exact Or.inr rfl
  | n+2, h2 =>
    exfalso
    exact absurd h2 (Nat.not_lt_of_le (Nat.le_add_left 2 n))

private theorem bool_xor_parity (a b : Nat) :
    decide ((a + b) % 2 = 1)
      = xor (decide (a % 2 = 1)) (decide (b % 2 = 1)) := by
  have hadd : (a + b) % 2 = (a % 2 + b % 2) % 2 :=
    E213.Meta.Nat.AddMod213.add_mod_gen a b 2
  rw [hadd]
  rcases mod_two_pure a with ha | ha <;>
    rcases mod_two_pure b with hb | hb <;>
    rw [ha, hb] <;> rfl

/-- parityLens.view r = odd/even determination of the leaves count. -/
theorem parityLens_view_eq_leaves_odd :
    ∀ r : Raw,
      parityLens.view r = decide (Lens.leaves.view r % 2 = 1) := by
  intro r
  induction r using Raw.rec with
  | a => decide
  | b => decide
  | slash x y h ihx ihy =>
      have hfsP : parityLens.view (Raw.slash x y h)
                    = xor (parityLens.view x) (parityLens.view y) := by
        apply Raw.fold_slash
        intro u v; cases u <;> cases v <;> rfl
      have hfsN : Lens.leaves.view (Raw.slash x y h)
                    = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      rw [hfsP, hfsN, ihx, ihy]
      exact (bool_xor_parity _ _).symm

/-- **Q37.2 witness**: leaves refines parity. -/
theorem leaves_refines_parity : Lens.leaves.refines parityLens := by
  intro x y hxy
  have hxy' : Lens.leaves.view x = Lens.leaves.view y := hxy
  show parityLens.view x = parityLens.view y
  rw [parityLens_view_eq_leaves_odd x, parityLens_view_eq_leaves_odd y, hxy']

end E213.Lens.Instances.Leaves.RefinesParity

namespace E213.Lens.Instances.Leaves.RefinesParity

open E213.Theory E213.Lens
open E213.Lens.Instances.Parity (parityLens)

/-- Witness Raw element with leaves=3, parity=true. -/
def sample3 : Raw :=
  Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide)) (by decide)

/-- **Negative direction**: parity does not refine leaves.
    Witness: Raw.a (leaves=1, parity=true) vs sample3 (leaves=3,
    parity=true).  Same parity, different leaves count. -/
theorem parity_not_refines_leaves : ¬ parityLens.refines Lens.leaves := by
  intro h
  have hpar : parityLens.view Raw.a = parityLens.view sample3 := by decide
  have hleaves : Lens.leaves.view Raw.a = Lens.leaves.view sample3 :=
    h _ _ hpar
  have h1 : Lens.leaves.view Raw.a = 1 := rfl
  have h3 : Lens.leaves.view sample3 = 3 := by decide
  rw [h1, h3] at hleaves
  exact absurd hleaves (by decide)

end E213.Lens.Instances.Leaves.RefinesParity
