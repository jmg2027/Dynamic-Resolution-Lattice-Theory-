import E213.Hypervisor.Lens.Instances.Parity
import E213.Hypervisor.Lens.Research.Lens.Lattice

/-!
# Research.LeavesRefinesParity: concrete witness for Q37.2

**Claim**: `Lens.leaves.refines parityLens`.

Reason: parity (xor fold) is determined by `% 2` of the leaves count.
Therefore if the leaves count is equal, parity is also equal → the
kernel of leaves ⊆ kernel of parity → leaves refines parity.

In the refines preorder from note 37: `Lens.leaves ⊑ parityLens`
(leaves is finer).
-/

namespace E213.Hypervisor.Lens.Research.Leaves.RefinesParity

open E213.Firmware E213.Hypervisor E213.Meta

private theorem bool_xor_parity (a b : Nat) :
    decide ((a + b) % 2 = 1)
      = xor (decide (a % 2 = 1)) (decide (b % 2 = 1)) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha
  all_goals rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  all_goals simp [Nat.add_mod, ha, hb]

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

end E213.Hypervisor.Lens.Research.Leaves.RefinesParity

namespace E213.Hypervisor.Lens.Research.Leaves.RefinesParity

open E213.Firmware E213.Hypervisor E213.Meta

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
  cases hleaves

end E213.Hypervisor.Lens.Research.Leaves.RefinesParity
