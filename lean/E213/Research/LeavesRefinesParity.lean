import E213.Meta.ParityLens
import E213.Research.LensLattice

/-!
# Research.LeavesRefinesParity: Q37.2 의 concrete witness

**주장**: `Lens.leaves.refines parityLens`.

이유: parity (xor fold) 는 leaves count 의 `% 2` 로 결정됨.
따라서 leaves count 가 같으면 parity 도 같다 → leaves 의
kernel ⊆ parity 의 kernel → leaves refines parity.

note 37 의 refines preorder 에서 `Lens.leaves ⊑ parityLens`
(leaves 가 더 finer).
-/

namespace E213.Research.LeavesRefinesParity

open E213.Firmware E213.Hypervisor E213.Meta

private theorem bool_xor_parity (a b : Nat) :
    decide ((a + b) % 2 = 1)
      = xor (decide (a % 2 = 1)) (decide (b % 2 = 1)) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha
  all_goals rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  all_goals simp [Nat.add_mod, ha, hb]

/-- parityLens.view r = leaves count 의 홀짝 판정. -/
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

end E213.Research.LeavesRefinesParity

namespace E213.Research.LeavesRefinesParity

open E213.Firmware E213.Hypervisor E213.Meta

/-- Witness Raw element with leaves=3, parity=true. -/
def sample3 : Raw :=
  Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide)) (by decide)

/-- **Negative direction**: parity 는 leaves 를 refine 하지 않음.
    Witness: Raw.a (leaves=1, parity=true) vs sample3 (leaves=3,
    parity=true).  같은 parity, 다른 leaves count. -/
theorem parity_not_refines_leaves : ¬ parityLens.refines Lens.leaves := by
  intro h
  have hpar : parityLens.view Raw.a = parityLens.view sample3 := by decide
  have hleaves : Lens.leaves.view Raw.a = Lens.leaves.view sample3 :=
    h _ _ hpar
  have h1 : Lens.leaves.view Raw.a = 1 := rfl
  have h3 : Lens.leaves.view sample3 = 3 := by decide
  rw [h1, h3] at hleaves
  cases hleaves

end E213.Research.LeavesRefinesParity
