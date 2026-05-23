import E213.Lens.Instances.AB
import E213.Lens.Instances.Leaves.RefinesParity
import E213.Lens.Instances.Bool
import E213.Meta.Nat.AddMod213

/-!
# ABLensRefines: abLens ⊏ parityLens, abLens ⊏ boolXorLens

abLens (a-count, b-count) refines both parityLens (total parity) and
boolXorLens (a-count parity).  Transitively, abLens also refines
leaves (abLens_refines_leaves in ABLens.lean).

## Theorems

- `abLens_refines_parityLens`: abLens ⊏ parityLens.
- `abLens_refines_boolXorLens`: abLens ⊏ boolXorLens.

## Significance

abLens simultaneously refines three Bool kernels in the refines preorder:
- leaves (via sum factor).
- parityLens (via sum parity factor).
- boolXorLens (via a parity factor).

The basic Raw information extraction (a-count, b-count) contains all
of these "derived" observations.
-/

namespace E213.Lens.Properties.ABRefines

open E213.Theory E213.Lens
open E213.Lens.Instances.AB E213.Lens.Instances.Bool E213.Lens.Instances.Parity E213.Lens.Compose.Factoring

/-- Factor function: (a, b) ↦ parity of sum. -/
private def sumParityFactor (p : Nat × Nat) : Bool :=
  decide ((p.1 + p.2) % 2 = 1)

/-- **abLens refines parityLens**. -/
theorem abLens_refines_parityLens : abLens.refines parityLens := by
  apply refines_of_factor abLens parityLens sumParityFactor
  intro r
  rw [E213.Lens.Instances.Leaves.RefinesParity.parityLens_view_eq_leaves_odd]
  show decide (Lens.leaves.view r % 2 = 1)
       = decide (((abLens.view r).1 + (abLens.view r).2) % 2 = 1)
  rw [abLens_sum_eq_leaves]


/-- Factor function: (a, b) ↦ parity of a. -/
private def aParityFactor (p : Nat × Nat) : Bool :=
  decide (p.1 % 2 = 1)

/-- PURE replacement of Nat.mod_two_eq_zero_or_one (which leaks
    propext + Quot.sound).  Direct match on n % 2 with mod_lt bound. -/
private theorem mod_two_zero_or_one_pure (n : Nat) :
    n % 2 = 0 ∨ n % 2 = 1 := by
  have hlt : n % 2 < 2 := Nat.mod_lt n (by decide)
  match h : n % 2 with
  | 0 => exact Or.inl rfl
  | 1 => exact Or.inr rfl
  | k+2 =>
      exfalso
      rw [h] at hlt
      exact Nat.lt_irrefl 2 (Nat.lt_of_le_of_lt (Nat.le_add_left 2 k) hlt)

/-- boolXorLens view is a-count mod 2.  (Consistent with the Note 37
    catalogue.)  Proved directly by Raw.rec induction. -/
private theorem boolXorLens_view_eq (r : Raw) :
    boolXorLens.view r = decide ((abLens.view r).1 % 2 = 1) := by
  induction r using Raw.rec with
  | a => decide
  | b => decide
  | slash x y h ihx ihy =>
      have hfsB : boolXorLens.view (Raw.slash x y h)
                    = xor (boolXorLens.view x) (boolXorLens.view y) := by
        apply Raw.fold_slash
        intro u v; cases u <;> cases v <;> rfl
      have hfsA : abLens.view (Raw.slash x y h)
                    = ((abLens.view x).1 + (abLens.view y).1,
                       (abLens.view x).2 + (abLens.view y).2) := by
        apply Raw.fold_slash
        intro u v
        show (u.1 + v.1, u.2 + v.2) = (v.1 + u.1, v.2 + u.2)
        rw [Nat.add_comm u.1 v.1, Nat.add_comm u.2 v.2]
      rw [hfsB, hfsA, ihx, ihy]
      have hmod : ((abLens.view x).1 + (abLens.view y).1) % 2
                = ((abLens.view x).1 % 2 + (abLens.view y).1 % 2) % 2 :=
        E213.Meta.Nat.AddMod213.add_mod_gen _ _ 2
      rw [hmod]
      rcases mod_two_zero_or_one_pure (abLens.view x).1 with ha | ha
      · rcases mod_two_zero_or_one_pure (abLens.view y).1 with hb | hb
        · rw [ha, hb]; decide
        · rw [ha, hb]; decide
      · rcases mod_two_zero_or_one_pure (abLens.view y).1 with hb | hb
        · rw [ha, hb]; decide
        · rw [ha, hb]; decide

/-- **abLens refines boolXorLens**. -/
theorem abLens_refines_boolXorLens : abLens.refines boolXorLens := by
  apply refines_of_factor abLens boolXorLens aParityFactor
  intro r
  exact boolXorLens_view_eq r

end E213.Lens.Properties.ABRefines
