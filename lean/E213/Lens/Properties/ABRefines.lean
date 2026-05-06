import E213.Lens.Instances.AB
import E213.Lens.Leaves.RefinesParity
import E213.Lens.Instances.Bool

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

open E213.Theory E213.Lens E213.Meta
open E213.Lens.Instances.AB E213.Lens.Compose.Factoring

/-- Factor function: (a, b) ↦ parity of sum. -/
private def sumParityFactor (p : Nat × Nat) : Bool :=
  decide ((p.1 + p.2) % 2 = 1)

/-- **abLens refines parityLens**. -/
theorem abLens_refines_parityLens : abLens.refines parityLens := by
  apply refines_of_factor abLens parityLens sumParityFactor
  intro r
  rw [E213.Lens.Leaves.RefinesParity.parityLens_view_eq_leaves_odd]
  show decide (Lens.leaves.view r % 2 = 1)
       = decide (((abLens.view r).1 + (abLens.view r).2) % 2 = 1)
  rw [abLens_sum_eq_leaves]

end E213.Lens.Properties.ABRefines

namespace E213.Lens.Properties.ABRefines

open E213.Theory E213.Lens E213.Meta
open E213.Lens.Instances.AB E213.Lens.Compose.Factoring

/-- Factor function: (a, b) ↦ parity of a. -/
private def aParityFactor (p : Nat × Nat) : Bool :=
  decide (p.1 % 2 = 1)

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
      rcases Nat.mod_two_eq_zero_or_one (abLens.view x).1 with ha | ha
      all_goals rcases Nat.mod_two_eq_zero_or_one (abLens.view y).1 with hb | hb
      all_goals simp_all [Nat.add_mod]

/-- **abLens refines boolXorLens**. -/
theorem abLens_refines_boolXorLens : abLens.refines boolXorLens := by
  apply refines_of_factor abLens boolXorLens aParityFactor
  intro r
  exact boolXorLens_view_eq r

end E213.Lens.Properties.ABRefines
