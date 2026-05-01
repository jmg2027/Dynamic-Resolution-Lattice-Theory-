import E213.Hypervisor.Lens
import E213.Research.Lens.Factoring

/-!
# Research.ABLens: Counting Raw.a and Raw.b separately

`abLens : Lens (Nat × Nat)` — view r = (number of Raw.a leaves in r,
number of Raw.b leaves in r).

## Position

Finer than Lens.leaves in the refines preorder (distinguishes Raw.a
from Raw.b).  Also finer than boolXorLens (full a-count vs mod 2).

- `abLens_refines_leaves` : Contains total-sum information of Lens.leaves.
- abLens kernel: Raw elements with the same `(a count, b count)`.

This is one concrete layer of note 41 Q41.3 ("number of kernels at
each level of the refines preorder").
-/

namespace E213.Research.Lens.AB

open E213.Firmware E213.Hypervisor E213.Research.Lens.Factoring

/-- Track Raw.a count and Raw.b count componentwise. -/
def abLens : Lens (Nat × Nat) where
  base_a := (1, 0)
  base_b := (0, 1)
  combine p q := (p.1 + q.1, p.2 + q.2)

private theorem abLens_sym (u v : Nat × Nat) :
    abLens.combine u v = abLens.combine v u := by
  show (u.1 + v.1, u.2 + v.2) = (v.1 + u.1, v.2 + u.2)
  rw [Nat.add_comm u.1 v.1, Nat.add_comm u.2 v.2]

/-- The sum of the two components of view equals the leaves count. -/
theorem abLens_sum_eq_leaves :
    ∀ r : Raw, (abLens.view r).1 + (abLens.view r).2 = Lens.leaves.view r := by
  intro r
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hfsA : abLens.view (Raw.slash x y h)
                    = abLens.combine (abLens.view x) (abLens.view y) :=
        Raw.fold_slash _ _ _ abLens_sym x y h
      have hfsL : Lens.leaves.view (Raw.slash x y h)
                    = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      rw [hfsA, hfsL]
      show (abLens.view x).1 + (abLens.view y).1
           + ((abLens.view x).2 + (abLens.view y).2)
           = Lens.leaves.view x + Lens.leaves.view y
      omega

/-- Factor function sum: (a, b) ↦ a + b. -/
private def sumFactor (p : Nat × Nat) : Nat := p.1 + p.2

/-- **abLens refines leaves**. -/
theorem abLens_refines_leaves : abLens.refines Lens.leaves := by
  apply refines_of_factor abLens Lens.leaves sumFactor
  intro r
  exact (abLens_sum_eq_leaves r).symm

end E213.Research.Lens.AB

namespace E213.Research.Lens.AB

open E213.Firmware E213.Hypervisor

/-- Witness: 2a + 1b. -/
def rAAB : Raw :=
  Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide)) (by decide)

/-- Witness: 1a + 2b. -/
def rABB : Raw :=
  Raw.slash Raw.b (Raw.slash Raw.a Raw.b (by decide)) (by decide)

theorem leaves_equates : Lens.leaves.view rAAB = Lens.leaves.view rABB := by decide

theorem abLens_distinguishes :
    abLens.view rAAB ≠ abLens.view rABB := by decide

/-- **abLens ⊏ Lens.leaves** strictly (same leaf count, different (a, b) distribution). -/
theorem leaves_not_refines_abLens : ¬ Lens.leaves.refines abLens := by
  intro h
  exact abLens_distinguishes (h rAAB rABB leaves_equates)

end E213.Research.Lens.AB
