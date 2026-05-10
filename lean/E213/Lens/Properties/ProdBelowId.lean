import E213.Lens.Instances.Identity
import E213.Lens.Lattice.Meet

/-!
# ProdBelowId: witness for Q39.2

`prodLens Lens.leaves Lens.depth ⊏ idLens` strictly.  That is,
there exist distinct Raw elements with equal (leaves, depth) pairs.

Witness:
- `rA` := `a / (a / (a/b))` — leaves=4, depth=3.
- `rB` := `a / (b / (a/b))` — leaves=4, depth=3.
- `rA ≠ rB` (the left side of the inner slash differs: a vs b).

Not distinguishable by (leaves, depth), but distinguishable by idLens.
-/

namespace E213.Lens.Properties.ProdBelowId

open E213.Theory E213.Lens
open E213.Lens.Instances.Identity E213.Lens.Lattice.Meet

/-- Witness A: `a / (a / (a/b))`. -/
def rA : Raw :=
  Raw.slash Raw.a
    (Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide)) (by decide))
    (by decide)

/-- Witness B: `a / (b / (a/b))`. -/
def rB : Raw :=
  Raw.slash Raw.a
    (Raw.slash Raw.b (Raw.slash Raw.a Raw.b (by decide)) (by decide))
    (by decide)

theorem rA_ne_rB : rA ≠ rB := by decide

theorem leaves_equal : Lens.leaves.view rA = Lens.leaves.view rB := by decide

theorem depth_equal : Lens.depth.view rA = Lens.depth.view rB := by decide

private theorem leaves_sym : ∀ u v : Nat, u + v = v + u := Nat.add_comm

/-- Inline 213-native max_comm (Lean-core Nat.max_comm leaks propext
    via Nat.max_eq_left).  Direct case-split via Nat.le_total. -/
private theorem nat_max_comm_pure (a b : Nat) : Nat.max a b = Nat.max b a := by
  rcases Nat.le_total a b with hab | hba
  · show (if a ≤ b then b else a) = (if b ≤ a then a else b)
    rw [if_pos hab]
    by_cases h : b ≤ a
    · rw [if_pos h]; exact Nat.le_antisymm h hab
    · rw [if_neg h]
  · show (if a ≤ b then b else a) = (if b ≤ a then a else b)
    rw [if_pos hba]
    by_cases h : a ≤ b
    · rw [if_pos h]; exact Nat.le_antisymm hba h
    · rw [if_neg h]

private theorem depth_sym :
    ∀ u v : Nat, 1 + max u v = 1 + max v u := by
  intro u v
  congr 1
  exact nat_max_comm_pure u v

/-- prod of (leaves, depth) equates rA and rB. -/
theorem prod_equates :
    (prodLens Lens.leaves Lens.depth).view rA
      = (prodLens Lens.leaves Lens.depth).view rB := by
  rw [prodLens_view _ _ leaves_sym depth_sym,
      prodLens_view _ _ leaves_sym depth_sym,
      leaves_equal, depth_equal]

/-- **idLens distinguishes them** (they are unequal Raw). -/
theorem idLens_distinguishes : idLens.view rA ≠ idLens.view rB := by
  rw [idLens_is_id, idLens_is_id]
  exact rA_ne_rB

/-- **Strict refinement**: prodLens (leaves, depth) does not refine
    idLens (a pair indistinguishable by prod is distinguishable by
    idLens).  That is, the kernel of prod is strictly larger than the
    kernel of idLens → prod ⊏ idLens but prod ≠ idLens. -/
theorem prod_not_refines_idLens :
    ¬ (prodLens Lens.leaves Lens.depth).refines idLens := by
  intro h
  exact idLens_distinguishes (h rA rB prod_equates)

end E213.Lens.Properties.ProdBelowId
