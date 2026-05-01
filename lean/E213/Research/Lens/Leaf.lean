import E213.Hypervisor.Lens
import E213.Research.Lens.Factoring
import E213.Meta.ParityLens

/-!
# Research.LeafLens: observing whether a Raw term is a leaf via a Lens

**Lens**: `leafLens : Lens Bool` extracts "is r a Raw.a or Raw.b?"
combine = const true.

This Lens sits **between leaves and parity** in the refines preorder —
coarser than leaves (less information), and incomparable with parity.

## Theorems

- `leafLens_view`: view r = "r is not a slash".
- `leaves_refines_leafLens`: leaves refines leafLens.
-/

namespace E213.Research.LeafLens

open E213.Firmware E213.Hypervisor E213.Research.LensFactoring

/-- Is r a leaf (Raw.a or Raw.b)? -/
def leafLens : Lens Bool where
  base_a := false
  base_b := false
  combine _ _ := true

/-- leaves r ≥ 1 for all r : Raw. -/
private theorem leaves_ge_one : ∀ r : Raw, 1 ≤ Lens.leaves.view r := by
  intro r
  induction r using Raw.rec with
  | a => decide
  | b => decide
  | slash x y h ihx ihy =>
      have hfs : Lens.leaves.view (Raw.slash x y h)
                   = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      rw [hfs]; omega

/-- leafLens.view r = decide (leaves r ≥ 2). -/
theorem leafLens_view_eq :
    ∀ r : Raw, leafLens.view r = decide (Lens.leaves.view r ≥ 2) := by
  intro r
  induction r using Raw.rec with
  | a => decide
  | b => decide
  | slash x y h ihx ihy =>
      have hfsL : leafLens.view (Raw.slash x y h) = true := by
        apply Raw.fold_slash
        intro u v; rfl
      have hfsN : Lens.leaves.view (Raw.slash x y h)
                    = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      have hx := leaves_ge_one x
      have hy := leaves_ge_one y
      rw [hfsL, hfsN]
      have : Lens.leaves.view x + Lens.leaves.view y ≥ 2 := by omega
      simp [this]

/-- **Lens.leaves refines leafLens** (leaves count determines
    leaf/slash status).  Via the factoring lemma. -/
theorem leaves_refines_leafLens : Lens.leaves.refines leafLens :=
  refines_of_factor Lens.leaves leafLens
    (fun n => decide (n ≥ 2)) leafLens_view_eq

end E213.Research.LeafLens

namespace E213.Research.LeafLens

open E213.Firmware E213.Hypervisor E213.Meta

/-- leafLens does not refine parityLens.
    Witness: Raw.a vs slash(a, slash(a,b)) — different leaf-ness
    but leafLens equates false/true... actually: a pair that are
    both slashes with different parity only.

    leafLens equates (Raw.slash a b) and slash(a, slash(a,b)):
    both are slashes → leafLens = true.  parity: 2 (even, false) vs
    3 (odd, true). Different. -/
def rAB : Raw := Raw.slash Raw.a Raw.b (by decide)
def rAAB : Raw :=
  Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide)) (by decide)

theorem leafLens_equates_slashes :
    leafLens.view rAB = leafLens.view rAAB := by decide

theorem parity_distinguishes_slashes :
    parityLens.view rAB ≠ parityLens.view rAAB := by decide

theorem leafLens_not_refines_parity :
    ¬ leafLens.refines parityLens := by
  intro h
  exact parity_distinguishes_slashes (h rAB rAAB leafLens_equates_slashes)

/-- parityLens does not refine leafLens either.
    Witness: Raw.a (leaf, parity=true) vs slash(a, slash(a,b))
    (slash, parity=true) — same parity, different leafness. -/
theorem parity_equates_leaf_slash :
    parityLens.view Raw.a = parityLens.view rAAB := by decide

theorem leafLens_distinguishes_leaf_slash :
    leafLens.view Raw.a ≠ leafLens.view rAAB := by decide

theorem parityLens_not_refines_leafLens :
    ¬ parityLens.refines leafLens := by
  intro h
  exact leafLens_distinguishes_leaf_slash
    (h Raw.a rAAB parity_equates_leaf_slash)

end E213.Research.LeafLens
