import E213.Lens.LensCore
import E213.Theory.Raw.API
import E213.Meta.Int213.Core
import E213.Meta.Int213.PolyIntMTactic

/-!
# DifferenceLensFounding — `ℤ` is the count-Lens read on an ordered pair

`seed/AXIOM/06_lens_readings.md` §6.7 states the doctrine: `ℤ` is not imported; it is the
count-Lens (`Lens.leaves = ⟨1,1,+⟩`) read on an *ordered pair* of chain-readings `(m, n)` as their
difference `m − n` — magnitude the Nat-style count, **sign the Bool-style involution `−(−x) = x`**
(the pair-swap), with the diagonal pair `(m, m)` mapping to the negation-fixed-point `0`.

This file makes that doctrine a theorem rather than a narrative.  The **difference-Lens**
`diffView x y = subNatNat (leaves x) (leaves y)` reads two `Raw` chains by the count-Lens and names
their difference, and it satisfies exactly the §6.7 characterization:

  1. the count-Lens is the **`+ℕ` axis** — `subNatNat (leaves x) 0 = ofNat (leaves x)` (`ℤ` wraps
     `ℕ`: the bare count is the difference against nothing);
  2. the diagonal (equal counts) is the **negation-fixed-point `0`** — `diffView x x = 0`;
  3. the sign is the **period-2 pair-swap** — `diffView x y = −(diffView y x)`.

So `ℤ` is genuinely the *first bundling rung* of the Lens tower above the count-Lens — a
construction on the count-Lens reading, not a bare imported type.  (The next rung, additivity / the
group structure inherited from `Raw.leaves_slash`, is `difference_lens_slash_additive`.)
-/

namespace E213.Lens.Number.DifferenceLensFounding

open E213.Theory (Raw)

/-- The **difference-Lens**: read two `Raw` chains by the count-Lens and name their difference. -/
def diffView (x y : Raw) : Int :=
  Int.subNatNat (Lens.leaves.view x) (Lens.leaves.view y)

/-- ★★★ **`ℤ` is the count-Lens on an ordered pair (the §6.7 doctrine, as a theorem).**  The
    difference-Lens satisfies the three characterizing facts: the count-Lens is its `+ℕ` axis (`ℤ`
    wraps `ℕ`); the diagonal of equal counts is the negation-fixed-point `0`; and the sign is the
    period-2 pair-swap `−(−x) = x`.  `ℤ` is thus a *construction on the count-Lens*, the first
    bundling rung of the Lens tower — not an imported type. -/
theorem difference_lens_founds_on_count :
    (∀ x : Raw, Int.subNatNat (Lens.leaves.view x) 0 = Int.ofNat (Lens.leaves.view x))
    ∧ (∀ x : Raw, diffView x x = 0)
    ∧ (∀ x y : Raw, diffView x y = - diffView y x) :=
  ⟨fun x => E213.Meta.Int213.subNatNat_zero _,
   fun x => Int.subNatNat_self _,
   fun x y => (E213.Meta.Int213.neg_subNatNat (Lens.leaves.view y) (Lens.leaves.view x)).symm⟩

/-- Right-cancellation in the (PURE-derived) additive group of `Int`. -/
private theorem add_right_cancel_int {a b k : Int} (h : a + k = b + k) : a = b := by
  have e : (a + k) + -k = (b + k) + -k := congrArg (· + -k) h
  rw [E213.Meta.Int213.add_assoc, E213.Meta.Int213.add_neg_cancel,
      E213.Meta.Int213.add_assoc, E213.Meta.Int213.add_neg_cancel,
      E213.Meta.Int213.add_comm a 0, E213.Meta.Int213.zero_add,
      E213.Meta.Int213.add_comm b 0, E213.Meta.Int213.zero_add] at e
  exact e

/-- The difference (`subNatNat`) is additive over `Nat` addition — the Grothendieck/group law of
    the difference-Lens, derived from the keystone `subNatNat_add_self`. -/
theorem subNatNat_additive (a b c d : Nat) :
    Int.subNatNat (a + c) (b + d) = Int.subNatNat a b + Int.subNatNat c d := by
  refine add_right_cancel_int (k := Int.ofNat (b + d)) ?_
  rw [E213.Meta.Int213.subNatNat_add_self (a + c) (b + d),
      show Int.ofNat (a + c) = Int.ofNat a + Int.ofNat c from rfl,
      show Int.ofNat (b + d) = Int.ofNat b + Int.ofNat d from rfl,
      ← E213.Meta.Int213.subNatNat_add_self a b, ← E213.Meta.Int213.subNatNat_add_self c d]
  ring_intZ

/-- ★★★ **The difference-Lens is a slash-homomorphism — `ℤ`'s group law is the count-Lens's,
    bundled.**  `diffView (x/x') (y/y') = diffView x y + diffView x' y'`: the difference-Lens
    inherits its additivity directly from the count-Lens's slash-additivity (`Raw.leaves_slash`,
    via `subNatNat_additive`).  So `ℤ` is not merely a structure with a sign — it is the count-Lens
    *bundled into a group*, the first genuine bundling rung of the Lens tower above `ℕ`. -/
theorem difference_lens_slash_additive (x x' y y' : Raw) (h : x ≠ x') (h' : y ≠ y') :
    diffView (Raw.slash x x' h) (Raw.slash y y' h') = diffView x y + diffView x' y' := by
  have hx : Lens.leaves.view (Raw.slash x x' h) = Lens.leaves.view x + Lens.leaves.view x' := by
    apply Raw.fold_slash; intro u v; exact Nat.add_comm u v
  have hy : Lens.leaves.view (Raw.slash y y' h') = Lens.leaves.view y + Lens.leaves.view y' := by
    apply Raw.fold_slash; intro u v; exact Nat.add_comm u v
  show Int.subNatNat (Lens.leaves.view (Raw.slash x x' h)) (Lens.leaves.view (Raw.slash y y' h'))
      = _
  rw [hx, hy]
  exact subNatNat_additive _ _ _ _

end E213.Lens.Number.DifferenceLensFounding
