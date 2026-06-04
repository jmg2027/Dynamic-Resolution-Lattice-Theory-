import E213.Lens.Number.FoldDuality

/-!
# The two folds generate a Klein four-group on the fixture; the third involution is fixed-point-free

`FoldDuality` showed negation `negQ` and reciprocal `recQ` are mirror involutions on the four-point
fixture `Q4 = {∞, 0, +1, −1}`: each fixes the two-element orbit the other swaps.  Composing them
closes the symmetry: `negQ` and `recQ` commute, and their composite

  `bothSwap := negQ ∘ recQ = recQ ∘ negQ`

is the **third non-identity involution** — it **swaps both** orbits at once (`0 ↔ ∞` *and*
`+1 ↔ −1`) and so is **fixed-point-free**.  Together with the identity, `{id, negQ, recQ, bothSwap}`
is the **Klein four-group** `ℤ/2 × ℤ/2` acting on the fixture, and the three non-identity elements are
completely distinguished by **which orbit they fix**:

  - `negQ` — fixes `{0, ∞}` (the 영무한대 / hole pair), swaps `{±1}`;
  - `recQ` — fixes `{±1}` (the units), swaps `{0, ∞}`;
  - `bothSwap` — fixes **neither** (the antipode, fixed-point-free).

So the additive fold, the multiplicative fold, and their composite exhaust the involutive symmetries
of the hole/unit fixture: the two founding folds are the two reflections whose product is the central
antipode, and the residue pair `{0, ∞}` and the unit pair `{±1}` are the two axes they act on.
-/

namespace E213.Lens.Number.FoldKlein

open E213.Lens.Number.FoldDuality (Q4 negQ recQ BothFixed Swapped)

/-- The third involution: swap **both** pairs at once (`0 ↔ ∞` and `+1 ↔ −1`). -/
def bothSwap : Q4 → Q4
  | .inf => .zero
  | .zero => .inf
  | .one => .negOne
  | .negOne => .one

/-! ## `bothSwap` is the composite of the two folds (which commute) -/

/-- `bothSwap = negQ ∘ recQ`. -/
theorem bothSwap_eq_negQ_recQ : ∀ x, negQ (recQ x) = bothSwap x := by intro x; cases x <;> rfl

/-- `bothSwap = recQ ∘ negQ` — so the two folds **commute**. -/
theorem bothSwap_eq_recQ_negQ : ∀ x, recQ (negQ x) = bothSwap x := by intro x; cases x <;> rfl

/-- The two folds commute (`negQ ∘ recQ = recQ ∘ negQ`). -/
theorem negQ_recQ_comm : ∀ x, negQ (recQ x) = recQ (negQ x) := by intro x; cases x <;> rfl

/-! ## `bothSwap` is a fixed-point-free involution -/

theorem bothSwap_involutive : ∀ x, bothSwap (bothSwap x) = x := by intro x; cases x <;> rfl

/-- ★★ `bothSwap` **swaps both** orbits — the antipode. -/
theorem bothSwap_swaps_both : Swapped bothSwap .zero .inf ∧ Swapped bothSwap .one .negOne :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- ★★★ `bothSwap` is **fixed-point-free**: it fixes no element of the fixture (the only one of the
    three non-identity involutions that fixes neither orbit). -/
theorem bothSwap_no_fixed : ∀ x, bothSwap x ≠ x := by intro x; cases x <;> decide

/-! ## The Klein four-group multiplication -/

/-- ★★★★ **`{id, negQ, recQ, bothSwap}` is the Klein four-group `ℤ/2 × ℤ/2`.**  Each non-identity
    element is an involution, and the three pairwise products close among them:
    `negQ·recQ = recQ·negQ = bothSwap`, `recQ·bothSwap = negQ`, `negQ·bothSwap = recQ`. -/
theorem klein_four_group :
    (∀ x, negQ (negQ x) = x)
    ∧ (∀ x, recQ (recQ x) = x)
    ∧ (∀ x, bothSwap (bothSwap x) = x)
    ∧ (∀ x, negQ (recQ x) = bothSwap x)
    ∧ (∀ x, recQ (negQ x) = bothSwap x)
    ∧ (∀ x, recQ (bothSwap x) = negQ x)
    ∧ (∀ x, negQ (bothSwap x) = recQ x) :=
  ⟨FoldDuality.negQ_involutive, FoldDuality.recQ_involutive, bothSwap_involutive,
   bothSwap_eq_negQ_recQ, bothSwap_eq_recQ_negQ,
   by intro x; cases x <;> rfl, by intro x; cases x <;> rfl⟩

/-- ★★★★ **The three folds are distinguished by which orbit they fix.**  `negQ` fixes the hole pair
    `{0, ∞}`; `recQ` fixes the unit pair `{±1}`; `bothSwap` fixes neither.  The additive fold, the
    multiplicative fold, and their antipode product exhaust the involutive symmetries of the fixture,
    one per choice of fixed orbit (hole, unit, none). -/
theorem klein_fixed_orbit_profile :
    BothFixed negQ .zero .inf
    ∧ BothFixed recQ .one .negOne
    ∧ (∀ x, bothSwap x ≠ x) :=
  ⟨FoldDuality.negQ_fixes_zeroInf, FoldDuality.recQ_fixes_units, bothSwap_no_fixed⟩

end E213.Lens.Number.FoldKlein
