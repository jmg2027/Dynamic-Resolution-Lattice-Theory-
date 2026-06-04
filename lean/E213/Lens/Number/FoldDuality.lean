import E213.Lens.Number.IntFoldForms

/-!
# One carrier, two folds, dual patterns — negation and reciprocal mirror each other

The two founding folds are negation (`ℤ = invert(+)`, additive) and reciprocal (`ℚ = invert(×)`,
multiplicative).  `IntFoldForms` gave the additive fold its status-symmetric carrier and showed
negation **fixes** the `{0, ∞}` pair.  Here both folds meet on the **shared four-point fixture**
`{∞, 0, +1, −1}` — the reciprocal-closed core of `ℤ̂` (the only integers with an integer reciprocal,
plus the hole `0` and its twin `∞`) — where both are total involutions and the duality is exact:

  - **negation** `negQ`: **fixes** the `{0, ∞}` pair (the 영무한대 / hole pair), **swaps** the
    `{+1, −1}` pair (the units);
  - **reciprocal** `recQ`: **swaps** the `{0, ∞}` pair, **fixes** the `{+1, −1}` pair.

So the two folds are not merely both status-symmetric (§6.9) — they are **mirror images**: each ℤ/2
action fixes the orbit the other swaps.  The `{0, ∞}` pair and the `{±1}` pair are the two
two-element orbits of the fixture, and the additive/multiplicative folds exchange which one is the
fixed locus and which is the swapped locus.  This is the sharpest form of "0 is to the additive fold
as 1 is to the multiplicative fold": negation's fixed pair (`{0,∞}`) is reciprocal's swapped pair, and
reciprocal's fixed pair (`{±1}`) is negation's swapped pair.
-/

namespace E213.Lens.Number.FoldDuality

/-- The shared four-point fixture `{∞, 0, +1, −1}`: the reciprocal-closed core of `ℤ̂`. -/
inductive Q4 where
  | inf
  | zero
  | one
  | negOne
  deriving DecidableEq

/-- Additive fold (negation) on the fixture: `∞ ↦ ∞`, `0 ↦ 0`, `+1 ↦ −1`, `−1 ↦ +1`. -/
def negQ : Q4 → Q4
  | .inf => .inf
  | .zero => .zero
  | .one => .negOne
  | .negOne => .one

/-- Multiplicative fold (reciprocal) on the fixture: `∞ ↔ 0`, `+1 ↦ +1`, `−1 ↦ −1`. -/
def recQ : Q4 → Q4
  | .inf => .zero
  | .zero => .inf
  | .one => .one
  | .negOne => .negOne

/-! ## Both folds are involutions -/

theorem negQ_involutive : ∀ x, negQ (negQ x) = x := by intro x; cases x <;> rfl

theorem recQ_involutive : ∀ x, recQ (recQ x) = x := by intro x; cases x <;> rfl

/-! ## Status-symmetry predicates (§6.9): the two admissible patterns on a pair -/

/-- An involution **fixes** a pair: both elements are its own image. -/
def BothFixed (f : Q4 → Q4) (a b : Q4) : Prop := f a = a ∧ f b = b

/-- An involution **swaps** a pair: each element is the other's image. -/
def Swapped (f : Q4 → Q4) (a b : Q4) : Prop := f a = b ∧ f b = a

/-! ## The exact duality -/

/-- ★★ Negation **fixes** the 영무한대 pair `{0, ∞}`. -/
theorem negQ_fixes_zeroInf : BothFixed negQ .zero .inf := ⟨rfl, rfl⟩

/-- ★★ Negation **swaps** the unit pair `{+1, −1}`. -/
theorem negQ_swaps_units : Swapped negQ .one .negOne := ⟨rfl, rfl⟩

/-- ★★ Reciprocal **swaps** the 영무한대 pair `{0, ∞}`. -/
theorem recQ_swaps_zeroInf : Swapped recQ .zero .inf := ⟨rfl, rfl⟩

/-- ★★ Reciprocal **fixes** the unit pair `{+1, −1}`. -/
theorem recQ_fixes_units : BothFixed recQ .one .negOne := ⟨rfl, rfl⟩

/-- The fixed points of negation are exactly the 영무한대 pair `{0, ∞}`. -/
theorem negQ_fixed_iff (x : Q4) : negQ x = x ↔ x = .zero ∨ x = .inf := by
  cases x <;> exact ⟨by decide, by decide⟩

/-- The fixed points of reciprocal are exactly the unit pair `{+1, −1}`. -/
theorem recQ_fixed_iff (x : Q4) : recQ x = x ↔ x = .one ∨ x = .negOne := by
  cases x <;> exact ⟨by decide, by decide⟩

/-- ★★★★ **The two folds are mirror images on the fixture.**  Negation fixes the 영무한대 pair
    `{0, ∞}` and swaps the units `{±1}`; reciprocal swaps `{0, ∞}` and fixes `{±1}`.  Each ℤ/2 fold
    fixes the orbit the other swaps — the additive and multiplicative folds exchange the roles of the
    hole pair and the unit pair. -/
theorem two_folds_dual_on_pairs :
    (BothFixed negQ .zero .inf ∧ Swapped negQ .one .negOne)
    ∧ (Swapped recQ .zero .inf ∧ BothFixed recQ .one .negOne) :=
  ⟨⟨negQ_fixes_zeroInf, negQ_swaps_units⟩, ⟨recQ_swaps_zeroInf, recQ_fixes_units⟩⟩

end E213.Lens.Number.FoldDuality
