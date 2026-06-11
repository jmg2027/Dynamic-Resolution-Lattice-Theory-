# 1 · The list and the question

## The list

Begin with less than usual.  Not "the natural numbers with addition
and multiplication", not Peano's axioms — just this: **a sorted list,
starting from a unit, spaced by that unit**.  Whether the unit is
written `1` or `단위` is indifferent; what matters is that there is a
first thing, a next thing, and nothing between a thing and its next.

On this list, *order is not extra structure*.  To say `a ≤ b` is to
say that stepping forward from `a` reaches `b` — and "stepping
forward" is a question with a witness:

> `a ≤ b`  means exactly  `∃x, a + x = b`.

The order *is* the +-question's solvability
(`Int213.subNatNat_eq_ofNat_iff` reads this back at the pair layer).
Nothing here is assumed about `+` beyond what the list gives: results
move backward along the list, never forward past their operands.

## The sandwich

If order is the primitive, then equality is **manufactured**.  Two
strict one-sided bounds at adjacent rungs leave no room:

> `a + x < b + 1` and `b < a + x + 1` force `a + x = b`
> (`Int213.eq_of_sandwich`).

The equation is the collapsed case of an inequality pair — the
*sandwich*.  This is not a curiosity but the volume's method: on a
sorted list the sandwich is the proper probe, and the equation is
what the sandwich looks like when it has fully closed.

Probing with the sandwich immediately shows something the equation
hides.  Locating an answer has **two halves with separate prices**
(`PairOp.sandwich_locates`, `PairOp.sandwich_unique`):

* **Existence** costs almost nothing: a reachable start (`f 0 ≤ b`)
  and escape (`x ≤ f x` — the list's "results only move backward").
  No monotonicity.  The proof is a bare scan: walk until you pass
  `b`; somewhere you stepped across it.
* **Uniqueness** costs exactly monotonicity, and nothing else.

Every floor, every division, every crossing in this volume is an
instance of this one split.  The ÷-sandwich
`a·x ≤ b < a·(x+1)` always locates (`NatDiv213.div_sandwich`), and
when two affine folds are compared — "where does the steeper one
overtake?" — the crossing sandwich

> `F(x) ≤ G(x)  ∧  G(x+1) < F(x+1)`

reduces *exactly* to the ÷-sandwich of the slot differences
(`NatDiv213.affine_cross_iff_div_sandwich`): the general question is
never "fold = constant" but "**where do two monotone folds cross**",
the constant being a degenerate crossing partner.

## The question

A question is a fold with one slot left open: `a + x = b`,
`a · x = b`, `x^a = b`.  Its data is the tuple of naturals filling
the closed slots.  Two principles, developed across this volume:

1. **The solution is represented by the question's slot tuple** — in
   standard expanded form.  `x + x = b` standardizes to `2·x = b`,
   so its solution is the pair `(2, b)`; `a^x = b` gives `(a, b)`.
2. **Slots are attached only where they preserve monotonicity in the
   unknown.**  This is what makes the sandwich applicable — and it is
   what excludes coding tricks: un-pairing a Gödel code is
   intrinsically non-monotone, so "everything is one slot" is not an
   admissible question.

What happens when a question has *no* answer on the list — when
`a + x = b` fails because `a` is too big, when `a·x = b` misses, when
`x·x = 2` finds nothing?  That is the subject of the next chapter,
and the engine of everything after it: **the unanswered question's
tuple is itself the new number.**
