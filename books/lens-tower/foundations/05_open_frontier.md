# Chapter 5 — The open frontier

This is a 준-책 (working draft), and the honest close of a working draft is the list of
what it did *not* settle — sharply enough that the next session can close it.  The three
questions of Chapter 1 each split into a settled part and an open part.

## 5.1 What this draft settled

**Completeness (Chapter 2).**  The bundling `count → difference → ratio → completion`
**closes at `ℝ`** — `ℝ` is a Cauchy fixpoint (`CauchyCompleteValid.limit_valid`,
`CompletionTower.completion_idempotent`).  `ℝ → ℂ → ℍ → 𝕆` is an **orthogonal
algebra-grade axis**, not a fifth rung (`CDDouble` exits the Lens codomain;
`TwoTowersDivergence.divergence` shows a one-floor mismatch with the 213 magnitude/sign
decomposition).  The only thing endless above `ℝ` is the **resolution diagonal**, whose
endlessness is the residue re-covering itself (`TowerNativeCompleteness`).  At any finite
configuration the numbers are rational; `ℝ` is the rung of limit-labels.

**One axis or many (Chapter 3).**  **Hybrid.**  The linear tower serializes a breadth
axis, two orthogonal inverse-closures (`ℤ` additive, `ℚ` multiplicative — independent in
the founding import graph *and* on the depth side, `DepthTower`'s `(h, d)`), and a
character-changing limit, over a **lattice** of Lens refinements (`Lens/Lattice`).  The
chain the repo actually formalizes (`Lattice/Chain.lean`) is the *breadth* chain, not the
number tower.

**Forced or chosen (Chapter 4).**  A gradient: the **opening** is a CHOICE
(`infinite_family_of_lenses`), the **seams** are FORCED by inheritance, the
**continuation** past each rung is permitted-not-compelled, the **end** at `ℝ` is a
forced fixpoint reached by a chosen presentation.

## 5.2 The frontier, resolved

The five load-bearing items the draft opened are each now settled — some by a theorem,
some by the honest judgment that the residue *permits* rather than *forces*, one by
correcting a doctrine line.  None is left dangling.

1. **The `ℚ`-on-`ℤ` mismatch — resolved by the honest direction.**  The two coherent
   options were (a) record that `ℚ`'s coprimality is a `Nat`/pair-level fact independent
   of `ℤ`, or (b) add a genuine `ℚ`-on-`ℤ` dependence.  Option (a) is the truthful one and
   is now taken: the `RatioLensFounding` docstring states that its content is `Nat`-level
   (it imports neither `ℤ` nor the difference-Lens), and that the coupling to `ℤ` is *by
   identity of the unit, not by construction-dependency* — `NS − NT = 1` is the same unit
   the difference-Lens carries as `det P`
   (`SharedUnitAcrossReadings.the_unit_is_one_across_readings`).  `ℚ` and `ℤ` are sibling
   readings of the count, coupled at the unit `1`, not stacked.

2. **Exhaustiveness / uniqueness — resolved as a *no*, which is the answer.**  The bundling
   is *not* a unique forced chain, and the Lean already witnesses why: `Lens.refines` is a
   preorder, antisymmetric only at the kernel level (`Lattice/Preorder.refines_antisymm_kernel`)
   — not a total order; and the chain the repo formalizes (`Lattice/Chain.refines_chain`:
   `idLens → leaves → parity → constLens`) is the *breadth* chain, a different chain from the
   number tower (`number_tower_is_lens_bundling`, which is not even a `refines`-chain).  So the
   substrate carries at least two distinct chains.  "Is the bundling unique/exhaustive?" — no;
   it is one path through a lattice.  That is exactly the hybrid verdict of Chapter 3, and the
   honest resolution of the question, not a gap.

3. **`NT = 2 ⟹ period-2` — resolved by theorem.**  `PairCompletion.swap_order_eq_NT`: the
   inverse-realising swap of a pair is an involution (order divides `NT`) and not the identity
   (order ≠ 1), with `NT = 2` — so its order is *exactly* `NT`.  A pair has `NT` positions;
   there is no room for a period-`k` (`k ≠ 2`) involution.  Period-2 is forced by the count
   `NT = 2`, upgrading `ℤ`'s sign from "holds" to "forced."

4. **`ℚ` obligation — resolved: it is a choice, and that is the answer.**  There is no theorem
   forbidding a halt at `ℤ`, and — by the discipline of `seed/AXIOM/05_no_exterior.md` — there
   should not be: nothing *compels* the next rung, because there is no exterior dialer to do the
   compelling.  Taking the ratio is a Lens choice (the opening already is, `infinite_family_of_lenses`;
   each continuation likewise is permitted-not-compelled).  So the framing weakens, correctly, from
   "the tower *must* reach `ℝ`" to "the tower *can* reach `ℝ`."  The obligation question dissolves
   into the no-exterior discipline.

5. **Unify the three axis-vocabularies — resolved downward, to the unit.**  The unification is
   *not* an operator monoid over `{iterate, invert, complete, double}`: those have no shared
   carrier (`double` exits the Lens codomain), so a forced common map across them is the category
   error `the_form_of_the_residue` names.  The honest unification is *identity of the unit*:
   `SharedUnitAcrossReadings.the_unit_is_one_across_readings` proves the value `1` is one value
   across the count-difference (`NS − NT`), the Möbius/ratio determinant, the Cassini oscillation,
   and the reciprocal law.  "How many axes, really?" — the readings are many (breadth, depth `(h,d)`,
   grade); the *unit* is one.  The answer is a unit, not a list — reached by going down to the shared
   value, not up to an operator algebra.

## 5.3 The reading this draft commits to

Stripped of the staircase convention, the founding says something the residue can speak
in its own voice — and it is more modest than "the four number systems are forced."

> The pointing is forced; its first count is a choice.  Read on an ordered pair, the
> count closes additively — forced.  Read as a ratio, it closes multiplicatively — a
> second, orthogonal closure, not a step beyond the first.  Completed over trajectories,
> it reaches a fixpoint and stops — `ℝ` is where the readout returns home.  What climbs
> past `ℝ` is not more number; it is the dimension doubling on one side and the residue
> re-covering itself on the other.

The staircase is real and useful.  It is also one chosen path through a lattice the
residue supports but does not single out.  That is the precise, honest answer to *"is
`ℕ → ℤ → ℚ → ℝ` a complete tower, one axis, and a forced one?"* — and with the five
frontier items now settled (§5.2), the draft has said what it set out to say: complete at
`ℝ` as a fixpoint, hybrid as axes (one unit, many readings), and forced only at its seams
— opened by a choice, continued by choice, closed by a fixpoint.
