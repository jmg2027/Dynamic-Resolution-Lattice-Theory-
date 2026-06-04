# G175 — the gapless self-similar spiral: one expansion engine, read at every scale

**Date**: 2026-06-02.  **Status**: synthesis (the single principle threading the arc).
**All cited results are closed ∅-axiom.**  **Anchors**: `Cauchy/DepthOverflowDuality`
(`overflow`, `minOverflow`, `least_overflow`, `gapless_unit_step`),
`Cauchy/DepthHeightDiagonal` (`diag_self_applies`, `height_diagonal_escapes`),
`Cauchy/DepthCeilingResidue` (`diag_not_in_seq`, `cantor_general`),
`Real213/SpiralRotationInvariant` (`Q_iterate_preserved`), `Real213/ProbeTwistConic`
(`Q_preserved`), `Real213/FloorReferenceForm`, `Lens/Bool213/SelfReferenceForms`
(`self_reference_two_forms`), `Lib/Math/FiveFloorUnification` (`five_floor_unifies`),
`seed/AXIOM/05_no_exterior.md` §5.1–5.7.

## The question

Without classical framing (no completed continuum, no ordinal stacking, no next cardinal),
what is expanding and how?  The intuition: a mechanism that expands *without gaps*, and the
mechanism is *itself* an instance of the same mechanism — a self-similar spiral, not an
infinite regress.  This note states that engine as one principle and pins each part to a
∅-axiom theorem already in the tree.

## The engine

> **distinguish → unit residue → that residue is the next operand → distinguish.**

Nothing is reached for from outside (no exterior, §5.1).  The surplus left by one act *is*
the operand of the next.  Three properties make it gapless and self-similar:

  1. **The step is the irreducible unit.**  Each act leaves the count-Lens residue of one
     distinguishing, `1` (§2.5).  `overflow bound val := bound i + 1 ≤ val i`: the next is
     the previous *plus the unit*.

  2. **The step has no interior — gapless.**  Between a value and its unit-successor there
     is nothing: `gapless_unit_step` (`¬∃ x, b < x < b+1`).  With `least_overflow` (every
     overflow `≥ b+1`), the minimal overflow is the *immediate* next.  There is no blank to
     fill because there is no element in the unit gap; the residue *is* the fill,
     simultaneously (§5.5 self-completion).

  3. **The engine applies to itself — self-similar.**  Naming the whole cascade is itself a
     distinguishing, so it leaves a residue and is itself a cascade-step:
     `diag_self_applies` (`diag (n ↦ diag (g n)) ≠ (n ↦ diag (g n)) r`) — collect the
     chain into a family and the same `diag` escapes it again.  Not a regress of different
     things: the *same* operation at every meta-level (`diag_not_in_seq` holds for every
     family, including ones built from diagonals).  The original proposal's *scale-invariant
     expansion / self-similar shift*.

## Two faces of the one spiral

The same self-applying engine reads two ways, by where it is taken — at the **floor** it
*conserves*, at the **ceiling** it *escapes*:

  - **Atomic / bounded (conserve).**  The `P = [[2,1],[1,1]]` shift (det 1, disc `5=NS+NT`)
    is the same step at every turn (`Pseq` iterates one `Pstep`), and the golden form
    `Q = m²−mk−k²` is its **rotation invariant**, conserved at *every* turn:
    `Q_iterate_preserved` (`Q(Pseq (m,k) n) = Q(m,k)` ∀n).  The orbit spirals *within* its
    hyperbola — bounded, recurrent (the golden floor, `FloorReferenceForm`).

  - **Residue / unbounded (escape).**  Naming the whole `ω^r` height-tower escapes every
    finite height (`height_diagonal_escapes`), and the act of naming is itself a step
    (`diag_self_applies`).  Each turn leaves the unit residue and opens the next rung —
    unbounded, the `ε₀`-direction (the ceiling).

These are not one operator (the atomic `Pstep` and the residue `diag` act on different
types — bundling them into a single map would be a category error).  They are the *same
self-applying structure* read at the two ends: a **conserved per-turn invariant** either
way — the golden `Q` (atomic) and the unit `1` (residue, the gapless surplus).  And the two
ends meet: `five_floor_unifies` — the conserving floor `P` (disc `5`) *is* the McKay E₈
endpoint mod `5`, so the bounded floor and the open ceiling close into one loop, the way the
diagonalisation residue (no top) and the det-one floor (`P`) are the two scales of one
self-cover (`completeness_without_completeness.md` Part V).

## The bounded sub-regimes: how a turn can fail to open

Within the bounded face, the self-reference of one turn has two forms
(`self_reference_two_forms`, §5.2): **Bool** — involution with no fixed point on its
values (`bool_not_no_fixed_point`): period-2 oscillation, the turn loops without settling;
**Nat** — every Raw is its own constructor (Lambek `decompose`) with well-founded descent
(`depth_drops`): period-1 convergence, the turn closes at the floor.  Oscillate (bounded
loop), converge (settle at the floor), or — the unbounded face — escape (the residue opens
the next rung).  Same engine, three outcomes, by what the unit residue does next.

## One line

Expansion is one gapless self-applying engine — distinguish, leave the indivisible unit,
that residue is the next operand — with **no blank** (nothing inside the unit step) and **no
exterior** (the engine applies to itself, every scale).  At the floor it conserves a
rotation invariant and spirals bounded (golden `Q`, every turn); at the ceiling each turn
escapes and opens the next (the residue, every level); the two ends are one loop, pinned at
the `5`-floor.  Not a continuum filled, not a tower stacked into blanks — a **self-similar
spiral**, the same atomic step read at every scale.

(Every clause above is a closed ∅-axiom theorem; this note only assembles them into the
single picture.  A *single Lean theorem* uniting the conserving and escaping faces is not
attempted — they are genuinely different operators, and the honest unification is this
shared structure plus the `5`-floor tie, not a forced common map.)
