# G168 — analysis ↔ logic single engine: the overflow duality, and ω₁^CK as gauge shift

**Date**: 2026-06-01.  **Status**: closed ∅-axiom result (Q3) + grounded narrative (Q2).
**Source of truth**: `lean/E213/Lib/Math/Cauchy/DepthOverflowDuality.lean` (7 PURE / 0
DIRTY).  **Anchors**: `Cauchy/DepthCeilingResidue` (`diag_not_in_seq`,
`ceiling_residue_is_pointing_residue`, `cantor_general`), `Real213/RateStratification`
(`Dominates`, `overtake_breaks_layer`), `seed/AXIOM/05_no_exterior.md`.

## The agenda these answer

The original proposal had two questions that lie **outside** the `G166` analysis-axis
program (T1–T4 = the W-vs-d stratification + coordinate→real generation):

  - **Core Q3 / Expected Impact (analysis–logic single engine).**  Is the mechanism
    producing the Cantor-diagonalisation residue *the same* as the coordinate
    mismatch at the branch point where tower completeness breaks (¬Htel)?  Formalise
    it as a finite-operation rearrangement.
  - **Core Q2 (Church–Kleene as gauge shift).**  Is `ω₁^CK` a wall, or a point where
    the observation language must change while the dynamics stay the same?

## Q3 — the overflow duality (formalised, ∅-axiom)

The two sides were each already closed but on opposite shores:

  - *logical*: `DepthCeilingResidue.diag_not_in_seq` — the diagonal `diag f i = f i i
    + 1` is no level `f i` of the family (Cantor residue, one scale up);
  - *analytic*: `RateStratification.overtake_breaks_layer` — where `W` overtakes the
    denominator quantum `(i+1)·d_{i+1} < W_i`, domination breaks (¬Htel).

`DepthOverflowDuality` exhibits the **single finite operation** under both.  Define

    Overflow bound val i := bound i < val i

By `Nat`'s definition of `<`, `Overflow bound val i ↔ bound i + 1 ≤ val i`
(`overflow_is_unit_surplus`): at the index built to contain it, the value exceeds the
closing bound by *at least the irreducible unit `1`* — the count-Lens residue of one
distinguishing (`05_no_exterior` §2.5; the failure-mode "Count-Lens import as Raw"
keeps `1` as a Lens reading, not a Raw cardinality).  Then **one operation, two
readings**:

  - `overflow_escapes` — a value overflowing the diagonal bound `i ↦ f i i` at every
    index is no level `f i`: it escapes the family (the residue).  Recovers
    `diag_not_in_seq` as `diag_escapes_via_overflow` (the diagonal is the
    unit-surplus overflow).
  - `overflow_breaks` — a `W` overflowing the denominator quantum at layer `i ≥ 1`
    breaks domination there (`= overtake_breaks_layer`).
  - ★★★ `overflow_dual_reading` — both at once.

So completeness's boundary (where `Htel` breaks) and pointing's surplus (the
diagonalisation residue) are **not two phenomena across a logic/analysis divide** —
they are one overflow, read once as "escapes the family" and once as "breaks the
bound".  This is honest about the discipline: the claim is *not* "¬Htel is literally
Cantor non-surjectivity" (that would be stereotype-matching).  The claim is the weaker,
provable one — both are the *same finite overflow operation* `bound + 1 ≤ val`, and
neither reading is privileged (per `05_no_exterior` §5.7, simultaneous Lens readings of
one residue event).  The tie back to the foundational residue is exact:
`ceiling_residue_is_pointing_residue` shows the diagonal escape is the `Object1`
pointing-cover surplus, so the unit-surplus that overflows here is the surplus
`Object1` leaves outside its image.

This realises the proposal's "analysis–logic single engine … combined at the ε₀
ceiling as the same algebraic object" — concretely, the unit `1` is that object, and
the engine is `Overflow`.

## Q2 — ω₁^CK as gauge shift (narrative, grounded in Q3)

A note on discipline first: "wall vs gauge shift" is itself an imported dichotomy
(`05_no_exterior` §5.4).  The 213-native move is not to argue one horn but to describe
the trajectory.  Here it is.

`DepthCeilingResidue` already proves the tower has **no top**: any reference that names
"all the levels so far" overflows them by the unit and lands outside
(`diag_not_in_seq`), making the next rung; the construction never terminates and never
escapes (`ceiling_reference_leaves_residue`).  `ω₁^CK` is the level where the
*single-axis, algorithmic* reading saturates — recursive ordinal notations are exactly
the reference levels `f i` reachable by one mode of pointing (computable diagonals).
At that level the **same** `Overflow` operation is still available (the unit surplus is
always there), but the value it produces is no longer named by *that* reading's
vocabulary.

So nothing in the dynamics changes at `ω₁^CK`: the overflow engine runs identically
above and below it.  What changes is which Lens reads the residue — the move the
proposal calls "first-order logic → embedding frame" is, in 213 terms, switching the
Lens that names the overflow, not crossing into an exterior.  There is no wall because
there is no exterior to put a wall against (`05_no_exterior` §5.1); `ω₁^CK` is where one
naming-Lens stops covering and another must be chosen, the foundational-scale image of
the *same* axis-handoff that `DepthDoubleExp`/`DepthExponentRecursion` make concrete on
the analysis side (one axis saturates, the recursion into the exponent takes over).
The "gauge shift" is a Lens-reading change of one self-covering closure — frozen/dynamic
(§5.7) at the scale of ordinal notations.

This part is *interpretation*, not a Lean theorem: there is no ∅-axiom numeric content
in "switch the naming vocabulary" beyond the top-lessness already proved.  Recording it
as narrative, honestly tier-1.

## Strengthening review (external proposal: Galois / deformation / endofunctor)

A reviewer proposed upgrading the "static" shared inequality to a "dynamic" structural
theorem by three routes.  Tested against the operators and the hard rules, not adopted
wholesale:

  - **Galois connection / adjunction (rate-acceleration ⊣ residue-lifting).**  Rejected
    as stated.  The overflow duality is *one definitional inequality* `bound + 1 ≤ val`
    read two ways — it is already canonical, so an adjunction wrapper between "two
    independent operators" is decorative, and the operators it splices (the analytic
    `diff`/`ratioLift` lowering of `DepthTower` and the logical `diag` raising) are a
    *separate* structure, not two adjoint halves of overflow.  The only genuine
    adjunction present is the trivial unit `Nat.succ ⊣ pred` on `(Nat, ≤)`; dressing it
    as "rate ⊣ residue" imports residual meaning (CLAUDE.md "Stereotype matching").  The
    *defensible* core of the idea — the duality has a structural generator, not just a
    coincidence — is real and is now formalised: `minOverflow bound = bound + 1` is the
    pointwise-**least** overflow (`least_overflow`), generated by the unit successor.

  - **Deformation invariance (one parametric function moves both facets).**  Rejected as
    a *symmetry*.  The logical facet has no denominator `d` to deform: `diag_not_in_seq`
    is unconditional, while the analytic break is contingent on the `W`-vs-`d` race.  So
    the two are **not** symmetric under a `d`-deformation.  The honest relationship is
    *minimality / specialisation*: the diagonal **achieves** the unit-surplus floor
    exactly (`diag_is_minOverflow`, unconditional), the break only **exceeds** it and
    only when `W` overflows (`overflow_breaks`, contingent).  The genuine stability that
    *is* shared — overflow is monotone in the value and invariant under a common shift —
    is formalised (`overflow_mono_val`, `overflow_shift`): these deformations preserve
    the single inequality, hence both readings, without a forced parametric symmetry.

  - **Endofunctor `tower_unimodular_invariant (α : Ordinal) (hα : α < Γ₀)`.**  Not
    implementable as written: there is **no `Ordinal` type and no `Γ₀`** in the
    ∅-axiom world (Mathlib is forbidden by the hard rules; `Ordinal`/`Veblen` are
    Mathlib).  The framework's native substitute is the Nat-indexed tower coordinate
    `DepthOmegaTower.Coord r` with `coord_wf` (well-founded for every `r`, the `ω^r`
    ladder).  The *good* part of the idea — define `T`'s det-1 step as a single
    generator and prove its invariant by one structural theorem over the native index,
    not an `_at_level_n` ladder (CLAUDE.md rule 9) — is the right shape for Phase 1, but
    over `Coord r` / the generator's iteration, not a classical `Ordinal`.  Left open
    below; it also overlaps the tower-coordinate track on the other branch.

The net: the "static → structural" instinct was right, and produced a genuine
generator + minimality + stability layer (`minOverflow`, `least_overflow`,
`diag_is_minOverflow`, `overflow_mono_val`, `overflow_shift`, 6 PURE).  The specific
classical frames (Galois adjunction, symmetric deformation, ordinal endofunctor) were
each either decorative, asymmetric, or Mathlib-dependent, and were declined in favour
of the ∅-axiom-honest statements.

## What remains open (still beyond T1–T4)

  - **Phase 1 transfinite projection (T into ε₀/Γ₀).**  `DepthOmegaTower` pins `ω^r`
    ∅-axiom; `ε₀`/`Γ₀`/Veblen remain the classical reading only.  A genuine ∅-axiom
    `ε₀`-level statement (e.g. the overflow engine iterated through the tower *height*
    as a single well-founded object) is the next foundational target — but it risks the
    "layer-by-layer enumeration smell" (CLAUDE.md), so it wants one structural theorem,
    not an `_at_level_n` ladder.
  - **A measurable falsifier from the overflow unit.**  The unit `1` is the gap quantum
    on the analysis side and the diagonal surplus on the logic side; whether it yields
    a DRLT-Standard falsifier (vs only a precision/structural theorem) is open.
