# G177 — the self-reference marathon: three outcomes, sharp, one unit

**Date**: 2026-06-02.  **Status**: synthesis + closed ∅-axiom results (foundational /
self-reference axis).  **All cited theorems closed PURE this marathon.**
**Anchors**: `seed/AXIOM/05_no_exterior.md` §5.2 (two/three forms of self-reference),
§5.5 (self-completion), §5.7 (frozen/dynamic).  Source files below.

## The thread

Continuing the branch's self-reference axis, this marathon took each of the *three
outcomes* G175 names for the one self-applying engine — **oscillate / converge / escape** —
from a qualitative statement to its **sharp** form, then tied them with the cross-scale
**unit `1`** and closed the §5.7 **frozen = dynamic** identification.  Two research agents
(inventory + axiom-claim extraction) fed the target list; the high-value, axiom-safe,
non-category-error candidates were closed in waves.

## The engine (G175, recalled)

> **distinguish → unit residue → that residue is the next operand → distinguish.**

Three outcomes by what the unit residue does next: **loop** (bounded, Bool), **settle**
(floor, Nat), **open the next rung** (unbounded, residue).  Each now has a sharp theorem.

## What is now closed (this marathon)

### Oscillate — period *exactly* 2 (`Lens/Bool213/SelfReferenceForms` §3–§4, 11/0)

  - `notIter` + `notIter_even`/`notIter_odd`/`notIter_orbit` — the `not`-orbit has only the
    two points `{r, not r}`.
  - ★ `bool_notIter_eq_self_iff` — `notIter k r = r ↔ even k` on a Bool value: period
    exactly 2 (odd iterates ruled out by `not r ≠ r`).
  - ★ `bool_min_period_two` — minimal period is exactly 2 (not 1, attained at 2).
  - ★ `oscillation_region_is_bool` — `not` is fixed-point-free **exactly** on the Bool
    values: off them it settles, the symmetric between `a / b` is swap-fixed
    (`not_fixes_between`, `between_not_bool`).  The period-2 region *is* the Bool-Lens image.

### Converge — well-founded + explicit bound + terminal-iff-atom (`Theory/Raw/Lambek` §5–§6, 22/0)

  - ★ `isPart_wf` — the peel relation is well-founded (qualitative termination).
  - ★ `descent_chain_drops` / `no_infinite_descent` — quantitative: each peel removes the
    unit `1`, a chain drops depth by ≥ its length, no chain exceeds `root depth`.
  - ★ `terminal_iff_atom` — a Raw is peel-terminal **iff** it is an atom: the descent stops
    at *exactly* the atomic floor.
  - ★ `self_completion_no_partial` — every Raw is exactly one of {atom, slash with a part},
    exhaustive + exclusive: no halfway-formed Raw (§5.5).

### Escape — never-closes + exact fixed-point characterization (`Lens/ResidueReentry` §3–§4, 12/0)

  - ★ `reentry_undifferentiated_nonfixed` / `residue_reentry_concrete` — the concrete
    non-fixed-point witness with an explicit Raw of disagreement.
  - ★ `reentry_fixed_iff` — the fixed points are **exactly** the round-tripping indicators
    (`P = Object1 r ∧ predicateToRaw n (Object1 r) = r`) — a proper refinement of
    "single-point" (single-pointedness is necessary, `reentry_fixed_imp_single`, not
    sufficient).

### The cross-scale unit (`Lib/Math/Cauchy/ReentryUnit`, 4/0)

  - ★ `slash_depth_is_minOverflow` — the slash constructor's depth is exactly `minOverflow`
    over its parts: the foundational pointing step *is* the tower's least overflow.
  - ★ `reentry_unit_across_scales` — the foundational descent (`Lambek`, converging) and the
    tower overflow (`DepthOverflowDuality`, escaping) move by the identical `Nat` unit `1`;
    only well-foundedness distinguishes the direction.  No operator forced across types —
    the shared object is the unit they both step by.

### Frozen = dynamic (`Lib/Math/Real213/FibCassiniNat`, +2/0) — the §5.7 open item, closed

  - ★ `convergent_never_frozen` — no Pell-Fibonacci convergent satisfies the frozen relation
    `Q = 0` (`a² = ab + b²`): Cassini gives `a² + 1 = ab + b²`, so `Q = −1` forever.
  - ★ `frozen_eq_dynamic` — the dynamic convergents approach the frozen φ-cut from below
    (`fib_convergent_below_phi`), conserve `Q` at the Pell unit (`fib_cassini_norm`), and
    never reach `Q = 0`.  The frozen φ is the limit; the gap is the conserved unit `1`,
    the count-Lens residue at the algebraic-fixed-point scale (never settling, §5.5).

### Synthesis capstone (`Lens/SelfReferenceThreeOutcomes`, 1/0)

  - ★ `self_reference_three_outcomes` — one ∅-axiom statement: the same Raw self-pointing
    reads three ways simultaneously, each sharp — oscillate (period exactly 2), converge
    (well-founded + terminal-iff-atom), escape (never closes).  Co-present, none privileged,
    no operator forced across the three types.

## The spine: one unit `1`

Every result here is the count-Lens residue of **one distinguishing**, read in one place:

| reading | the unit `1` | direction | fate |
|---|---|---|---|
| oscillate (Bool) | the toggle (period 2 = two of one) | in place | loops, never settles |
| converge (Nat) | `part_depth_succ_le`: `c.depth + 1 ≤ p.depth` | down | settles at floor (WF) |
| escape (residue) | `overflow_is_unit_surplus`: `bound + 1 ≤ val` | up | never closes (top-less) |
| frozen/dynamic | Pell unit `Q = −1` vs frozen `Q = 0` | the gap | approaches, never reaches |

`reentry_unit_across_scales` proves the converge-unit and the escape-unit are the *same*
`Nat` `1`; `frozen_eq_dynamic` shows the same unit is the never-closing gap at the algebraic
scale.

## Open (foundational axis)

  - **Concrete non-round-tripping indicator** — CLOSED (`ResidueReentry` §5):
    `object1_b_singlepoint_nonfixed` — `Object1 Raw.b` is single-pointed yet non-fixed, its
    encoding being `numeral 0 ≠ b` (`object1_b_encodes_to_numeral_zero`).  The
    `reentry_fixed_iff` refinement is now concrete: single-pointedness does not imply
    fixedness.
  - **ε₀ as a native diagonal limit** — whether iterating the height-diagonal yields a native
    `ε₀` (no Mathlib `Ordinal`) or bottoms out at `ω^ω` (genuinely uncertain; `G173`).
  - **Rejected (category error)** — a single self-applying operator unifying `not`, the peel
    relation, `Object1`, the trace-doubling `D`.  They act on different types; the honest
    unification is the *shared unit* (`reentry_unit_across_scales`), not a forced map (G175).

## Files

`Lens/Bool213/SelfReferenceForms`, `Theory/Raw/Lambek`, `Lens/ResidueReentry`,
`Lib/Math/Cauchy/ReentryUnit`, `Lib/Math/Real213/FibCassiniNat`,
`Lens/SelfReferenceThreeOutcomes`.  Narrative anchors: `G172`, `G175`, `G176`, this note.
