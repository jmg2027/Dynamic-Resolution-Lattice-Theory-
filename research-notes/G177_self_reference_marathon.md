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

### The shared unit (`Lib/Math/Cauchy/ReentryUnit`, 4/0)

  - `peel_overflow_is_unit` — **the load-bearing link**: a peel, read through the tower's
    `Overflow` predicate, reduces to the same unit surplus `c.depth + 1 ≤ p.depth` the tower
    uses (via the shared `overflow_is_unit_surplus`).  The one place two `1`s from different
    files are proven the same `Nat` successor.
  - `slash_depth_is_minOverflow` — lighter: `(x/y).depth` and `minOverflow` are both `(·)+1`,
    so agree modulo `add_comm` (a shared `+1` *shape*, not a deep fact).
  - `reentry_unit_across_scales` — bundles the three; only the `peel_overflow_is_unit`
    conjunct is load-bearing.  **No operator forced across types** — the shared object is the
    `Nat` unit, and only that conjunct proves two such units the same.

### Dynamic-vs-frozen `Nat` shadow (`Lib/Math/Real213/FibCassiniNat`, +2/0)

This is the ∅-axiom `Nat` shadow of §5.7, **not** an identification of frozen with dynamic
(that needs the real limit, outside the `Nat` reach):

  - ★ `convergent_never_frozen` — no Pell-Fibonacci convergent satisfies the homogeneous
    frozen relation `a² = ab + b²`: Cassini gives `a² + 1 = ab + b²`, so it sits one `Nat`
    step off.
  - `dynamic_approaches_never_reaches_frozen` — bundles: each convergent lies below the
    frozen cut φ (`fib_convergent_below_phi`), satisfies the Cassini form, and never lands on
    `a² = ab + b²`.  The orbit approaches φ and stays exactly the Cassini step `+1` off.
    (Whether this `+1` is "the same" unit as the descent/overflow steps is narrative — no
    `Nat` term links them here.)

### Boolean-algebra completion (`Lens/Bool213/Raw`, +9/0) — the oscillation substrate

Rounds out the `{T,F}` algebra the oscillation side lives on: `and_compl`/`or_compl`
(complement `x ∧ ¬x = ⊥`, `x ∨ ¬x = ⊤`), `and_T_right`/`and_F_right`/`or_F_right`/`or_T_right`
(identity + null bounds), `and_assoc213`/`or_assoc213` (associativity); `bool213_boolean_algebra_laws`
bundles them.  With the prior comm/idem/distrib/absorption/De Morgan, this is the complete
*equational* signature of the two-element Boolean algebra (no `BooleanAlgebra` typeclass
constructed — equational laws only, by `{T,F}` case-split).

### Synthesis capstone (`Lens/SelfReferenceThreeOutcomes`, 1/0)

  - ★ `self_reference_three_outcomes` — one ∅-axiom statement: the same Raw self-pointing
    reads three ways simultaneously, each sharp — oscillate (period exactly 2), converge
    (well-founded + terminal-iff-atom), escape (never closes).  Co-present, none privileged,
    no operator forced across the three types.

## The spine: the unit `1` (what is proved vs. what is narrative)

The four readings each move by a `+1`.  **Only one cross-reading identity is proved**: the
converge-unit and the escape-unit are the *same* `Nat` successor
(`ReentryUnit.peel_overflow_is_unit`).  The rest of the table is a thematic grouping, not a
single proved `1`:

| reading | the `+1` | proved same as others? |
|---|---|---|
| converge (Nat) | `part_depth_succ_le`: `c.depth + 1 ≤ p.depth` | **yes** — = escape-unit (`peel_overflow_is_unit`) |
| escape (residue) | `overflow_is_unit_surplus`: `bound + 1 ≤ val` | **yes** — = converge-unit |
| oscillate (Bool) | period 2 (two of one toggle) | no — narrative grouping |
| frozen/dynamic | Cassini step `a²+1` vs frozen `a²` | no — narrative grouping |

So the honest claim: the converge and escape steps are literally the same `Nat` unit; the
oscillation period-2 and the Cassini `+1` are *thematically* the same "one distinguishing"
but are not linked to that unit by any `Nat` term.  The spine is a real identity between two
of the four, plus a reading over the other two.

## Open (foundational axis)

  - **Concrete non-round-tripping indicator** — CLOSED (`ResidueReentry` §5):
    `object1_b_singlepoint_nonfixed` — `Object1 Raw.b` is single-pointed yet non-fixed, its
    encoding being `numeral 0 ≠ b` (`object1_b_encodes_to_numeral_zero`).  The
    `reentry_fixed_iff` refinement is now concrete: single-pointedness does not imply
    fixedness.
  - **ε₀ as a native diagonal limit** — whether iterating the height-diagonal yields a native
    `ε₀` (no Mathlib `Ordinal`) or bottoms out at `ω^ω` (genuinely uncertain; `G173`).
  - **General Cassini for `L`** — `∀ n, L n · L(n+2) − L(n+1)² = d` (the conserved
    determinant), generalising the three `decide` instances `cassini_at_{one,two,three}` in
    `Mobius213/Px/CharPolySelf`.  The quantity is conserved by `L_cayley_hamilton`; the step
    is a 2-var `Int` identity (`poly_id2`).  Easy–medium; deferred (the closely-related
    `FibCassiniNat.fib_cassini_norm` already gives the ∀n convergent Cassini).
  - **Rejected (category error)** — a single self-applying operator unifying `not`, the peel
    relation, `Object1`, the trace-doubling `D`.  They act on different types; the honest
    unification is the *shared unit* (`reentry_unit_across_scales`), not a forced map (G175).

## Files

`Lens/Bool213/SelfReferenceForms`, `Theory/Raw/Lambek`, `Lens/ResidueReentry`,
`Lib/Math/Cauchy/ReentryUnit`, `Lib/Math/Real213/FibCassiniNat`,
`Lens/SelfReferenceThreeOutcomes`.  Narrative anchors: `G172`, `G175`, `G176`, this note.
