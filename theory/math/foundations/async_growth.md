# Asynchronous Growth — the point–line system, its ladder, and the honest census

**Status**: Closed ∅-axiom (74 PURE across `Theory/Raw/{Async,
AsyncReach}`, the `Slash` pair-injectivity API, and six
`UniverseChain` census modules).

## Overview

Raw growth read as an **asynchronous event system**: a state is the
list of points so far; one event — `fire x y` — contrasts two
distinct present points whose pair is absent and adjoins
`Raw.slash x y`.  The system originates in the founding dialogue
(`seed/ORIGIN_RAW.md`): the axiom rebuilt from "difference" alone,
then read as growth with **no global clock**.  The line/point
two-event split of that dialogue is a Lens on the one constructor —
the line is the pair caught, the point the same pair reified.

What closes here, in 213-native terms:

1. **The forced ladder** — determinism ends exactly at the first
   composite; one further firing is swap-canonical; the next firing
   diverges beyond the swap gauge.  "Which snapshot" is from then on
   a foliation (simultaneity) Lens choice.
2. **The depth-2 boundary is order-internal** — no run is forced
   through the 5-element census; what distinguishes depth ≤ 2 is
   past-completeness, a property of the ancestor order.
3. **Conflict-freeness** — reachable snapshots are subterm-closed,
   any two embed in a common reachable snapshot (no fairness), and
   every Raw is reached: the system's limit is all of Raw, stated
   finitely.
4. **The honest census** — `rawCount n = 2, 3, 5, 12, 68, …`
   genuinely counts canonical Raws of depth ≤ n (soundness +
   completeness + Nodup), with quadratic normal form, purely
   periodic mod-5 readout, a strict base-2 double-exponential
   sandwich, the mediated agreement of the two 5s, and the
   event-cost fold `dagSize` locating where the tree-Lens and the
   DAG-Lens first split.

## Lean source

| File | PURE | Core results |
|---|---|---|
| `lean/E213/Theory/Raw/Async.lean` | 14 | `step1_forced`, `level2_canonical`, `level3_diverges`, `level2_swap_partner` |
| `lean/E213/Theory/Raw/AsyncReach.lean` | 12 | `reach_closed`, `reach_extend`, `reach_joinable`, `every_raw_reached`, `list_reached`, `memDec` |
| `lean/E213/Theory/Raw/Slash.lean` (additions) | +3 | `slash_val_lt`, `slash_val_gt`, `slash_inj` |
| `lean/E213/Lib/Math/Foundations/UniverseChain/RawPastCompleteness.lean` | 6 | `depthLe2_past_complete`, `depth3_boundary` |
| `…/AtomicityCensusBridge.lean` | 8 | `choose2_fixed`, `two_fives`, `mediating_fixed_point_unique` |
| `…/RawCountQuadratic.lean` | 9 | `choose2_add`, `choose2_double`, `rawCount_normal_form`, `rawCount_mod5_cycle`/`_table` |
| `…/RawCountBounds.lean` | 6 | `census_step_lower/upper`, `rawCount_lower`, `rawCount_upper`, `rawCount_sandwich` |
| `…/RawDagSize.lean` | 8 | `dag_census`, `dag_sandwich_le3`, `sharing_starts_at_depth3` |
| `…/RawEnumeration.lean` (honest-count section) | +8 | `enum_pairwise`, `enum_members`, `enum_complete`, `honest_count` |

∅-axiom status: 0 DIRTY (`STRICT_ZERO_AXIOM.md`).
A recurring landmine closed twice here: the Lean-core list-`∈`
decidability instance leaks `propext`; membership is handled by
explicit `Mem` constructors (`Async`) and a hand-rolled `memDec`
(`AsyncReach`).

## Narrative

### The system is Raw

States are point lists containing the two atoms; `Step` fires
`Raw.slash x y h` for present, distinct `x, y` whose pair is absent.
The no-self-pair clause is the `x ≠ y` hypothesis; direction-freedom
is the slash-symmetry canonical form; "brackets are the boundary
itself" (the dialogue's §3) is the constructor.  Under the
occurrence-net Lens the system is conflict-free — points are never
consumed — and this single fact drives everything in the third
section below.

### The forced ladder (fused semantics)

`step1_forced`: the only successor of `{a, b}` adjoins `a/b` — the
two diagonal pairs are excluded by the clause, and `slash_comm`
collapses the two orders.  `level2_canonical`: every 2-step state is
*exactly* one of the two lists adjoining `a/(a/b)` or `b/(a/b)` — an
exact list disjunction, stronger than equality-up-to-swap; the two
outcomes are one `Raw.swap` orbit (`level2_swap_partner`).
`level3_diverges`: two 3-step runs — the depth-2 completion vs the
depth-3 fork `a/(a/(a/b))` — disagree as point-sets *and still
disagree after a global swap* (witness: `b/(a/b)`).  Event-indexed
boundaries are semantics-tagged (the split line/point reading
diverges one event earlier, inside level-2 work); the
semantics-invariant clauses are: determinism ends at the first
composite, exactly one further firing is swap-canonical, the next is
not.

### The depth-2 boundary is past-completeness

No run is forced through the 5-element depth-≤2 census (a run may
build a depth-3 term before completing depth 2), so the census's
distinction is not run-internal.  It is order-internal: every term
of depth 1 and 2 contains the *whole previous depth-downset* in its
subterm closure (`depthLe2_past_complete`), while at depth 3 exactly
one of the 7 terms — the full join `(a/(a/b))/(b/(a/b))` — survives
the same filter (`depth3_boundary`).  The census population is 5 and
its connected-contrast-graph coordinate readout is `5 − 1 = 4`: the
same 5 → 4 reading as the self-pointing-axis omission of the
geometrization ansatz, now anchored to an order property rather than
to any privileged truncation depth (the parametric census
`configCountD` privileges no level).

### Conflict-freeness: closure, joinability, totality

`reach_closed`: every reachable snapshot is subterm-closed — the
proof's key is **pair injectivity** (`slash_inj`: equal slashes have
equal unordered input pairs, the direction-free clause's only
freedom).  `reach_joinable`: any two reachable snapshots embed in a
common reachable snapshot — one run replayed on top of the other,
firing only the missing events; constructive, finite, no fairness.
Divergent asynchronous observers are never in conflict, only
incomparable, and re-converge in finitely many steps.
`every_raw_reached`: by structural induction with joinability, some
run constructs any given term — the fairness-free, finite form of
"the limit of growth is all of Raw"; `list_reached` extends this to
any finite point-set jointly.

### The honest census and its structure

`honest_count`: `enumTreeDepth n` lists **exactly** the canonical
Trees of depth ≤ n — soundness and completeness by one strict
invariant, `Pairwise (cmp · · = .lt)`, which propagates through the
pair-generation using only the lex head structure of `cmp` and
`cmp_self_eq` (no transitivity, no sorting machinery) — without
repetition, and with length `rawCount n`.  So the recurrence values
count the actual population, and the following are facts about that
population:

- **Quadratic normal form** (`rawCount_normal_form`):
  `2·T(n+1) + T(n) = T(n)² + 4` — the census recursion is a
  conjugated pure quadratic map.
- **Mod-5 readout** (`rawCount_mod5_cycle`): purely periodic, period
  3, cycle `(2, 3, 0)` — an instance of the generic self-restart of
  towers `2 + q(x)`, `q(0) = 0`, mod their own depth-2 value; the
  213-specific content is only that the depth-2 value *is* 5.
- **Base-2 sandwich** (`rawCount_sandwich`):
  `2^(2^(n+1)) < rawCount (n+3) < 2^(2^(n+2))`, strict both sides,
  lower bound sharp at the base (both sides 5).  The census tower is
  graded by the `d = 2 = NT` slice of `configCountD`, not the
  `d = 5` slice.
- **The two 5s, mediated** (`two_fives`): atomicity's Diophantine
  `5 = pairSize + closureSize` and the census `5 = 2 + C(3,2)` agree
  through one fixed point — `choose2 n = n ↔ n = 3` among positives
  (`choose2_fixed`) — and `3` is simultaneously `closureSize` ("the
  pair plus their relation", literally `Raw.level1_set`) and the
  level-≤1 population.  Not an identity of definitions, not
  numerology: a mediated theorem.
- **The event-cost fold** (`dag_census`): history is a DAG — each
  term is created once — so `Raw.leaves` (tree fold) has no event
  cost meaning; `dagSize` = distinct composite subterms does.  Over
  all 12 terms of depth ≤ 3: `depth ≤ dagSize ≤ leaves − 1`, with
  the strict gap (`sharing_starts_at_depth3`) at exactly the three
  `a/b`-reusing terms — where the tree-Lens and the DAG-Lens first
  split.

## Open frontier

- **Exact-membership converse**: `Closed P ∧ Nodup P ⟹ ∃ reachable
  s` with the same membership (the argmin-by-depth fill
  construction; `list_reached` gives the ⊇ form).
- **Fused step-3 swap-class census** (= 4): needs a state
  enumeration function.
- **Uniform `depth ≤ dagSize ≤ leaves − 1`** by `Raw.rec` induction,
  and minimal-run-length = `dagSize`.
- **Axes**: a definition of "stable independent directions" of the
  growth order and whether `(NS, NT) = (3, 2)` forces their count —
  the order-statistics route is constrained by the divergence of the
  bare ordering fraction (any finite dimension readout must live at
  the past-completeness boundary or in the deployment Lens).

## Cross-references

`seed/ORIGIN_RAW.md` (the founding dialogue, verbatim);
`theory/math/foundations/universe_chain.md` (atomicity → Möbius →
pentagonal closure; the census cluster's elder sibling);
`seed/AXIOM/05_no_exterior.md` §5.7 (frozen/dynamic; no external
time axis — the foliation Lens);
`theory/math/geometry/geometrization_conjecture.md` (the 5 → 4
chart readout);
`Lib/Math/Cohomology/Fractal/ConfigCount.lean` (the parametric
count family).
