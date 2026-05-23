# G134 — Cardinality cut-off principle: follow-up research roadmap

*(Continuation roadmap for the cardinality cut-off principle
extracted from the G125-G133 chain.  Principle promoted to
`theory/meta/cardinality_cutoff_principle.md`; this note
catalogues concrete next campaigns.)*

## §0 Anchor

The principle (per `theory/meta/cardinality_cutoff_principle.md`):

> For any **external sequence** `f : ℕ → ℕ` with unbounded
> growth and any **DRLT-internal complexity class** `H_k ⊆ ℕ`
> with explicit uniform bound `M_k`, for every fixed `k` there
> exists `m_0(k)` with `f(m) ∉ H_k` for all `m ≥ m_0(k)`.

The exemplar (G125-G133):
  · `f(m) = L_m` (Aurifeuillean L-coefficient of `Φ_{2·5·m²}(5)`)
  · `H_k` = depth-`k` Hunter values over `{2, 3, 5}` ∪ `{+, *, ^}`
  · At `k = 1`: `M_1 = 3125`, all `L_m for m ≥ 3` outside `H_1`.

This roadmap catalogues five concrete continuation campaigns.

## §1 Direction A — Depth-2 cardinality bound at Aurifeuillean

**Goal**: extend `cutoff_marathon_at_depth_1` to depth 2.

**Difficulty**: depth-2 includes `pow gd (pow gd gd) = 5^3125`
(~2184-digit number).  Uniform bound `M_2` is astronomical;
direct enumeration of values intractable.

**Strategy**:
  1. **Restrict the pow operator** — depth-2 with `pow` only on
     leaf×leaf (no nested pow).  Reduces `M_2` to manageable.
     Specifically: depth-2 with non-nested pow has `M_2 ≤ 3125
     · 3125 = ~10^7`.  Then `L_3 = 8.5·10^8 > 10^7` gives the
     cut-off.
  2. **Bounded-parameter Fin quantification** — encode depth-2
     forms as `Fin n × Fin n × Fin op × Fin n × Fin n × Fin op`
     parameter tuples, decide-enumerate.  Already done at
     small Fin in `AurifeuilleanCutoff.lean`; extend to capture
     more depth-2 forms.
  3. **Algebraic incompatibility** — show specific Aurifeuillean
     L_m has prime factorisation properties incompatible with
     `pow gd k` forms for `k ≤ small`.  Requires Galois-side
     infrastructure.

**Estimated**: 1-2 sessions, 50-100 PURE new theorems.

**Lean target**: `Lib/Math/Cohomology/Fractal/AurifeuilleanCutoffDepth2.lean`
extending the existing infrastructure.

## §2 Direction B — Aurifeuillean L unboundedness theorem

**Goal**: prove `∀ B, ∃ m, L_m > B` formally in Lean, eliminating
the "L_m ≫ 3125" verbal premise of the depth-1 cut-off.

**Difficulty**: requires either
  · Computing `L_m` for specific large `m` via
    cyclotomic polynomial evaluation (`Φ_{2·5·m²}(5)`) and
    Schinzel–Brent norm extraction — substantial infrastructure.
  · An asymptotic lower bound argument
    `L_m ≥ 5^{m²·c}` for explicit `c` — easier but still
    nontrivial (uses `φ(2·5·m²) ≥ m²` and Aurifeuillean
    factorisation).

**Strategy** (recommended):
  1. Compute `L_3, L_7, L_9` externally (Python).  Embed as
     decidable instances in Lean (`L_at_m3 := 850554441`,
     `L_at_m7 := big_number`, etc.).
  2. Show `L_at_m3 > 3125`, `L_at_m7 > L_at_m3`, … as a finite
     chain of decide-checks.
  3. State the unboundedness existentially: `∀ B ≤ huge_cap,
     ∃ m ∈ {1, 3, 7, 9, ...}, L_m > B`.  Bounded version of
     the unboundedness claim.

**Estimated**: 1 session, 10-20 PURE.

**Lean target**: extend `AurifeuilleanFullCutoff.lean` or create
`AurifeuilleanLUnbounded.lean`.

## §3 Direction C — Apply cut-off principle to other external
sequences

**Goal**: demonstrate the principle's reusability by applying
to a non-Aurifeuillean external sequence.

**Candidates**:
  · **Cyclotomic values at other bases**: `Φ_n(d)` for
    `(n, d) ∈ {(10, 7), (12, 5), …}`.  Each defines a sequence
    indexed by `n`; growth is well-understood.
  · **Pell number sequence** (related to G119 dyadic FSM):
    `P_n` (Pell numbers) grow as `(1+√2)^n`.  Hunter cut-off at
    each depth `k` immediately gives `m_0(k)`.
  · **Fermat numbers** `F_n = 2^(2^n) + 1`: doubly-exponential
    growth, cut-off at depth 1 immediate.
  · **Lucas sequences** `L_n(P, Q)`: parametric; cut-offs depend
    on `(P, Q)`.

**Strategy**: for one chosen sequence, run the three-step
methodology (§5 of principle): locate, diagnose, prove-refined.
Each yields a new Lean file with the cut-off capstone.

**Estimated**: 1-2 sessions per sequence.

**Most natural choice**: **Pell number sequence** (G119
connection brings 213-internal motivation).

## §4 Direction D — Hunter atomic prime closure question

**Goal**: investigate whether the Hunter atomic prime catalogue
`{2, 3, 5, 7, 13, 41, 137, 521}` is closed under specific
depth-`k` Hunter operations.

**Question**: define `HunterAtomicPrime = {p prime : p ∈ catalogue}`.
Is `HunterAtomicPrime` closed under
  · `(a + b) mod p` for `a, b ∈ HunterAtomicPrime`?
  · `(a * b) mod p`?
  · `a^b mod p`?

If yes, we have a **finite arithmetic substructure** that's
closed under Hunter operations — a 213-internal "ring" of
atomic primes.

**Motivation**: G126 showed mod-41 → constant 9 = NS² and
mod-137 → 86 = Rn.  Both are catalogue atoms.  If this pattern
extends to all pairs, the catalogue forms a self-referential
arithmetic closure.

**Strategy**:
  1. Compute pairwise `(a + b) mod p` for all triples
     `(a, b, p) ∈ HunterAtomicPrime^3`.  Finite (8^3 = 512
     entries).
  2. Check which entries are themselves catalogue atoms or
     small Hunter expressions.
  3. Identify closure structure.

**Estimated**: 1 session, ~20-30 PURE table theorems.

**Lean target**: `Lib/Math/Cohomology/Fractal/HunterAtomicClosure.lean`.

## §5 Direction E — Cut-off depth as complexity measure

**Goal**: define `hunterComplexity(v) := min {k : v ∈ H_k}` as a
DRLT-native complexity measure on naturals.  Investigate its
properties.

**Conjectures**:
  · `hunterComplexity(521) = 3` (depth-3 witness, no smaller).
  · `hunterComplexity(29) = 2` (depth-2 witness).
  · `hunterComplexity(8) = 1` (depth-1 witness).
  · `hunterComplexity(p)` for atomic primes — characterise.

**Question**: is `hunterComplexity(v) ≤ O(log v)` for all `v`?
By Frobenius `v ≤ 2x + 3y`, so depth `O(log v)` suffices via
repeated addition.  But for "nice" numbers (with multiplicative
structure), depth is much smaller.

**Lean infrastructure**:
  · Define `hunterComplexityOf : Nat → Option Nat` via bounded
    search.
  · Prove specific values for catalogue atoms.

**Estimated**: 1-2 sessions, ~30-50 PURE.

**Most ambitious**: prove a **complexity hierarchy theorem**
`{v : hunterComplexity(v) ≤ k}` form a proper chain in `k`.

## §6 Direction F — Generalise to other DRLT primitive sets

**Goal**: replace `{NS, NT, d, c}` with a different primitive
set and re-derive the cut-off principle.

**Motivation**: the principle is parametric in the DRLT
internal primitives.  Different physics-base selections induce
different Hunter algebras and different cut-off behaviour.

**Candidates**:
  · `{1/α_em, e-folds, …}` from `catalogs/physics-constants.md`
  · `{NS², NT², d², c²}` (squared primitives, smaller dynamic
    range).
  · `{NS, NT, d}` only (drop `c = NT`, no redundancy).

**Each candidate** would have its own `H_k` hierarchy, its own
cut-off slices, its own catalogue-atom set.  Comparison reveals
which slice of external sequences each primitive set "sees".

**Estimated**: ambitious; 3-5 sessions to derive a useful
comparison.

## §7 Prioritisation

| Direction | Difficulty | Yield | Recommended order |
|---|---|---|---|
| B (L unboundedness) | Low | Closes premise of §3 of principle | 1st |
| D (atomic prime closure) | Low-Mid | New 213-internal substructure | 2nd |
| A (depth-2 cut-off) | Mid | Extends marathon to next depth | 3rd |
| C (Pell sequence cut-off) | Mid | Demonstrates reusability | 4th |
| E (hunterComplexity measure) | Mid-High | New 213-native invariant | 5th |
| F (alternate primitive sets) | High | Comparison framework | 6th |

**Quick win**: Direction B (L unboundedness via finite chain) —
1 session, closes the premise of the existing depth-1 cut-off.

**Most structurally interesting**: Direction D (catalogue prime
closure) — could reveal a closed arithmetic substructure
intrinsic to DRLT atomicity.

**Most generalising**: Direction C (Pell sequence cut-off) —
proves the principle isn't Aurifeuillean-specific.

## §8 Non-goals

  · **Literal `∀ depth` cut-off** — falsified per Frobenius.  Do
    not re-attempt.
  · **Aurifeuillean depth-3 enumeration in Lean kernel** — known
    intractable (22M expressions, 5^3125 values).  Skip.
  · **Full Aurifeuillean L formalisation as a Lean function** —
    requires cyclotomic polynomial degree formalisation at
    base 5, multi-session infrastructure.  Defer indefinitely
    unless Direction B's finite chain suffices.

## §9 Cross-references

  · `theory/meta/cardinality_cutoff_principle.md` — principle.
  · `theory/math/cohomology/aurifeuillean.md` — exemplar
    application chapter.
  · `lean/E213/Lib/Math/Cohomology/Fractal/AurifeuilleanFullCutoff.lean`
    — exemplar Lean (28 PURE).
  · `research-notes/archive/G133_cutoff_marathon.md` — marathon
    execution record (archived).
  · `research-notes/archive/G125_aurifeuillean_n_u.md` — G125
    closure (predecessor).
  · `catalogs/atomic-integers.md` — Hunter primitive catalogue.

## §10 Status

This roadmap is the **planning artifact** for the cut-off
principle's continuation.  No Lean content yet; each direction
is a candidate campaign waiting to be scheduled.

Direction B (L unboundedness finite chain) is the recommended
**next session start**.  All other directions are unscheduled
candidates.
