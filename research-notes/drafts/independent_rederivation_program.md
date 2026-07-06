# Independent rederivation program — from the raw utterances alone

**Status**: Tier-1 memo.  Written at the originator's request: *if the
entire repository except the raw utterances (`seed/ORIGIN.md`,
`seed/ORIGIN_RAW.md`) were erased, how should the research be redone
independently?*  This is a plan for a fresh derivation, not a critique
of the existing corpus; where it diverges from the corpus, the
divergence is deliberate and stated.  Intended to be executable by a
future agent with no other context.

Input scope: `ORIGIN.md` §1–§8 (physics chain) + `ORIGIN_RAW.md`
§1–§10 (difference chain).  Nothing else.

---

## 0. First decision: do not fuse the two seeds early

The raw utterances contain two distinct programs:

- **Program A** — the difference calculus (`ORIGIN_RAW` §1–§10):
  minimal contrast, brackets-as-boundary, asynchronous growth.
- **Program B** — physics constraints (`ORIGIN` §1–§8): resolution
  covariance, lattice information invariance, non-completion of
  singularities.

Develop A as autonomous pure mathematics.  Quarantine B as a
constraint list.  The bridge is introduced later as exactly one
explicit hypothesis (B1 below).  Rationale: early fusion lets physics
numbers pull the mathematics, structurally enabling postdictive
numerology.

---

## Program A — the difference calculus (in priority order)

### A1. Define the object twice; test the equivalence (~2–3 weeks)

The object-primary formalization (a type with elements `a`, `b`,
`a/b`) is one reading.  But `ORIGIN_RAW` §2 says *a, b are not
objects (objects are not defined yet); only the difference is*.
Taken literally, this licenses a **dual formalization**: the carrier
is the set of *distinction-events*; points are derived as
reifications of distinctions.  This matches the §8 two-event reading
exactly (line = distinction occurring, point = distinction reified).

Build both in a proof assistant (one file each) and either prove an
equivalence functor or **find the asymmetry**.  An asymmetry would be
the first discovery: the raw utterances would then contain two
inequivalent theories.

### A2. The diagonal theorem as milestone 1 — including the hard half (~month 1)

The easy half (days): any faithful self-cover of the free difference
structure is never total (Cantor diagonal, constructive).  The entire
philosophy hangs on this one theorem; pin it first.

The hard half: **classify the residue's shape**.  If the image of
self-indication is the family of "equals-r" predicates, what exactly
is in the complement, and by what descriptive-complexity grading does
it stratify?  Moving from "a residue exists" (existence) to "the
residue has this form" (structure) is where new mathematics can live.

### A3. The asynchronous event system — the richest vein

Honest assessment: `ORIGIN_RAW` §1–§4 (the recursion of difference)
ultimately lands on known deep mathematics (initial algebras, the
Lawvere fixed-point schema).  §5–§10 (point–line generation, lockstep
rejection, two pure events, the level-2 limit) is the least developed
and most generative seed.  Invert the corpus's apparent emphasis:
less axiom exegesis, more event-system mathematics.

Concretely:

1. **Write a ~200-line enumerator first** (days).  Exhaustively
   enumerate all runs up to N events; observe state counts and
   invariants empirically.  Query resulting sequences against OEIS —
   cheap, immediate external anchoring.  Prove afterwards.
2. **Order-invariance theorem** (weeks): which quantities are
   invariant across all maximal runs?  This is the precise
   formalization of the §6 lockstep suspicion — "no global clock" =
   "only what is invariant across all linearizations is real."
   Existing tools: Winskel event structures, causal partial orders.
3. **Level-2 obstruction theorem**: turn the §9 observation
   ("natural-number strata work to level 2, not beyond") into a
   theorem — *no ℕ-valued grading compatible with both event types
   exists beyond level 2*.  Then answer the §10 question ("which
   number scale above?") **by computing the universal grading object,
   not by shopping for scales**.  Whether it is ordinals or the poset
   itself, compute the universal solution the system forces.  This is
   the only honest shape an answer to the originator's closing
   command can take.

### A4. Lens as a theorem-bearing object

Define Lens = structure-preserving readout out of the initial object;
study the category of readouts.  Then "the residue is outside every
view" becomes a precise statement: *characterize what the
intersection of images over a definable class of Lenses misses*.
Claims like "count is Lens output" become theorems, not slogans.

### A5. Reconstruction ladder with smuggling certificates

Every reconstruction (ℕ, ℤ, …) ships with a machine-checked
**smuggling certificate**: a formal statement of exactly which Lens
was applied and that the base needed nothing else.  Added discipline:
every reconstruction must state its **nearest classical object and
the list of classical theorems reproduced** — so that "we rebuilt X"
means X's standard theorems hold, not that X-shaped vocabulary
exists.

---

## Program B — physics

### B1. Exactly one bridge, and it is the bet the raw utterances actually license

`ORIGIN` §6–§7 ("isn't resolution the minimum unit of information",
"lattice-unit information is invariant anyway") combined with A gives:
**spacetime = one run of the A3 event system; one event = one
distinction (one bit); information invariance = exactly one
distinction per event.**  Resolution covariance then becomes
linearization-dependence of event order.

Key observation: the §6–§8 asynchrony (denial of a global clock) and
special relativity's denial of absolute simultaneity are **the same
structural move**.  Half the mathematics exists: causal set theory
(Malament's theorem — causal order determines the conformal metric)
and Rideout–Sorkin classical sequential growth.  First physics task:
map the A3 system onto causal sets and compute **what the two event
types add** to bare causal sets (vs. Rideout–Sorkin, whose events
lack the internal tree structure from A1).

### B2. Numeric quarantine

No constant (α, mass ratios, …) enters the canon without a
**pre-registered forcing derivation** — write what value the
structure forces *before* computing, then compare — machine-checked
end to end.  The raw utterances contain no numbers; that is the
project's cleanest asset.  Preserve that state as long as possible.
And **kill-tests before predictions**: Lorentz-violation bounds (GRB
time-of-flight etc.) are the standard graveyard of
resolution-covariance proposals; B1 must pass them first.

### B3. ħ last

The §8 command (construct the wave function and Planck constant) only
after B1 yields a metric-like invariant.  Its honest form then:
"action = the count of distinctions along a run", with existing
attempts ('t Hooft's cellular-automaton QM) kept alongside as the
**adversarial comparison class**.

---

## Process — what to change about how the corpus grew

The non-seed corpus was produced by coding agents elaborating the
originator's prompts.  Agents optimize for coherence with the
existing corpus; over generations this thickens internal vocabulary
and thins external audit.  Countermeasures for the redo:

1. **Budgeted refutation track.**  Builders to breakers at roughly
   2:1.  Standing bounty on every central claim: a rival-primitive
   construction (relation-first, negation-first) reaching the same
   milestone.  The sufficiency ≠ uniqueness gap stays managed, open.
2. **Bilingual ledger from day one.**  Internal term ↔ nearest
   classical object ↔ classical theorems imported/reproduced.
   Internal vocabulary (Lens, residue, fold) is good for coherence
   and bad for external audit; the ledger is the only device that
   catches a known result renamed as a new one.
3. **Keep the ∅-axiom contract.**  For a project claiming "assume
   nothing", a proof assistant plus an empty axiom footprint is
   exactly the right falsifiability instrument.  This — and the
   verbatim quarantine of the raw utterances — are the parts of the
   existing approach to carry over unchanged.
4. **Order under scarce resources**: A2 diagonal (days) → A3
   enumerator (days) → A3 order-invariance / level-2 obstruction
   (weeks) → A1 duality (weeks) → B1 causal-set mapping (month+).
   **If only one thing can be done: the A3 universal grading
   object** — it answers the originator's own closing question (§10)
   with a computation instead of a choice, and its success or failure
   is the litmus test for whether the program is real.
