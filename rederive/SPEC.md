# SPEC — the asynchronous distinction system (pinned definitions)

**Status**: root document of the independent rederivation program
(`research-notes/drafts/independent_rederivation_program.md`).
**Input scope (hard rule)**: this program derives from
`seed/ORIGIN.md` and `seed/ORIGIN_RAW.md` ONLY.  No other repository
content (in particular `lean/E213/`, `theory/`, `seed/AXIOM/`) may be
read, cited, or imported by any agent working under this SPEC.
Classical mathematics may be used freely and must be cited in the
bilingual ledger (`rederive/LEDGER.md`).

The raw utterances underdetermine the system at several points.
Every such point is pinned here with a stated choice, a rationale,
and the alternative that the refutation track must assess.

---

## 1. The two formalizations (both are first-class)

**F-obj (object-primary).**  Carrier = "somethings" (points).  Two
atoms `a`, `b` (ORIGIN_RAW §2: pointing at `a` forces a minimal
contrast `b`).  A pairing of two *distinct* somethings yields a new
something (§3).  Pairing is unordered (§3: no absolute order) and
never self-applied (§3: nothing exists to distinguish `x` from `x`).

Concretely: **Tree** = the smallest family containing atoms `a`, `b`
and closed under `pair {x, y}` for `x ≠ y`, where `pair` takes an
unordered two-element set.  Distinct pairs give distinct trees; the
two children are recoverable from a composite tree.

**F-ev (event-primary).**  ORIGIN_RAW §2 says `a`, `b` are *not
objects* ("objects are not defined yet") — only the difference is.
Taken literally: carrier = distinction-events; "points" are derived
as reifications.  The design of F-ev is a deliverable (task M2), not
pinned here.  The program must either prove F-obj ≅ F-ev or exhibit
the asymmetry.

## 2. The asynchronous event system (from ORIGIN_RAW §5–§8)

State = `(T, U)` where

- `T` ⊆ Tree — the points present ("caught" somethings),
- `U` ⊆ P₂(T) — pairs joined by an *unresolved* line.

**Identification (pinned):** a line **is** the unordered pair
`{x, y}` it joins, and the point a line resolves into **is** the tree
`pair {x, y}`.  (§8: Event 1 turns a line into a new point; the new
point is the reification of exactly that contrast.  Nothing else in
the raw text individuates the new point.)

Initial state: `T₀ = {a, b}`, `U₀ = ∅`.
(Variant to test: `U₀ = {{a,b}}` — "draw the line joining the two
points" as part of the initium.  Expected immaterial; refuters check.)

Events (exactly two kinds, §8):

- **link `{x, y}`** (Event 2, Pair → Line): enabled iff `x, y ∈ T`,
  `x ≠ y`, `{x,y} ∉ U`, and `pair{x,y} ∉ T`.
  Effect: `U := U ∪ {{x,y}}`.
- **resolve `{x, y}`** (Event 1, Line → Point): enabled iff
  `{x,y} ∈ U`.  Effect: `T := T ∪ {pair{x,y}}`, `U := U \ {{x,y}}`.

A **run** = a (finite or infinite) sequence of events, each enabled
in the state its predecessors produce.  A run is **maximal** if no
enabled event is forever neglected (weak fairness).

### Choice points (each with the pinned choice and the live alternative)

| # | Underdetermined in raw text | Pinned choice | Rationale | Alternative (refutation track) |
|---|---|---|---|---|
| C1 | Does a resolved line persist as a joining? | Yes: `pair{x,y} ∈ T` counts as "joined", so link never repeats on the same pair | §5 lines are drawn once; re-linking would create a duplicate contrast of the *same* two, which §3 gives no basis for | Lines vanish on resolve; re-link allowed (system becomes non-terminating per pair — check what survives) |
| C2 | Are the two atoms distinguishable from each other? | Yes, `a ≠ b` | §2: `b` is the minimal contrast *for* `a` — the first distinction is real | Indistinguishable atoms (quotient by the swap `a ↔ b`) — check which theorems are swap-invariant |
| C3 | Can a new point link to points created after it? | Yes — enabledness is stateless in history | §7–§8: pure asynchrony, no generation bookkeeping | Generation-restricted linking (lockstep §5 reading) — expected to be exactly the foliation the §6 tension rejects |
| C4 | Self-pair | Forbidden (`x ≠ y` as trees) | §3: no operand for self-distinguishing | — (no live alternative; raw text is explicit) |
| C5 | Simultaneity | No simultaneous events; concurrency = order-freedom, not co-occurrence | §8 defines *pure* single events | True-concurrency semantics (event structures) — should be the *conclusion* (poset), not an input |

## 3. The research questions (this session's targets)

- **Q1 (order-invariance).**  Prove: any two enabled events commute
  (persistence + no conflict); hence all maximal runs realize the
  same causal partial order **D** and converge to the same limit
  (`T∞` = all Trees).  Runs = linear extensions of **D**.  This is
  the precise form of §6's lockstep rejection.
- **Q2 (level-2 obstruction, from §9).**  Conjecture: **D** admits a
  height function but **no rank function** (no `ℕ`-grading in which
  every covering step increments by exactly 1); every violation
  involves an element above the level-2 zone, and the *first*
  violation is computable and lies just past the five level-≤2
  objects.  Also: the natural `ℕ`-folds (depth, size, generation)
  agree up to level 2 and provably diverge at level 3.  Either result
  makes §9 ("strata work to level 2, not beyond") a theorem.
- **Q3 (universal grading, from §10).**  Do not shop for a scale.
  Define the category of gradings of **D** (monotone maps to a
  chosen class of ordered structures, compatible with both event
  types) and *compute* the universal object.  Expected: the universal
  grading is **D** itself (or its height multigrading); every numeric
  scale is a non-injective fold.  The content is in Q2's obstruction
  — otherwise Q3 risks tautology (refuters must check this).
- **Q4 (duality).**  F-obj ≅ F-ev, or a concrete asymmetry.

## 4. Discipline (inherited from the program memo)

- Proof-assistant work: zero `sorry`, zero external axioms
  (`#print axioms` empty — no `propext`, `Quot.sound`,
  `Classical.choice`), zero Mathlib.  Fresh package under
  `rederive/lean/`, independent of the corpus.
- Every classical concept used gets a ledger entry:
  internal term ↔ nearest classical object ↔ theorems imported.
- No numerology: no physical constant may be mentioned as a result.
- English artifacts; builders do not commit (the session driver
  commits).
