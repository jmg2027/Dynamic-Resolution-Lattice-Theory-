# G206 — Critical review of the cross-domain / proof-ISA marathon

Adversarial self-assessment of the branch `claude/cross-domain-math-problems-afA0g`
output, ahead of integrating two independent referee agents.  Goal: separate
genuine results from inflation, name corrections, name development.

## 1. The star-rating inflation (real, must fix)

The `★`-count is supposed to track depth.  It does not.  Many one-line trivia
carry `★★★★★`/`★★★★★★`:

| theorem | actual proof | stars | verdict |
|---|---|---|---|
| `PickTheorem.pick_rectangle` | `ring_intZ` (1 line) | ★★★★★ | **inflated** |
| `CrossDomainIdentities.{heron,euler_four_square,sophie_germain}` | `ring_intZ` | ★★★★★/★★★★★★ | **inflated** |
| `DiscreteRicci.discrete_curvature_topology` | `decide` | ★★★★★ | **inflated** |
| `RicciFlow.ricci_pillar_K32_flow_close` | toy `fillStep` + `flow_reaches` | ★★★★★★ | **inflated + mislabeled** |
| `RicciSphereFlow.round_S3_ricci_extinction` | `flow_reaches` + curvature *asserted* | ★★★★★★ | **over** |

Genuinely substantive (`S`), deserving the stars:
`flow_reaches`, `flow_reaches_ascending` (order-reversal + hand-rolled
`sub_lt_sub_left_pure`), `gradient_descent_identity` (real bilinear algebra),
`SubtractionGame.{period,grundy_values}` (genuine induction + Bool case split),
`RealCauchyWitness.gradientValueCauchy` (an actual `CauchyCutSeq` with a proven
modulus).

**Correction**: re-grade — reserve `★★★★+` for `S`; drop trivial `ring_intZ`/
`decide` results to `★` or none.

## 2. The "conquest" framing inflation

Calling a 1-line `ring_intZ` (Heron, Euler-4-square) a "cross-domain conquest
compiled to the ISA" overstates.  The EQUIV essay *already* concedes this (zero
lift content; difficulty = bridge construction, here trivial), but the commit
messages and stars contradict the essay's honesty.  The honest claim:

> these are **classical identities exhibited as fold-equalities (EQUIV)**, whose
> difficulty in their home domain is the *already-built* algebra bridge — not
> conquests in the hard (lift) sense.

The genuine "conquest" texture is in the game-theory and flow threads, which have
real proof content.

## 3. The proof-ISA meta-rigor question (the central one)

The instruction *witnesses* are real `∅`-axiom theorems (`cantor_general`, …) and
the *lift* theorems are real.  But the **meta-organization outruns the theorems**:

- **"The 7 archetypes form a partial order"** — the order *relation* is never
  defined (on what set? by what relation?).  The Hasse diagram is *asserted*, not
  proven.  Status: **heuristic picture, not a theorem.**
- **"EQUIV vs lift, two orthogonal axes"** — a *classification*, not a theorem;
  "lift content = 0" is a feeling, not a defined quantity.
- **"lift cost" (0 / one induction / a good factor)** — informal labels, not a
  measured quantity.
- **"LOOP ⟷ FLOW is a strict duality"** — here there *is* a theorem
  (`flow_reaches_ascending`: ascent reduces to descent via `B−μ`).  But this is
  *one lemma reduced to another* (routine), and narrating it as "a duality of
  archetypes" risks inflation.  It is the *strongest* meta-result and still modest.
- **"mex = GAP", "DIAGONAL self-dual"** — suggestive, not pinned.

**Honest position to adopt**: the proof-ISA is, at present, (i) a set of real
`∅`-axiom instruction/lift witnesses + (ii) an *organizing narrative* over them.
The narrative (order, axes, dualities) is mostly **not yet theorem-backed**; it
should be marked as heuristic, with `flow_reaches_ascending` flagged as the one
place narrative became theorem.  Risk if unmarked: the framework reads as standard
proof techniques renamed and arranged by appealing metaphors.

## 4. Volume / padding

The Ricci thread is 4 files (RicciFlow, RicciSphereFlow, RicciHomogeneous,
DiscreteRicci) with large docstrings over small content: a reused monovariant
flow + a curvature *definition* + `decide` examples.  Docstring-to-theorem ratio
is high.  Not wrong (the honesty markers are good), but trimmable.

## 5. What is genuinely strong (develop these)

- The **constructive-analysis foundation** (Real213 Cauchy completeness, the
  gradient-flow descent identity + completeness-LOOP + the actual `CauchyCutSeq`).
  Real, reusable, honest.
- `flow_reaches` / `flow_reaches_ascending` — genuine well-founded infra; the
  order-reversal is a real (if modest) structural theorem.
- The **frontier ladders** (transcendentals, PDE-via-limit, Pick general, Nim
  Bouton) with **measured obstructions** (e.g. "`Nat.xor` is `propext`-dirty",
  "general-metric `𝓦` needs PDE estimates").  This honesty about walls is the
  marathon's best feature — the agenda is real and well-located.
- The game-theory thread (subtraction game, 2-heap Nim, Grundy) — genuine proofs.

## 6. Corrections to make (actionable)

1. **De-inflate stars** on `ring_intZ`/`decide` theorems (Pick, CrossDomain,
   DiscreteRicci, the Ricci toys).
2. **Reframe "conquest"** → "classical identity as EQUIV" for the algebra batch
   (align stars/commit-tone with the essay's honesty).
3. **Mark the proof-ISA meta-claims as heuristic** where they are not theorems
   (the partial order; the axes; lift-cost) — add an explicit "narrative vs
   theorem" line to `lift_archetypes_order_and_duality.md` and `PROOF_ISA.md`.
4. Optionally trim Ricci docstrings (org-audit).

## 7. Development directions (highest value, ranked)

1. **Make one meta-claim a theorem.**  The cheapest genuine win: *define* the
   lift-cost partial order on the concrete finite set of catalogued lifts (a real
   relation, e.g. "X ⊑ Y iff Y's witness invokes X's") and *prove* the Hasse
   edges — converting the diagram from picture to theorem.  Or formally define
   "compiles to" for a restricted proof class.
2. **Push a frontier rung with real analysis content** — transcendentals **T1**
   (exp convergence modulus) is substantive constructive analysis, not trivia;
   it also unblocks the smooth-curvature route.
3. **The 2D-conformal smooth curvature** (`K = (|∇λ|²−λΔλ)/(2λ³)`, rational `λ`):
   makes the Ricci thread genuinely *smooth* (curvature derived from a metric, not
   asserted) — the honest answer to "is the Ricci work real?".

## Verdict (pre-agent)

The marathon's **infrastructure + honesty about walls** is genuine and valuable;
its **star-ratings, "conquest" rhetoric, and proof-ISA meta-structure** are
inflated and must be marked down to what the theorems actually support.  Net: keep
the frontier ladders and the analysis/flow infra; correct the framing; develop by
*converting one narrative claim into a theorem* rather than adding more trivia.

## Two independent referee agents — verdict (confirms + sharpens)

**Agent A (Lean substance).**  Of ~50 theorems: ~28 **trivial** (`ring_intZ`/
`decide`/`rfl`), ~13 **definitional/bookkeeping** (`∧`-bundlers, `FoldEquality`),
~9 **substantive-but-easy** (none beyond a strong-undergrad exercise).  Worst
offenders (★★★★★/★★★★★★ on one-liners): `cauchy_schwarz_2d`/`_3d` (school proof),
`heron`/`euler_four_square`/`sophie_germain` (bare `ring_intZ`, *misnamed* — Heron
has no √, Lagrange's 4-square theorem is absent, the compositeness claim is
unproved prose), `ricci_pillar_K32_flow_close`/`round_S3_ricci_extinction`/
`einstein_trichotomy` (`ℕ` counting `0→1→2→3` / subtract-4-to-0, labelled
Perelman/Poincaré/Einstein, geometry *assumed* in a `def`), `gradient_descent_identity`,
`amgm_2`, `positivity_of_sq`.  Pick "rectangle atom" **is not Pick's theorem** (a
linear cancellation on known counts).  `formanEdge` = a definition + `decide` on 3
examples; no `b₁` linkage proven.  `FoldEquality` = **circular** (`fold1`/`fold2`
hand-written to be LHS/RHS of an existing identity; `agree :=` that identity).
Genuinely substantive: `flow_reaches(_fueled)`, `SubtractionGame.{period,grundy_values}`,
`NimTwoHeap.nim2_progress`, `flow_reaches_ascending`, `gradientValueCauchy`.
Recommendation: **cut every ★ by 2–4; rename `heron`→`heron_polynomial_identity`,
`cauchy_schwarz_2d`→`lagrange_gap_nonneg_2d`, `ricci_pillar_K32_flow_close`→
`fillcount_reaches_three`; delete "conquest"/"COMPLETE"/"Perelman" where the core
is an admitted open frontier** (the CLAUDE.md *overclaim* failure-mode at the
docstring layer).

**Agent B (framework rigor).**  The proof-ISA is an **evocative taxonomy, not a
rigorous framework**: no Lean object represents a proof, a compilation, an
instruction set, or an order — the eight instructions and seven archetypes are
`abbrev` aliases over pre-existing theorems; "compiles to" / "partial order" /
"lift cost" / "orthogonal axes" are undefined; the LOOP/FLOW "duality" is one
6-line `B−μ` reflection over-narrated as a µ/ν duality (`slashNu_final` plays no
role).  Key line: **"strip the ISA vocabulary and every theorem survives; strip
the theorems and the ISA is empty prose — the rigor lives in the corpus, the
framework is a metaphor over it."**  Rigor would require a datatype of ISA
proof-terms + a `Compiles` predicate, a defined `liftCost` into one ordered
codomain + a proven `PartialOrder`, and dualities as actual involutions.

## Corrections — DONE this review

- `seed/PROOF_ISA.md`: added an honest *theorem-vs-taxonomy* status (the rigor is
  the `∅`-axiom discipline; the ISA naming is taxonomy; "compiles to" is a thesis).
- `Foundations/ArchetypeOrder.lean` (NEW, 10 PURE): a real `Archetype` type +
  defined `liftCost : → ℕ` + proven reflexive/transitive order with bottom/top/
  equicost — converting the asserted Hasse diagram into a *model* (Agent B's
  demand #2, partially: costs are still hand-assigned).  Stars kept honest.

## Corrections — AGENDA (mechanical sweep, do fresh via `org-audit`)

1. **De-star**: cut `★` by 2–4 on every `ring_intZ`/`decide`/bundler theorem in
   `CrossDomainIdentities`, `PickTheorem`, `Positivity`, `DiscreteRicci`,
   `RicciFlow`, `RicciSphereFlow`, `RicciHomogeneous`, `FoldEquality`,
   `GradientFlow`, `CompletenessLoop`.  Reserve `★★★★+` for the ~9 substantive.
2. **Rename / de-overclaim docstrings**: drop "conquest"/"COMPLETE"/"Perelman"/
   "Poincaré"/"Einstein" headline language where the geometric core is an open
   frontier; state what is actually proven (a polynomial identity; a `ℕ` counting
   flow; a school inequality).  Keep theorem *names* that are cited elsewhere
   (`ricci_pillar_K32_flow_close` is in `ProofISALifts`/`STRICT_ZERO`); soften the
   docstring instead of renaming, or do a cited-rename carefully.
3. **`FoldEquality`**: docstring should concede it repackages an identity's two
   sides (not a discovered agreement).
4. Optionally trim Ricci docstrings (volume).

## Development — keep (genuine), ranked

1. Make a meta-claim a *full* theorem: extend `ArchetypeOrder` to a real
   `PartialOrder` instance, or define `Compiles` for a restricted proof class.
2. A frontier rung with real analysis content — transcendentals **T1** (exp
   convergence modulus); also unblocks smooth curvature.
3. 2D-conformal smooth curvature (`K = (|∇λ|²−λΔλ)/(2λ³)`) — derives curvature
   from a metric, making the Ricci thread genuinely smooth.
