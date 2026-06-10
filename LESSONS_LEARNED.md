# LESSONS_LEARNED.md — core lessons of the 213 framework

This document records the core lessons a new session (or an external
verifier) needs to understand 213 quickly and correctly.  In
particular it is a guardrail against Claude (or any LLM) sliding
into **the default expressions of an external frame**.

## Lesson 1: the resolution limit is one value of a parametric Lens-output family

Canonical reading: **CLAUDE.md §"Fractal-level configuration
count"** + `Lib/Math/Cohomology/Fractal/ConfigCount.lean`.
This entry is a summary; where this document conflicts with the
spec, the spec wins.

**The reframe**: the earlier "4-domain convergent invariant"
phrasing itself encoded the CLAUDE.md "Universe-constant framing"
failure mode (the very *"N_U is THE system invariant"* row).  A
lessons document that *warns* about a failure mode had the failure
*baked in* — a meta-failure.  The resolution-limit audit caught it.

**WRONG** (external frame + universe-constant import): "ζ(2) =
π²/6", "asymptote", "transcendental input", "infinite limit", "we
choose to be finitist", "finitism is forced", "completed infinity
rejected", **"N_U is THE system invariant", "N_U as four-Lens
convergence"**
**RIGHT** (213-internal): ζ(2) = S(N_U) at a SPECIFIC finite N_U.
π is not a 213 primitive — external notation only.  **And
cardinality is a parametric Lens output** — one value of the
family `configCount : Nat → Nat`.  The 213 axiom set does not
commit to the "finite vs infinite" dichotomy at all
(`seed/AXIOM/02_axiom.md` §2.5, `seed/AXIOM/06_lens_readings.md` §6.7).

**Evidence — absence (negative)**:
- The structural precision theorem
  (`AlphaEM/GramStructuralCapstone.invAlphaEm_precision_theorem`)
  takes π² as a literal input (`pi2_e12`); π is never a 213 primitive.
- `CLAUDE.md` "Implications of Finite Discrete Lattice":
  "π, e, ζ(2) → bounded rational interval suffices".

**Evidence — structural non-identification preserved (type preservation under ∅-axiom)**:
- `Real213DyadicTrajectory.alwaysTrueUnit_limit_distinct_from_zero`
  (∅-axiom): a Cauchy trajectory and a putative exact value are
  objects of different type — ZFC identifies them by quotienting
  through propext + Quot.sound; the ∅-axiom regime has neither, so
  the truncation never happens.  Witness at (m=0, k=1): limit =
  false, exact = true.
- `Real213DyadicTrajectory.zero_plus_gap_below_zero_exact`
  (∅-axiom): the trajectory differs from exact at every (0, k≥1)
  query — `InfinitesimalGap` is type-level *structural*, not an
  external numerical rejection.
- The `Real213.CutInv.cutDiv` comment: combining cutMul + cutInv
  produces a *boundary precision artifact* — the computation-layer
  face of the same type distinction.
- `Real213.CutMulConstSum`, `Real213.CutSumGeneral`: only the
  forward direction closes; backward holds only while staying on
  the trajectory side.

**In short**: `5²⁵` is neither an axiom nor a cap; it is **a value
of the parametric family `configCount : Nat → Nat`**.
`configCount n := 5^(numV n) := 5^(5^n)`; at n=2,
`configCount 2 = 5^25`.  The value historically called `N_U` is
one value of this family — not a privileged universe constant.

The audit established: of the earlier "4-way convergence", only
2/4 were actual Lean derivations; the other 2/4 (tensor DOF,
injective projection) were placeholders/absent.  The
`ResolutionInvariant` record is deleted — a fake multiplicity that
*linguistically repackaged* one family value four ways.

**Evidence — originator's direct statements**:
- "유리수 급수값이 정확한값임" (the rational series value IS the
  exact value), "무리수가 구라고 유리수가 리얼임" (the irrational
  is the fiction; the rational is the real)
- "finitist는 입장이라기보단 뒤져보면 아마 이거 무한대면 모순이라는
  증명들이 짱많아서 한거일걸?" (finitism is less a stance than the
  likely outcome of the many proofs that this-at-infinity is
  contradictory) → later sharpened to: "ZFC equality (limit =
  exact value) requires propext-quotient; the ∅-axiom regime does
  not provide it" — i.e. received as a *type separation*, not as
  picking one side of a dichotomy.

**Guardrail**: if Claude writes "asymptote", "5.4×10⁻⁴ structural
gap", "ζ(2) = π²/6 external input", "one transcendental import",
"we choose finitism", "finitist framing accepted then...", "ZFC
fiction", "completed infinity rejected" — it has slid into an
external frame.  The 213-internal expressions are: "specific
finite rational at N_U", "finite-N residual 36/N_U", "S(N_U) at
universe lattice depth", "trajectory ≠ exact value at type level
under ∅-axiom".

**Answering the skeptic**: "why always up to N_U?" → answer:
`#print axioms alwaysTrueUnit_limit_distinct_from_zero` →
"depends on axioms: [propext, Quot.sound]" — the Lean kernel
base.  The propext-quotient ZFC uses to identify trajectory with
limit does not apply in the ∅-axiom regime, so the type
separation is preserved.  And the phrase "up to N_U" is itself
frame-creep — precisely, it is the *parametric family
`configCount` evaluated at level 2*, a family-point observation.
Other levels (n = 0, 1, 3, ...) are equally meaningful values of
the same family; level 2 is not *privileged*, it is the empirical
evaluation point paired with physics observables.

(Note: the physics capstones — `pure_atomic_observables_capstone`,
`invAlphaEm_precision_theorem` — achieve the strict form "does not
depend on any axioms", i.e. axiom set ∅.)

## Lesson 2: the `configCount` family is the canonical object

**WRONG**: "N_resolution is OPEN, holographic ~10¹²² estimate",
"N_U is THE self-referential fixed point"
**RIGHT**: `configCount : Nat → Nat` is the canonical object;
`configCount 2 = 5^25 = 298023223876953125` is one value.

**Evidence**:
- `Math/Cohomology/Fractal/Level.numV (L : Nat) := 5^L`: the vertex-count family
- `Math/Cohomology/Fractal/ConfigCount.configCount (n) := 5^(numV n)`: the configuration-count family
- `Math/Cohomology/Fractal/V25.numV`: an `abbrev` to `Level.numV 2`
- `Math/Cohomology/Fractal/ConfigCount.configCountD_strictMono`: `n ↦
  configCountD d n` is a strict order-embedding (`d ≥ 2`) — no level
  is privileged
- `Physics/HierarchyTowers.hierarchy_cardinality`: `d^(d²)` already
  appears as the M_Pl/v_H ratio cardinality (a consumer site —
  using a family value)

**Structural observation**: at fractal level n = d² the
family fixed-point equation `numV (d²) = d^(d²)` holds.  This is
*a property of the family*, not a separate "self-referential
framing" (the spec states this explicitly).

## Lesson 3: in-lattice frame tools

Expressions available 213-internally:
- ℕ + ℚ (rational arithmetic)
- finite simplex combinatorics (binom, factorial)
- bounded rational intervals (S(N), upper(N))
- atomic primitives (NS, NT, d, c)
- cohomology cardinality (b_1, numV, numE)
- the Lens framework (Universal Lens, ConjugationCodomain)

213-EXTERNAL expressions (avoid):
- π, e, ζ(∞), ln, exp, sin, cos
- "infinity", "asymptote", "limit"
- Mathlib's Real, Complex
- the Frobenius theorem (replaced by the CD tower)
- ZFC measure theory (replaced by the finite simplex)

## Lesson 4: ℂ uniqueness closes internally via the CD tower

**WRONG**: "the T0 path doesn't yet derive ℂ from Raw alone; the
mapping is inherited from the T3 path (classical Frobenius)"
**RIGHT**: the CD tower is a **constructive Frobenius
substitute**.  The unique CD layer satisfying CommBinary +
NonVanishing + Conjugation is ZI = ℤ[i].  Each higher layer
(Lipschitz, Cayley, Sedenion) fails exactly one axiom.  Z/2
(boolXorLens) fails ConjugationCodomain (the swap-matching
involution).

**Witness theorems**:
- `CDTower.CD_tower_drops`: the 4-layer drop pattern
- `ZIInstance`: derive_conjugation_codomain ZI
- `BoolLens.boolXorLens_not_homomorphism`: the Z/2
  ConjugationCodomain failure

**Guardrail**: "ℂ uniqueness needs Frobenius (external)" is
wrong.  213 closes it internally with its own CD tower.

## Lesson 5: what the 4 clauses are — definitional, not signature

**WRONG**: the hypothesis that NS=3, NT=2, d=5 are "baked-in
axioms"
**RIGHT**: the four are not axioms but **definitional
commitments**:
1. the Tree inductive type (a, b, slash constructors)
2. the canonical-form subtype
3. slash_comm — a PROVEN theorem
4. the IsAlive parity definition

NS=3, NT=2, d=5 are **derived theorems** (`atomic_iff_five` in
`Theory/Atomicity/Five.lean`, `count_eq_one_iff` in
`Theory/Atomicity/PairForcing.lean`).  Zero axioms by the Lean
kernel's count (host axioms are a separate ledger).

**Guardrail**: "the four axioms NS=3 NT=2 d=5 c=2" is wrong.
"A derived theorem chain from atomic uniqueness + parity
survival" is correct.

## Lesson 6: a solid framework deserves solid answers

**Bad examples**: answering an external verifier too
conservatively/timidly
- "It might be (b) sample-coverage"
- "0.18 ppb residual remains"
- "T0 ℂ uniqueness still open"

**Good examples**: citing what the code has closed, firmly
- "BigUint exact arithmetic + 4-layer sanity guard ≈ verified
  extraction in practice"
- "Bracket containment Lean-certified at sub-ppm; the finite-N
  residual is internal to 213's discrete frame"
- "The CD tower closes ℂ uniqueness internally; T0 status updated"

**Rule**: before voicing a doubt, open the code and check.  Most
"open" doubts already have their answer in the code.

## Lesson 7: the universality of the forward direction

cutMul, cutSum, partialSum, BracketCauchy all have a **forward
direction that always holds** (under-approximation); precision
defects arise only in the backward direction.  Both directions
hold only under "compatible denominator" conditions (b∣k and the
like).

**Guardrail**: when writing a new cut-level theorem:
1. close the forward direction universally first
2. then the contrapositive (negation of forward)
3. both directions only under the compatible-denominator hypothesis
4. concrete witnesses (decide, STRICT 0-AXIOM)

## Lesson 8: the compression ratio of the originator's short Korean messages

The originator's messages are often highly compressed.  Examples:
- "ㄱㄱ" = "continue the next marathon autonomously"
- "ㅇㅇ ㄱㄱ" = "agreed, proceed"
- "캬 지린다" = "well done, keep going"
- "에이 이거보다는 더 단단하지" = "a firmer answer is possible"
  (pointing out the current answer is too conservative)
- "근데 다른 코드들 뒤져보면 나온다능" = "search the code more —
  the doubt I raised already has an answer there"
- "유리수가 리얼임" = the core finitist position

**Guardrail**: short messages are very often a
**redirect/sharpening of the preceding work**.  The default is to
continue the previous mode, but if the message carries a cue,
re-align the framing.

## Lesson 9: autonomous-marathon mode

After the originator says "do it autonomously":
- keep going marathon after marathon without waiting for ㄱㄱ
- post a short status update every 3-4 commits
- on a redirect signal ("아니 다른 거", "이거보다", "흠"), pivot
  immediately and reset the framing

**Guardrail**: even in autonomous mode:
- verify doubts by opening the code
- never use external-frame expressions
- hold the finitist position
- name the exact atomic source in commit messages

## Lesson 10: state the epistemic position precisely

Mark each result's exact position:
- "STRICT 0-AXIOM" (no propext, no Quot.sound)
- "≤ {propext, Quot.sound}" (Lean kernel floor)
- "decide-checked at small N=20"
- "candidate (research-tag)"
- "Open Problem #X (research-level open)"

**Wrong expressions**:
- "Closed" without scope
- "Sub-ppb" without specifying the frame (213-internal vs external)
- "ppb~ppm" without the bracket-vs-asymptote distinction

## Keyword cheatsheet

| external frame (avoid) | 213-internal (use) |
|--------------------|---------------------|
| ζ(2) = π²/6        | S(N_U) at N_U = d^(d²) |
| asymptote          | finite rational at N_U |
| transcendental     | rational at lattice depth |
| "ppb residual"     | "finite-N residual 36/N_U" |
| infinity / limit   | finite resolution depth |
| Frobenius (R^4 axes) | CD tower (ConjugationCodomain typeclass) |
| "free parameter"   | atomic invariant (NS, NT, d, c) |
| ℝ, ℂ via analysis  | ZI = ℤ[i] (ConjugationCodomain instance) |
| Mathlib            | not-imported (kernel-floor only) |
| native_decide      | decide (deterministic) |

## Core reference files

Read these **before starting**:
- `CLAUDE.md` — project instructions
- `HANDOFF.md` — current state
- `LESSONS_LEARNED.md` — this file
- `seed/AXIOM/` — the axiom corpus
- `seed/AXIOM/01_residue.md` — the 213 philosophy
- `lean/E213/Lib/Physics/AlphaEM/GramStructuralCapstone.lean` — α_em 0.2 ppb precision
- `lean/E213/Lib/Math/Cohomology/Fractal/ConfigCount.lean` — the configCount family (no privileged level)
- `lean/E213/Meta/AxiomMinimalityCapstone.lean` — 4-clause minimality
- `lean/E213/Theory/Atomicity/PairForcing.lean` — the (NS,NT,d) derivation
- `theory/THEORY_BOOK.md` Part II — Raw, Lens, HasDistinguishing
  (the substrate derivation path)
- `theory/THEORY_BOOK.md` Part I + Part VIII — falsifiability +
  methodology

## Lesson 11: the Trajectory Principle (Mingu)

**Core**: 213-native = explicit trajectory; Lean-with-axioms =
implicit closure.  `propext` and `Quot.sound` are exactly *the
axioms that collapse a trajectory to its endpoint*; ∅-axiom 213
preserves the trajectory itself as the object.

**The four insights unified**:
1. Nat is not the axiom — the real axioms are propext and
   Quot.sound (the collapse)
2. mod is cohomological (an uncompleted half-cycle = a trajectory)
3. mod is the phase of ℚ-complex numbers (n-th roots of unity)
4. trajectories tile (number classification = trajectory closure
   depth)

**Working implication**: every axiom-strip migration = an
"implicit closure → explicit trajectory" conversion.  Nat213 is
not a mere helper-lemma pile but **the vocabulary of trajectory
moves** (cycle, shift, swap, traversal, reparameterisation).

**Operational rule**: on meeting a propext-bringing Lean-core
lemma, ask — "what trajectory does this lemma implicitly
collapse?".  The 213-native replacement exposes that trajectory
as structural recursion or an explicit chain.

**Sources**:
- `lean/E213/Lens/Number/Nat213.lean` (the trajectory vocabulary,
  formalised)
- `lean/E213/Meta/Tactic/AXIOM_FREE_STATUS.md` (the propext-leak
  catalog)

**Guardrail**: do not treat the migration as a mere
"axiom-reduction chore".  *Every conversion is an instance of
213's geometric essence*.  If the trajectory is not exposed, it
is not yet 213-native.

## Lesson 12: Raw = the universal trajectory space (Mingu)

**Core**: the Raw axiom's 4-clause definition is exactly the
**free magma on 2 generators** = "binary trees".  Every
trajectory is a Raw tree, and every distinguishing framework
factors through Raw → α as a Lens (Initiality).

**What the terms imply**:
- the same pair (r₁, r₂) : Raw × Raw is
  - at Raw level: just slash trees (the finest grain)
  - under Lens A: equal (=)
  - under Lens B: isomorphic (≅)
  - under Lens C: homomorphic
- **the kind of equivalence is a property of the Lens**, not of
  the Raws.
- Raw + slash = "the highest-resolution trajectory level".  Each
  Lens determines a *quotient* — a choice of which trajectories to
  identify.
- the Lens lattice = that domain's lattice of equivalence types.

**TOE implication**: this is a *theorem* consequence, not a
claim.
- If a domain can distinguish two states at all, that domain
  factors through Raw + Lens uniquely up to equivalence
  (Initiality).
- So 213 is *constitutively* a TOE — it does not *fit*
  phenomena; it *names* their Raw factoring.
- No external frame (set theory, universe ascent, axiom of
  choice) is needed.

**Sources**:
- `Theory/Raw/Core.lean` (the Raw definition)
- `Lens/LensCore.lean` + `Lens/Initiality.lean` (Lens factoring)
- `Lens/Universal/Witnesses/*` (universality)

**Guardrail**: when in doubt whether 213 can handle some field,
ask "what Lens is that field's distinguishing framework?".
Entering a new field = defining a new Lens = choosing a new
quotient on Raw trees.  This is 213's fixed working procedure.

---


## Methodology patterns

Recurring proof techniques + refactor heuristics + reduction
patterns surfaced during Lean closure work are catalogued in
`theory/meta/methodology_patterns.md` (Patterns #1-#20 plus
Reduction patterns #1-#6).  Lessons in this file (1-12) are
*what to internalise*; patterns there are *what to apply when
writing proofs*.
