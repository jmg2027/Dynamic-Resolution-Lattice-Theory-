# G139 — Cohomology open-frontier marathon

**Branch**: `claude/cohomology-marathon-qOxOX`.
**Status**: Active.

Multi-session marathon advancing the five `theory/math/cohomology/`
open frontiers carried over from G138:

  · `bipartite.md` — universal `∀ NS NT c, kerSizeDelta0Direct = 2`.
    Blocker: no `GraphWalk/` infra.  Estimate 5–8 sessions.
  · `k32_higher_cohomology.md` — general Steenrod `cup_i` (i ≥ 2),
    non-vacuous Adem / Cartan, Massey triple `⟨ω, ω, ω⟩`.
  · `fractal.md` — structural Gram self-energy derivation,
    ∀-coprime eventual periodicity, truth-table Lean witness.
  · `cupaw.md` — self-referential lex-cup Leibniz ∀(k, l).
    Decomposition machinery (Decomp + UniversalLift + AlgLift{α, β})
    already in place.
  · `hodge_conjecture.md` — HC²¹³ variant automation.

## Strategy

Each closure ships as 213-native ∅-axiom PURE.  Cardinality
cut-off applications follow the Pell / Lucas / Fibonacci /
Tribonacci template from G134 §7.  Higher cup_i and Massey
extend the K_{3,2}^{(c=2)} Steenrod-algebra stack from G132.

## Phase 1 — this session

  1. **G139-A Padovan cut-off** — extend Direction C to a fifth
     external sequence.  Triple Hunter-generator coincidence at
     odd indices `(P_3, P_5, P_7) = (NT, NS, d)`, contrasting
     Fibonacci's consecutive-index pattern.
  2. **G139-B K_{3,2} cup_3 at 4-skeleton** — formalise the
     `cup_3 : C² × C² → C¹` Alexander-Whitney instance and the
     vacuous self-pairing `ω ⌣_3 ω` at the 4-skeleton truncation
     (lands in `C¹` but `2 + 2 - 3 = 1` mapping is empty in the
     simple AW restriction; document the structural ladder
     extension).
  3. **G139-C Eventual periodicity at (5, 11)** — explicit
     instance using the existing `pow_mod_period_pure` /
     `configCountD_mod_pure`.  Closes the depth-1 case at
     `p = 11` parametrically (the existing `configCountD_5_mod_11`
     deferred parametric form).

## Phase 2 (next session candidates)

  · ∀-coprime eventual periodicity via pigeonhole on `d^n % (p-1)`.
  · CupAW Leibniz at a new bidegree (3, 1) or (1, 3) via the
    existing `LeibnizUniversalLift` + Decomp.
  · K_{3,2} higher Steenrod `Sq^3`, `Sq^4` (vacuous at 4-skeleton).
  · Massey triple at 4-skeleton with explicit landing-space audit.

## Phase 3+ (deferred)

  · Truth-table `Fintype`-style witness (`Fintype.card`-equivalent
    in 213-native Lean).
  · `GraphWalk/` infrastructure (multi-session).
  · Gram self-energy structural step (physics-layer).
  · Hodge conjecture variant automation (extends 31-capstone tree).

## Cross-references

  · `theory/math/cohomology/{bipartite, k32_higher_cohomology,
    fractal, cupaw, hodge_conjecture}.md` — chapters.
  · `theory/meta/cardinality_cutoff_applications.md` — G134
    six-direction template.
  · `HANDOFF.md` — G138 corpus synthesis carry-over.
