# Bishop subsumption (Bishop comparison / AsLensOutput doctrine)

How DRLT's Lens-output function space subsumes Bishop's constructive
ℝ program — without constructing ℝ piece-by-piece.  Companion to
Real213-Analysis deep dive §2 (deep-dive reading) and `Lib/Math/Real213/Core/AsLensOutput.lean`
(formal carrier).

## The doctrinal claim

User directive (2026-04-26):

  > "Aren't there infinitely many different ways to extract natural
  > numbers from 213?  Of course reals exist then.  Computation? You
  > can always pick any way to operate on those infinitely many
  > natural numbers."

  > "The Bishop program itself is redundant within 213 — the Lens
  > space of 213 already contains the reals.  Everything built in the
  > marathon — cutSum, cutMul, cutMaxMin — are valid choices within
  > the framework."

## Why this is a subsumption, not a re-construction

Classical analytic constructions of ℝ:
  · Cauchy sequences (Bishop's choice for constructive analysis)
  · Dedekind cuts (set-theoretic)
  · Decimal / signed-digit expansions
  · ...

Each is a **separate construction effort** that builds ℝ from
(rational sequences | sets | digit streams) with careful definitions
of equality, ordering, arithmetic, completeness.  Bishop's program is
the most delicate of these because it must hand-rebuild every operation
with explicit ε-N moduli.

DRLT's approach:
  · The Lens-output function space `Raw → Bool` (or `Nat → Nat → Bool`
    after count-Lens application) is **structurally present** the
    moment the axiom + Lens framework is committed.
  · ℝ is a **choice of subspace**: pick `Cut := Nat → Nat → Bool` with
    a specific interpretation (`c m k = true ⟺ x ≤ m/k`).  Operations
    like `cutSum`, `cutMul`, `cutMid` are **chosen functions** that
    happen to satisfy rational arithmetic under that interpretation.

The key insight: **the function space `Nat → Nat → Bool` is not a
construction of ℝ; it is a space large enough to contain ℝ for free**.
Operations are then named, not invented.

## Operational realisation

`lean/E213/Lib/Math/Real213/Core/AsLensOutput.lean`:
```lean
/-- Reals as cuts.  Lens-output realisation — no construction needed,
    only a named subspace of the universal `Nat → Nat → Bool`. -/
abbrev RealAsLensOutput := Nat → Nat → Bool
```

Subsequent files (`CutSum.lean`, `CutMul.lean`, `CutMid.lean`, etc.)
each pick a function in this space and prove the interpretation
identity.

## Status: what's formalized vs. what's deferred

**Formalised** (current state):
  · `RealAsLensOutput := Nat → Nat → Bool` (the abbrev).
  · `Real213` struct (Layer 2) ↔ `chainToCut` bridge ↔ `RealAsLensOutput`
    (Layer 3).
  · Per-operation correctness (cutSum, cutMul, cutMid, ...): each
    operation's identity at concrete rational pairs proven via
    `decide` or pointwise reduction (e.g., `cutSum_int_int`,
    `cutMul_one_const_at`).
  · Algebraic structure (CutPoset, lattice, dyadic completeness).

**Deferred** (Bishop comparison / REAL-RES6 — 3-5 sessions):
  · Bishop ↔ DRLT formal equivalence:
    - Bishop's `CauchyReal` ≃ DRLT's `Real213` modulo equiv
    - Bishop's operations ↔ DRLT's cut operations
    - Where DRLT extends Bishop (Lens-output framing, graded structure)
  · Universal characterisation: prove `RealAsLensOutput` satisfies
    the Bishop axioms (Cauchy completeness, Archimedean, decidable
    order at rationals).

## Why the deferral is principled (not a gap)

The Bishop comparison is a **bridge into another framework**, not a
DRLT-internal closure.  213's falsifiability rule (`AXIOM/04_falsifiability.md`
§5.2.1) demands that DRLT predictions hold without external axioms.
The Bishop comparison is a TRANSLATION layer, not a derivation.

The PURE proof status of `RealAsLensOutput`, the cut operations, and
the algebraic structure (verified by `#print axioms`) is the
DRLT-internal closure.  Bishop subsumption is the *outer claim* that
DRLT's space is bigger — to make it formal Lean-level requires an
external Bishop API to compare against, which is outside the
∅-axiom contract.

## Cross-references

  · `lean/E213/Lib/Math/Real213/Core/AsLensOutput.lean` — formal carrier.
  · `research-notes/G108_real213_analysis_deep_dive.md` §2 — deep-dive
    reading.
  · `seed/RESOLUTION_LIMIT_SPEC.md` — relates `RealAsLensOutput` to the
    finite-N_U bound (cuts evaluated at m, k ≤ N_U).
  · `LESSONS_LEARNED.md` Pattern #17 (framework-internal subsumption).
  · `catalogs/cross-domain-identifications.md` — math↔physics bridges
    sit on top of `RealAsLensOutput`.

## Future research direction (REAL-RES6 / Bishop comparison follow-up)

The full Bishop ↔ DRLT comparison is **5-7 sessions of bridge work**:

  1. Implement minimal Bishop API in 213 namespace (Cauchy sequences,
     ε-N modulus, fundamental sequence equivalence).
  2. Prove `RealAsLensOutput` ↔ Bishop carrier (via chainToCut +
     dyadic bisection).
  3. Prove operations match (cutSum ↔ Bishop's `+`, cutMul ↔ `·`, etc.).
  4. Characterise extensions: DRLT's graded structure, Lens-output
    realisation, and resolution-limit ceiling.

This is **doctrinal closure**, not predictive enhancement.  DRLT's
falsifier surface (`seed/FALSIFIABILITY_SURFACE_SPEC.md`) is
independent of the Bishop comparison.
