# The modulus-degree ladder — grading "completes" beyond the binary

**Question that opened this** (originator, 2026-06-10): what happens at modulus
degree 2, 3, … — `W ~ N(m,k)²`, `N(m1,k1)×N(m2,k2)`, or other shapes?

**Status**: the algebraic pillar is **closed** at degrees 2 and 3; the graded
rate generator (rung 1) is **closed** (`RateModulus.graded_total_modulus`,
`N = k^s + 1`); the two-real separation modulus and the measure-modulus schema
are **open**.

## The conversion law (the frame)

A total cut modulus is always `N(m,k) = rate⁻¹(distance(m,k))` — a distance
lower bound composed with the inverse convergence rate.  The "degree" of the
modulus is the growth class of `N` in `k`, and it factors as
(degree of the distance certificate) / (rate exponent of the pointing).

## Closed (the algebraic pillar)

- **Degree 2** — φ: the form `m²−mk−k²`, `|Q| ≥ 1`; closed-form cut
  (`PhiAsCut.masterCut`), and the squared comparison `4k² < b²` in
  `FibCassiniNat.qb_lt_pk` is the `ε·k² < d²` schema instance.
- **Degree 3** — ∛2 (`Real213/CubeRootTwoCut`, 31 PURE): side-decision reduces
  to the all-additive `ε_i·k³ < d_i³`; the `Nat` strictness `+1` *is* the form
  margin `|m³−2k³| ≥ 1`.  Dyadic bisection presentation ⟹ total modulus
  `N(m,k) = 3k+5`; the completed fold **equals** the frozen form cut
  (`cbrt_limit_eq_form`).  Key structural reading: the algebraic degree enters
  as the **probe exponent `k^s` in the schedule**, and the form makes the
  modulus presentation-robust — *any* presentation with a cube-slack rate
  completes.  The rate race (`W` vs `d`, `holonomic_modulus.md`) and its
  presentation-dependence (`Zeta3Cut.zeta3_presentation_overtakes`) are the
  transcendental-only regime.

## Rungs (status inline)

0. **The exact degree of an arbitrary irrational** (originator, second round).
   The "tight, no-more-no-less" degree is the irrationality measure `μ(x)`,
   and it splits into three rungs of very different status: (i) the universal
   floor `μ ≥ 2` is **constructive** (Dirichlet pigeonhole — foldable with the
   repo's `Pigeonhole`); (ii) for algebraics the exact value is `2` regardless
   of polynomial degree `d` (Thue–Siegel–Roth) but **ineffectively** — no
   computable constant, no fold receipt; the degree-`d` form schedule
   (`CubeRootTwoCut`'s `k³`) is the generic *effective* receipt, with
   number-specific effective descents (Baker-type, ∛2 down to `≈ 2.47`) paid
   for by transcendence-theory work; (iii) for arbitrary irrationals `x ↦ μ(x)`
   is not computable from the pointing — receipts only squeeze it from both
   sides (presentations witness `μ ≥`, form/measure certificates witness
   `μ ≤`), and the meeting point is generally receipt-less.  The "next term
   below the degree" expansion is real but lives on a **log scale**, not a
   power scale (`|e − p/q| ≍ (log log q / log q)/q²`), matching the lex
   `(height, rate)` ordinal of `CompletabilityGrade`: the refinement axis
   between exponents is ordinal/scale-like.
0′. **Irrational degree + the degree cascade** (originator, second round).
   The degree spectrum is the full continuum: for every real `τ ≥ 2` there are
   reals with `μ(x) = τ` exactly (Jarník; level set has Hausdorff dimension
   `2/τ`), constructible by prescribing CF growth `a_{n+1} ≈ q_n^{τ−2}`.  So
   `μ` is a self-map of `[2,∞]` and the cascade `x ↦ μ(x) ↦ μ(μ(x)) ↦ …` is
   its orbit: generically it collapses (`μ = 2` a.e., then rational, end);
   an infinite nontrivial cascade needs a chain of very-well-approximable
   degrees.  Two 213-native objects fall out: (a) **the self-degree fixed
   point** `μ(τ) = τ` — a number that is exactly its own cut's degree, built
   by a self-referential CF (growth schedule read off the number's own
   approximants); conjecture-grade, a residue-self-pointing shape on the
   degree Lens; (b) **operational cascade = modulus composition**: a schedule
   `N(m,k) = k^e` must *call e's own modulus* to evaluate `⌈k^e⌉`, so
   irrational-degree moduli are receipts taking receipts as arguments — a
   call-tree of folds, formalizable now as a schedule functional consuming a
   `CauchyCutSeq`.  **The functional is BUILT** (`Real213/ModulusComposition`,
   30 PURE): `powSched c B k = ⌈k^{p/2^k}⌉` with `p` read off the exponent cut
   (`dyUp`, sound under integer witness + forward doubling; `rootCeil` exact by
   sandwich), calibrated (`powSched_rat`: integer `s` returns exactly `k^s`),
   instantiated at degree ∛2 (`cbrtPow_at_two = 3` — the ladder eats its own
   degree-3 brick as an exponent) and degree e (`ePow_at_two = 7`, the kernel
   evaluating `eulerCauchySeq.N` inside the schedule), and iterated once:
   `eSelfScheduled` — e rescheduled by a schedule querying e's own modulus,
   limit-preserving (`reschedule_limit_eq`).  **And the degree-as-cut backbone is LANDED** (`powSched_mono`: exponent-cut
   order transports to schedule order, so the threshold "a degree-τ schedule
   suffices for x" is monotone — a cut one level up; its decidability = the
   effective-μ question, Roth-grade).  Still open here: *tightness* of
   `dyUp` (lower witness needs the ratio/rescale property), and a real whose
   *intrinsic* degree is irrational (Jarník construction) rather than a
   rescheduled presentation.
1. **Graded rate generator** — **CLOSED** (`RateModulus` / `RateStratification`,
   all ∅-axiom).  The margin telescope parametrized by a probe schedule
   `ρ : ℕ → ℕ`: `HtelS a d ρ` (margin `e_i + 1/(ρ_i·d_i)` non-increasing) plus
   one admitted layer (`k ≤ ρ i₀`) ⟹ cut constant past `i₀+1`
   (`rateS_cut_const`).  `ρ = id` recovers `Htel`/`N = k+2` definitionally;
   `ρ = rootFloor s` (new `Meta/Nat/RootFloor`, calibration
   `rootFloor s (k^s) = k`) gives `graded_total_modulus`: **`N(m,k) = k^s + 1`**
   (one better than the conjectured `k^s + 2`).  Per-layer form `DominatesS W d ρ`
   with `htelS_iff_dominatesS` (characterization at every grade) and
   `overtakeS_breaks_layer`.  The forgiven factor, measured at the admission
   layer `i = r^s`, is `r^{s−1}` (slack defended `1/(r·d)` vs the identity
   schedule's `1/(r^s·d)`) — the note's conjectured `i^{s−1}` reads correctly in
   probe units, not layer units.  Strictness witnessed end to end: `sepDen`
   (`d_{i+1} = (⌊√i⌋+2)·d_i`, `W = d`) is root-2-dominated everywhere but breaks
   `Dominates` at layer 4 (`graded_stratification`), and with numerators
   `a_{i+1} = (⌊√i⌋+2)·a_i + 1` (cross-det relation solved over ℕ) the pair
   `sepNum/sepDen` is an actual presentation completing at `N = k²+1`
   (`sep_graded_modulus`) — a real rescued outside the degree-1 class.  Rescue
   is now graded the way `CompletabilityGrade` grades break.  Narrative:
   `theory/math/analysis/holonomic_modulus.md` §4.
2. **Conditional measure-modulus schema** — `effective measure μ + Cauchy rate
   ⟹ constructed N`.  Instance: Wallis-π with `μ(π) ≤ 7.11` would carry a
   degree-≈7 modulus; the formalization cost of the measure is thereby isolated
   in one hypothesis.  (π moves from "hypothesis modulus" to "conditional
   degree-7 modulus".)
3. **Two-real separation modulus** — the genuine `N(m1,k1)×N(m2,k2)` object:
   deciding `x ≤ y` for two folds needs a joint `|x−y|` lower bound.  The
   one-probe gap quantum `1/(k·d_i)` is already bilinear (probe × convergent,
   the Farey/Stern-Brocot `det = ±1`); the two-fold version is new machinery
   (`cutLe` currently sidesteps it).
4. **Higher algebraic instances** — degree-4+ form cuts (e.g. `√2+√3`,
   `x⁴−10x²+1`), and the cubic-unit narrative: at degree 2 the binary form
   carries an infinite unit orbit (Pell, `W ≡ 1` floor); at degree 3 the binary
   slice of the rank-1 unit orbit is finite (Thue/Delaunay–Nagell — hard), the
   orbit needing the full rank-3 lattice.  Why the self-similar P-orbit story
   does not lift to degree 3 as binary dynamics.

## The 213 reading

The fold/residue correction refines from a dichotomy into a **filtration**:
modulus degree = how many receipts the pointing carries (0 = the form is the
cut; 1 = the rate is its own receipt; s = receipt-of-receipt; no finite degree
= toward reached-by-none).  Residue-lint: this is a Lens-grading of
*pointings*, not an ontological stratification of the residue — the residue
sits in no rung; the ladder classifies the ways of pointing at it.

## Pointers

- Closed: `lean/E213/Lib/Math/NumberSystems/Real213/CubeRootTwoCut.lean`,
  `PhiAsCut`/`FibCassiniNat` (degree 2), `holonomic_modulus.md` (degree-1 class);
  rung 1: `Real213/{RateModulus,RateStratification}.lean` (graded generator,
  `HtelS`/`DominatesS`/`graded_total_modulus`) + `Meta/Nat/RootFloor.lean`
- Break-grading: `CompletabilityGrade`, `RefinedCompletabilityEngine`
- ζ(3) companion frontier: `zeta3_free_modulus.md`
