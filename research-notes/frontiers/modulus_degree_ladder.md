# The modulus-degree ladder — grading "completes" beyond the binary

**Question that opened this** (originator, 2026-06-10): what happens at modulus
degree 2, 3, … — `W ~ N(m,k)²`, `N(m1,k1)×N(m2,k2)`, or other shapes?

**Status**: the algebraic pillar is **closed** at degrees 2 and 3; the graded
transcendental generator and the two-real separation modulus are **open**.

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

## Open rungs

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
   limit-preserving (`reschedule_limit_eq`).  Still open here: *tightness* of
   `dyUp` (lower witness needs the ratio/rescale property), and a real whose
   *intrinsic* degree is irrational (Jarník construction) rather than a
   rescheduled presentation.
0″. **The `exp(p/q)` instance of the rate-free regime** (cross-branch, proven).
   `ExpLog/ExpUnitModulus`: the unit-fraction family `exp(1/q)` completes through
   the e-generator verbatim (`expUnitCauchySeq`, modulus `k+2`, uniform in `q`),
   and for `p ≥ 2` the factorial presentation provably overtakes
   (`exp_pq_presentation_overtakes`, layer `q+9`; `exp_pq_no_htel` via
   `htel_iff_dominates`) — the sharpest concrete boundary case for rung 1 / the
   dyadic-bracket route: a *transcendental of measure 2* whose natural pointing is
   rate-free.  Whoever builds rung 1 (or the `CubeRootTwoCut`-style schedule for a
   series tail) should test it on `exp(2)` first.  **The fold side is now built**
   (`ExpLog/ExpRationalCut`, 18 PURE): `expPQAb : AbCutSeq` for every `exp(p/q)`
   (`q ≥ 1`), with the doubled-tail upper bracket `S_{N+j} ≤ (a_N(N+1)q + 2p^{N+1})/d_{N+1}`
   past the threshold `2p ≤ (N+2)q` (the geometric halving as one Nat invariant), and
   `e²` localized in `(7, 904/120]` — the ζ(3) posture (fold closed, free modulus
   open) now holds for all rational exp arguments.
1. **Graded rate generator** — refine the binary `Dominates`
   (`RateStratification`) with polynomial slack: `Dominates_s` forgiving an
   `i^{s−1}` factor of overtake, generalizing `rate_total_modulus` to
   `N(m,k) = k^s + 2`.  Makes "rescue" graded the way `CompletabilityGrade`
   already grades "break" (lex `(height, rate)` ordinal) — the two axes become
   symmetric.
2. **Conditional measure-modulus schema** — ✅ **the schema is BUILT**
   (`AbCutSeq.sep_cauchy` / `toCauchySep`): a separation schedule `I : Nat → Nat`
   ("every `false` reading at resolution `k` already shows at layer `I k`")
   completes any fold with the constructed modulus `N(m,k) = I k` — the
   effective-irrationality cost isolated in the one hypothesis `hsep`.
   **Instantiated at `exp(p/q)`** (`ExpRationalCut` §5, `expPQCauchySep`): the §3
   bracket reduces `hsep` to *one arithmetic statement per resolution* ("no
   fraction of denominator `k` lies in the `I k`-th bracket"), with the strict
   squeeze `d·m < a·k ≤ U-bracket < d·m` closing the above-schedule case.  What
   remains open is supplying `hmeas` unconditionally (Padé/Hermite effective
   irrationality of exp, `I k ≈ 2p/q + O(log k)`); Wallis-π instantiates the same
   `toCauchySep` in one line whenever its `μ(π) ≤ 7.11`-grade separation
   hypothesis is supplied (π moves from "hypothesis modulus" to "conditional
   degree-7 modulus").
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

0‴. **The CF pointing is universally rate-carrying — packaged + first transcendental
   instance** (cross-branch follow-up).  `cf_universal_total_modulus` (already in
   `ContinuedFractionModulus`) is now packaged with the explicit constant into
   `cfCauchySeq : CauchyCutSeq` (`N(m,k) = k+2`, §6), and instantiated at
   **Lambert's `coth(1/q) = [q; 3q, 5q, …]`** (`cothUnitCFCauchySeq`, anchors
   `21/16`, `coth(1) ∈ (5/4, 3/2]`) — the repo's first *transcendental* completed
   through its CF, unconditionally.  The pointing dichotomy is now a theorem pair:
   the series pointing of `exp(p/q)` (`p ≥ 2`) carries no rate (`exp_pq_no_htel`),
   the CF pointing of the same number family carries everything.  **The weld** —
   Lambert CF correctness (Padé/Bessel identity: the CF real = series `coth(1/q)`)
   — is the remaining identity; once welded, `e^{2/q} = (coth(1/q)+1)/(coth(1/q)−1)`
   is one cut-Möbius step, discharging `ExpRationalCut`'s measure hypothesis on the
   sharpest route.

0⁗. **The weld, stage 1 — the series side of the Lambert ladder is built**
   (`ExpLog/LambertWeld.lean`, 7 PURE).  The Bessel contiguity
   `F_{n−1} = (2n+1)Fₙ + u·F_{n+1}` (`f_n(j) = 1/((2j)!!(2n+2j+1)!!)`, coefficient
   identity `(2n+1)+2j = 2n+2j+1`) is delivered **division-free at every truncation**:
   `FNum q n J` (Horner: `FNum(J+1) = (2J+2)(2n+2J+3)q²·FNum(J) + 1`) with
   `weld_ladder : (2n+2J+3)·FNum n J = (2n+3)·FNum (n+1) J + 2J·FNum (n+2) (J−1)`,
   and the bottom rungs collapse to cosh/sinh exactly (`(2j)!!(2j−1)!! = (2j)!`):
   `weld_base` (cosh enters at `n = −1`), `sinhNum_eq_FNum_zero` (`n = 0` IS sinh).
   So `coth(1/q) = q·F_{−1}/F_0` and the unrolled ladder IS `[q; 3q, 5q, …]`.
   **Stage 2 (the finite weld identity, open)**: pair with the CF convergent
   polynomials — `F_{−1}·B̃_n − F_0·Ãₙ = ±u^{n+1}·F_{n+1}` truncated (induction on
   `n` along `weld_ladder`), bridge `cfPn (cothCF q) n = q^{n+1}·Ãₙ(1/q²)`, then
   order-transfer pins `cothUnitCFCauchySeq q` between the cosh/sinh brackets.
   Lean note: PolyNatM's normalizer does **not** drop `0·atom` monomials and chokes
   on un-reduced `(J+1)−1` index atoms — close `J = 0` rungs by `rfl` (all-literal
   defeq) and re-ascribe IHs with reduced indices.

## The 213 reading

The fold/residue correction refines from a dichotomy into a **filtration**:
modulus degree = how many receipts the pointing carries (0 = the form is the
cut; 1 = the rate is its own receipt; s = receipt-of-receipt; no finite degree
= toward reached-by-none).  Residue-lint: this is a Lens-grading of
*pointings*, not an ontological stratification of the residue — the residue
sits in no rung; the ladder classifies the ways of pointing at it.

## Pointers

- Closed: `lean/E213/Lib/Math/NumberSystems/Real213/CubeRootTwoCut.lean`,
  `PhiAsCut`/`FibCassiniNat` (degree 2), `holonomic_modulus.md` (degree-1 class)
- Break-grading: `CompletabilityGrade`, `RefinedCompletabilityEngine`
- ζ(3) companion frontier: `zeta3_free_modulus.md`
