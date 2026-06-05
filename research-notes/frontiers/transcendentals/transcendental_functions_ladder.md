# Frontier marathon — convergent transcendental functions (∅-axiom)

**Status**: OPEN marathon, standalone.  **Tier**: 1.  One of the two genuinely-hard
blocks split off from the A6 Ricci core (`ricci_flow_smooth_core.md`): the smooth
route is gated on having `exp`, `sin`, `cos`, `sqrt` as *convergent* `Real213`
functions with *derivative rules* — not the current stubs.  This is a
self-contained analysis program: a future `autonomous-research` session picks the
next rung, proves it ∅-axiom, commits, advances the ladder.

## Current state (repo-first)

- **exp**: `Real213/ExpLog/CutExpSeries.lean` — `expPartialSum x N = Σ_{k<N} xᵏ/k!`,
  `cutExp x N` (truncation depth `N`).  **Convergence modulus is the explicit
  follow-up** (geometric majorant `Mⁿ/n!`; ratio-test argument not yet done).
- **sin / cos / exp / sqrt**: `Real213/Core/Functions.lean` — **stubs** returning
  `fun _ _ => true` (placeholders, no computation).
- **sqrt**: only as Pell-convergent irrationality witnesses (`Irrational/Sqrt2Cut`),
  not a smooth function.
- **Series infra**: `Analysis/Series/{CutSequence,CutSeries,CutGeomSeries}`,
  `CauchyComplete`, `BracketCauchyModulus`; **IVT / root-finding**:
  `Analysis/DyadicSearch/{IVT,MinimalRootLens}` (for `sqrt` via `x²−a`).
- **Termwise derivative** of polynomials: `Differentiation/DifferentiableInstances`
  (`cutPowFnIsDifferentiable`) — the bridge to differentiating a power series.

## Ladder (each rung ∅-axiom; `#print axioms` empty)

T1. **exp convergence modulus** — ⚙️ **ratio-test core DONE** (`ExpLog/CutExpModulus.lean`,
    5 PURE): the geometric majorant `Mⁿ/n!` is proven at the term-magnitude level —
    `pow_half_step` → `expTerm_ratio_half` (each Taylor term ≤ half the previous once
    `2M ≤ k+1`, cross-multiplied) → `expTerm_geom_majorant` (`2ʲ·M^{N+j}·N! ≤ Mᴺ·(N+j)!`)
    → `expTail_geom_decay` (tail `≤ term(2M)·2^{−j}`, dyadic modulus `j ↦ 2ʲ`).  The
    *rate* (the hard analytic content) is closed.  **Remaining (T1→T2 bridge)**: package
    the rate into a `CauchyCutSeq` over the cut-level `expPartialSum` (reuse the
    `CompletenessLoop` / `RealCauchyWitness` / `eulerCauchySeq` idiom + `CauchyCutSeq`) —
    this lifts the term decay to the partial-sum Cauchy property as a `Real213` point.
    Also proven: `expTerm_antitone` (terms non-increasing past `2M`) — the
    alternating-series-test input T2 needs.
    ⚙️ **Algebraic route** (`ExpLog/CutExpConvergents.lean`, 5 PURE): exp(m) rational
    convergents for *every* integer arg — `expNum m`, `exp_cross_det` (cross-det
    `m^{n+1}·n!`, generalizes `euler_cross_det`), `exp_convergents_mono`.  **Honest
    finding**: the clean `RateModulus` rate `N(m,k)=k+2` is **m=1-special** (e); the rate
    certificate `i(i+1)m^{i+1}+i ≤ (i+1)²` fails for m≥2 at i=1 (`exp_two_rate_fails_at_one`),
    so general exp(m)'s modulus is the analytic `2m`-threshold majorant above — the two
    routes are complementary.  **Routes unified**: `exp_increment_eq_taylor` (the convergent
    increment `e_{i+1}−e_i = m^{i+1}/(i+1)!` IS the next Taylor term) + `exp_increment_geom_decay`
    (so convergent gaps inherit the `2m`-threshold geometric decay).  The RateModulus margin
    `1/(i·d_i)` is e-tied (bounds `~1/(i·i!)`, not exp(m)'s `~m^{i+1}/(i+1)!` at any threshold) —
    the analytic route is the only one for m≥2; a *generalized*-margin RateModulus (rate
    `m^{i+1}/(i+1)!` not `1/(i·i!)`) would be the algebraic capstone (open).
T2. **sin / cos convergent series** — ⚙️ **convergence modulus DONE by comparison**
    (`ExpLog/CutTrigModulus.lean`, 4 PURE + `expTerm_le_of_ge` in CutExpModulus): the
    `sin`/`cos` term magnitudes are the `exp` terms at odd/even indices, so they inherit
    `exp`'s engine — `cosTerm_geom_decay` / `sinTerm_geom_decay` (geometric majorant,
    decay `term(m)/2^{2k}`) + `cosTerm_antitone` / `sinTerm_antitone` (non-increasing
    past the threshold — the alternating-series-test hypothesis).  **Remaining**: the
    *signed* cut-level series `sinCut x N = Σ(−1)ᵏ x^{2k+1}/(2k+1)!`, `cosCut` even-power
    (replacing the `Core/Functions.lean` stubs); their alternating partial sums bracket
    the limit *because* of the antitone magnitudes proven here.
T3. **derivative rules** — ⚙️ **coefficient level DONE** (`exp_deriv_coeff_fixed` in
    CutExpModulus; `sin_deriv_coeff`/`cos_deriv_coeff` in CutTrigModulus, 3 PURE):
    `d/dx exp = exp` (fixed point), `d/dx sin = cos`, `d/dx cos = −sin` — all from the one
    factorial shift `(n+1)·n! = (n+1)!` (exp = fixed point, sin↔cos = 2-cycle; the cos
    sign-flip lives in the Int213 difference-Lens).  **Remaining**: the cut-level termwise
    statement `d/dx expPartialSum N = expPartialSum (N−1)` via the `IsDifferentiable`
    add/mul/`cutPow` instances (`cutPowFnIsDifferentiable`).
T4. **sqrt as a smooth function** — `sqrtCut a` via bisection / Newton on `x²−a`
    (`DyadicSearch/IVT` / `MinimalRootLens`), with convergence modulus,
    `(sqrtCut a)² = a` (up to `cutEq`), and `d/dx sqrt = 1/(2 sqrt)`.
T5. **functional equations / identities** — `sin²+cos² = 1`, `exp(a+b) =
    exp a · exp b` (Cauchy-product of the series); the engine certificates that
    make the transcendentals usable downstream.
    ⚙️ **`choose`↔factorial bridge done** (`NumberTheory/DyadicFSM/FLT/ChooseFactorial.lean`,
    1 PURE): `choose (k+j) k · (k!·j!) = (k+j)!` (division-free `C(n,k)=n!/(k!(n−k)!)`), proven
    from the absorption identity `choose_succ_mul` by induction.  This is the bridge `exp(a+b)`
    needs: cross-multiplying the Cauchy convolution `Σ (aʲ/j!)(bᵏ/k!)` by `n!` turns it into
    `Σ C(n,j) aʲ bⁿ⁻ʲ = (a+b)ⁿ` (binomial theorem) via exactly `C(n,j)·j!·(n−j)!=n!`.
    ⚙️ **general 2-var binomial DONE** (`BinomialTwoVar.lean`, 2 PURE): `binom2_theorem`
    (`(a+b)ⁿ = Σ_{k≤n} C(n,k)aᵏbⁿ⁻ᵏ`) via `binomSum2_step` (common-form reduction, Pascal +
    `sumTo` helpers + `b`-exponent congruences).  **Remaining**: the cut-level series Cauchy
    convolution `(Σaʲ/j!)(Σbᵏ/k!) = Σ(a+b)ⁿ/n!` (combine `binom2_theorem` + `choose_mul_factorials`
    at the `Real213` series level) + `sin²+cos²=1`.

## Downstream unblocked

T1–T4 unblock the **smooth round-sphere curvature** the honest way (Gauss
curvature of `ds²=dθ²+sin²θ dφ²` needs `d²/dθ²(sin²θ)` — T2+T3), and `sqrt`
unblocks the general (non-conformal) orthogonal-metric Gauss formula.  Together
with the 2D-conformal ladder (which needs *no* transcendentals) they complete the
smooth side of A6.

## Honest boundary

This is ordinary constructive analysis (Bishop-style), fully in-reach `∅`-axiom —
*not* the hard part of Perelman.  It is "hard" only as volume of careful Cauchy /
factorial bookkeeping, not as a conceptual wall.  Start at **T1**.
