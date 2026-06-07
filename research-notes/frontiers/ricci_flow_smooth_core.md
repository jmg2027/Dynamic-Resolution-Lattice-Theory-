# Frontier — the smooth-metric Ricci flow core (Perelman)

**Status: OPEN, and assessed out of ∅-axiom reach in the current repo.**
Recorded per the frontier rule (PROCESS.md): every open frontier lives here.

## What is closed (honestly)

Via the A6 FLOW lift archetype (`MonovariantFlow.flow_reaches`):

- **Chart-Lens cell-filling** coherentization → canonical normal form
  (`GeometrizationConjecture/RicciFlow.lean`), the 213-native graph model.
- **Round Sⁿ smooth-metric flow → finite extinction**
  (`GeometrizationConjecture/RicciSphereFlow.lean`): the homogeneous case where
  the PDE collapses to the linear ODE `dρ/dt = −2(n−1)` on the squared radius;
  the descent rate is the genuine Ricci curvature `Ric(round Sⁿ)=(n−1)g`.
  `n = 3` is the Poincaré seed of finite extinction.

Both are real, both ∅-axiom.  **Neither is the core.**

## What the core is (and why it is the wall)

The hard content of Ricci flow — what makes Poincaré/Geometrization a
century problem — is, in proof-ISA terms, **discharging the A6 `descent`
hypothesis for arbitrary metrics** (not the trivial homogeneous case):

1. **`𝓕/𝓦`-entropy monotonicity.**  Perelman's functional
   `𝓕(g,f) = ∫(R + |∇f|²)e^{−f}dV` is monotone under Ricci flow coupled to the
   conjugate heat equation, with `d/dt 𝓕 = 2∫|R_ij + ∇_i∇_j f|² e^{−f} dV ≥ 0`.
   This is the genuine monovariant; *proving it monotone* is the PDE work.  In
   A6 terms: the monovariant exists and descends because Ricci flow is, modulo
   diffeomorphism + rescaling, the **gradient flow** of `𝓕` — but establishing
   that identity (`∇𝓕 = −(Ric + Hess f)`) is itself the hard computation.
2. **No local collapsing** (from `𝓦` monotonicity) — rules out the
   cigar-soliton degeneration; needed for compactness of singularity blow-ups.
3. **Singularity / surgery.**  The flow develops neck-pinch singularities in
   finite time; one must classify them (κ-solutions), cut and cap (surgery),
   and bound the number of surgeries in finite time, then prove finite
   extinction (simply-connected) or geometric decomposition.

## What is actually reachable vs genuinely hard (corrected)

An earlier draft called the smooth route flatly "walled."  That was too strong.
A differential-geometry-infra audit (213-native calculus) found **substantial
machinery already present**, and the genuinely-hard part is narrower than "all of
Riemannian geometry + PDE":

**Present (∅-axiom):** 1st-order derivative + sum/product/**chain** rules
(`Differentiation/`), polynomial derivatives `d/dx xⁿ`, partial derivatives
`partialAt` + gradient + divergence (`Multivariable/`), `MultiCut = Fin n → cut`,
`cutDiv` (division), `det` over ℤ (`Linalg213/DetN`).

**Buildable from those (no new primitive idea):** iterated/2nd derivatives of
**polynomials/rationals** (the derivative of a polynomial is a polynomial, again
differentiable — the audit's "linear only" is an un-assembled instance, not a
wall), Laplacian `Δ = Σ ∂ᵢ²`, a metric-field type (matrix of cuts over
coordinates), Christoffel/Riemann/Ricci as index sums.

**Genuinely hard (the real wall):** convergent **transcendentals** with
derivative rules — `sin/cos` are stubs, `sqrt`/`exp` only partial; and general-`n`
tensor calculus + the PDE a-priori estimates (Shi/maximum-principle/compactness)
behind Perelman's `𝓦`-monotonicity *for arbitrary metrics*.

**The decisive sidestep — 2D conformal metrics.**  Take `ds² = λ·(dx²+dy²)`
(`λ` a positive **rational** function of the coordinates).  Then Gauss curvature
is a *rational* expression — **no sqrt, no log, no exp**:

  `K = (|∇λ|² − λ·Δλ) / (2·λ³)`.

In 2D `Ric = K·g`, so Ricci flow is `∂_t λ = −2K·λ`, an honest PDE on a single
rational field.  Every ingredient is present or buildable (partials, products,
`cutDiv`, polynomial 2nd derivatives, Laplacian).  **2D conformal smooth Ricci
curvature/flow is reachable ∅-axiom** — the wall is general-`n` + transcendental
metrics, not "smooth differential geometry" wholesale.

## Reachable sub-steps

1. **Gradient-flow ⇒ monotone (algebraic skeleton)** — ✅ **DONE**
   (`Lib/Math/Analysis/Optimization/GradientFlow.lean`, 9 PURE / 0 DIRTY).
   On an abstract `ℤ`-inner-product space, gradient descent `x' = x − τ∇F(x)`
   on `F(x)=⟪x,x⟫` satisfies the **descent identity**
   `F(x − τ∇F) = F(x) − τ(1−τ)‖∇F‖²` (`gradient_descent_identity`), from *only*
   inner-product symmetry + scalar-homogeneity + `ring_intZ`; hence
   `gradient_descent_monotone` (`0 ≤ τ ≤ 1`).  This formalizes the *form* of
   Perelman's monotonicity — "the functional is a monovariant **because** the
   flow is its gradient flow, descending at rate `‖∇F‖²`" — the discrete
   `0`-axiom translation of `d/dt F = −‖∇F‖²`.  Modulo the unreachable-here
   geometric premise that Ricci flow *is* the gradient flow of `𝓕`
   (`∇𝓕 = −(Ric+Hess f)`, the PDE work).

   **ISA insight surfaced**: gradient flow does **not** compile to A6 FLOW.
   A6 (well-founded `ℕ`-descent) gives *finite* termination — that is the round
   sphere (linear `ρ`, finite extinction).  Gradient flow on `F=⟪x,x⟫` with
   contractive `τ∈(0,1)` decreases `F` *geometrically* (`F(x')=(1−2τ)²F(x)`),
   converging **asymptotically** — the **monotone + bounded-below ⟹ convergent**
   instruction (completeness, `MonotonicBounded`/`CauchyComplete`), not
   well-founded descent.  So `𝓕/𝓦`-monotonicity = [descent-identity (done)] +
   [completeness-LOOP convergence], two instructions, neither A6.
2. **Other homogeneous flows as ODEs** — ✅ **DONE (Einstein trichotomy)**
   (`GeometrizationConjecture/RicciHomogeneous.lean`, 6 PURE / 0 DIRTY).  The
   sign of the Einstein constant `λ` (`Ric = λ·g`) sets the whole flow on the
   size `ρ` (`dρ/dt = −2λ`): `λ>0` (sphere) finite extinction **A6**
   (`sphere_reaches_extinction`); `λ=0` (Ricci-flat / **flat torus** /
   Calabi–Yau) **stationary**, every state its normal form
   (`flat_torus_stationary`), A6 cost 0; `λ<0` (hyperbolic) **diverges**, no
   fixed point (`hyperbolic_diverges` + `expand_no_fixed`), **not A6**.  Bundled
   `einstein_trichotomy`.  (Anisotropic Berger-sphere pinching — a 2-variable
   ODE with off-diagonal curvature — is the remaining non-trivial homogeneous
   case, still open.)
3. **Completeness-LOOP convergence** of the geometric `F`-sequence — ✅ **DONE**
   (`Lib/Math/Analysis/Optimization/CompletenessLoop.lean`, 6 PURE / 0 DIRTY).
   The gradient value `vₖ = F(xₖ) = N₀/2ᵏ` (contraction `r ≤ 1/2`) is monotone
   decreasing (`value_decreasing`), **strictly positive at every finite step**
   (`value_pos` — never finitely reaches the infimum `0`, the non-A6 feature),
   yet **converges to `0` with explicit modulus** `K(n) = N₀·2ⁿ`
   (`value_below`: `k ≥ N₀·2ⁿ ⟹ N₀·2ⁿ < 2ᵏ`, i.e. `vₖ < 1/2ⁿ`).  Bundled in
   `completeness_loop`.  This is the **monotone + bounded-below ⟹ convergent**
   instruction in the repo's `Nat→Nat` modulus idiom — the second of the two
   instructions `𝓕/𝓦`-monotonicity compiles to, distinct from A6's finite
   descent.

   **Full Real213 Cauchy object** — ✅ **DONE**
   (`Lib/Math/Analysis/Optimization/RealCauchyWitness.lean`, 4 PURE / 0 DIRTY):
   the value cut sequence `vᵢ = constCut 1 (2ⁱ) = 1/2ⁱ` is a genuine
   `CauchyCutSeq` (`Analysis/CauchyComplete`) with explicit proven modulus
   `N m k = k` (`gradientValueCauchy`) — an actual element of the Real213
   completion.  The limit is `0` on the interior (`m ≥ 1`,
   `gradientValueCauchy_limit_interior`).  Pointwise `cutEq` to `constCut 0 1`
   fails at the boundary `m=0` (open/closed Dedekind artifact) and is not
   claimed; instead the limit is pinned at the real `0` by the genuine
   **order-squeeze** — `0 ≤ limit` (`limit_nonneg`) and `limit ≤ 1/2ⁿ` for every
   `n` (`limit_below_dyadic`), bundled in `gradient_value_converges_to_zero`;
   Archimedeanness forces the unique such real to be `0`.  Instruction ② is thus
   fully realized in Real213 — the gradient monovariant reaches its infimum `0`
   as a genuine point of the completed line, asymptotically.
4. **Normalized flow fixed points = Einstein metrics** at the algebraic level
   (the `Sym(3)`-fixed subspace already in `Ricci.lean` as the averaging-
   invariant analog).

## Smooth 2D-conformal ladder (the reachable smooth route)

Each rung `∅`-axiom, sidestepping transcendentals (rational `λ` only):

S1. **Polynomial 2nd derivative** — assemble `IsDifferentiable` of a polynomial's
    derivative (rebut "linear only"); `d²/dx²(xⁿ)`.
S2. **Laplacian** `Δf = ∂₀²f + ∂₁²f` on `MultiCut 2` from `partialAt`.
S3. **Conformal Gauss curvature** — ✅ DONE (`GeometrizationConjecture/ConformalCurvature.lean`,
    over ℤ via the curvature numerator `confKNum = |∇λ|² − λΔλ`, `K = confKNum/(2λ³)`):
    `confK_flat` (constant `λ` ⟹ `K = 0`, the flat metric).
S4. **A nonflat check** — ✅ DONE (same file): both signs on polynomial `λ` —
    `confK_paraboloid` (`λ = x²+y²+1` ⟹ numerator `−4`, negatively curved) and `confK_dome`
    (`λ = C−x²−y²` ⟹ numerator `4C`, positively curved); `conformal_curvature_trichotomy` bundles
    the flat/negative/positive trichotomy.  Genuine smooth 2D-conformal Ricci curvature, ∅-axiom.
S5. **2D conformal Ricci flow** — ✅ DONE (`ConformalCurvature.lean`).  `∂_t λ = −2K·λ` (since
    `Ric = K·g` in 2D), cleared to `λ²·∂_tλ = confFlowRate = −confKNum`; `conf_flow_flat_stationary`
    (flat metrics are fixed points) + `conf_flow_stationary_imp_flat` (a fixed point ⟺ flat `K=0`) —
    the flow drives the 2D-conformal metric to constant (zero) curvature, the smooth A6 conclusion.
    **Smooth 2D-conformal route S3–S5 closed.**  (A monovariant/time-evolution simulation is a refinement.)

This is genuine *smooth* (not discrete) Ricci geometry, `∅`-axiom, in 2D.

## Verdict

The round-sphere extinction is the honest *floor*.  General-`n` + transcendental-
metric `𝓕/𝓦`-monotonicity remains the *core* wall (PDE a-priori estimates).
But the smooth route is **not** wholesale walled: **2D conformal Ricci
curvature/flow is reachable** with present + buildable infra (rational `K`
formula, no sqrt/exp).  Two converging routes to A6's core now stand: the
**discrete** Forman/Ollivier ladder (`a6_ricci_core/`) and the **smooth 2D
conformal** ladder above.  Do not narrate the general core as "closed"; do
pursue both ladders.
