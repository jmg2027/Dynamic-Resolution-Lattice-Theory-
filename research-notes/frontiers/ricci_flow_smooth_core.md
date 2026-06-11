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

## The general-`n` Ricci *lower bound* — the synthetic (CD(K,N)) bypass

The wall above is the smooth *flow* with metric tensors.  The Ricci *lower
bound* in general dimension — "Ric ≥ K, dim ≤ N" — has a **synthetic**
characterization that needs no metric tensor at all: the Bakry–Émery
curvature-dimension condition `CD(K,N)`,

  `Γ₂(f) ≥ K·Γ(f) + (1/N)(Lf)²`,

built from the carré du champ `Γ(f) = ½Σ(f(y)−f(x))²` and its iterate
`Γ₂ = ½LΓ − Γ(f,Lf)` of the graph Laplacian `L`.  Lott–Sturm–Villani /
Bakry–Émery: in the smooth case `CD(K,N)` is *equivalent* to `Ric ≥ K, dim ≤ N`
— so `CD(K,N)` IS the dimension-independent meaning of a Ricci lower bound, and
it is a finite polynomial inequality, `∅`-axiom.

**Done** (`GeometrizationConjecture/BakryEmery.lean`): the discrete Bochner
identity makes `Γ₂` an exact sum of squares — `bochner_line`
(`4Γ₂ = (Lf(x−1))² + 2(Lf(x))² + (Lf(x+1))²`, the flat `Ric = 0` Bochner with no
negative term) ⟹ `cd_0_2_line` (the line/large cycle is `CD(0,2)`); and
`bochner_triangle` (`Γ₂ = (5/2)Γ + ½(f₁−f₂)²`) ⟹ `cd_triangle` (the triangle
`C₃ = K₃` is `CD(5/2,∞)`, the complete-graph value `(n+2)/2`).  This is the
**fourth** curvature frame (Forman, Gauss–Bonnet, Ollivier, Bakry–Émery), all
agreeing on the sign, and the one that is *defined* dimension-independently — so
"general-`n` Ricci lower bound" is reachable synthetically even while the smooth
`n`-tensor flow stays walled.

**Done** (`BakryEmery.lean` §3): the complete graph `K_m` for general `m` is
`CD((m+2)/2, ∞)` (`cd_complete_graph`, 9 PURE) — the `gridSumZ`-over-neighbours
generalization of `bochner_triangle`, via the closed form `gamma2C = (k+3)·gammaC +
sosGap` (`bochner_complete`) with `sosGap = Σ_jΣ_{j'}(b j'−b j)² ≥ 0` a manifest
double sum of squares (`k = m−1`, `k+3 = m+2`).  **Reachable next (no new idea):**
the discrete Lin–Yau curvature (the optimal `K` in `CD(K,∞)`) as a max over test
functions.  **Still walled:** the *transcendental* Perelman
`𝓦`-entropy `∫[τ(R+|∇f|²)+f−n](4πτ)^{−n/2}e^{−f}` (needs the `n`-dim Gaussian =
`exp` integration; the discrete `𝓦`-analog is the rung-3 energy decay).

## General-`n` conformal **scalar** curvature — the conformal route pushed past 2D

The 2D-conformal Liouville curvature **generalizes to all `n`** for the *scalar*
curvature (`ConformalCurvature.lean` §S6, PURE).  For `g = λ·δ` on `ℝⁿ` the conformal
factor `φ = ½ln λ` cancels, leaving the **rational** (no transcendental) scalar
curvature `R = −(n−1)(4λΔλ + (n−6)|∇λ|²)/(4λ³)` — `confRNumN` is the numerator over ℤ.
It **reduces exactly to the 2D case** (`confRNumN_eq_confKNum`: `confRNumN 2 = 4·confKNum`,
`R = 2K`), validating the general formula against the established `n = 2`.  At **`n = 3`**
— the Poincaré/Geometrization dimension — the flat/positive/negative trichotomy is closed
on polynomial `λ` at the origin 2-jet (`conformal_scalar_curvature_3d`: dome `48C`,
paraboloid `−48`).  So the conformal route is **not** stuck at 2D; the general-`n`
*scalar* curvature is reachable.

The conformally-flat Ricci **tensor** itself is now reached too (`ConformalCurvature.lean`
§S7, PURE): `confRicOffNum`/`confRicDiagNum` (numerators `×4λ²`), validated by the trace
identity `confRicTrace3` (`Σ_i Ric_{ii} = confRNumN`, so `R = (1/λ)·tr Ric` = the §S6 scalar).
`confRic3_dome_origin`: the 3D dome `λ = C−r²` is **Einstein at its origin** (`Ric` isotropic
— off-diagonal `0`, diagonal `16C`, `Ric ∝ g`).  **Honest boundary (narrowed)**: the
*conformally-flat* Ricci tensor (not just the scalar) is now `∅`-axiom in general `n`; the
residual wall is the Ricci tensor of an *arbitrary* metric (general `g_{ij}`, its inverse,
Christoffel/Riemann as index sums), transcendental metrics, and the *flow* with PDE a-priori
estimates (and Ricci flow not preserving conformality for `n ≥ 3`).

**General-metric tensor calculus opened** (`Geometry/TensorCalculus.lean`, PURE,
dimension-free): the **Christoffel symbols of the first kind** `Γ_{kij} = ½(∂_i g_{kj} +
∂_j g_{ki} − ∂_k g_{ij})` — the inverse-free part (no `g^{lm}`, no division) — with the
genuine general-`n` identities `chris1_symm` (lower-pair symmetry / torsion-free),
`chris1_metric_compat` (`Γ_{kij}+Γ_{jik} = ∂_i g_{kj}`, metric compatibility `∇g = 0`), and
`chris1_flat`.  Dimension-free: indices arbitrary `Nat`, the metric enters only via its
derivative tensor `dg a b c = ∂_a g_{bc}` (symmetric in the last two slots).  **Next rungs**:
the second-kind `Γ^l_{ij} = g^{lm}Γ_{mij}` and the Riemann/Ricci tensors need the metric
**inverse** `g^{lm}` (adjugate/`det` over ℤ) + second derivatives.  The **inverse-bearing
layer is now opened** (`TensorCalculus.lean` §2, PURE): the `det`-scaled second kind
`2·det·Γ^l_{ij} = Σ_m adj^{lm}·2Γ_{mij}` (`chris2xDet`, `gridSumZ` over `m`), its lower-pair
symmetry (`chris2_symm`), and — the key — `chris2_lower`: `Σ_l g_{pl}·(2 det Γ^l_{ij}) =
det·2Γ_{pij}`, the raising-then-lowering consistency, from the abstract inverse property
`g·adj = det·I` (`hadj`) via `gridSumZ` Fubini + the Kronecker collapse.  The **Riemann tensor** is now constructed (`TensorCalculus.lean` §3, PURE): `riemUp`
`R^l_{ijk} = ∂_jΓ^l_{ik} − ∂_kΓ^l_{ij} + Σ_m(Γ^l_{jm}Γ^m_{ik} − Γ^l_{km}Γ^m_{ij})` from the
connection `Gam` and its derivative `dGamma` (abstract, as the metric entered via `dg`), with
the defining `(j,k)`-antisymmetry `riem_antisym_jk` (`R^l_{ijk} = −R^l_{ikj}`, the curvature
`2`-form / commutator structure) and `riem_flat` (`Γ≡0 ⟹ R≡0`).  **Next rung**: the further
Riemann symmetries (first Bianchi, pair symmetry) the **Ricci tensor** `Ric_{ik} = Σ_l R^l_{ilk}`
(`ricciFromRiem`, `ricci_flat`) and the **first Bianchi identity** `R^l_{ijk}+R^l_{jki}+
R^l_{kij}=0` (`riem_bianchi1`, for a torsion-free `Γ`) are now ∅-axiom too (§4).  So the
algebraic tensor calculus — Christoffel (both kinds) → Riemann → Ricci + Bianchi — stands,
dimension-free.  The **metric-tied Riemann symmetries** are now closed too (`TensorCalculus.lean` §5, PURE):
the lowered curvature 2-jet `2R_{iklj} = ∂_i∂_j g_{kl} + ∂_k∂_l g_{ij} − ∂_i∂_l g_{kj} −
∂_k∂_j g_{il}` (`riemLow`, the Riemann tensor in normal coordinates) has **all four**
symmetries from the 2-jet symmetries (`hd`: `∂∂` commute, `hg`: `g` symmetric): the two
antisymmetries (`riemLow_antisym_ik/_lj`, pure `ring`), the pair/block symmetry
(`riemLow_pair_symm`), and the first Bianchi (`riemLow_bianchi1`, moved-over form to dodge the
zero-polynomial `ring` gap).  So the full algebraic Riemannian curvature tensor calculus —
Christoffel (both kinds) → Riemann → Ricci → Bianchi → all curvature symmetries — stands,
dimension-free, ∅-axiom.  The **scalar curvature** is now closed too (`TensorCalculus.lean` §6, PURE): `det·R =
Σ_{i,j} adj^{ij}·Ric_{ij}` (`scalarFromRicci`, the `g^{-1}` double contraction over ℤ), with
the **Einstein** relation `scalar_einstein`: `Ric = λ·g ⟹ R = λ·n` (constant scalar = Einstein
constant × dimension, since `tr(adj·g) = n·det`).  So the **entire algebraic Riemannian
curvature tensor calculus** — metric 2-jet / Christoffel (both kinds) + raising/lowering →
Riemann (+ all four symmetries) → Ricci → Bianchi → scalar (+ Einstein) — now stands,
dimension-free, ∅-axiom.  The residual wall is precisely the **analysis**: transcendental
metrics (`sin/cos/exp/sqrt` with convergent derivative rules) and the PDE a-priori estimates
(Shi/maximum-principle/compactness) behind Perelman's `𝓦`-monotonicity — the genuine
century-problem core, out of ∅-axiom reach with the current toolset.

  (`ring_intZ` note: its normalizer cannot certify an expression that reduces to the **zero
  polynomial** `= 0`; the Bianchi per-`m` cyclic cancellation was closed with the pure helper
  `hexcancel` (`sub_add_cancel_int` + `sub_self_zero`) instead — `omega` would close it but
  leaks `propext`+`Quot.sound`, so is barred.)

## Verdict

The round-sphere extinction is the honest *floor*.  General-`n` + transcendental-
metric `𝓕/𝓦`-monotonicity (the smooth *flow* with PDE a-priori estimates) remains
the *core* wall.  But the smooth route is **not** wholesale walled, on three fronts:
**2D conformal Ricci curvature/flow is reachable** (rational `K`, no sqrt/exp), the
**general-`n` conformal *scalar* curvature is reachable** (`confRNumN`, the conformal
route past 2D — incl. the `n = 3` Poincaré dimension), and the **general-`n` Ricci lower
bound is reachable synthetically** via the Bakry–Émery `CD(K,N)` condition
(`BakryEmery.lean`) — the dimension-independent meaning of `Ric ≥ K` as a sum-of-squares
fact.  Converging routes to A6's core stand: the **discrete** Forman/Ollivier/Bakry–Émery
ladder (`a6_ricci_core/`) + its **Lichnerowicz spectral bridge** (`DiscreteLichnerowicz`),
the **smooth conformal** ladder (now general-`n` scalar), and the **synthetic CD(K,N)**
condition.  Do not narrate the general smooth-flow core as "closed" — the Ricci *tensor* +
*flow* for `n ≥ 3` and transcendental metrics + PDE a-priori estimates are the residual
wall; do pursue all routes.

## Panel exploration of the residual wall (4 mathematician agents) + the consensus brick

A 4-agent panel (hard-analyst / PDE-analyst / Perelman-𝓦-specialist / 213-native skeptic)
explored the residual wall against the actual repo state.  Convergent findings:

- **Transcendentals are NOT the century-problem wall — they are an un-assembled `Real213`
  library stub.**  The hard analytic rate IS already PURE: `exp`/`sin`/`cos` series with proven
  geometric-decay moduli (`Real213/ExpLog/CutExpModulus`, `CutTrigModulus`, 4+4 PURE) and the
  derivative coefficient identities (`exp_deriv_coeff_fixed : (n+1)·n! = (n+1)!`, etc., 3 PURE).
  The only gap is *packaging* `expPartialSum x` into a `CauchyCutSeq` (template: `eulerCauchySeq`)
  to retire the `Core/Functions.lean` stubs.  Smallest brick: `expCauchySeq (x) : CauchyCutSeq`
  → `expCut x`.  (Per the repo's own "Transcendental-as-exterior" failure mode, this should be
  dropped from the "wall" statement.)
- **The discrete→continuous PDE limit is a SOLVED pattern, not a wall.**  The discrete maximum
  principle is fully proven (`heatIter_range`, `heatStep_mono`); the "limit step" is purely
  representational — promote the sup-norm sequence to a `Real213` `cutLe` via the
  `RealCauchyWitness` order-squeeze idiom (~40 lines).  The TRUE analytic wall is **P4 Li–Yau /
  differential Harnack** (needs genuine `Real213` division for `|∇u|²/u` + a discrete
  Bochner-with-Ricci — both absent; the `Nat`-numerator trick breaks at `∇log`).
- **Perelman's monotonicity integrand is NOW a ∅-axiom SOS** (the standout): since `Ric` exists
  (`ricciFromRiem`) and `Hess f = ∂_i∂_j f` is the same `2`-jet pattern, the rate
  `d/dt 𝓕 = 2∫|Ric_{ij}+∇_i∇_j f|²e^{−f}dV ≥ 0` becomes, with the integral a finite `gridSumZ`
  and weight `1`, the manifest SOS `perelman_rate_nonneg : 0 ≤ Σ_{i,j}(Ric_{ij}+Hess_{ij}f)²`
  (`TensorCalculus.lean` §7) — **built this panel, PURE, no new primitive**.  So the *monovariant
  + non-negative rate* of Perelman's entropy (curvature term included) is ∅-axiom.
- **213-native reframing**: `𝓦`-monotonicity's *content* is discrete entropy descent (the
  Lott–Sturm–Villani / Bakry–Émery `CD(K,N)` synthetic precedent), not the Gaussian dress; a
  reachable rung is a discrete χ²-entropy `Ent(μ)=Σ μ(μ−1)` descending under `lazyHeatStep`
  (same shape as `ricci_energy_monotone`, applied to the measure field).

**Corrected wall (panel consensus).**  Dropped from the wall: "transcendental metrics" (a
`Real213` packaging stub).  Now ∅-axiom: the monotonicity integrand SOS (`perelman_rate_nonneg`).
The GENUINE residual wall was (i) the weighted **integration-by-parts** identity that *connects*
`∇𝓕` to the flow `∂_t g = −2Ric` (so "Ricci flow IS the gradient flow of 𝓕" stays a premise),
(ii) the `(4πτ)^{−n/2}e^{−f}` Gaussian normalization of the true `𝓦`, (iii) **Li–Yau Harnack**
(nonlinear), and (iv) **κ-solution / surgery classification + no-local-collapsing compactness** —
the last is the genuine, un-reframable century-problem core.  Reachable next bricks (all
recorded): `expCauchySeq` (still open — see scoping below), the `Real213`-cut maximum
principle (✅ closed — `HeatEq/MaxPrincipleReal.heat_max_principle_real`: data in `[A,B]`
⟹ the averaged field `heatIter/2ᵗ`, as a `Real213` cut, stays in `[A,B]` in the cut order
for all `t`; generic bridge `constCut_le_constCut`), and the χ²-entropy descent
(✅ closed — `ricci_chi_entropy_monotone`, see below).

**`expCauchySeq` — ✅ the unit-fraction family closed** (`ExpLog/ExpUnitModulus.lean`,
14 PURE).  The euler generator extends **verbatim** to `exp(1/q)` for every `q ≥ 1`:
convergents `a_n/(qⁿ·n!)` (`a_{n+1} = (n+1)q·a_n + 1`), cross-determinant exactly the
denominator (`expU_cross_det`), and the `Htel` side condition reduces to
`i(i+1)+i ≤ (i+1)²·q` — true for all `q ≥ 1`.  So `expUnitCauchySeq q` is a genuine
`CauchyCutSeq` with total modulus `N(m,k) = k+2`, uniformly in `q` (instances: `e` at
`q = 1`, definitionally `eulerNum/eulerDen`; `√e = exp(1/2)` at `q = 2`).  The
`Core/Functions.lean` `expCut` placeholder is retired (no consumers; doc points to the
genuine objects).  **Honest residual**: `exp(p/q)`, `p ≥ 2` — the cross-det becomes
`p^{i+1}·d_i`, which *exceeds* the `1/(i·d_i)` margin envelope `RateModulus.Htel`
hardcodes (the early Taylor increments are genuinely bigger), so the needed
generalization is a **parametric-margin `RateModulus`** (margin `B_i/(i·d_i)` with a
tail-bound certificate `B_i`, fed by `CutExpModulus.expTail_geom_decay`) or the
multiplicative route `exp(p/q) = exp(1/q)ᵖ` through cut multiplication — a separate
marathon, recorded.  **Upgraded after merging `claude/zeta-3-holonomic-fold-gbjygu`**
(the modulus-degree-ladder branch): the rate-free-ness is now **proven** —
`exp_pq_presentation_overtakes` / `exp_pq_no_htel` (`ExpUnitModulus` §6, the
`zeta3_presentation_overtakes` mirror via `RateStratification.htel_iff_dominates`):
the factorial presentation's cross-det `p^{i+1}·dᵢ` overtakes at layer `q+9`, so no
`Htel` exists for it.  The constructive route is therefore the **dyadic-bracket
schedule** (`CubeRootTwoCut` pattern: presentation change, modulus from the
`CutExpModulus` tail bound) or the graded generator (`modulus_degree_ladder.md`
rung 1) — exactly the merged branch's frame.

**Bochner-with-Ricci coupling** — ✅ first rung closed (`DiscreteLichnerowicz` §4):
on `K_m` the Bakry–Émery gradient-semigroup commutation holds as an **identity** —
`Γ(P_c u) = (c−m)²·Γ(u)` pointwise (`km_gradient_contraction`; `P_c = c·id + L`,
`τ = 1/c` numerator form) — and since the gap `m` dominates the curvature `(m+2)/2`
(Lichnerowicz, `m ≥ 2`), the cleared `CD((m+2)/2,∞)`-rate estimate
`4·Γ(P_c u) ≤ (2c−(m+2))²·Γ(u)` follows (`km_be_gradient_estimate`): the curvature
constant enters the gradient decay exactly as in the smooth Bakry–Émery/Li–Yau theory.
**Open next rung**: the same commutation *inequality* on a non-vertex-transitive graph
(star / `K_{a,b}`, where it is no longer exact) — the genuine `CD(K,∞) ⟹ gradient
estimate` implication beyond the spectral case.

## The four wall items: discrete cores closed (this session)

Each of (i)–(iv) now has its **discrete core** ∅-axiom (the smooth/manifold statements stay
open; see honest boundaries below):

- **(i) Weighted IBP** — ✅ discrete core DONE (`GeometrizationConjecture/WeightedGreen.lean`,
  11 PURE).  On an arbitrary symmetric-weight finite graph (the weight playing `e^{−f}dV`):
  `weighted_green` (`⟨f,g⟩_w = −2·Σ_x g·L_w f` — with `g := μ` exactly Perelman's
  `∫Δf·e^{−f} = ∫|∇f|²e^{−f}`), and `dirichlet_gradient_identity`
  (`𝓕_w(f+h) = 𝓕_w(f) − 4Σ h·L_w f + 𝓕_w(h)`): the linear response of the weighted Dirichlet
  energy along *any* direction is the pairing against the weighted Laplacian — **the flow
  generated by `L_w` IS the gradient flow of `𝓕_w`**, with SOS rate (`flow_rate_sos`) and
  mass conservation (`wlap_mass_conservation`).  Engine: `gridSumZ_antisym_zero`
  (Fubini-reflection of an antisymmetric kernel + doubling cancellation, division-free).
- **(ii) The `𝓦` Gaussian** — ✅ discrete core DONE (`DiscreteGaussian.lean`, 8 PURE +
  `Combinatorics/Binomial` additions).  The binomial kernel `u(t,x) = C(t,x)` is the discrete
  heat fundamental solution (δ-init, Pascal = heat step), and `gaussian_normalization` —
  `Σ_x u(t,x) = 2^t` for **all** `t` — is exactly the `(4πτ)^{−n/2}` content (the kernel
  stays a probability measure along the flow); `gaussian_mean` pins the first moment
  (`⟨x⟩ = t/2`).  The de Moivre–Laplace continuum limit is *not* claimed.
- **(iii) Li–Yau Harnack** — ✅ discrete core DONE (`binom_log_concave` +
  `gaussian_li_yau`/`harnack_forward`).  The kernel's spatial **log-concavity**
  `u(t,x)·u(t,x+2) ≤ u(t,x+1)²` is the division-free cleared form of `Δlog u ≤ 0` (the
  Li–Yau gradient estimate) — the `Real213`-division wall is sidestepped by
  cross-multiplication; proof = the subtraction-free absorption identity
  `(k+1)C(n,k+1) + kC(n,k) = nC(n,k)` (pure Pascal double induction) + positive cancellation.
  Harnack propagation `u(t,x) ≤ u(t+1,x), u(t+1,x+1)` follows.  **Still open**: the manifold
  Li–Yau `Δlog u ≥ −n/2t` under `Ric ≥ 0` (needs the discrete Bochner-with-Ricci coupling)
  and Hamilton's matrix Harnack.
- **(iv) Surgery classification** — ✅ discrete core DONE (`DiscreteSurgery.lean`, 15 PURE).
  `gauss_bonnet_general` (any finite graph: handshake ⟹ `Σ_v(2−deg v) = 2χ`); the surgery
  step (cut a neck edge, connectivity kept) raises `χ` by exactly `1` and total curvature by
  exactly `+2`; `surgery_dichotomy` — every connected state is **round** (`b₁ = 0`, curvature
  `+2`, terminal) or **neck-bearing** (`b₁ ≥ 1`, curvature `≤ 0`, surgery applies); A6
  termination (`flow_reaches`) with the **exact count**: precisely `b₁` surgeries to the round
  state (`surgery_count`); `K_{3,2}`: ledger `−2 → 0 → +2` in 2 surgeries.  **Still open**:
  the smooth κ-solution classification (shrinking solitons / Bryant), canonical-neighbourhood
  geometry, and **no-local-collapsing compactness** — the latter is now the sharpest single
  remaining wall item.

**No-local-collapsing, discrete core** — ✅ DONE (follow-up session;
`DiscreteGaussian.lean` §4 + `Binomial.lean` unimodality).  `binom_le_central`
(`C(2n,k) ≤ C(2n,n)` ∀k — rising/falling halves from the same absorption identity as the
Li–Yau estimate) + `gaussian_normalization` give `no_local_collapsing`:
`2^{2n} ≤ (2n+1)·u(2n,n)` — the kernel's central value dominates the **average density**,
so mass cannot escape into a thin neck (the cigar exclusion, in kernel form); with
`kernel_le_mass` (`u(t,x) ≤ 2^t`) the central density is **pinched**
(`kernel_density_pinch`) — the `𝓦` ⟹ κ-noncollapsing implication, discrete.  The
**χ²-entropy descent** is also closed (`RicciFlowDiscrete.ricci_chi_entropy_monotone`:
`V(K') ≤ 16·V(K)`, `V(K) = n·ΣK² − (ΣK)²`, from `lazy_l2_norm_bound` + mass conservation —
the curvature field's χ²-divergence from the constant/round state is non-increasing).
**What remains of (iv)** — the genuinely smooth part: compactness extraction (blow-up
limits), canonical neighbourhoods, soliton classification, on a manifold.

Lean-tooling lesson (recurring): `rw` with a *defeq-rfl* lemma (`Nat.add_zero`,
`Nat.mul_zero`) can silently no-op at a hypothesis — close such goals with
`exact (Nat.add_zero _).symm`-style terms or goal-side rewrites instead.  Core
`Nat.add_right_cancel` / `Nat.sub_sub` are `propext`-dirty: use
`NatRing213.nat_add_right_cancel` and a `congrArg Nat.pred` induction (`sub_one_sub`).
