# Frontier marathon — a-priori PDE estimates (∅-axiom, continuous-via-limit)

**Status**: OPEN marathon, standalone.  **Tier**: 1.  The analytic engine behind
Perelman's monotonicity — maximum principle, gradient (Li–Yau) estimates,
Shi-type derivative bounds, compactness.

## The goal is the CONTINUOUS estimate (not the discrete one)

The actual conquest is **continuous** Ricci flow PDE; a discrete graph estimate
alone proves only a *different* (discrete) theorem.  But in 213 "continuous" is
**built constructively from discrete data**: `Real213` = Cauchy sequences of cuts
+ modulus, and all of the repo's continuous analysis (`Differentiation`,
`Integration`) *is* the `Real213` limit of discrete approximants with a
convergence modulus.  So the honest path to a continuous PDE estimate is:

  **prove the discrete estimate UNIFORMLY in the mesh resolution `h`, with a
  convergence modulus, then pass to the `Real213` limit — that limit IS the
  continuous estimate.**

Discrete is the *substrate*, not the goal; the limit step is what makes each rung
a continuous theorem (exactly the `CompletenessLoop` / `RealCauchyWitness`
pattern, where a discrete-with-modulus object became a genuine `Real213` point).

## What stays genuinely walled (separate from discrete-vs-continuous)

Even with continuous-via-limit estimates on `ℝⁿ`, the **smooth-manifold layer**
(charts/atlases, tensor fields on them, covariant derivative) is a further
infrastructure block.  That layer — not the discrete↔continuous passage — is the
remaining wall for full Perelman.  The 2D-conformal route
(`ricci_flow_smooth_core.md`) sidesteps it by staying in one chart.

## Current state (repo-first)

- **Discrete heat / wave**: `Analysis/ODE/HeatEqDiscrete.lean` (`heatStepNum`,
  periodic-grid averaging), `WaveEqDiscrete`.  `heatStep_const` only; **no
  maximum principle / oscillation decay yet**.
- **Limit engine**: `Real213` completion + `Analysis/CauchyComplete`,
  `Cauchy/MonotonicBounded`, `BracketCauchyModulus`, `CompletenessLoop` — the
  machinery that turns "uniform discrete + modulus" into a `Real213` statement.
- **Monovariant**: `Foundations/MonovariantFlow` (A6 `flow_reaches`).

## Ladder (each rung: discrete-uniform-in-`h` + modulus → `Real213` limit; ∅-axiom)

P1. **Maximum principle** — ⚙️ **discrete step DONE** (`Analysis/ODE/HeatEqDiscrete.lean`,
    4 new PURE): the heat step is a neighbour average, so `u ≤ B` ⟹ `heatStepNum ≤ 2B`
    (`heatStep_le_two_max`, no hot spots), `A ≤ u` ⟹ `2A ≤ heatStepNum`
    (`heatStep_two_min_le`, no cold spots), range `[A,B]` preserved (`heatStep_range`,
    sup-norm contraction), oscillation non-increasing (`heatStep_osc_bound`).  **Iterated
    to all time** (`heatIter`): data in `[A,B]` ⟹ the `t`-step field stays in `[2ᵗA, 2ᵗB]`
    (averaged in `[A,B]`) for every `t` (`heatIter_le/_ge/_range`) — the maximum principle
    for the whole evolution, `‖u(t)‖∞ ≤ ‖u(0)‖∞`.  All uniform
    in the grid length `n` (the mesh).  **Remaining**: the `Real213` limit step — pass the
    uniform-in-`h` discrete bound to the continuous maximum principle (the `CompletenessLoop`
    pattern: uniform-discrete-with-modulus → `Real213` statement).
P2. **Oscillation decay** — `osc u = max u − min u` is a monovariant; uniform
    rate → continuous smoothing (the "no local collapsing" seed).
    ⚠️ **Obstruction found (honest)**: *strict* oscillation decay is **false** for the
    current non-lazy step `heatStepNum = u_{x−1}+u_{x+1}` (no self-weight).  On an
    even-length periodic grid the **checkerboard** mode `u = 0,1,0,1,…` maps under one
    step to `2,0,2,0,… = 2·(checkerboard)` — the doubled field is the *same* mode, so the
    averaged oscillation is **preserved**, not decayed.  This is the eigenvalue `cos π = −1`
    of the stencil `(½,0,½)` (`|λ| = 1`, no spectral gap).  **Fix**: use the *lazy* step
    `(¼,½,¼)`, i.e. `lazyHeatStepNum = u_{x−1} + 2u_x + u_{x+1}` (numerator of `4·u_new`),
    whose eigenvalues `(1+cos θ)/2 ∈ [0,1]` give a genuine gap (`λ < 1` off the constant
    mode).  The P1 maximum principle already proven holds for *both* stencils (convex
    combinations); only the strict *decay* needs the lazy weight.
    ⚙️ **lazy step implemented** (`HeatEqDiscrete.lean`, 6 PURE): `lazyHeatStepNum =
    u_{x−1}+2u_x+u_{x+1}`, its maximum principle (`lazyHeatStep_le_four_max`/`_four_min_le`),
    and the concrete spectral-gap witness `lazy_checker_collapses` (the length-4
    checkerboard `→` constant in one lazy step, osc `1→0`) vs `nonlazy_checker_hot`/`_cold`
    (the non-lazy step preserves it).  **Remaining**: the general (any `n`, any field)
    oscillation contraction rate + the `Real213` limit.
P3. **Energy / Dirichlet decay** — `E(u) = Σ(u_{i+1}−u_i)²` decreases (discrete
    Bochner / gradient estimate); the limit = continuous energy decay, rate a
    `‖∇u‖²` (ties to gradient-flow descent identity ①).
P4. **Li–Yau / differential-Harnack** — gradient bound `|∇u|²/u` along the flow
    (the real depth; discrete-Harnack → continuous limit).
P5. **Shi-type estimate** — curvature-derivative bound along the *Ricci* flow;
    feeds `a6_ricci_core/` rung 3 (the discrete Ricci side) and, via limit, the
    continuous side.

## Honest boundary

P1–P3 (discrete + limit) are genuinely reachable ∅-axiom.  P4–P5 are the real
analytic depth and may stall — record where.  The discrete graph estimates
(`a6_ricci_core/`) are a *parallel* theory (Forman/Ollivier), not the conquest;
*this* ladder, with the limit step, targets the **continuous** estimate the
conquest needs.  Start at **P1** (discrete maximum principle on `HeatEqDiscrete`,
then its uniform-in-`h` + `Real213` limit).
