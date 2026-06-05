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

P1. **Maximum principle** — discrete: heat step does not raise max / lower min on
    the grid; uniform in mesh; the limit = the continuous maximum principle.
P2. **Oscillation decay** — `osc u = max u − min u` is a monovariant; uniform
    rate → continuous smoothing (the "no local collapsing" seed).
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
