# Frontier marathon — a-priori PDE estimates (∅-axiom, discrete)

**Status**: OPEN marathon, standalone.  **Tier**: 1.  The second genuinely-hard
block split off from the A6 Ricci core (`ricci_flow_smooth_core.md`): the analytic
engine behind Perelman's monotonicity — maximum principle, gradient (Li–Yau)
estimates, Shi-type derivative bounds, compactness.  The smooth-manifold versions
need Riemannian geometry + real PDE theory (the genuine wall).  The **213-native
route is the *discrete* a-priori estimates** on finite grids / graphs — which are
exactly what discrete Ricci flow convergence (the discrete A6 core,
`a6_ricci_core/`) actually consumes.  A future session picks a rung, proves it
∅-axiom, advances.

## Why this is the engine, not a detour

Discrete Ricci-flow convergence (`a6_ricci_core/` rung 3: drive the flow to a
constant-curvature fixed point) is *proved* with discrete a-priori estimates:
the curvature monovariant descends because of a discrete maximum principle on the
flow.  So this marathon and the discrete-Ricci marathon are coupled — this one
supplies the analytic lemmas, that one consumes them.

## Current state (repo-first)

- **Discrete heat / wave**: `Analysis/ODE/HeatEqDiscrete.lean` (`heatStepNum`,
  the periodic-grid averaging step), `WaveEqDiscrete`.  `heatStep_const`: a
  constant field is fixed.  **No maximum principle / oscillation-decay yet.**
- **Monovariant / convergence engine**: `Foundations/MonovariantFlow` (A6
  `flow_reaches`), `Analysis/Cauchy/MonotonicBounded`, `CompletenessLoop`.
- **Discrete curvature**: `GeometrizationConjecture/DiscreteRicci` (Forman).

## Ladder (each rung ∅-axiom; `#print axioms` empty)

P1. **Discrete maximum principle** — on a finite periodic grid, the heat step
    (averaging) does not increase the max nor decrease the min:
    `max (heatStep u) ≤ max u` and `min u ≤ min (heatStep u)`.  Foundational; uses
    only `Nat`/`Real213` order on the finite grid (`lInfNorm`-style max).
P2. **Oscillation decay** — `osc u = max u − min u` is a monovariant under the
    heat step (`osc (heatStep u) ≤ osc u`), strict unless `u` is constant; hence
    (via A6 `flow_reaches` / `MonotonicBounded`) the flow converges to the
    constant (the discrete smoothing / "no local collapsing" seed).
P3. **Discrete energy / Dirichlet decay** — `E(u) = Σ (u_{i+1}−u_i)²` decreases
    along the heat step (discrete Bochner / gradient estimate seed); rate =
    a discrete `‖∇u‖²` (ties to the gradient-flow descent identity ①).
P4. **Discrete Li–Yau / gradient bound** — a bound on `|∇u|²/u` along the flow
    (harder; the discrete differential-Harnack seed).
P5. **Discrete Shi-type estimate** — bound on the discrete Hessian/curvature
    derivative along the *Ricci* flow (feeds `a6_ricci_core/` rung 3 directly).

## Honest boundary

P1–P3 are genuinely reachable ∅-axiom (finite-grid order + algebra).  P4–P5 are
the real depth and may stall — record where.  The *smooth* a-priori estimates
(Shi/maximum-principle on manifolds, compactness) stay the wall; this ladder is
the discrete substitute that the discrete A6 core actually needs.  Start at
**P1** (discrete maximum principle on `HeatEqDiscrete`).
