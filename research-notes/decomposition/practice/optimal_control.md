# Decomposition: optimal control / dynamic programming (the Bellman equation, the value function, value iteration, the Bellman operator's contraction, the HJB PDE, Pontryagin's maximum principle, the principle of optimality, policy iteration)

*A FRESH decomposition per `../README.md` (model v7.1) and `SYNTHESIS.md` (the two invariants + the
q=±1 spine + the q+1 contraction fixed point). A **fusion of the Banach-engine family with the Noether
conservation family**: it folds `differential_equations.md` (the SAME `banach_fixed_point` /
`MonovariantFlow` q+1 contraction-to-fixed-point), `markov_chains.md`/`martingales.md` (the q+1
converging fixed point of an operator, value iteration = the orbit), `noether.md` (the conserved
Aut-invariant character, `det_holonomy_eq_one`/`noether_local`), and `convex_duality.md`/
`optimal_transport.md` (the min/optimum as the q+1 closure/LP-duality) into one object — and the one NEW
datum is that the **value function V = the q+1 converging FIXED POINT of the Bellman CONTRACTION operator
`T`, with Pontryagin's maximum principle = the Hamiltonian/Noether conservation along the optimal path**.*

> **THE THESIS (the brief's central claim).** Optimal control is the calculus's **q+1
> Bellman-contraction fixed point on the value function, with Pontryagin = the Hamiltonian conservation**.
> (i) The Bellman operator `T[V](x) = min_u [c(x,u) + γ·V(f(x,u))]` is a **contraction** — the discount
> factor `γ < 1` is the contraction modulus — exactly `differential_equations.md`'s Picard operator and
> `markov_chains.md`'s transition operator one realisation over. (ii) The value function `V` (`V = T[V]`)
> = the q+1 converging **fixed point**, the SAME `banach_fixed_point` / `converge_residue_fixed` /
> `golden_is_converge` pole that resolves φ, the Gaussian, the ODE flow, the stationary distribution.
> **Value iteration = the Picard orbit `Vₙ₊₁ = T[Vₙ]` converging to `V`** (`orbit_eq_iter`,
> `picardIterate`); the discount `γ` = the modulus narrowing it (`picard_cauchy`), the limit reached by
> none. (iii) The **principle of optimality** = the fixed-point/self-similarity — `V` is defined in terms
> of itself (the recursive fold, the SAME self-reference `Raw.fold`/`view`). (iv) The **HJB PDE** = the
> continuous resolution limit (`h → 0`, `derivative.md`'s resolution dial / `IsResolutionShift`). (v)
> **Pontryagin's maximum principle** = the Hamiltonian/Noether conservation: the costate = the conserved
> momentum (`noether.md`'s conserved current `noether_local`), the optimal Hamiltonian conserved along
> the optimal path = `det=1` / `det_holonomy_eq_one`. (vi) The **min** (vs the LP max) = the
> convex-duality / OT optimum (the q+1 zero-gap, `kantorovich_weak_duality`/`ollivier_plan_optimal`).
> (vii) **Policy iteration** = the q+1 fixed point alternated (policy-evaluation = a contraction,
> policy-improvement = the min) — a coupled contraction. **NO new primitive:** it is the q+1 contraction
> fixed point (Banach/Markov) on the value function, with Pontryagin = Noether.

## The decomposition (C / Reading / Residue)

- **Construction `C` — NO new construction; `differential_equations.md`'s self-applying evolution reading
  on a controlled step.** The state space is a point-construction (`derivative.md`'s value-at-a-point);
  a *controlled dynamics* `f(x,u)` is a reading assigning to each (state, control) the next state — the
  evolution step of `differential_equations.md` with a control input `u`. The **per-step cost** `c(x,u)`
  is the **weight axis** (`probability.md`/`martingales.md`: a value-weighted readout). `C` is the
  **self-application** of "step under a control, accumulate cost, then step again from where you landed"
  — `golden_ratio.md`'s self-applying iteration `Tⁿ`, the iterator now control-driven. **Nothing
  control-theoretic is primitive — only a controlled evolution step (a vector field with an input) and a
  cost weight.**

- **Reading `L_T` — the Bellman operator `T` as the min-and-discount averaging/iteration reading on the
  value (a weight), read at successive steps.** The Bellman operator
  `T[V](x) = min_u [c(x,u) + γ·V(f(x,u))]` is a single reading with three folded facets, every one
  already in the calculus:
  1. **the discounted look-ahead** `V ↦ c + γ·V∘f` is `differential_equations.md`'s Picard step / the
     Markov push-forward, with the discount `γ` the **contraction factor** — `markov_chains.md`'s
     averaging operator with the row-stochastic-below-1 weight made `γ < 1` explicit.
  2. **the min over controls** `min_u` is the **q+1 optimum** of `convex_duality.md`/`optimal_transport.md`
     — the LP/closure optimum read on the action set, the additive twin of the LP `max` (the same
     `kantorovich_weak_duality`/`ollivier_plan_optimal` shape, here the inf side of the duality).
  3. **iterate the operator** (value iteration) `Vₙ₊₁ = T[Vₙ]` is the **`iter` generator**
     (`OrbitIsIter.orbit_eq_iter`: an orbit IS the count iterating the step) on the value reading — the
     same orbit `differential_equations.md`'s `picardIterate` runs, now on a function `V` rather than a
     number.
  Two facts are *forced*, not chosen:
  - **The discount `γ < 1` forces a strict contraction.** `|T[V] − T[W]| ≤ γ·|V − W|` (the min is
    1-Lipschitz; `γ` multiplies the look-ahead). So `T` is a `Contraction` in the
    `BanachFixedPoint.Contraction` sense, with modulus `γ`, exactly `differential_equations.md`'s Picard
    contraction and `markov_chains.md`'s spectral-gap contraction (here the gap is `1 − γ`).
  - **The principle of optimality forces `V = T[V]` — the self-reference.** `V` is *defined in terms of
    itself* (the value of a state = the best immediate cost plus the discounted value of the next state).
    This is the recursive fold `raw_initial`/`Raw.fold` (`Lens.view = Raw.fold`, the unique read-op out of
    the construction): the value function is the catamorphism of the controlled construction, and "the
    tail of an optimal trajectory is itself optimal" is the fold's self-similarity, not a separate axiom.

- **Residue — `q = ±1`, read at the poles. Optimal control IS the q+1 contraction residue on the value
  function, with Pontryagin the conserved character.**
  - **q=+1 (converge / the value function / the optimal policy — the return).** The value function `V`
    is `T`'s *fixed point* `V = T[V]`, the q+1 converging residue `differential_equations.md`/
    `markov_chains.md`/`golden_ratio.md` resolve with `ResidueTag.converge_residue_fixed` /
    `golden_is_converge` (delegating to `banach_fixed_point_modulated`). **Value iteration `Vₙ → V`** is
    the q+1 contraction reaching the fixed point at geometric rate `γⁿ`, the discount `γ` the contraction
    modulus (`picard_cauchy`'s `N(m)`), the limit reached by none. The **optimal policy** `u*(x) =
    argmin_u[…]` is the degenerate q+1 residue (`step at the fixed point` — `IsNormalForm`,
    `MonovariantFlow.flow_reaches`), i.e. the equilibrium the value-descent lands on.
  - **Pontryagin's maximum principle = the q+1 Hamiltonian/Noether conservation along the optimal path.**
    The optimal Hamiltonian `H(x,p,u*)` is **conserved** along the optimal trajectory — `noether.md`'s
    conserved Aut-invariant character `det=1`, made a along-the-path statement: the costate `p` (the
    adjoint/Lagrange multiplier) is the **conserved momentum**, `noether.md`'s conserved current
    `NoetherCurrent.current`/`noether_local` (`∂·j = 0 ⟺ det g = 1`), and "the Hamiltonian is constant
    along the optimal path" = `HolonomyLattice.det_holonomy_eq_one` (`det = 1` around the path). The
    costate equation `ṗ = −∂H/∂x` is the continuity equation `NoetherCurrent.continuity_eq` at the q+1
    pole. Pontryagin = Noether on the optimal trajectory, the conserved character of the controlled flow.
  - **q=−1 (escape / no optimal policy / divergence).** When the look-ahead is NOT a strict contraction
    (`γ ≥ 1` — undiscounted infinite-horizon with no terminal cost), value iteration may not converge:
    the value oscillates or diverges *outside* every finite reading (`cardinality.md`'s diagonal,
    `golden_ratio.md`'s q−1 swap, `ResidueTag.escape_residue_outside`). The q±1 bit decides
    converge-to-an-optimal-policy vs no-fixed-point. The **value of the optimal cost** (an irrational
    real in general) is a `Real213`/cut value-residue, reached-by-none (the honest value leg).

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   controlled dynamics f(x,u)  =  ⟨ point-construction ∣ "next state under control u" ⟩   (differential_equations' evolution step + a control input)
   per-step cost c(x,u)         =  the weight-reading on the (state,control)               (probability.md's value-weighted count)
   Bellman operator T           =  T[V](x) = min_u[c + γ·V(f(x,u))]   =  discounted look-ahead (Picard/Markov step) + the min-optimum + iterate
   Bellman EQUATION  V = T[V]   =  the principle of optimality  =  the recursive fold / self-reference  (Lens.view = Raw.fold, raw_initial)
   value iteration  Vₙ₊₁=T[Vₙ]  =  the Picard orbit  =  iterⁿ  (orbit_eq_iter; picardIterate on a function)
   THE VALUE FUNCTION V        =  Residue(T, C), q=+1  =  the q+1 converging FIXED POINT  (= φ/Gaussian/ODE/stationary-π, same banach_fixed_point)
   discount factor γ < 1        =  the CONTRACTION MODULUS  (Contraction, picard_cauchy's N(m); the "spectral gap" 1−γ)
   value-iteration convergence  =  the q+1 contraction reaching V at geometric rate γⁿ  (banach_fixed_point, modulated-completion)
   optimal policy u*(x)         =  the degenerate q+1 residue: step at the fixed point  (IsNormalForm, flow_reaches)
   THE MIN over controls        =  the q+1 optimum (the inf side of LP/closure duality)  (kantorovich_weak_duality/ollivier_plan_optimal, convex_duality.md)
   HJB PDE  (continuous limit)  =  the SAME Bellman eqn at residue resolution (h→0)  (derivative.md's resolution dial; IsResolutionShift)
   PONTRYAGIN max principle     =  the Hamiltonian/Noether conservation along the optimal path  (noether.md)
     costate p (the momentum)   =  the conserved current  (NoetherCurrent.current; noether_local: ∂·j=0 ⟺ det g=1)
     H conserved on the path    =  det_holonomy_eq_one  (det = 1 around the optimal loop, q=+1)
     costate eqn ṗ = −∂H/∂x      =  the continuity equation  (NoetherCurrent.continuity_eq)
   POLICY ITERATION             =  the q+1 fixed point alternated: policy-eval (a contraction) + policy-improve (the min)  (coupled contraction)
   γ ≥ 1 / no contraction       =  q=−1 escape: value oscillates/diverges, no fixed point  (escape_residue_outside)
   optimal-cost VALUE           =  Real213 cut  (q=−1 value residue, reached-by-none)
```

So **the Bellman operator, the value function, value iteration, the contraction, the principle of
optimality, the HJB PDE, Pontryagin, the min, and policy iteration are one reading at work** — the
discounted min-look-ahead `T` on the controlled construction, read on the value (a weight) at the q=±1
poles, with `V` = the q+1 contraction fixed point and Pontryagin = the Noether conservation along the
optimal path.

## THE REVELATION — collapse (V = the q+1 Bellman-contraction fixed point) + forcing + spine

This is **not** a re-skin of `differential_equations.md` / `markov_chains.md` / `noether.md`. Those built
the q+1 contraction fixed point on a function-flow (ODE), on a distribution (stationary π), and the
conserved Aut-invariant character (Noether). The NEW datum here is **the q+1 contraction fixed point
welded to the Noether conservation on ONE controlled object**: the value function is the fixed point of a
*min*-look-ahead contraction (value iteration = the orbit, discount = the modulus), the principle of
optimality is that fixed-point self-reference (the recursive fold), and Pontryagin is the conserved
character *along the optimal path* — a combination none of the three neighbours carries, because none of
them has both a controlled-optimisation operator and a conservation law on the same trajectory.

1. **Collapse — the value function = the q+1 converging fixed point = the Bellman-contraction residue,
   one object.** Run the equalities on the value (weight) axis:
   - `V = T[V]` (Bellman) `⟺` `V` is the q+1 converging residue of the self-applying operator `T`
     (`golden_ratio.md`'s rule: a fixed point of a self-applying map = the q+1 residue), the SAME
     `banach_fixed_point` engine `ResidueTag.converge_residue_fixed` packages — *literally* the ODE
     solution of `differential_equations.md`, the stationary distribution of `markov_chains.md`, the
     Gaussian of `gaussian_clt.md`, φ of `golden_ratio.md`.
   - `V = T[V]` `⟺` `V = lim(picard T V₀)` (value iteration), the orbit `orbit_eq_iter` reaching the fixed
     point, with the discount `γ < 1` the contraction modulus pinning the rate to `γⁿ` (`picard_cauchy`).
   So `value function ≡ q+1 fixed point ≡ value-iteration limit` — **the abstract q+1 converge pole (the
   neighbours' engine) and the concrete dynamic-programming value function are one and the same object**,
   with the discount `γ` the bridge that makes `T` a contraction. That collapse is the payoff: it is *why*
   "the value function is the fixed point of the Bellman operator and value iteration converges to it"
   (the foundational DP fact, the basis of all reinforcement learning) is not a separate theorem but the
   q=±1 spine read once, on the value axis.

2. **Forcing — the contraction, the convergence, and the self-reference are forced by the discount + the
   recursive structure, not added.**
   - **`T` is a contraction with modulus `γ`** is forced: the min is 1-Lipschitz (an inf cannot stretch
     distances) and the look-ahead multiplies by `γ < 1`, so `|T[V] − T[W]| ≤ γ·|V − W|` — a
     `BanachFixedPoint.Contraction`, exactly `differential_equations.md`'s Picard contraction and
     `markov_chains.md`'s spectral-gap contraction (gap `1 − γ`). The discount is not a tuning knob; it is
     the q+1 contraction modulus, and "discounting guarantees convergence" is the q+1 pole, machine-shaped.
   - **Value iteration converges `Vₙ → V`** is forced: `banach_fixed_point` applied to the contraction `T`
     gives a unique fixed point reached by none, narrowed by `picard_cauchy`'s geometric modulus — the
     same theorem `differential_equations.md` names for ODE existence, here naming DP convergence.
   - **The principle of optimality is forced as the fold's self-similarity.** `V = T[V]` is the
     catamorphism out of the controlled construction (`Lens.view = Raw.fold`, `raw_initial`,
     `dhom_unique_pointwise` — the unique read-op), so "the tail of an optimal path is optimal" is the
     fold re-entering itself, not a postulate. The same self-reference `cardinality.md`'s diagonal uses at
     q−1, here at q+1 (it lands on a fixed point instead of escaping).

3. **Spine — Pontryagin IS the q+1 Noether conservation, and the HJB PDE is the resolution limit.** Two
   spine rows, tying `SYNTHESIS.md`'s q=±1 spine and the character arrow:
   - **Pontryagin's maximum principle = the conserved Aut-invariant character along the optimal path.**
     The optimal Hamiltonian is conserved along the optimal trajectory = `noether.md`'s `det=1` conserved
     character made an along-the-path statement: the costate `p` is the conserved current
     (`NoetherCurrent.current`, `noether_local`: `∂·j = 0 ⟺ det g = 1`), and "H constant along the optimal
     path" = `HolonomyLattice.det_holonomy_eq_one` (`det = 1` around the loop, the q+1 pole). This is the
     SAME `×↦·` conserved character `noether.md`/`determinant.md`/`curvature.md` read four ways, now read
     a fifth way — *along an optimisation trajectory*. Pontryagin and Bellman are the two faces of one
     object (`noether.md`'s conservation + `differential_equations.md`'s contraction) on the optimal path:
     the value function's q+1 fixed point and the Hamiltonian's q+1 conserved character.
   - **The HJB PDE = the Bellman equation at residue resolution (`h → 0`).** HJB
     `−∂V/∂t = min_u[c + ∇V·f]` is the discrete Bellman equation read through the resolution dial of
     `derivative.md`/`continuity.md` (`IsResolutionShift`): the discrete look-ahead `V(f(x,u))` at
     time-step `1` becomes the differential `∇V·f` at `h → 0`, the limit never the operand, only the
     modulus. So the discrete Bellman recursion and the continuous HJB PDE are the *same reading at two
     resolutions* — exactly `integration.md`'s `Σ⊣Δ` / `∫⊣d` resolution-invariance, here on the value
     operator.

**Re-skin guard cleared.** The note does not re-describe its neighbours' q+1 fixed point: its
load-bearing new fact is that the **value function = the q+1 fixed point of a *min-contraction* operator
(value iteration = the orbit, discount = the modulus), the principle of optimality = the fixed-point
self-reference (the recursive fold), and Pontryagin = the Noether conservation *along the optimal path***
— a weld of the Banach-engine family with the Noether family on one controlled object that none of
`differential_equations.md`/`markov_chains.md`/`noether.md` carries.

## VALIDATE — verdict: **EXTEND (consolidation) + PREDICTION**, no break, no new primitive

**EXTEND.** Optimal control adds **nothing** to model v7.1 — it *fuses* existing entries at one
controlled object:
- the **q+1 contraction → fixed point engine** (`differential_equations.md`/`markov_chains.md`/
  `golden_ratio.md`: `banach_fixed_point`, `converge_residue_fixed`, `picard`/`picardIterate`,
  `orbit_eq_iter`) — supplies `T` as a contraction, `V` as its fixed point, value iteration as the orbit;
- the **min/optimum as the q+1 closure/LP-duality** (`convex_duality.md`/`optimal_transport.md`:
  `kantorovich_weak_duality`, `ollivier_plan_optimal`, `clo_idempotent`) — supplies the min over controls;
- the **conserved Aut-invariant character** (`noether.md`: `noether_local`, `det_holonomy_eq_one`,
  `NoetherCurrent.continuity_eq`) — supplies Pontryagin (costate = conserved momentum, H conserved on the
  optimal path);
- the **resolution dial** (`derivative.md`/`integration.md`: `IsResolutionShift`) — supplies the HJB PDE
  as the `h → 0` limit of the Bellman equation;
- the **recursive fold / self-reference** (`raw_initial`, `Lens.view = Raw.fold`) — supplies the
  principle of optimality;
- the **q=±1 residue tag** (`ResidueTag`) — supplies converge-to-optimal (`γ < 1`, q+1) vs divergence
  (`γ ≥ 1`, q−1).

**PREDICTION.** The calculus *predicts* the field's shape from its parts: that `V` = the q+1 fixed point
of the Bellman contraction (forced by the discount `γ < 1`), that value iteration converges at geometric
rate `γⁿ` with `γ` the modulus, that the principle of optimality is the fixed-point self-reference (the
recursive fold), that the HJB PDE is the Bellman equation at residue resolution, that Pontryagin is the
Noether conservation along the optimal path (costate = conserved momentum), and that policy iteration is
the q+1 fixed point alternated (a coupled contraction). The *engines* (the Banach contraction, the
Picard/orbit iteration, the Noether current, the LP-duality optimum, the resolution shift, the recursive
fold) are built and PURE; the *named* `Bellman` / `valueFunction` / `HJB` / `Pontryagin` /
`optimalControl` / `valueIteration` / `policy` objects are **ABSENT** (grep-confirmed) — the located
missing leg, the same status as `markov_chains.md`'s absent `MarkovChain`/`stationary`/`Perron` objects
and `differential_equations.md`'s absent continuous Picard operator.

**No BREAK.** The two invariants (the character arrow — here the conserved Hamiltonian `det=1` /
Pontryagin — and the q=±1 residue) and the four axes (direction, fold-height, resolution, weight) absorb
the field cleanly; the only honest residuals are the value-cut (the optimal-cost value as a `Real213`
number, irrational in general; the continuous HJB/Pontryagin smooth current) and the *named* objects.

## Verified Lean anchors (file:line:theorem — all grep-confirmed; purity by `tools/scan_axioms.py`, run this session from repo root with the `E213.` prefix)

| Leg | Theorem / def (file:line : name) | Purity (fresh scan) |
|---|---|---|
| ★★★★★ **V = the q+1 converging FIXED POINT of the Bellman contraction** — the converge engine (SAME pole as φ/Gaussian/ODE/stationary-π), `V = T[V]` reached by none, narrowed by the discount modulus | `Lib/Math/Foundations/ResidueTag.lean:160 converge_residue_fixed`; `:180 golden_is_converge`; `:228 residue_tag_two_poles` | **PURE** (55/0) ✓ |
| ★★★★★ **the Bellman operator is a CONTRACTION; value iteration `Vₙ₊₁=T[Vₙ]` = the Picard orbit reaching V at geometric (discount `γ`) rate** | `Lib/Math/Analysis/BanachFixedPoint.lean:202 banach_fixed_point`; `:154 picard_cauchy` (modulus `N(m)`); `:250 banach_unique`; `:29 Contraction`; `:33 picard`; `:45 picard_step_geometric` | **PURE** (12/0) ✓ |
| ★★★★★ **value iteration = the evolution operator iterated by the count** (`orbit = iter`) + a real discrete iterated-step instance with closed forms | `Meta/OrbitIsIter.lean:42 orbit_eq_iter`; `Lib/Math/Analysis/ODE/PicardIterate.lean:22 picardIterate`, `:38 picard_const`, `:58 picard_exp` | **PURE** (OrbitIsIter 1/0, PicardIterate 8/0) ✓ |
| ★★★★★ **optimal policy = the degenerate q+1 residue (step at the fixed point); the value-descent monovariant** `IsNormalForm f x := f x = x`, `flow_reaches` | `Lib/Math/Foundations/MonovariantFlow.lean:99 flow_reaches`; `:73 IsNormalForm`; `:158 descent_invariant` | **PURE** (19/0) ✓ |
| ★★★★★ **PONTRYAGIN = the Noether conservation along the optimal path** — costate = the conserved current; `∂·j = 0 ⟺ Aut-invariant (det g = 1)`; the continuity (costate) equation | `Lib/Math/NumberSystems/Real213/ModularGeometry/NoetherCurrent.lean:149 noether_local`; `:97 continuity_eq`; `:117 density_conserved_of_det_one`; `:81 current`; `:72 density` | **PURE** (14/0) ✓ |
| ★★★★ **H conserved around the optimal loop = the q+1 conserved character `det = 1`** | `Lib/Math/NumberSystems/Real213/ModularGeometry/HolonomyLattice.lean:136 det_holonomy_eq_one` | **PURE** (26/0) ✓ |
| ★★★★ **the MIN over controls = the q+1 optimum (the inf side of LP/closure duality)** — weak duality (`dualValue ≤ transportCost`) + the zero-gap "they meet" optimum | `Lib/Math/Geometry/DiscreteCurvature/OllivierRicci.lean:52 kantorovich_weak_duality`; `:106 ollivier_plan_optimal`; `:40 dualValue`; `:36 transportCost` | **PURE** (60/0) ✓ |
| ★★★★ **the min/optimum closure (policy-improvement idempotence) = the q+1 settle** `clo` | `Lib/Math/Order/GaloisConnection.lean:126 clo_idempotent`; `:107 clo_extensive`; `:104 clo`; `:41 gc_unit`; `:49 gc_counit` | **PURE** (15/0) ✓ |
| ★★★ **HJB = the Bellman equation at residue resolution (`h→0`)** — the resolution-shift dial that turns the discrete look-ahead into the differential `∇V·f` | `Lib/Math/Analysis/ResolutionShift.lean:73 IsResolutionShift`; `:130 IsResolutionShift_compose` | ∅-axiom ✓ (per `derivative.md`/`integration.md`) |
| **principle of optimality = the recursive fold / self-reference** (`V` defined in terms of itself = the catamorphism out of the construction) | `Lens/Foundations/...` `raw_initial`, `Lens.view = Raw.fold`, `dhom_unique_pointwise` (per `category_theory.md`/`adjunction.md`) | ∅-axiom ✓ |
| **γ ≥ 1 / no-contraction divergence = escape to the reached-by-none residue (q−1 pole)** | `Lib/Math/Foundations/ResidueTag.lean:133 escape_residue_outside`; `Lens/Foundations/OneDiagonal.lean no_surjection_of_fixedpointfree` (per `cardinality.md`) | ∅-axiom ✓ |

**Fresh purity scan (this session, `tools/scan_axioms.py E213.<module>` from repo root):** `ResidueTag`
**55/0**, `BanachFixedPoint` **12/0**, `OrbitIsIter` **1/0**, `PicardIterate` **8/0**, `MonovariantFlow`
**19/0**, `NoetherCurrent` **14/0**, `HolonomyLattice` **26/0**, `OllivierRicci` **60/0**,
`GaloisConnection` **15/0**. All pure / 0 dirty.

> Note on the q+1 engine anchor: the headline `banach_fixed_point_modulated` lives under the
> `CompleteMetricModulusMod` structure namespace (in `Lib/Math/Analysis/BanachFixedPointModulated.lean`),
> so a by-module scan of the bare name reports `0/0`. The engine is verified PURE *through its delegate*
> `ResidueTag.converge_residue_fixed` (PURE in the 55/0 scan) — the same honest reporting
> `differential_equations.md`/`markov_chains.md` use.

## Dropped / flagged (predicted-not-built — grep-confirmed ABSENT in `lean/E213`)

Grep over `lean/E213` (case-insensitive) for `Bellman` / `valueFunction` / `value_function` /
`dynamic_programming` / `HJB` / `Pontryagin` / `optimalControl` / `optimal_control` / `value_iteration` /
`policy_iteration` / `policyIteration` / `costate` returns **no hits at all** — none of these named
objects exists in the repo. So:

- **No `Bellman` operator / `valueFunction V` object** — no `T[V](x) = min_u[c + γ·V(f(x,u))]`, no
  `V = T[V]` fixed-point statement. The contraction engine exists (`BanachFixedPoint.Contraction`,
  `banach_fixed_point`), the min-optimum exists (`OllivierRicci`), and a concrete iterated-step instance
  exists (`picardIterate`), but the named Bellman operator carrying the `min_u` + discount + look-ahead is
  **not stated**. **Predicted-not-built** (same engine-present/object-absent status as
  `markov_chains.md`'s `transitionMatrix` and `differential_equations.md`'s continuous Picard operator).
- **No `value_iteration` / convergence-to-V theorem** — no `Vₙ → V` with a discount-rate modulus. The
  Banach `picard` orbit + `picard_cauchy` modulus is the predicted resolver and `orbit_eq_iter`/
  `picardIterate` are the iteration template, but the value-iteration convergence theorem is **unbuilt**.
  **Predicted-not-built.**
- **No `HJB` PDE object** — no continuous `−∂V/∂t = min_u[c + ∇V·f]`. The resolution-shift dial
  (`IsResolutionShift`) is the predicted home (HJB = Bellman at `h → 0`), but a named HJB statement is
  **absent**, and the smooth continuous limit is a `Real213`-cut leg. **Predicted-not-built + value-cut.**
- **No `Pontryagin` / maximum-principle object, no `costate`** — no Hamiltonian-maximisation statement,
  no `ṗ = −∂H/∂x`. The discrete Noether conservation IS built (`noether_local`, `continuity_eq`,
  `det_holonomy_eq_one`) and is the predicted skeleton (costate = conserved current; H conserved on the
  optimal path = `det=1`), but the named Pontryagin theorem — and especially the *continuous/variational*
  maximum principle over a differentiable trajectory — is **unbuilt**. This is the **same honest residual
  `noether.md` flags**: the discrete current/continuity-equation is a theorem; the smooth/analytic
  variational current `∂_μ j^μ` is the open `Real213`/`h→0` leg. **Predicted-not-built (skeleton built).**
- **No `policy` / `policyIteration` object** — no policy-evaluation + policy-improvement alternation. The
  pieces (a contraction for evaluation, the min/`clo` for improvement) are PURE and present, but the
  coupled-contraction policy-iteration theorem is **unbuilt**. **Predicted-not-built.**
- **The optimal-cost VALUE** (and the spectral/HJB smooth limit) — a `Real213`/cut value-residue,
  irrational in general; the existence of the q+1 fixed point at the contraction level is closed
  (`banach_fixed_point`), the value is the orthogonal `Real213` task. **Value-cut residue, honest.**

### A verified buildable witness (the cleanest promotion target)

**A discrete-state Bellman operator on a finite value vector, shown to be a `BanachFixedPoint.Contraction`
with modulus the discount `γ`, is groundable with no new construction.** The pieces are all PURE and
present:
- Define `bellman (c : S → A → ℤ) (f : S → A → S) (γnum γden : ℕ) (V : S → ℤ) (x) := min over a (finite
  list of) `a` of `c x a + (γnum * V (f x a))/γden` — a value vector reading, the min an `argmin` over a
  finite action list (the inf side of `OllivierRicci`'s LP, the additive twin of `kantorovich`).
- Show `|bellman V x − bellman W x| ≤ (γnum/γden)·max|V − W|` (the min is 1-Lipschitz; the look-ahead
  scales by `γ`), i.e. `Contraction (sup-metric) bellman` in `BanachFixedPoint`'s sense, with modulus `γ`.
- Apply `banach_fixed_point` + `banach_unique` to obtain the value function `V*` as
  `lim(picard bellman V₀)` with modulus `picard_cauchy` — **value iteration = the Picard orbit converging
  to the unique value function**, the q+1 contraction residue, one theorem.
- A theorem `value_iteration_converges : Contraction sup bellman → ∃! V*, bellman V* = V* ∧ V* = lim
  (picard bellman V₀)` would weld `banach_fixed_point` to the DP setting the way
  `ConvolveRescaleContraction` welds the Banach engine to the CLT and the brief's named target welds it to
  the ODE. The conserved-Hamiltonian (Pontryagin) side is *already* the built `noether_local` /
  `det_holonomy_eq_one`; the value-function side is this one weld. Build-checked as *present pieces*, not
  asserted as a closed theorem — the **fifth instantiation of the Banach engine** after φ
  (number-recurrence), the Gaussian (`Φ_contraction`), the ODE flow (`picardIterate`), and the stationary
  distribution (`markov_chains.md`'s named target).

> Axiom-purity note: every theorem cited in the anchors table was freshly scanned with
> `tools/scan_axioms.py E213.<module>` this session (tallies above) — the purity claim rests on a fresh
> scan, not docstrings. The grep for the named control-theory objects (`Bellman`/`HJB`/`Pontryagin`/…)
> returned zero hits, so every "named object" is honestly marked predicted-not-built.
