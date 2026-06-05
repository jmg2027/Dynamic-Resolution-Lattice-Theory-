# Session Handoff — 2026-06-05 (transcendentals T1/T2 + PDE P1/P2 marathon)

## Branch
`claude/transcendentals-pde-marathon-93F1Y` — all work pushed.  `cd lean && lake build` clean on the
touched modules (`ExpLog.CutExpModulus`, `ExpLog.CutTrigModulus`, `Analysis.ODE.HeatEqDiscrete` +
downstream `Analysis.ODE`, `Analysis.ODE.Capstone`).  Autonomous marathon — invoke `autonomous-research`
each session to continue.

## The arc
Two genuinely-hard blocks were split off the A6 Ricci core (`ricci_flow_smooth_core.md`) into standalone
ladders; this session drove their first rungs, **all strict ∅-axiom** (`#print axioms` empty):
- **Transcendentals** (`research-notes/frontiers/transcendentals/transcendental_functions_ladder.md`)
- **Discrete PDE estimates** (`research-notes/frontiers/pde_estimates/discrete_pde_estimates_ladder.md`)

## What was done this session (21 new PURE theorems)

### T1 — exp Taylor convergence modulus (ratio-test core) — `ExpLog/CutExpModulus.lean` (NEW, 6 PURE)
The convergence-modulus follow-up `CutExpSeries` deferred ("ratio-test argument not yet done").  Worked at
the term-magnitude level `Mᵏ/k!` (`M` bounds `|x|`), no cut comparison:
- `pow_half_step` → `expTerm_ratio_half` — each Taylor term ≤ **half** the previous once `2M ≤ k+1`
  (cross-multiplied `2·M^{k+1}·k! ≤ Mᵏ·(k+1)!`).
- `expTerm_geom_majorant` — `2ʲ·M^{N+j}·N! ≤ Mᴺ·(N+j)!` for `2M ≤ N+1` (geometric tail ratio `1/2`).
- `expTail_geom_decay` — base `N=2M`: tail decays as `term(2M)·2^{−j}`, dyadic modulus `j ↦ 2ʲ`.
- `expTerm_le_of_ge` (gap-antitone) + `expTerm_antitone` — terms non-increasing past `2M`.

### T2 — sin/cos convergence modulus by comparison — `ExpLog/CutTrigModulus.lean` (NEW, 4 PURE)
`sin`/`cos` term magnitudes ARE `exp` terms at odd/even indices, so they inherit the engine:
`cosTerm_geom_decay`/`sinTerm_geom_decay` (decay `term(m)/2^{2k}`) + `cosTerm_antitone`/`sinTerm_antitone`
(alternating-series-test hypothesis).

### T1 algebraic route — exp(m) convergents + cross-determinant — `ExpLog/CutExpConvergents.lean` (NEW, 5 PURE)
Generalizes `EulerModulus`'s e-convergent arithmetic to **exp(m) at every integer arg**: `expNum m`
(`A_{n+1}=(n+1)A_n+m^{n+1}`), `expNum_one` (=`eulerNum`), `exp_cross_det` (cross-det `m^{n+1}·n!`),
`exp_convergents_mono`.  **Honest finding**: the clean `RateModulus` modulus `N(m,k)=k+2` is **m=1-special**
— the rate certificate `i(i+1)m^{i+1}+i ≤ (i+1)²` fails for `m≥2` at `i=1` (`exp_two_rate_fails_at_one`).
General exp(m)'s modulus is the analytic `2m`-threshold majorant (`CutExpModulus`); the two routes are
complementary.  (+ `HeatEqDiscrete.lazy_eq_nonlazy_plus_self`: `lazy = non-lazy + 2u_x`, the spectral-gap reason.)
**Routes unified** (`exp_increment_eq_taylor`, `exp_increment_geom_decay`, `eulerDen_eq_factorial`): the
convergent increment `e_{i+1}−e_i` IS the next Taylor term `m^{i+1}/(i+1)!`, so the gaps inherit the
analytic `2m`-threshold geometric decay — exp(m)'s Cauchy rate, analytically sourced.

### T3 — formal derivative rules (coefficient level) — `CutExpModulus` + `CutTrigModulus` (3 PURE)
`exp_deriv_coeff_fixed` (`d/dx exp = exp`, fixed point), `sin_deriv_coeff` (`d/dx sin = cos`),
`cos_deriv_coeff` (`d/dx cos = −sin`) — all from the one factorial shift `(n+1)·n! = (n+1)!` (exp =
fixed point, sin↔cos = 2-cycle; cos sign-flip in the Int213 difference-Lens).  Cut-level termwise
`d/dx expPartialSum N = expPartialSum (N−1)` (via `IsDifferentiable` instances) remains.

### P1 — discrete heat maximum principle — `Analysis/ODE/HeatEqDiscrete.lean` (extended, 4 PURE)
`heatStep_le_two_max`/`heatStep_two_min_le` (no hot/cold spots), `heatStep_range` (sup-norm contraction),
`heatStep_osc_bound` (oscillation non-increasing).  **Iterated to all time** (`heatField`, `heatIter`):
`heatIter_le`/`heatIter_ge`/`heatIter_range` — data in `[A,B]` ⟹ `t`-step field in `[2ᵗA,2ᵗB]` (averaged in
`[A,B]`) for every `t`, i.e. `‖u(t)‖∞ ≤ ‖u(0)‖∞`.  Uniform in mesh ⟹ `Real213`-limit ready.

### P2 — obstruction found + lazy-step fix — same file (7 PURE)
**Honest finding**: strict *oscillation* decay is **false** for the non-lazy stencil `(½,0,½)` — the
checkerboard `0,1,0,1` maps to `2·checkerboard` (eigenvalue `−1`, no spectral gap).  The genuine smoothing
operator is the **lazy** step `lazyHeatStepNum = u_{x−1}+2u_x+u_{x+1}` `(¼,½,¼)`: `lazyHeatStep_const`,
`lazyHeatStep_le_four_max`/`_four_min_le` (maximum principle), and the concrete witness
`lazy_checker_collapses` (length-4 checkerboard → constant in one lazy step, osc `1→0`) vs
`nonlazy_checker_hot`/`_cold`.  **Strong (strict) maximum principle** (`heatStep_strict_at_max`,
`lazyHeatStep_strict_at_max`): a max site with a strictly-below neighbour drops *strictly* — for *both*
stencils; the non-lazy max then *relocates* (`[0,1,0,1]→[2,0,2,0]`), so local strict drop ≠ global decay
(the lazy self-weight pins the extremum).  **Comparison principle** (`heatStep_mono`, `lazyHeatStep_mono`,
`heatIter_mono`): order-preservation `u ≤ v ⟹ heatStep u ≤ heatStep v` (and for all time) — the parabolic
estimate the max principle is a special case of (`heatStep_le_two_max_via_comparison`).

## Next targets (priority order)
1. **T1→T2 bridge**: package the proven exp term-decay rate into a `CauchyCutSeq` over the cut-level
   `expPartialSum` (reuse `eulerCauchySeq`/`RealCauchyWitness`/`CompletenessLoop` idiom) — lifts the rate to
   a genuine `Real213` point.  The bridge is **done at the rate level**: `CutExpConvergents` proves the
   convergent increment = Taylor term (`exp_increment_eq_taylor`) and that the gaps decay geometrically
   past `2m` (`exp_increment_geom_decay`).  Remaining = the cut-level stabilization: define
   `cs i = constCut (expNum m i) (eulerDen i)` and prove `CauchyCutSeq.cauchy` from the gap decay (the
   delicate `decide`-cut bookkeeping, RateModulus-style but with the m-dependent rate).  NOTE: a *shifted*
   `RateModulus` is **not** the path — its margin `1/(i·d_i)` is e-tied (bounds `~1/(i·i!)`, not exp(m)'s
   `~m^{i+1}/(i+1)!` at any threshold).  The algebraic capstone would need a *generalized-margin* RateModulus
   (rate `m^{i+1}/(i+1)!`).  Then the **signed** `sinCut`/`cosCut` series replacing the
   `Real213/Core/Functions.lean` stubs (alternating partial sums bracket via the antitone magnitudes).
2. **P2 general**: oscillation contraction *rate* for the lazy step at general `n` / general field (the
   spectral-gap estimate, not just the n=4 checkerboard witness), then the `Real213` limit → continuous
   smoothing.  **P3** energy/Dirichlet decay `E(u)=Σ(u_{i+1}−u_i)²`.
3. **T3** derivative rules (`d/dx exp = exp`, termwise via `cutPowFnIsDifferentiable`); **T4** `sqrt`.
4. Both ladders feed the A6 Ricci core (`a6_ricci_core/`), still ON HOLD until they deliver.

## File map (this session)
```
lean/E213/Lib/Math/NumberSystems/Real213/ExpLog/CutExpModulus.lean   ← T1 (NEW, 6 PURE)
lean/E213/Lib/Math/NumberSystems/Real213/ExpLog/CutTrigModulus.lean  ← T2 (NEW, 4 PURE)
lean/E213/Lib/Math/Analysis/ODE/HeatEqDiscrete.lean                  ← P1+P2 (extended, +11 PURE)
research-notes/frontiers/transcendentals/transcendental_functions_ladder.md  ← T1/T2 marked
research-notes/frontiers/pde_estimates/discrete_pde_estimates_ladder.md      ← P1/P2 marked + obstruction
STRICT_ZERO_AXIOM.md                                                 ← all logged
lean/E213/Lib/Math/NumberSystems/Real213/ExpLog/INDEX.md             ← +2 files (count 16)
```
