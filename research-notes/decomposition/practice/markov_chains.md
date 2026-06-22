# Decomposition: Markov chains (a transition matrix P, the stationary distribution π, Perron–Frobenius, mixing / convergence to stationarity, detailed balance / reversibility, ergodicity, the spectral gap / mixing time)

*A FRESH decomposition per `../README.md` (model v7.1) and `SYNTHESIS.md` (the two invariants + the
q=±1 spine). A **three-neighbour fusion on the weight axis**: it folds `random_walks.md` (the averaging
/ Laplacian operator `A = I − Δ` and its q=+1 averaging fixed point), `martingales.md` (the q=+1
conditional-expectation fixed point), and `ergodic_theory.md` (measure-preserving / Birkhoff /
ergodicity = the dim-1 constant kernel) into one object — and the one NEW datum is that the **stationary
distribution π = the q+1 converging fixed point of the transition operator = the Perron eigenvector
(eigenvalue exactly 1, the q+1 fixed VALUE)**, with the rest of the spectrum (the spectral gap) = the
convergence MODULUS, and reversibility = the q±1 time-symmetry.*

> **THE THESIS (the brief's central claim).** A Markov chain is the calculus's **q+1 converging fixed
> point of the transition operator, read on the weight axis (a distribution), with the stationary
> distribution = the Perron eigenvector**. (i) The transition matrix `P` acting on distributions = the
> averaging/iteration operator — `random_walks.md`'s `A = I − Δ`, the q+1 contraction. (ii) The
> stationary distribution `π` (`πP = π`) = the q+1 converging FIXED POINT — the SAME
> `banach_fixed_point_modulated` / `golden_is_converge` / `converge_residue_fixed` pole that resolves φ,
> the Gaussian, the ODE flow, the invariant measure (`ergodic_theory.md`): the distribution `P` cannot
> change, the eigenvector for eigenvalue 1. (iii) Perron–Frobenius (top eigenvalue exactly 1, positive
> eigenvector) = the q+1 pole made spectral — the top eigenvalue IS the q+1 fixed value `1`, the rest of
> the spectrum (the spectral gap `1 − |λ₂|`) controls the convergence RATE (the modulus). (iv)
> Convergence to stationarity / mixing = the q+1 contraction reaching the fixed point; the spectral gap =
> the contraction modulus. (v) Detailed balance / reversibility = the **q±1 symmetry** — the chain = its
> time-reversal, the symmetric (`disc_symmetric_nonneg`) q+1 case. (vi) Ergodicity = `ergodic_theory.md`'s
> "invariant = constant" = the q+1 unique fixed point (dim-1 kernel). **NO new primitive:** it is
> `random_walks.md`'s averaging operator + `martingales.md`'s q+1 weight-axis fixed point with the Perron
> eigenvalue, dialed once.

## The decomposition (C / Reading / Residue)

- **Construction `C` — NO new construction; `random_walks.md`'s `⟨ V (count) | symmetric Adj + edge
  weight ⟩` exactly.** A Markov chain has no construction of its own. The state space is
  `graph_theory.md`/`random_walks.md`'s graph `⟨ V (count-reading, `cardinality.md`) | a pair-reading on
  V×V ⟩` carrying the **weight axis** (`probability.md`/`martingales.md`): the transition step adds only
  the per-edge weight `P(x→y)`, with `Σ_y P(x→y) = 1` (each row a distribution — the weight-reading
  *fibred over the out-edges of `x`*, exactly `random_walks.md`'s `P = D⁻¹A`). A *distribution* `μ` over
  states is the weight-reading itself (`probability.md`'s `P = ratio∘count`). **Nothing
  Markov-theoretic is primitive — only a graph (count + pair-reading) and a row-stochastic edge weight.**

- **Reading `L_P` — the transition operator `P` as the averaging/iteration reading on the weight axis,
  read at successive steps.** Two facets, one reading:
  1. **`P` acting on a function `f` (the "backward"/observable side)** `(Pf)(x) = Σ_y P(x→y) f(y)` is the
     **averaging reading** `random_walks.md`'s `A = I − D⁻¹Δ` verbatim — the neighbour-average of `f`
     weighted by the transition row. `Pf = f` ⟺ `f` harmonic ⟺ the q+1 averaging fixed point
     (`random_walks.md`'s three-names-one-object).
  2. **`P` acting on a distribution `μ` (the "forward"/push-forward side)** `μ ↦ μP`, `(μP)(y) = Σ_x μ(x)
     P(x→y)` is `ergodic_theory.md`'s push-forward `T_*` on weights — the reading-of-readings whose fixed
     point is the invariant measure. **`πP = π` is the q+1 converging fixed point of `μ ↦ μP`** — the
     SAME `banach_fixed_point_modulated` engine, here read on the σ-step dial (which step) instead of a
     metric contraction, exactly `martingales.md`'s filtration-refinement step one level over.
  Two facts are *forced*, not chosen:
  - **Row-stochasticity forces the q+1 fixed value `1`.** `Σ_y P(x→y) = 1` means `P·𝟙 = 𝟙` (the all-ones
    observable is the q+1 averaging fixed point — `random_walks.md`'s `Δ𝟙 = 0`, the constant Laplacian
    kernel). The DUAL statement `πP = π` pins a *distribution* fixed point; the shared eigenvalue is
    **exactly `1`** — the Perron value is the q+1 fixed VALUE, not a free dial.
  - **Reversibility (detailed balance `π(x)P(x→y) = π(y)P(y→x)`) forces a SYMMETRIC operator.** Under the
    `√π`-rescaling `S(x,y) = √π(x) P(x→y) /√π(y)`, detailed balance ⟺ `S` symmetric, so by
    `random_walks.md`/`spectral.md`'s `Mat2SymmetricSpectrum.disc_symmetric_nonneg` the spectrum is
    **real** — the q+1 corner; a reversible chain never goes elliptic. This is the q±1 *symmetry* bit:
    the chain equals its time-reversal.

- **Residue — `q = ±1`, read at the poles. The whole field IS the residue doctrine on the transition
  operator, made spectral.**
  - **q=+1 (converge / stationary / ergodic — the Perron fixed point, the return).** The stationary
    distribution `π` is `μ ↦ μP`'s *fixed point* `πP = π`, the q+1 converging residue
    `martingales.md`/`ergodic_theory.md`/`golden_ratio.md` resolve with
    `ResidueTag.converge_residue_fixed`/`golden_is_converge` (delegating to
    `banach_fixed_point_modulated`). Perron–Frobenius makes this **spectral**: the top eigenvalue is
    *exactly* `1` (the q+1 fixed value) with a **positive** eigenvector (`π > 0`), and on an
    irreducible/connected chain `π` is **unique** — `dim` of the eigenvalue-1 space `= 1`, *literally*
    `ergodic_theory.md`'s "ergodic = invariant subspace = constants = dim ker = 1 =
    `graph_theory.md`'s Laplacian `λ₀ = 0`" (`closed_const`/`closed_root_determines`/
    `pathLaplacian_const_kernel`). **Ergodicity = q+1 collapse to the unique Perron fixed point.**
  - **The spectral gap = the convergence MODULUS (the rate, not the residue's existence).** The rest of
    the spectrum `1 > |λ₂| ≥ …` sits *below* the Perron value. Convergence `μP^n → π` is the q+1
    contraction reaching the fixed point at geometric rate `|λ₂|^n` — the **spectral gap `1 − |λ₂|` is the
    contraction modulus** (`ConvolveRescaleContraction`'s exact dyadic-halving rate, `DyadicCompletion`'s
    completion-limit), the **mixing time** `≈ 1/(1−|λ₂|)·log(…)` its readout. This is `derivative.md`'s
    resolution dial / `gaussian_clt.md`'s `picard_cauchy` modulus: the limit `π` is reached by none, the
    modulus narrows it.
  - **q=−1 (escape / non-mixing — periodicity, reducibility, the boundary).** When the operator is NOT a
    strict contraction below `1`, mixing fails: a **periodic** chain has an eigenvalue `−1` (or a root of
    unity) of modulus 1 — the q−1 escape pole, an oscillation *outside* every averaging step that never
    decays (the checkerboard never settles). A **reducible** chain has `dim` of the eigenvalue-1 space
    `> 1` — `ergodic_theory.md`'s non-ergodic split, `graph_theory.md`'s disconnected graph (`dim ker
    L > 1`). The **spectral-gap / mixing-time VALUE** (the `|λ₂|`, irrational in general) is a
    `Real213`/√-cut value-residue, reached-by-none (`spectral.md`'s honest q−1 value leg).

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   Markov chain (Xₙ)         =  ⟨ V (count) | pair-reading + row-stochastic edge weight ⟩, weight-reading at step n  (C — NO new construction; random_walks + martingales' weight)
   transition matrix P        =  the averaging/iteration reading  (random_walks.md's A = I − D⁻¹Δ; row-stochastic ⟹ P·𝟙 = 𝟙)
   P acting on observable f    =  (Pf)(x) = Σ_y P(x→y)f(y)  =  the neighbour-average  (= random_walks' Af; Pf=f ⟺ harmonic)
   P acting on distribution μ  =  μ ↦ μP  =  ergodic_theory's push-forward T_* on weights  (the reading-of-readings, CLT level)
   STATIONARY π  (πP = π)     =  Residue(μ↦μP, C), q=+1  =  the q+1 converging FIXED POINT  (= φ/Gaussian/ODE/invariant-measure, same banach_fixed_point_modulated)
   PERRON–FROBENIUS           =  the q+1 pole made SPECTRAL: top eigenvalue = 1 (the q+1 fixed VALUE), eigenvector π > 0
   irreducible ⟹ π unique     =  dim(eigval-1 space) = 1  =  ergodic = dim ker = 1 = graph_theory's λ₀=0  (closed_const, closed_root_determines)
   CONVERGENCE  μPⁿ → π        =  the q+1 contraction reaching the fixed point  (modulated-completion, DyadicCompletion/picard_cauchy)
   SPECTRAL GAP  1 − |λ₂|     =  the convergence MODULUS  (the contraction rate; mixing time ≈ 1/gap · log)  ← the rest of the spectrum below Perron
   MIXING                     =  the q+1 contraction below eigenvalue 1 reaching π  (gap > 0 ⟹ μPⁿ → π geometrically)
   DETAILED BALANCE / REVERSIBLE = π(x)P(x→y)=π(y)P(y→x)  =  the q±1 SYMMETRY: chain = time-reversal  (√π-rescaled P symmetric ⟹ disc_symmetric_nonneg, real spectrum)
   ERGODICITY                 =  invariant = constant = q+1 unique fixed point  (= ergodic_theory.md; rotInvariant_is_constant; the dim-1 collapse)
   PERIODIC (eigenvalue −1)   =  q=−1 escape: the oscillation never decays  (the checkerboard mode; lazy_checker_collapses kills it, nonlazy keeps it)
   REDUCIBLE (dim>1)          =  q=−1: the non-ergodic split  (graph_theory's disconnected graph, dim ker L > 1)
   spectral-gap / mixing VALUE =  Real213/√disc cut  (q=−1 VALUE residue, reached-by-none — spectral.md's Fiedler/λ₂ value)
```

So **the transition matrix, the stationary distribution, Perron–Frobenius, mixing, reversibility, and
ergodicity are one reading at work** — the averaging/iteration operator `P` on `random_walks.md`'s graph,
read on the weight axis at the q=±1 poles, with the stationary distribution = the q+1 Perron fixed point
and the spectral gap = the convergence modulus.

## THE REVELATION — collapse (π = the q+1 Perron fixed point) + forcing + spine

This is **not** a re-skin of `random_walks.md` / `martingales.md` / `ergodic_theory.md`. Those built the
q+1 fixed point on a function (harmonic), on a filtration (martingale), and as an invariant measure. The
NEW datum here is **the q+1 fixed point made SPECTRAL via Perron**: the stationary distribution is the
*eigenvector for eigenvalue exactly 1*, the top eigenvalue IS the q+1 fixed VALUE, and the spectral gap
(the rest of the spectrum, below 1) is the convergence MODULUS — a thing none of the three neighbours
record, because none of them carry the row-stochastic operator whose Perron value is pinned to 1.

1. **Collapse — the stationary distribution = the q+1 converging fixed point = the Perron eigenvector,
   one object.** Run the equalities on the weight axis:
   - `πP = π` (stationary) `⟺` `π` is the q+1 converging residue of `μ ↦ μP`
     (`golden_ratio.md`'s rule: a fixed point of a self-applying map = the q+1 residue), the SAME
     `banach_fixed_point_modulated`/`golden_is_converge` engine `ResidueTag.converge_residue_fixed`
     packages — *literally* the invariant-measure fixed point of `ergodic_theory.md`'s `T_*`, the
     Gaussian of `gaussian_clt.md`, φ of `golden_ratio.md`.
   - `πP = π` `⟺` `π` is the eigenvector of `P` for eigenvalue **`1`** (the q+1 fixed value). By
     Perron–Frobenius this eigenvalue is the *top* one, `1` exactly (row-stochasticity forces `P·𝟙 = 𝟙`,
     so `1 ∈ spec P`; the spectral radius `= 1` is the dual), with a *positive* eigenvector `π`.
   So `stationary ≡ q+1 fixed point ≡ Perron eigenvector` — **the abstract q+1 converge pole (the
   neighbours' engine) and the concrete Perron eigenvalue `1` are one and the same object**, with
   row-stochasticity the bridge that pins the eigenvalue to `1`. That collapse is the payoff: it is *why*
   "the stationary distribution is the leading eigenvector" (the classical Perron statement, the basis of
   PageRank and of all mixing theory) is not a coincidence but the q=±1 spine read once, spectrally.

2. **Forcing — Perron's three classical claims are forced by the q+1 pole + row-stochasticity, not
   added.**
   - **Top eigenvalue exactly `1`** is forced: row-stochasticity `Σ_y P(x→y) = 1` IS `P·𝟙 = 𝟙` (the
     constant observable is the q+1 averaging fixed point, `random_walks.md`'s `Δ𝟙 = 0` /
     `pathLaplacian_const_kernel`), so `1` is an eigenvalue; the maximum principle (an average cannot
     exceed its inputs — `random_walks.md`'s "no interior escape", built as `heatStep_le_two_max` /
     `lazyHeatStep_le_four_max`) forces the spectral radius `≤ 1`, hence `1` is the *top* eigenvalue.
   - **Uniqueness of `π` (irreducible ⟹ dim = 1)** is forced: it is *literally* `ergodic_theory.md`'s
     ergodicity = the dim-1 constant kernel = `graph_theory.md`'s connectivity (`closed_const`,
     `closed_root_determines`, `pathLaplacian_const_kernel`). Irreducible = connected = the eigenvalue-1
     space is one-dimensional = the unique Perron fixed point. (Reducible = disconnected = `dim ker > 1` =
     non-ergodic, the q−1 split.)
   - **Convergence `μPⁿ → π` (the gap is the rate)** is forced: below the Perron value `1`, the operator
     is a strict contraction on the mean-zero subspace with factor `|λ₂| < 1`, so the q+1 modulated
     completion-limit applies — `μPⁿ` converges to `π` at geometric rate `|λ₂|ⁿ`, the spectral gap
     `1 − |λ₂|` the contraction modulus (`ConvolveRescaleContraction.Φ_contraction`'s exact-rate
     instance; `DyadicCompletion.orbit_to_center_completion` the completion-limit template). The mixing
     time is the modulus's readout `≈ 1/(1−|λ₂|)·log(1/ε)`.

3. **Spine — reversibility IS the q±1 symmetry, and periodicity IS the q−1 escape.** This is the
   sharpest tie to `SYNTHESIS.md`'s q=±1 spine, with TWO spine rows:
   - **Detailed balance / reversibility = the q±1 SYMMETRY bit.** `π(x)P(x→y) = π(y)P(y→x)` says the
     chain run forward = the chain run backward (the time-reversal). Under `√π`-rescaling this makes `P`
     conjugate to a **symmetric** operator, so by `Mat2SymmetricSpectrum.disc_symmetric_nonneg` the
     spectrum is **real** (`disc ≥ 0`, the q+1 corner) — *the same symmetric-spectrum theorem*
     `random_walks.md` and `ergodic_theory.md` use for the Laplacian/transfer operator. A reversible chain
     is the q+1, real-spectrum, symmetric case; a non-reversible chain can have complex eigenvalues (the
     q−1 elliptic escape, `disc < 0`, `spectral.md`). Reversibility = "the chain = its time-reversal" =
     the symmetric/q+1 case, exactly the q±1 *direction/symmetry* bit (the `ℤ`/`det`/`∂` orientation fold,
     here a time-orientation).
   - **Mixing vs periodicity = the q=±1 converge/escape poles, with a BUILT witness.** A mixing chain
     (gap `> 0`) is q+1: the contraction reaches `π`. A **periodic** chain is q−1: an eigenvalue of
     modulus 1 below the Perron value (e.g. `−1` for period 2) is an oscillation that *never decays* —
     `OneDiagonal.no_surjection_of_fixedpointfree`'s escape flavour on the spectral circle. The repo's
     discrete heat equation makes this a **theorem**: the **non-lazy** averaging step `(½,0,½)` keeps the
     checkerboard mode hot/cold forever (`nonlazy_checker_hot`/`nonlazy_checker_cold` — eigenvalue
     `cos π = −1`, no spectral gap, period-2 = q−1 escape), while the **lazy** reversible step `(¼,½,¼)`
     **collapses the checkerboard to the constant in one step** (`lazy_checker_collapses`: `q+1`, the gap
     is opened, the chain mixes to its stationary constant). "Make the chain lazy to ensure
     aperiodicity/mixing" — a textbook Markov-chain move — is here the q−1→q+1 switch, machine-checked.

**Re-skin guard cleared.** The note does not re-describe its three neighbours' q+1 fixed point: its
load-bearing new fact is that the **stationary distribution = the Perron eigenvector = the q+1 fixed
point made spectral**, with (a) the top eigenvalue pinned to the q+1 fixed value `1` by row-stochasticity,
(b) the spectral gap (the rest of the spectrum) = the convergence modulus, and (c) reversibility = the
q±1 time-symmetry tying `disc_symmetric_nonneg`, with periodicity vs mixing the q−1/q+1 poles *witnessed*
by `nonlazy_checker_hot` vs `lazy_checker_collapses`. None of `random_walks.md`/`martingales.md`/
`ergodic_theory.md` carries the row-stochastic operator whose Perron value is `1`, so the spectral
pinning is genuinely new.

## VALIDATE — verdict: **EXTEND (consolidation) + PREDICTION**, no break, no new primitive

**EXTEND.** Markov chains add **nothing** to model v7.1 — they *fuse* three existing weight-axis entries
at one spectrally-pinned q+1 fixed point:
- the **averaging/iteration operator** (`random_walks.md`: `P = D⁻¹A = I − D⁻¹Δ`, row-stochastic, `Pf=f`
  ⟺ harmonic) — supplies the construction `C` and the operator `P`;
- the **q+1 converging weight-axis fixed point** (`martingales.md`/`ergodic_theory.md`: the same
  `banach_fixed_point_modulated`/`golden_is_converge` pole, `T_*` push-forward) — supplies `π` as the
  fixed point;
- the **dim-1 constant kernel = ergodicity = connectivity** (`ergodic_theory.md`/`graph_theory.md`:
  `closed_const`/`closed_root_determines`/`pathLaplacian_const_kernel`) — supplies uniqueness of `π`;
- the **symmetric real spectrum** (`spectral.md`/`Mat2SymmetricSpectrum.disc_symmetric_nonneg`) —
  supplies reversibility = q±1 symmetry; the spectral gap = the rest of the spectrum;
- the **q=±1 residue tag** (`ResidueTag`) — supplies mixing/periodicity (converge/escape) and
  reducibility (the dim>1 split).

**PREDICTION.** The calculus *predicts* the field's shape from its parts: that `π` = the Perron
eigenvector = the q+1 fixed point (forced by row-stochasticity pinning the eigenvalue to `1`), that the
top eigenvalue is exactly `1` with a positive eigenvector and is *unique* iff the chain is irreducible
(= ergodicity = dim-1 kernel = connectivity), that convergence `μPⁿ → π` is the q+1 contraction with the
spectral gap as the modulus / mixing time, and that reversibility = the q±1 time-symmetry forcing a real
spectrum (`disc_symmetric_nonneg`), with periodicity the q−1 escape (the undecaying eigenvalue-`−1` mode).
The *engines, the symmetric-spectrum corner, and a concrete row-stochastic averaging operator with a
witnessed aperiodicity/mixing collapse are built and PURE* (`Discrete` 30/0, the lazy stencil); the
*named* `MarkovChain`/`transitionMatrix`/`stationary`/`Perron`/`mixing`/`detailedBalance`/`reversible`
objects are **ABSENT** (grep-confirmed) — the located missing leg, the same status as `random_walks.md`'s
absent `RandomWalk`/`transitionMatrix P=D⁻¹A` and `ergodic_theory.md`'s absent measure-preserving/Koopman
objects.

**No BREAK.** The two invariants (character arrow — here the averaging step / the `×↦·` independence of
product chains — and the q=±1 residue) and the four axes absorb the field cleanly; the only honest
residuals are the value-cut (the second eigenvalue `|λ₂|` / mixing-time as a `Real213`/√ number,
irrational in general) and the *named* objects.

## Verified Lean anchors (file:line:theorem — all grep-confirmed; purity by `tools/scan_axioms.py`, run this session from repo root with the `E213.` prefix)

| Leg | Theorem / def (file:line : name) | Purity (fresh scan) |
|---|---|---|
| ★★★★★ **P = the averaging operator over an ARBITRARY finite weighted graph** `Δf(x)=Σ_y w(x,y)(f(y)−f(x))` (= `−wLap`, the generator of `P = I − D⁻¹Δ`) + **mass conservation** `Σ_x Δf=0` (P redistributes mass without creating it — the row-stochastic / stationarity invariant) | `Lib/Math/Geometry/DiscreteCurvature/WeightedGreen.lean:58 wLap`; `:125 wlap_mass_conservation`; `:91 weighted_green` (discrete Green/IBP); `:68 wDirichlet`; `:191 dirichlet_gradient_identity` | **PURE** (11/0) ✓ |
| ★★★★★ **a CONCRETE row-stochastic averaging operator (the lazy reversible random-walk step on a cycle), with the q+1 stationary CONSTANT preserved** `(¼,½,¼)`, `P·c = c` (numerator `4c`) | `Lib/Math/Analysis/ODE/HeatEq/Discrete.lean:214 lazyHeatStep_const`; `:40 heatStep_const` (non-lazy `(½,0,½)`, `P·c=2c`) | **PURE** (30/0) ✓ |
| ★★★★★ **mixing vs periodicity = q+1 vs q−1, WITNESSED** — the lazy step **collapses the checkerboard (the period-2 / eigenvalue-`−1` mode) to the stationary constant in ONE step** (gap opened, mixes); the non-lazy step keeps it oscillating forever (no gap, q−1 escape) | `…/Discrete.lean:335 lazy_checker_collapses` (= 2 ∀x, q+1); `:324 nonlazy_checker_hot` (=2), `:328 nonlazy_checker_cold` (=0, q−1) | **PURE** ✓ |
| ★★★★ **maximum principle (P is a contraction on the sup-norm — Perron radius ≤ 1, no escape above stationarity)** `u≤B ⟹ Pu≤B` (lazy + non-lazy); `lazyHeatStep_strict_at_max` (strict decay below the max away from constants = the gap) | `…/Discrete.lean:221 lazyHeatStep_le_four_max`; `:64 heatStep_le_two_max`; `:157 heatIter_range` (in `[A,B]` ∀t); `:291 lazyHeatStep_strict_at_max` | **PURE** ✓ |
| ★★★★★ **π = the q+1 converging FIXED POINT** — the converge engine (SAME pole as φ/Gaussian/ODE/martingale/invariant-measure), `πP=π` | `Lib/Math/Foundations/ResidueTag.lean:160 converge_residue_fixed`; `:180 golden_is_converge`; `:228 residue_tag_two_poles` | **PURE** (55/0) ✓ |
| ★★★★★ **Perron uniqueness = ergodicity = irreducibility = the dim-1 constant kernel = graph λ₀=0** (`P·𝟙=𝟙` the q+1 constant eigenvector; connected ⟹ unique stationary) | `Lib/Math/NumberSystems/Real213/Mat2/GraphLaplacian.lean:127 pathLaplacian_const_kernel`; `:134 pathLaplacian_eigen_zero`; `Lib/Math/Combinatorics/GraphConnectivity.lean:61 closed_const`; `:79 closed_root_determines` | **PURE** (GraphLaplacian 16/0, GraphConnectivity 8/0) ✓ |
| ★★★★ **reducible = q−1 non-ergodic split (dim>1) vs ergodic return reached exactly (q+1)** — the cyclic measure-preserving instance, invariant ⟹ constant, and the non-ergodic contrast | `Lib/Math/Combinatorics/CyclicErgodic.lean:197 birkhoff_period_eq_space`; `:240 rotInvariant_is_constant`; `:282 nonergodic_invariant_not_constant`; `:207 measure_preserving` | **PURE** (26/0) ✓ |
| ★★★★ **detailed balance / reversibility = the q±1 SYMMETRY ⟹ real spectrum** (√π-rescaled P symmetric; symmetric ⟹ `disc≥0`, the q+1 corner; non-reversible can go elliptic `disc<0` = q−1) | `Lib/Math/NumberSystems/Real213/Mat2/Mat2SymmetricSpectrum.lean:83 disc_symmetric_nonneg` | **PURE** (9/0) ✓ |
| ★★★★ **the spectral gap dissolves the eigenvalue readout: top eigenvalue (Perron) `= e₁`-ish, gap `= disc = (μ−ν)²`** — `tr=e₁`/`det=e₂`, spectrum = the q+1 scale-residues, gap-squared = the discriminant | `Lib/Math/NumberSystems/Real213/Mat2/Mat2Spectrum.lean:115 tr_eq_e1`; `:103 det_eq_e2`; `:167 disc_eq_gap_squared`; `:186 spectrum_roots`; `:204 det_tr_split_is_e1_e2` | **PURE** (9/0) ✓ |
| ★★★★ **convergence μPⁿ → π = the q+1 contraction at geometric (spectral-gap) rate** — the contraction modulus on a reading-of-readings + the genuine completion-limit | `Lib/Math/Probability/Limit/ConvolveRescaleContraction.lean:345 Φ_contraction`; `:471 orbit_to_center`; `:419 center_fixed`; `Lib/Math/Probability/Limit/DyadicCompletion.lean:366 orbit_to_center_completion`; `:328 Φhat_contraction` | **PURE** (ConvolveRescale 20/0, DyadicCompletion 32/0) ✓ |
| periodicity/transience = escape to the reached-by-none residue (Cantor/Gödel/measure escape, the q−1 pole) | `Lib/Math/Foundations/ResidueTag.lean:133 escape_residue_outside`; `Lens/Foundations/OneDiagonal.lean:51 no_surjection_of_fixedpointfree` (per `cardinality.md`) | ∅-axiom ✓ |

**Fresh purity scan (this session, `tools/scan_axioms.py E213.<module>` from repo root):** `Discrete`
**30/0**, `WeightedGreen` **11/0**, `ResidueTag` **55/0**, `GraphLaplacian` **16/0**,
`GraphConnectivity` **8/0**, `CyclicErgodic` **26/0**, `Mat2SymmetricSpectrum` **9/0**, `Mat2Spectrum`
**9/0**, `ConvolveRescaleContraction` **20/0**, `DyadicCompletion` **32/0**. All pure / 0 dirty.

> Note on the q+1 engine anchor: the headline `banach_fixed_point_modulated` lives under the
> `CompleteMetricModulusMod` structure namespace, so a by-module scan of `BanachFixedPointModulated`
> reports `0/0` (no top-level constants of that bare name). The engine is verified PURE *through its
> delegate* `ResidueTag.converge_residue_fixed` (PURE in the 55/0 scan) — the same honest reporting
> `random_walks.md`/`martingales.md`/`ergodic_theory.md` use.

## Dropped / flagged (predicted-not-built — grep-confirmed ABSENT in `lean/E213`)

Grep over `lean/E213` (case-insensitive) for `markovchain`/`markov_chain`/`stationary`/`perron`/
`transition.matrix`/`transitionMatrix`/`stochastic.matrix`/`mixing`/`detailed.balance`/`reversible`/
`spectral.gap`/`transferOperator`/`koopman`/`measurePreserving` returns **no real Markov-chain-object
hits**. The only matches are unrelated: (i) `…/Real213/Markov/*` is the **Diophantine** Markov tree
`x²+y²+z²=3xyz` (`MarkovTree.lean`) — NOT a transition matrix; (ii) `stationary` = Ricci-flow fixed
points (`flat_torus_stationary`, `ricci_uniform_stationary`) and a conformal flat-metric fixed point
(`ConformalCurvature.lean:86`); (iii) `mixing` = physics flavour-mixing-angle docstrings; (iv)
`spectral gap` = the Lichnerowicz / Yang–Mills / heat-equation gaps (the heat one is the relevant
*phenomenon*, not a named Markov object); (v) `reversible` = a one-word Odometer docstring. So:

- **No `MarkovChain` / `transitionMatrix P` / `stochasticMatrix` object** — no row-stochastic operator
  carrying `Σ_y P(x→y) = 1`, no `μ ↦ μP` push-forward. The averaging operator exists *constructed*
  (`WeightedGreen.wLap`) and a *concrete row-stochastic averaging step* is built (`lazyHeatStepNum`,
  `(¼,½,¼)` on a cycle = a reversible lazy random-walk transition), but the named `MarkovChain`/`P`
  object with the stochasticity proof is **not stated**. **Predicted-not-built** (same `P = D⁻¹A` gap
  `random_walks.md`/`graph_theory.md` located for PageRank).
- **No `stationary` distribution object `πP = π`** — no `π : distribution` with the fixed-point proof.
  The q+1 fixed-point engine (`converge_residue_fixed`/`golden_is_converge`) is the predicted resolver
  and the constant-kernel uniqueness is built (`pathLaplacian_const_kernel`/`closed_const`), but the
  named stationary distribution is **absent**. **Predicted-not-built.**
- **No `Perron`/`Perron–Frobenius` theorem** — no "top eigenvalue exactly 1, positive eigenvector,
  unique on irreducible" statement. The pieces — `P·𝟙=𝟙` (the constant q+1 eigenvector), the maximum
  principle (`lazyHeatStep_le_four_max`, spectral radius ≤ 1), uniqueness = dim-1 kernel
  (`closed_root_determines`) — are all PURE and present; the **weld** into a named Perron theorem is
  **unbuilt**. **Predicted-not-built** (a clean buildable witness — see below).
- **No `mixing` / `convergence to stationarity` / `mixingTime` object** — no `μPⁿ → π` statement with a
  spectral-gap rate. `ConvolveRescaleContraction`/`DyadicCompletion` are the q+1 contraction /
  completion-limit templates, `lazy_checker_collapses` the *witness* that the lazy step kills the
  slowest non-constant mode, but the general convergence theorem is **unbuilt**. The mixing-time / `|λ₂|`
  VALUE is a `Real213`/√-cut (q−1 value residue, irrational in general). **Predicted-not-built + value-cut.**
- **No `detailedBalance` / `reversible` predicate** — no `π(x)P(x→y)=π(y)P(y→x)`, no √π-symmetrization.
  The symmetric-spectrum corner is built (`disc_symmetric_nonneg`), the q±1 symmetry tie is the
  prediction, but the named reversibility predicate is **absent**. **Predicted-not-built.**
- **No `ergodic`/`irreducible`/`aperiodic`/`periodic` predicate (Markov sense)** — the q±1 tag
  (`ResidueTag`) is the predicted home (ergodic/mixing = `.converge`, periodic/reducible = `.escape`),
  the ergodic return + non-ergodic split are built for the cyclic instance (`CyclicErgodic`), and the
  aperiodicity collapse is witnessed (`lazy_checker_collapses` vs `nonlazy_checker_hot/cold`), but no
  Markov-chain ergodicity/periodicity predicate exists. **Predicted-not-built.**
- **The spectral-gap / second-eigenvalue VALUE `|λ₂|`** — a `Real213`/√disc cut (q−1 value residue),
  irrational in general; existence of a real spectrum at the symmetric/reversible level is closed
  (`disc_symmetric_nonneg`), the value is the orthogonal `Real213` task. **Value-cut residue, honest.**

### A verified buildable witness (the cleanest promotion target)

**A `2×2` lazy reversible Markov chain — top eigenvalue exactly 1 (the stationary/Perron fixed point),
real spectrum, and a positive spectral gap — is groundable with no new construction.** The pieces are
all PURE and present:
- A `2×2` doubly-stochastic `P = [[1−p, p],[p, 1−p]]` (`p ∈ (0,1)`, `0 < 1−p`) is **symmetric**, so
  `Mat2SymmetricSpectrum.disc_symmetric_nonneg` gives a real spectrum (reversibility = q+1 corner), and
  `Mat2Spectrum.tr_eq_e1`/`det_eq_e2`/`disc_eq_gap_squared` give `spec P = {1, 1−2p}` (Perron value `1` =
  `tr − det`-readout; the gap `1 − |1−2p| = 2·min(p,1−p) > 0`).
- `P·(1,1) = (1,1)` is the q+1 constant eigenvector (`pathLaplacian_const_kernel`-style, a one-line
  `decide`/`ring`); the uniform `π = (½,½)` is the stationary distribution `πP = π` (the dual fixed point).
- A theorem `markov2_perron : P symmetric stochastic → spec P = {1, gap} ∧ P·𝟙 = 𝟙 ∧ 0 < gap` would weld
  `disc_symmetric_nonneg` + `Mat2Spectrum`'s Vieta readout into a named *Perron-for-the-2-state-chain*
  statement, with `lazy_checker_collapses` already the n-state aperiodicity-mixing witness. This is the
  *same* gap `random_walks.md`/`spectral.md` named (the operator-kernel / charPoly-factoring weld), here
  with the Markov reading making the promotion target concrete: **`spec P = {1, λ₂}` with `1` the q+1
  Perron value and `1 − |λ₂|` the mixing gap, real because `P` is symmetric (reversible)**, derivable
  from `disc_symmetric_nonneg` + the `Mat2Spectrum` Vieta lemmas. Build-checked as *present pieces*, not
  asserted as a closed theorem.

> Axiom-purity note: every theorem cited in the anchors table was freshly scanned with
> `tools/scan_axioms.py E213.<module>` this session (tallies above) — the purity claim rests on a fresh
> scan, not docstrings.
