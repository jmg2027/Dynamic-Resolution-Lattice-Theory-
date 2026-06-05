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

## Why ∅-axiom-unreachable here

- Requires **Riemannian geometry** (smooth manifolds, metric/connection/
  curvature tensors), **tensor calculus**, and **PDE existence + a priori
  estimates** (Shi estimates, maximum principles, compactness) — none present in
  `lean/E213/`, and **Mathlib is forbidden** (hidden axioms).
- Even the *statement* of `𝓕`-monotonicity needs integration on manifolds and
  the conjugate heat equation; the *proof* is Fields-level analysis.
- The proof-ISA position is honest about this (`seed/PROOF_ISA.md`,
  *Honest status*): the ISA supplies the compilation target (FLOW: find a
  monovariant; prove it descends), it does **not** auto-solve.  For the round
  sphere the monovariant and its descent are trivial; for general metrics
  *finding `𝓦` and proving its descent IS the conquest*.

## Reachable sub-steps (if pursued)

Ranked by tractability, each a genuine fragment that does *not* require the full
PDE machinery:

1. **Gradient-flow ⇒ monotone (algebraic skeleton).**  In a finite-dimensional
   inner-product space (over `Q213`/`Real213`), gradient descent
   `x' = x − τ∇F(x)` on a quadratic `F` decreases `F` (`F(x') ≤ F(x)`, strict
   off critical points).  This formalizes the *form* of Perelman's monotonicity
   — "the functional is a monovariant because the flow is its gradient flow" —
   modulo the (unreachable-here) geometric premise that Ricci flow *is* that
   gradient flow.  ∅-axiom-feasible; the most informative next step.
2. **Other homogeneous flows as ODEs.**  Ricci flow on flat tori (`Ric=0`,
   fixed point), or pinching on Berger spheres / Bianchi classes — each a
   finite-dim ODE compiling onto A6 FLOW, like the round sphere.
3. **Normalized flow fixed points = Einstein metrics** at the algebraic level
   (the `Sym(3)`-fixed subspace already in `Ricci.lean` as the averaging-
   invariant analog).

## Verdict

The round-sphere extinction is the honest *floor*; the `𝓕/𝓦`-monotonicity for
general metrics is the *core* and the wall.  A6 FLOW correctly *locates* the
core (it is the `descent`-hypothesis discharge) without crossing it.  Do not
narrate the core as "closed."
