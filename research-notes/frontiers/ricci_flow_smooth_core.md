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
2. **Other homogeneous flows as ODEs.**  Ricci flow on flat tori (`Ric=0`,
   fixed point), or pinching on Berger spheres / Bianchi classes — each a
   finite-dim ODE compiling onto A6 FLOW, like the round sphere.
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

## Verdict

The round-sphere extinction is the honest *floor*; the `𝓕/𝓦`-monotonicity for
general metrics is the *core* and the wall.  A6 FLOW correctly *locates* the
core (it is the `descent`-hypothesis discharge) without crossing it.  Do not
narrate the core as "closed."
