# Real213 — Module Index (sub-organized 2026-05-13)

213-native real-number type via Dedekind cut.  67 files in 7 sub-clusters.

## Sub-clusters

| Dir | Files | Topic |
|---|---|---|
| `Core/` | 11 | type + Equiv + ValidCut + Dyadic + Functions + Poset |
| `Sum/` | 11 | cutSum + signedSum family |
| `Mul/` | 15 | cutMul/Inv/Pow/Poly + ConstCutScale + CutBinary/Double/Distance |
| `Lattice/` | 5 | cutMax/Min/Mid + LatticeEq + ScaleLattice |
| `Bisection/` | 3 | bisection + continuity (CutBisection{,Algo}, CutContinuity) |
| `ExpLog/` | 13 | CutExp/Log series + ODE + Geom* (Cauchy convergence) + EulerCut (e) / PiCut (π) |
| `Cauchy/` | 1 | ChainToCut (Method A Nat213 chain → cut bridge, via `Lens.Number.Nat213.Bridge.value_toRaw*`) |

## Top-level

`Real213.lean` — umbrella aggregator.

**Named-constant cuts via `AbCutSeq`**:
  - `AbCutSeq.lean` — ★ every monotone-bounded ab-sequence is a `Real213` cut
    (the shared carrier: valid/ratio/nesting/eventual-const/completion/
    `limit_brackets`).  Instances: `ExpLog/EulerCut` (e), `ExpLog/PiCut` (π),
    `PhiAbCut` (φ).
  - `PhiAbCut.lean` — φ as an `AbCutSeq`; the algebraic/transcendental split as a
    theorem (φ completes with closed-form modulus `N=2k`, e/π take it as a
    hypothesis — algebraicity *is* the closed-form modulus).
  - `MobiusProbeTwist.lean` — the cut-probe lattice `(m,k)` is twisted by the
    Möbius `P = [[2,1],[1,1]]` (`Pstep (m,k) = (2m+k, m+k)`); P preserves rational
    order (det `= NS−NT = 1`), so the twist sends cuts to cuts
    (`cutThroughP_ratio`).  The two probe axes are braided by the `(NS,NT)=(3,2)`
    matrix.
  - `PhiProbeFixed.lean` — ★ **φ is the fixed cut of the probe-twist**:
    `cutThroughP phiCut = phiCut` (∀, PURE).  The cut-level shadow of "φ is the
    eigenvector of P".  Both sides reduce to the subtraction-free master invariant
    `masterCut m k = decide(k ≤ 2m ∧ mk+k² ≤ m²)` (the φ-norm `m² ≥ mk+k²`).
  - `ProbeTwistFixedPoint.lean` — the dichotomy: φ's cut is twist-fixed, a
    transcendental's is not (`e_not_fixed`: `cutThroughP (eulerCut 4) 3 1 ≠
    eulerCut 4 3 1`, witnessed by the probe `3/1 ↦ 7/4`).  φ is the twist's
    eigen-direction; e/π are moved by the two-axis braid.
  - `ProbeTwistDynamics.lean` — ★ *how* a non-φ cut wobbles: `twist_undoes_step`
    proves `cutThroughP (constCut (2p+q)(p+q)) = constCut p q`, i.e. the probe-twist
    runs the Pell recurrence **backwards** on the value (`f⁻¹`, expanding away from
    φ), the exact inverse of advancing the convergents (`f`, contracting toward φ).
    φ is the lone common fixed point `f(φ)=f⁻¹(φ)=φ`.
  - `ProbeTwistConic.lean` — ★ the *shape* the wobble traces: `Q_preserved` proves
    `Pstep` conserves the φ-norm `Q(m,k) = m²−mk−k²` (sign-free Nat form), so each
    orbit stays on its hyperbola `Q = N` (φ-convergents on `Q=−1`, the `(2,1)`-orbit
    on `Q=+1`, e's `(65,24)` on `Q=2089`).  `N` is the conserved orbit-label;
    φ the common asymptote (discriminant `5 = NS+NT`).
  - `SpiralRotationInvariant.lean` — ★ the rotation invariant conserved at **every** turn:
    `Q_iterate_preserved` — `Q(Pseq (m,k) n) = Q(m,k)` for all `n` (induct + `Q_preserved`,
    via the pure additive `add_cancel_chain`).  The golden form is the scale-invariant of
    the self-similar `P`-shift — the same form preserved identically at every iteration.

**Modulus + tower-native completeness + stratification** (narrative
`theory/math/analysis/{holonomic_modulus, tower_native_completeness}.md`):
  - `RateModulus.lean` — ★ the general "rate-carrying ⟹ total modulus `N=k+2`"
    generator (`rate_total_modulus`).  A monotone convergent cut `a_i/d_i` with a
    non-increasing margin (`Htel`, the rate certificate) completes; `Htel_of_crossdet`
    reduces the certificate to a *smallness law* on the cross-determinant
    `W_i = a_{i+1}d_i − a_i d_{i+1}` against the denominator's discrete growth — the
    bridge where the divergence ladder (`W`) meets the modulus generator.
  - `HolonomicReal.lean` — the `Holonomic`/`HolonomicReal` bundle (recurrence + Cauchy
    cut-sequence + valid limit); φ and e instances with constructed modulus.
  - `RateStratification.lean` — ★ the smallness law as a layer-by-layer **W-vs-d
    comparison**.  `Dominates W d i`; `htel_iff_dominates` upgrades `Htel_of_crossdet`
    from implication to *characterization* (`Htel` ⟺ domination at every layer);
    `dominated_free_modulus`; `overtake_breaks_layer` (the boundary); the unimodular
    det-1 floor (`W ≡ 1`, `T=[[2,1],[1,1]]`) is dominated against `d_i=(i+1)(i+2)`
    everywhere (`floor_dominates_all`) — the trivially-free bottom (`tower_stratification`).
  - `CrossDetOvertake.lean` — ★ completability boundary: `CrossDetSmall`, below ⟹ free,
    the double-exponential overtake break.  (Companion to `RateStratification`: the same
    W-vs-d boundary, presented as a `CrossDetSmall` predicate + double-exp witness.)
  - `LiouvilleModulus.lean` — ★ the Liouville constant's cross-determinant equals its
    denominator (`W=c^{k!}`), so it carries a free modulus — tame on this axis.
  - `CrossDetEqDenom.lean` — ★ the general `W=d` theorem behind both e and Liouville
    (`crossdet_eq_denom_total_modulus`); both reprove as one-liners.
  - `ReciprocalSeries.lean` — ★ the `W=d` line as a ratio-parametrized reference family:
    `Σ 1/d` reciprocal series from a ratio `g` (`recip_total_modulus`, free iff `g_i≳i`);
    e = linear-ratio point (`den (·+1) = factorial`).
  - `CrossDetConstDenom.lean` — ★ the `W=const` rung (`crossdet_const_total_modulus`) +
    φ (Fibonacci convergents `fib(2i+2)/fib(2i+1)`) as its named instance, through the
    same bridge as e/Liouville.
  - `GeometricThreshold.lean` — ★ the exact growth-rate boundary: geometric `W=r^i`
    over `d=q^i` is free **iff** `r < q` (`geom_boundary_iff`).
  - `PresentationDependence.lean` — ★ `CrossDetSmall` reads the representation, not the
    real: `rcut` is rescaling-invariant (`rcut_rescale`) while the smallness condition
    is not (e's `×2` representation breaks it — same real).
  - `IntensionalCompletability.lean` — ★ the intensional reduction: the bridge
    `CrossDetSmall` is antitone under rescaling (`crossDetSmall_rescale_antitone` —
    rescaling up only loses it, so the gcd-reduced presentation is canonical), while the
    *completion* is presentation-invariant (`modulus_rescale_invariant`).  The test is
    presentation-relative; the truth (the cut's completion) is not
    (`completability_is_intensional`).
  - `ScalingOrbit.lean` — ★ the rescaling orbit `(c·a, c·d)` of a presentation: a monoid
    action (`scaleBy_one`/`scaleBy_comp`) inside one cut (`scaleBy_preserves_cut`), with
    `CrossDetSmall` antitone along it (`orbit_free_implies_base_free`) and a unique
    `Reduced` base (`reduced_scaling_trivial`) — the canonical point to read the cut's
    rung (`scaling_orbit_structure`).
  - `FloorReferenceForm.lean` — ★ the det-one floor's reference form is **indefinite**:
    the golden `Q = m²−mk−k²` (`ProbeTwistConic.Q_preserved`, the P-orbit invariant) takes
    both signs (`golden_indefinite`, `Q(2,1)=+1`, `Q(1,1)=−1`) → unbounded hyperbolic
    orbits → convergent line → the completing bottom rung (`floor_reference_is_indefinite`).
    The completability-side (disc+5, line) complement of `EisensteinSignature` (disc−3,
    curve).
  - `TowerNativeCompleteness.lean` — ★ `tower_native_completeness_program`, the five
    pieces (boundary, Liouville, closure, generator, residue) bundled.

**Markov spectrum + modular-geodesic** (narrative
`theory/math/analysis/markov_uniqueness.md` +
`theory/essays/p_orbit/the_modular_geodesic_lens.md`):
  - `MarkovTree.lean` / `MarkovUniqueness.lean` / `MarkovInjectivity.lean` —
    the Markov-number tree, the uniqueness statement, and the injectivity
    reading (`markovNum` injective ⟺ `MarkovMaxUnique`).
  - `SternBrocotMarkov.lean` — ★ the Stern-Brocot ⟷ Markov bridge: size
    reading strictly monotone under descent (§30), slope determines size
    (§32), the forward + reverse bridges closing the iff
    (`markovMaxUnique_iff_markovNum_injective`, §33–§34), and the orbit-
    realizability kernel `H` (`OrbitRealizabilityH`).
  - `Continuant.lean` — Euler continuants `K[a₁..aₙ]` + monotonicity (the
    Aigner core tool for the continuant/Markov program).
  - `ModularGeodesicLens.lean` — ★ the geodesic engine as a Raw-Lens:
    `mediantLens` + `mediantLens_view_reachable` (mediant-Lens view ⊆
    `SternBrocotReachable`, ∅-axiom) — the residue read at `ℍ/PSL(2,ℤ)`.

## Architecture notes

- Real = (sequence + modulus) pair — type-level form of Cauchy completeness.
- Cut = `Nat → Nat → Bool` (m, k ↦ "value ≤ m/k").
- Real213 marathon: ~90% PURE — most CutSum/CutMul/Lattice
  paths propext-free via pointwise eq + ChainToCut bridge.

PURE 진행: see STRICT_ZERO_AXIOM.md.
