# G172 — three Lagrange/Markov threads (Stern-Brocot, φ/π extremes, Hurwitz cosines)

**Tier 1 (volatile).**  Working note for three approximation-spectrum threads off the Markov
arc (`theory/math/analysis/markov_spectrum.md`).  ∅-axiom anchors built; deeper connections
recorded.

## Thread A — Markov tree ↔ Stern-Brocot (conceptual; anchor partial)

The Markov tree (triples of `x²+y²+z²=3xyz` under Vieta jumping, `MarkovTree`) and the
Stern-Brocot tree (rationals via mediants) are **the same binary tree**: Markov numbers are
classically indexed by rationals `p/q ∈ (0,1)` / by the Stern-Brocot tree, i.e. by words in
the two mediant matrices `L = [[1,0],[1,1]]`, `R = [[1,1],[0,1]]` (which generate the monoid
inside `SL(2,ℤ)` whose elliptic completion is `PSL(2,ℤ) = ℤ₂*ℤ₃`, `ModularElliptic`).

Repo handle: `Mobius213SternBrocot.sternBrocotEq` (mediant closure of `(0,1),(1,0)`),
`Cohomology/BipartiteStermBrocotClassification.k32_sternBrocot_position`.  Both Markov-Vieta
(`markov_vieta`) and Stern-Brocot are binary branchings on `SL(2,ℤ)` data; the two principal
Markov spines are the repo's **Fibonacci** (`markov_fibonacci_branch`, the `LL…`/golden side,
`√5`) and **Pell** (`markov_pell_branch`, the `RL…`/silver side, `√8`) — exactly the two
extreme Stern-Brocot spines (`0/1 → 1/n` and `1/1 → n/1`).  **Open**: a clean ∅-axiom bijection
`Markov triples ↔ Stern-Brocot rationals` needs the L/R-word indexing; the spines are anchored,
the full indexing is the continuation.  (Famous *Markov uniqueness conjecture* = injectivity of
this indexing — classically open.)

## Thread B — φ/π extremes (∅-axiom anchor: `Real213/ModularGeometry/LagrangeExtremes`)

The two poles of the spectrum, in 213-native terms:

  - **φ = the floor.**  CF `[1;1,1,…]` = the all-`1`s sequence: `phi_cf_periodic`
    (`Periodic 1`), `phi_cf_quasipoly` (`QuasiPolyCF 1`, the simplest Hurwitzian, tier 0),
    `phi_pq_minimal` (partial quotients pointwise `≤` every valid CF — the constant-`1`
    floor).  Minimal partial quotients ⟹ slowest denominators (`cfQn_fib` lower bound
    attained, `qₙ = fibₙ`) ⟹ worst-approximable; and `golden_min_attained_on_fib`
    (`Q(fib(2n+2),fib(2n+1)) = −1`) gives the `W=±1` floor = Markov value `√5`.  Bundled in
    `phi_is_spectrum_floor`.
  - **π = the opposite pole.**  Partial quotients unbounded (`[3;7,15,1,292,…]`, `a₄=292`,
    later `20776`): large quotients ⟹ exceptionally good rational approximations ⟹ Lagrange
    value pushed up (conjecturally `λ(π)=∞`).  Where φ has every `aᵢ=1` (tightest), π has no
    bound.

Same spiral coordinate, two readings: φ/π are opposite extremes of the *approximation* axis
(minimal vs unbounded partial quotients) exactly as they are of the *CF-holonomicity* axis
(periodic tier 0 vs conjecturally non-Hurwitzian).

## Thread C — Hurwitz `2cos(2π/n)` ↔ crystallographic (∅-axiom anchor: `crystallographic_cosines`)

`2cos(2π/n)` is an algebraic integer of degree `φ(n)/2`; it is a *rational* integer iff
`n ∈ {1,2,3,4,6}` (the crystallographic / `CyclotomicTraceDegree.crystallographic_restriction`
set).  `ImaginaryQuadraticUnitTrichotomy.crystallographic_cosines`: the Eisenstein-trace
`ztrace u = 2·re − im` (`= u + conj u`) of the order-6 unit powers `ζ₆¹..ζ₆⁶` is
`1, −1, −2, −1, 1, 2` — exactly `2cos(2πk/6)`.  So the **order-6 axis (π/circle, Eisenstein)
carries the full integer cosine spectrum `{2,1,−1,−2}`**, the trace-reading of the `{2,4,6}`
unit axis (`axis_binary_cover`).

Deeper (not built): the Hecke groups `H(λ_q)`, `λ_q = 2cos(π/q)`, have their own Lagrange
spectra; `q ∈ {3,4,6,∞}` are the arithmetic/crystallographic Hecke groups (`λ = 1, √2, √3, 2`),
tying the `2cos` values to the spectrum structure — the continuation of thread C.

## ∅-axiom anchors added (this note)

- `Real213/ModularGeometry/LagrangeExtremes` (4 PURE) — φ as the minimal-CF spectrum floor.
- `ImaginaryQuadraticUnitTrichotomy.{ztrace, crystallographic_cosines}` — the crystallographic
  integer cosines as Eisenstein traces.
- (pre-existing, reused) `markov_fibonacci_branch`, `markov_pell_branch` (Stern-Brocot spines),
  `golden_min_attained_on_fib`, `modular_generator_orders`, `crystallographic_restriction`.
