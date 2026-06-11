# ζ(3): from the built fold to the free (constructed) total modulus

**Status**: blueprint complete — see `zeta3_blueprint.md` (both bricks verified; formalization plans only, no open mathematics).  The fold itself is **closed** —
`Real213/Zeta3Cut.lean` (35 PURE / 0 DIRTY) builds ζ(3)'s Apéry convergents as
an `AbCutSeq` (exact ℕ recurrence via the growth-invariant engine, closed-form
Casoratian `6·(m!)⁶`, bracket `601/500 < ζ(3) ≤ 1203/1000`, completion to a
`ValidCut` limit given a modulus).  What stays open is the **e-grade upgrade**:
a *constructed* total modulus (`holonomic_modulus.md` generator), making ζ(3) a
`HolonomicReal` with no convergence hypothesis — the π-posture → e-posture step.

## Why the built presentation cannot supply it (proved)

`Zeta3Cut.zeta3_presentation_overtakes`: the factorial-cleared pair
`(zeta3Num, zeta3Den) = (aₙ·(n!)³, bₙ·(n!)³)` has cross-determinant
`aperyCasDet m = 6·(m!)⁶`, which overtakes the denominator quantum at layer 9
(`RateStratification.overtake_breaks_layer`) — the presentation is **rate-free**;
`htel_iff_dominates` says no `Htel` certificate exists for it.  Rate is a
property of the pointing, not the real
(`PresentationDependence.crossDetSmall_is_presentation_dependent`).

## The rate-carrying presentation and its exact cost

The reduced presentation has denominators `dₙ = 2·lcm(1..n)³·bₙ` (`bₙ` the Apéry
numbers `1, 5, 73, 1445, …`) and numerators `Aₙ = 2·lcm(1..n)³·aₙ ∈ ℕ`.  Its
tail is `~ α⁻²ⁿ` (`α = (1+√2)⁴ ≈ 33.97`) against gap quantum `1/(k·dₙ)`, and
`tail·k·dₙ ~ k·(lcm³/α)ⁿ → 0` because `e³ ≈ 20.1 < α`.  The two classical
arithmetic inputs, both unformalized here:

1. **Numerator integrality** — `2·lcm(1..n)³·aₙ ∈ ℕ`, where
   `aₙ = Σₖ C(n,k)²C(n+k,k)²·(Σ_{m≤n} 1/m³ + Σ_{m≤k} (−1)^{m−1}/(2m³C(n,m)C(n+m,m)))`.
   The binomial-divisibility core of Apéry's proof.
2. **The lcm bound** — `lcm(1..n) < 3ⁿ` (Hanson 1972; any bound `< α^{1/3} ≈ 3.236`
   per step works).  Elementary but a genuine formalization project
   (multinomial / primorial route).

Supporting (easy once 1–2 exist): `bₙ ≥ 32ⁿ`-type growth from the recurrence
(the `Zeta3Cut` growth invariant already gives `bₙ₊₁ ≥ (n+1)³·…`-style bounds;
a geometric lower bound is a small variant), then `Htel` via
`RateModulus.Htel_of_crossdet` on the reduced cross-determinant
`Wₙ = 6·(2·lcm(1..n)³)²/n³·…` smallness, and `rate_total_modulus` instantiates.

## The clearing-growth criterion (why the two bricks are necessary)

For ANY series pointing `Σ pₙ/qₙ` cleared over denominators `Dₙ` with integer
ratios `ρₙ₊₁ = Dₙ₊₁/Dₙ`, the cleared increment is `eₙ₊₁ = pₙ₊₁·Dₙ₊₁/qₙ₊₁`, the
cross-determinant is `Wₙ = eₙ₊₁·Dₙ`, and the smallness condition collapses to

  `i(i+1)·eᵢ₊₁ + i ≤ (i+1)·ρᵢ₊₁`   ⟺ roughly  **`qₙ₊₁ ≳ n·pₙ₊₁·Dₙ`** —

the next term-denominator must beat (index) × (numerator) × (running clearing).
Consequences (each verified exactly):
  * **Engel-type series pass**: `Σ 1/(q₁⋯qₙ)` with `qᵢ ≥ i` has `e = 1`,
    `W = Dₙ`, condition `i²+2i ≤ (i+1)qᵢ₊₁` — this is exactly why `exp(1/q)`
    (`qᵢ = iq`) carries the free modulus (`expUnitCauchySeq`), and why
    `exp(p/q)`, `p ≥ 2` fails (`e = pⁿ⁺¹` exponential vs linear steps —
    `exp_pq_no_htel`).
  * **`ζ(s)` defining series fail by factorial margin**: over the product
    clearing `Dₙ = (n!)ˢ` the increment is `e = (n!)ˢ⁻⁰·…/(n+1)ˢ = Dₙ` (NOT 1 —
    `1/kˢ` is not Engel), so `W = Dₙ²` and the condition needs
    `(n+1)ˢ ≥ n·Dₙ` — hopeless.  (A first-glance "the e-pattern applies to
    `Σ1/n³` verbatim" is a trap: the `+1` of the exp recursion is `+Dₙ` here.)
  * **The only window is quasi-polynomial clearing**: `Dₙ` must grow slowly
    enough that `qₙ₊₁ ≳ n·Dₙ` stays satisfiable while still clearing all
    denominators — i.e. `Dₙ = lcm`-type (the holonomic_modulus ladder's
    quasi-polynomial rung), which for ζ(3) forces exactly the two classical
    bricks: numerator integrality (`2lcm³aₙ ∈ ℕ`) and the lcm growth bound
    (Hanson `< 3ⁿ`, budget `< α^{1/3} ≈ 3.236`).  They are not artifacts of
    Apéry's route — every series-type presentation needs them.

Both bricks now have complete verified proof blueprints — `zeta3_blueprint.md`:
brick 1 via a finitized Chebyshev 30-block recursion (`c = √10 < 3.236`; Hanson
rejected — sub-0.5% margin, unbounded Sylvester tail), brick 2 as pure
divisibility chains with no p-adic theory (trinomial double identity + KeyDiv
via the finite-difference witness).

## Payoff when closed

`zeta3HolonomicReal : HolonomicReal` — ζ(3) joins φ and e in the unconditional
real API; the saved-correction chain ("weight-4 Eisenstein atom = ζ(3) =
holonomic = constructible cut") closes end-to-end at the e-grade, and the
modular-period thread's analytic atom is a fully constructed object.

## Pointers

- Built side: `lean/E213/Lib/Math/NumberSystems/Real213/Zeta3Cut.lean`
- Generator: `RateModulus.rate_total_modulus`, `RateStratification.htel_iff_dominates`
- Narrative: `theory/math/analysis/holonomic_modulus.md` (§4 frontier)
- Period-thread context: `residue_expression_atlas.md` (this directory),
  "Correction (it is a fold, not the residue)"
