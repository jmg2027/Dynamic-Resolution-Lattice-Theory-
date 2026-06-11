# Async growth ↔ merged main — cross-domain insights

Branch: the asynchronous growth arc
(`theory/math/foundations/async_growth.md`).  Main brought in: the
discrete-curvature / Lichnerowicz spectral arc, the primitive-root /
multiplicative-order + LTE arc, and the Cauchy–Schwarz
certificate-depth essay.  Three bridges, ranked by buildability.

## 1. LTE two ways: index-LTE vs orbit-LTE (buildable comparison)

Main's Fibonacci arc closed the lifting-the-exponent law
`ν₅(F_n) = ν₅(n)` — one 5-adic digit per index-multiplication at the
ramified prime of `ℚ(√5)`.  The census tower has the *orbit*
analogue, machine-verified in the debate and partially closed:

  - mod 5: attracting 3-cycle, `v₅(T(n+3) − T(n)) = ⌊(n+1)/3⌋ + 1`
    — one 5-adic digit per cycle (`rawCount_mod5_cycle` is the
    digit-0 layer; the valuation law is open);
  - mod 7^k: parabolic translation, period `7^(k−1)` — the additive
    shadow of the same "one digit per period" phenomenon;
  - mod 2^k: expanding (`|f'|₂ = 2`), no periodicity — the LTE
    regime *fails* exactly where the multiplier is a unit.

Insight: LTE is not about Fibonacci or about quadratic maps — it is
the statement "the multiplier at the cycle is divisible by p", read
once on an index action (main) and once on an orbit map (branch).
*Buildable first brick*: `v₅(rawCount (n+3) − rawCount n) ≥ 1` for
all n (the mod-5 cycle already gives it — one subtraction lemma),
then the exact `⌊(n+1)/3⌋ + 1` law as the orbit-LTE theorem.

## 2. The growth order as a curvature carrier (conceptual, checkable)

Main's curvature arc puts Forman edge curvature and Laplacian
spectra on graphs; its crossdomain note already flags `K_{3,2}` as
carrying both a golden (`a+b = 5`) and a curvature signature.  The
branch supplies the *canonical* graph family these could live on:
the Hasse diagram of the ancestor order, depth-graded, with the
past-completeness boundary at depth 2 (`depth3_boundary`).
Question: does Forman curvature of the depth-≤n Hasse diagram see
the boundary — e.g. a sign change or extremum at the depth-2 layer,
where the census is 5 and the contrast graph reads 5 − 1 = 4?
*Checkable*: the depth-≤3 diagram is 12 vertices; `formanEdge` from
main's `DiscreteRicci` applies as-is.

## 3. Certificate depth of the census squeeze (observation)

Main's essay reads Cauchy–Schwarz instances by the depth of their
positivity certificate.  The census sandwich
(`census_step_lower/upper`) is depth-0 in exactly that sense: both
squeeze steps are one Lagrange-square completion away from the
doubled identity `2·T(n+1) + T(n) = T(n)² + 4` (over ℤ:
`8T(n+1) = (2T(n)−1)² + 15`).  The growth constant
`K = 1.24602…` is then an Aho–Sloane orbit constant whose
*existence* needs only the depth-0 certificate — a small instance
of "inequality = POSITIVITY ∘ LOOP" from main's
`inequalities_positivity_fold_crossdomain` board.
