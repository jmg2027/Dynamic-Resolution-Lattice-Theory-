# The modulus-degree ladder — grading "completes" beyond the binary

**Question that opened this** (originator, 2026-06-10): what happens at modulus
degree 2, 3, … — `W ~ N(m,k)²`, `N(m1,k1)×N(m2,k2)`, or other shapes?

**Status**: the algebraic pillar is **closed** at degrees 2 and 3; the graded
transcendental generator and the two-real separation modulus are **open**.

## The conversion law (the frame)

A total cut modulus is always `N(m,k) = rate⁻¹(distance(m,k))` — a distance
lower bound composed with the inverse convergence rate.  The "degree" of the
modulus is the growth class of `N` in `k`, and it factors as
(degree of the distance certificate) / (rate exponent of the pointing).

## Closed (the algebraic pillar)

- **Degree 2** — φ: the form `m²−mk−k²`, `|Q| ≥ 1`; closed-form cut
  (`PhiAsCut.masterCut`), and the squared comparison `4k² < b²` in
  `FibCassiniNat.qb_lt_pk` is the `ε·k² < d²` schema instance.
- **Degree 3** — ∛2 (`Real213/CubeRootTwoCut`, 31 PURE): side-decision reduces
  to the all-additive `ε_i·k³ < d_i³`; the `Nat` strictness `+1` *is* the form
  margin `|m³−2k³| ≥ 1`.  Dyadic bisection presentation ⟹ total modulus
  `N(m,k) = 3k+5`; the completed fold **equals** the frozen form cut
  (`cbrt_limit_eq_form`).  Key structural reading: the algebraic degree enters
  as the **probe exponent `k^s` in the schedule**, and the form makes the
  modulus presentation-robust — *any* presentation with a cube-slack rate
  completes.  The rate race (`W` vs `d`, `holonomic_modulus.md`) and its
  presentation-dependence (`Zeta3Cut.zeta3_presentation_overtakes`) are the
  transcendental-only regime.

## Open rungs

1. **Graded rate generator** — refine the binary `Dominates`
   (`RateStratification`) with polynomial slack: `Dominates_s` forgiving an
   `i^{s−1}` factor of overtake, generalizing `rate_total_modulus` to
   `N(m,k) = k^s + 2`.  Makes "rescue" graded the way `CompletabilityGrade`
   already grades "break" (lex `(height, rate)` ordinal) — the two axes become
   symmetric.
2. **Conditional measure-modulus schema** — `effective measure μ + Cauchy rate
   ⟹ constructed N`.  Instance: Wallis-π with `μ(π) ≤ 7.11` would carry a
   degree-≈7 modulus; the formalization cost of the measure is thereby isolated
   in one hypothesis.  (π moves from "hypothesis modulus" to "conditional
   degree-7 modulus".)
3. **Two-real separation modulus** — the genuine `N(m1,k1)×N(m2,k2)` object:
   deciding `x ≤ y` for two folds needs a joint `|x−y|` lower bound.  The
   one-probe gap quantum `1/(k·d_i)` is already bilinear (probe × convergent,
   the Farey/Stern-Brocot `det = ±1`); the two-fold version is new machinery
   (`cutLe` currently sidesteps it).
4. **Higher algebraic instances** — degree-4+ form cuts (e.g. `√2+√3`,
   `x⁴−10x²+1`), and the cubic-unit narrative: at degree 2 the binary form
   carries an infinite unit orbit (Pell, `W ≡ 1` floor); at degree 3 the binary
   slice of the rank-1 unit orbit is finite (Thue/Delaunay–Nagell — hard), the
   orbit needing the full rank-3 lattice.  Why the self-similar P-orbit story
   does not lift to degree 3 as binary dynamics.

## The 213 reading

The fold/residue correction refines from a dichotomy into a **filtration**:
modulus degree = how many receipts the pointing carries (0 = the form is the
cut; 1 = the rate is its own receipt; s = receipt-of-receipt; no finite degree
= toward reached-by-none).  Residue-lint: this is a Lens-grading of
*pointings*, not an ontological stratification of the residue — the residue
sits in no rung; the ladder classifies the ways of pointing at it.

## Pointers

- Closed: `lean/E213/Lib/Math/NumberSystems/Real213/CubeRootTwoCut.lean`,
  `PhiAsCut`/`FibCassiniNat` (degree 2), `holonomic_modulus.md` (degree-1 class)
- Break-grading: `CompletabilityGrade`, `RefinedCompletabilityEngine`
- ζ(3) companion frontier: `zeta3_free_modulus.md`
