# G169 — Spiral-coordinate classification of reals (multi deep-research + ∅-axiom build)

A finer classification of reals than algebraic/transcendental, conjectured by Mingu Jeong
as a "layered spiral" (층/나선/축/잉여).  Four parallel deep-research threads (literature +
repo) grounded it, with two honest corrections.  Built ∅-axiom on `claude/goal-g166-A6MVE`.

## The two orthogonal count-coordinates (the proven core)

A real — more precisely a **holonomic presentation** of one — sits at:

1. **LAYER = divergence depth** ∈ `ℕ ∪ {∞}` (`Cauchy/DivergenceLadder…`): lifts
   (cross-det → ratio → finite differences) to a constant floor.  φ 1, e 3, π 6,
   Liouville ∞.
2. **AXIS = arithmetic unit-group order** ∈ **exactly `{2,4,6}`** (`ℤ`, `ℤ[i]`, `ℤ[ω]`):
   the order of `R^×` for the ring carrying the cut's approximation.

These are **orthogonal** and both are 213-native counts.  Residue = layer `∞` + the
top-less tower (`DepthCeilingResidue`).

## Honest corrections (research overturned two of my framings)

- **Triangular `{1,3,6}` is a coincidence.**  `depth = 2 + deg(cross-det ratio polynomial)`;
  the degree is any `d ≥ 0`, so the depth spectrum is all of `ℕ ∪ {∞}` (depths 2, 4, 5
  occupied by geometric / Bessel `I₀(2)` / Apéry `ζ(3)`-class constants).  φ/e/π land on
  1/3/6 because their ratio-degrees are 0/1/4 — *not* triangular.  Selection, not law.
  (`SpiralLayer.depth_spectrum_unrestricted` proves every depth is realized.)
- **Depth is intensional (presentation-dependent), not a property of the bare real.**  The
  *regular* continued fraction has cross-det `≡ ±1` for **every** real (`cf_det_sq`,
  depth 1) — the depths 3/6 live in the *series* presentations (e: factorial; π: Wallis).
  So the layer classifies the holonomic representation; the bare real is the gauge orbit
  (matches `IntensionalCompletability`).  (`SpiralLayer.depth_is_intensional`.)

## Research findings (cited)

- **Depth ⊥ Mahler/Koksma/μ.**  Mahler puts e and π **both in S**; μ puts both at 2.  *No*
  approximation-quality invariant separates e from π.  The only classical axis that does is
  **continued-fraction holonomicity** (e patterned `[2;1,2,1,1,4,…]`, π irregular) — and our
  depth (e 3 < π 6) rides exactly that axis.  "rate-carrying vs rate-free" = "holonomic CF
  vs non-holonomic CF"; π's CF non-holonomicity is *observed, not proven* (open).
  (Bugeaud; Roth; Zeilberger–Zudilin μ(π)≤7.103; Cohn arXiv:math/0601660.)
- **Unit-group orders exactly `{2,4,6}`.**  Dirichlet: imaginary-quadratic unit group is
  finite (= roots of unity); `φ(m) ≤ 2 ⇒ m ∈ {1,2,3,4,6}` ⇒ orders `{2,4,6}`, with 4,6
  pinned to `ℚ(i)`, `ℚ(√−3)`.  (Built: `ZIUnits` 4-theorem mirroring `ZOmegaUnits` 6-theorem.)
- **Complex CF convergence is conditional** (Hurwitz `|aₙ| ≥ √2` + admissibility /
  forbidden blocks; Dani–Nogueira), unlike the unconditional real case (any `aᵢ ≥ 1`).  This
  confirms G168: the real line (2-axis) is the only *unconditionally*-completing axis; the
  Eisenstein real-slice embeds (`eisenstein_real_slice_completes`).
- **Cross-det cycles the full unit group only with a unit-coefficient recurrence.**  The
  canonical CF cross-det is `(−1)ⁿ ∈ {±1}` in every ring; the full `R^×` rotation needs
  `q` a primitive unit (my `omegaFib`, `q = ω`, period 6 = `eisenstein_floor_rotation`).
  Honest: this is a specific algebraic recurrence, not the canonical Hurwitz CF.
- **CM-period shadow per axis** (Chowla–Selberg, `w` = unit order in the exponent):
  `Γ(1/2)~π` (boundary) / `Γ(1/4)` (disc −4) / `Γ(1/3)` (disc −3).  Single-`Γ` collapse is
  exact only for the small-disc `h=1` cases — our three axes.

## Built (∅-axiom, all PURE)

- `Real213/SpiralLayer.lean` (2): `depth_is_intensional`, `depth_spectrum_unrestricted`.
- `CayleyDickson/Integer/ZIUnits.lean` (6): the Gaussian 4-theorem (`ZI_units_exact_four`).
- `CayleyDickson/Integer/GaussianCrossDet.lean` (11): `gaussian_floor_rotation` — the ℤ[i]
  floor rotates with order 4 (`q = i`, `μ = −i`), the middle rung; the axis spectrum
  `{2,4,6}` is now geometrically realized at all three orders (2 = `W=±1`, 4 = `−i`,
  6 = `−ω`).
- `Real213/SpiralCoordinate.lean` (1): `spiral_coordinate` — the two orthogonal counts
  (layer intensional + unrestricted, axis spectrum `{2,4,6}`), bundled.

## Open frontier

- π's continued-fraction non-holonomicity (would make "π is rate-free" a theorem, not an
  observation).
- Whether the layer and axis counts have a common origin in the `(NS,NT)` atomic structure,
  or are genuinely independent (current evidence: independent — layer spectrum `ℕ`, axis
  spectrum `{2,4,6}`).
