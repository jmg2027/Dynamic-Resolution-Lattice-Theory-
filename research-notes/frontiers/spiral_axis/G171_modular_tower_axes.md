# G171 — the axis/lattice/shape/constant tower (SL(2)→PSL→SL(3); e→π→ζ(3))

**Tier 1 (volatile).**  Records a proposed correspondence table and an honest assessment of
which rows are proven (in this repo), which are a real pattern, and which are speculative.

## The proposed table

| axis layer | dominant lattice group | algebraic shape | 213-native state transition |
|---|---|---|---|
| 2-axis plane | `SL(2,ℤ)` | **Line** | `W = d` linear-engine irreducible-unit passage (e) |
| 2-3 cycle | `ℤ₂ * ℤ₃` | **Circle** (π) | 6-period rotation-kernel closure of the 2D lattice (π) |
| 3-axis space | `SL(3,ℤ)` | **Sphere / 3-manifold** | knot-volume equilibrium under ternary-factorial dominance (ζ(3)) |

## Verdict: rows 1–2 are proven here; the constant column is a real pattern; row 3 is partly speculative.

### The spine (rows 1–2) = what the repo already closed

Decisive classical fact: **`ℤ₂ * ℤ₃ ≅ PSL(2,ℤ)`** (the modular group).  Verified ∅-axiom in
`Real213/ModularElliptic` (`modular_generator_orders`): the elliptic generators
`S = [[0,−1],[1,0]]` (`S² = −I`, `S⁴ = I`, **order 4**) and `U = [[0,−1],[1,1]]`
(`U³ = −I`, `U⁶ = I`, **order 6**), `det = 1`.  Then:

  - order **4 = |ℤ[i]^×|** (Gaussian, the `i`-point), order **6 = |ℤ[ω]^×|** (Eisenstein, the
    `ω`-point) — exactly the spiral **axis `{4,6}`** (`ImaginaryQuadraticUnitTrichotomy`);
  - central **`−I` = the "binary" 2 (the Cassini sign)**; mod `±I` the orders are `2, 3`,
    the free factors of `ℤ₂ * ℤ₃ = PSL(2,ℤ)` — i.e. `axis_binary_cover`'s `{4,6} = 2·{2,3}`
    and the crystallographic restriction `{1,2,3,4,6}`;
  - `U³ = −I` (period 6) = `EisensteinCompletion.eisenstein_floor_rotation` = π's depth 6
    (`DepthPiQuartic`).

So **row 2 (2-3 cycle, `ℤ₂*ℤ₃`, π, 6-period) is the modular group's elliptic skeleton = the
spiral axis.**  Row 1 (line, e) is the *hyperbolic* regime: `disc > 0` (golden/Pell, real,
non-compact line, e/√5), CF convergents in `SL(2,ℤ)` (`det = W = ±1 = cf_det_sq`), e's `W=d`
linear engine, depth 3.

**Precise refinement.**  Rows 1–2 are **not two different groups in two dimensions** — they
are `SL(2,ℤ)` (hyperbolic, line) vs its central quotient `PSL(2,ℤ) = ℤ₂*ℤ₃` (elliptic,
circle), related by the central `−I` (the binary 2-fold cover).  "Line vs circle" is the
**discriminant-sign dichotomy** already closed in `two_engines_one_map` /
`disc_sign_is_field_type`: `disc>0` hyperbolic/real/growing (e, golden) vs `disc<0`
elliptic/periodic/compact (π, Eisenstein, `M³=−I`).

### The constant column e → π → ζ(3) = a real depth/dimension tower

`e` (`Σ 1/n!`, linear recurrence, divergence depth 3) → `π` (`≈ ζ(2) = π²/6`, depth 6) →
`ζ(3)` (Apéry).  `π ↔ ζ(2)` is the right identification (Apéry/Beukers proved `ζ(2), ζ(3)`
irrationality by the same kind of P-recursions).  This is the "1,2,3-dimensional" zeta tower.
Solid as a pattern.

### Row 3 (`SL(3,ℤ)`, 3-manifold, knot volume, ζ(3)) — honest split

  - `ζ(3)` = the degree-3 zeta (Apéry irrationality) — **solid**;
  - `ζ(3) ↔` hyperbolic 3-manifold volume — **genuine thread**: ζ(3) is the Borel regulator
    of `K₃(ℚ)`, and 3-manifold volumes live in the Bloch group / dilogarithm; but
    "knot-volume equilibrium" is **poetic, imprecise**;
  - `SL(3,ℤ)` — plausible dimensional lift of `SL(2,ℤ)`, but **unbuilt** here (repo is 2D:
    `P`-matrix, `K_{3,2}`) — **speculative**;
  - "ternary factorial" — e is factorial (order-1 recurrence); Apéry's ζ(3) recurrence has
    `n³` (cubic) coefficients, so its divergence depth would be higher than π's 6.

**Meta-principle caution:** row 3 imports more than it earns (`SL(3,ℤ)`, "knot equilibrium"
are forcible maps).  Keep `ζ(3)/Apéry` and the Borel-regulator/volume thread; flag `SL(3)` and
knot-equilibrium as conjecture.

## Buildable next rung

`ζ(3)`'s divergence depth via the **Apéry recurrence**
`n³ aₙ = (34n³ − 51n² + 27n − 5) aₙ₋₁ − (n−1)³ aₙ₋₂` — the `DepthPiQuartic` analog (π depth
6) for the 3-axis, completing the depth tower **e = 3 → π = 6 → ζ(3) = ?**.  This makes the
"constant + depth" of row 3 precise and drops the speculative `SL(3)`/knot parts.

## Lean anchors (this note's solid content)

- `Real213/ModularElliptic.modular_generator_orders` — `S` order 4, `U` order 6, `det 1`;
  `PSL(2,ℤ) = ℤ₂*ℤ₃`, the `{4,6}` axis with `−I` central.
- `ImaginaryQuadraticUnitTrichotomy.axis_binary_cover` — `{4,6} = 2·{2,3}`, midpoint `−1`.
- `CayleyDickson/Tower/SpiralAxisCrystallographic` — `{2,4,6}` = even half of `{1,2,3,4,6}`.
- `two_engines_one_map`, `disc_sign_is_field_type` — line (hyperbolic) vs circle (elliptic).
- `DepthPiQuartic.piRatio_polyDepth` — π depth 6; `DivergenceDepth` — e depth 3.
