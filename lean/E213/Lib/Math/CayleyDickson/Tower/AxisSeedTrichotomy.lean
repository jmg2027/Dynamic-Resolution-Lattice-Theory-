import E213.Lib.Math.CayleyDickson.Integer.ZOmega
import E213.Lib.Math.CayleyDickson.Tower.TraceDoublingMap

/-!
# The three axes and their algebraic correspondences

A question (parallel branch): viewing the reals through their *algebraic
correspondences*, `e ↔ 1` (the unit) and `π ↔` the unit circle.
213-native: `e` is the unit of the `2`-axis; `π` is the residue of the
`2-3-2-3` spiral.  Then **what is the `3`-axis real value and its
algebraic correspondence?**

The marathon framework answers the *algebraic* half exactly.  The three
atomic quantities `{NT, NS, NS+NT}` index three axes, and each carries a
seed `√(radicand)`, an algebraic number, a minimal polynomial, and a
dynamical type under the trace-doubling map `D(x) = x² − NT`:

| axis    | radicand | algebraic number | min poly      | `D`-type             | rung |
|---------|----------|------------------|---------------|----------------------|------|
| `2`     | `NT`     | `√2` (bare surd) | `x² − NT`     | even fixed `+2` (unit) | `E₇` |
| `3`     | `−NS`    | `ω` (cube root 1)| `x² + x + 1`  | odd fixed `−1` (ord 3) | `E₆` |
| `2+3`   | `NS+NT`  | `φ` (golden)     | `x² − x − 1`  | hyperbolic escape (P)  | `E₈` |

So the **`3`-axis algebraic correspondence is `ω`** — the primitive cube
root of unity (Eisenstein), root of the cyclotomic `Φ₃ = x² + x + 1`,
seed `√(−NS) = √−3`, trace `ω + ω̄ = −1` (the *odd* fixed point of `D`,
dual to the unit's *even* fixed point `+2`).  Where the `2`-axis (`√NT`)
is the bare doubling `x² − NT` and the `2+3` spiral (`√(NS+NT) = √5`) is
the golden/hyperbolic `φ`, the `3`-axis is the Eisenstein `ω`: the
order-`3`, the `E₆` rung.

The minimal-polynomial discriminants are the *field* discriminants of
`Phase 19`: `x²−NT → 4·NT = 8`, `Φ₃ → −NS = −3`, `x²−x−1 → NS+NT = 5`.

## The transcendental half (interpretive)

The proven content above is the *algebraic* correspondence.  The
*real/transcendental* value the question gestures at — the analogue of
`e` (`2`-axis) and `π` (the `2-3` spiral) for the pure `3`-axis — is, by
the same CM/period ladder, the **equianharmonic (Eisenstein) period**: the
period of the `j = 0` elliptic curve with complex multiplication by
`ℤ[ω]` (a `Γ(1/3)`-value).  `e` is the multiplicative-group unit (`𝔾_m`,
the cusp), `π` the cyclotomic period (the circle), and the `3`-axis the
hexagonal-lattice period.  This file does not formalise the
transcendental layer (periods are not `∅`-axiom integer data); it pins the
algebraic skeleton it hangs on.
-/

namespace E213.Lib.Math.CayleyDickson.Tower.AxisSeedTrichotomy

open E213.Lib.Physics.Simplex.Counts
open E213.Lib.Math.CayleyDickson.Integer.ZOmega
open E213.Lib.Math.CayleyDickson.Tower.TypeOOctahedral
open E213.Lib.Math.CayleyDickson.Tower.TypeEIcosian
open E213.Lib.Math.CayleyDickson.Tower.TraceDoublingMap (Di)

/-- **`2`-axis — the bare surd `√NT`.**  `(√2)² = NT`; minimal polynomial
    `x² − NT` (no linear term); `D`-even fixed point `+2 = trace(unit)`;
    radicand `NT`.  The `E₇` rung. -/
theorem axis_two_bare :
    (ZRt2.mul ⟨0, 1⟩ ⟨0, 1⟩ - ⟨(NT : Int), 0⟩ = (⟨0, 0⟩ : ZRt2))  -- (√2)² − NT = 0
    ∧ (Di (NT : Int) = NT)                                          -- D-fixed: the unit, +2
    ∧ (4 * (NT : Int) = 8) := by decide                            -- min-poly disc = 4·NT (field disc)

/-- **`3`-axis — the Eisenstein `ω`, the algebraic correspondence.**
    `ω² + ω + 1 = 0` (`Φ₃`); `trace ω = ω + ω̄ = −1`, the `D`-odd fixed
    point; `normSq ω = 1` (a unit); radicand `−NS`; `Φ₃` discriminant
    `−NS = −3`.  The `E₆` rung. -/
theorem axis_three_eisenstein :
    (ZOmega.mul ⟨0, 1⟩ ⟨0, 1⟩ + ⟨0, 1⟩ + ⟨1, 0⟩ = (⟨0, 0⟩ : ZOmega))   -- ω²+ω+1 = 0
    ∧ ((⟨0, 1⟩ : ZOmega) + ZOmega.conj ⟨0, 1⟩ = ⟨-1, 0⟩)               -- trace ω = −1
    ∧ (Di (-1 : Int) = -1)                                             -- D-odd fixed point
    ∧ (ZOmega.normSq ⟨0, 1⟩ = 1)                                       -- unit
    ∧ ((1 : Int) ^ 2 - 4 * 1 = -(NS : Int)) := by decide               -- Φ₃ disc = −NS

/-- **`2+3` axis — the golden `φ`, the spiral.**  `φ² − φ − 1 = 0`;
    `D`-hyperbolic (escapes from `trace P = NS`); radicand `NS+NT`;
    discriminant `NS+NT = 5 = disc P`.  The `E₈` rung. -/
theorem axis_two_three_golden :
    (ZPhi.mul ⟨0, 1⟩ ⟨0, 1⟩ - ⟨0, 1⟩ - ⟨1, 0⟩ = (⟨0, 0⟩ : ZPhi))    -- φ²−φ−1 = 0
    ∧ (Di (NS : Int) = 7 ∧ (NS : Int) < Di (NS : Int))               -- D-hyperbolic escape
    ∧ ((3 : Int) ^ 2 - 4 * 1 = (NS : Int) + NT) := by decide         -- disc = NS+NT = disc P

/-- ★★★ **The axis trichotomy.**  The three atomic quantities
    `{NT, −NS, NS+NT}` are the radicands of the three exceptional seeds,
    realised as three algebraic numbers — the bare surd `√NT` (`2`-axis,
    `E₇`), the Eisenstein `ω` (`3`-axis, `E₆`), the golden `φ` (`2+3`
    spiral, `E₈`) — distinguished by their dynamical type under the one
    map `D(x) = x² − NT`: even fixed point, odd fixed point, hyperbolic
    escape.  The `3`-axis algebraic correspondence is `ω`. -/
theorem axis_seed_trichotomy :
    -- 2-axis: √NT, bare, even fixed point.
    ((ZRt2.mul ⟨0, 1⟩ ⟨0, 1⟩ - ⟨(NT : Int), 0⟩ = (⟨0, 0⟩ : ZRt2)) ∧ Di (NT : Int) = NT)
    -- 3-axis: ω, Eisenstein, odd fixed point, radicand −NS.
    ∧ ((ZOmega.mul ⟨0, 1⟩ ⟨0, 1⟩ + ⟨0, 1⟩ + ⟨1, 0⟩ = (⟨0, 0⟩ : ZOmega))
        ∧ Di (-1 : Int) = -1 ∧ (1 : Int) ^ 2 - 4 * 1 = -(NS : Int))
    -- 2+3 spiral: φ, golden, hyperbolic, radicand NS+NT.
    ∧ ((ZPhi.mul ⟨0, 1⟩ ⟨0, 1⟩ - ⟨0, 1⟩ - ⟨1, 0⟩ = (⟨0, 0⟩ : ZPhi))
        ∧ (NS : Int) < Di (NS : Int) ∧ (3 : Int) ^ 2 - 4 * 1 = (NS : Int) + NT)
    -- the three radicands are the atomic triple {NT, −NS, NS+NT}.
    ∧ ((NT : Int) = 2 ∧ -(NS : Int) = -3 ∧ (NS : Int) + NT = 5) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.CayleyDickson.Tower.AxisSeedTrichotomy
