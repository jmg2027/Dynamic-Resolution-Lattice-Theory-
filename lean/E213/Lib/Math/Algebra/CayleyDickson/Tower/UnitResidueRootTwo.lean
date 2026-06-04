import E213.Lib.Math.Algebra.CayleyDickson.Tower.ExceptionalTraceSeed
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI

/-!
# `√2` is the morphological residue of the unit itself

A question opened on the exception `E₇/√2`: `disc P` (the `5`-engine)
always yields `5 = NS+NT`, so it can never re-produce `√2`; the octahedral
seed appears only on the *diagonal* (as a trace) and as the field
discriminant `8`, never as `disc P`.  The intuition to test: **`√2` is a
residue of the unit / identity itself** — not of the Möbius `P`-orbit.

This file is the deep dive, and it confirms the intuition sharply.

## `√2 = √(trace of the unit)` — and uniquely so

In the scaled quaternion convention the identity is `1 = ⟨2,0,0,0⟩`, so
its trace (real coordinate) is `2 = NT`.  The order-`8` octahedral unit
`g₈` satisfies

  `trace(g₈)² = trace(1) = NT`            (`root_two_is_sqrt_unit_trace`)

— `√2` is the *bare square root of the unit's own trace*.  Crucially this
is **not** shared by `√5`: `trace(g₅)² ≠ trace(1)`
(`root_five_is_not_sqrt_unit_trace`).  Among the exceptional seeds, only
`√2` is the square root of the unit trace.  That is the precise sense in
which `√2` belongs to the unit and not to the `P`-orbit.

## The mechanism: the dyadic self-square-root tower of the unit

Why does it land exactly on `NT`?  Because `g₈` sits on the **2-power
tower of repeated square roots of the unit**:

  `1  →²  −1  →²  i  →²  g₈`     (orders `2⁰, 2¹, 2², 2³`)
  trace:  `2,  −2,  0,  √2`

`g₈² = i` (the order-`4` unit, trace `0`) and `g₈⁴ = −1` (trace `−2`).
So `g₈ = (−1)^{1/4} = √√(−1)`: the 4th root of the negative unit.  Its
trace-square is `trace(g₈)² = 2 + trace(g₈²) = 2 + 0 = 2 = NT`.  The seed
`√2` is the trace-shadow of halving the unit's distinction three times —
the pure `NT`-power (`2³ = 8`) doubling, which is exactly the
Cayley–Dickson doubling direction (each CD step adjoins a `√(−1)`).  `√5`
(order `5`, not a power of `NT`) is off this tower entirely.

## `√2 = |1 + i|` — the ramified prime, "unit + first distinction"

At the bottom CD layer `ℤ[i]` the magnitude reading is the same residue:

  `(1+i)² = 2i`,   `N(1+i) = (1+i)·conj(1+i) = 2 = NT`.

`2` *ramifies*: `(2) = (1+i)²`.  `1 + i =` unit `+` its first
distinction; its norm is `NT`, its magnitude `√2`.  Ramification is a
self-coincidence — the prime meeting its own conjugate — so `√2` is
literally the magnitude of the unit displaced by one distinction, the
square root of the ramified `NT = 2` (the count-Lens reading of the first
distinguishing).

## Bare vs golden: the minimal polynomial

`trace(g₈) = √2` satisfies `x² − NT = 0` — *no linear term*, a balanced
(bare) square root.  `trace(g₅) = φ − 1` satisfies `x² + x − 1 = 0` — the
golden polynomial *with* a linear shift, and `(φ−1)² = 2 − φ` is itself
irrational.  Among the seeds, `√2` is the unique one whose minimal
polynomial is `x² − (unit trace)`: the bare morphological residue.

**Synthesis.**  `E₇/√2` is not an external import nor an unanchored
accident: it is the unit's own residue under the Cayley–Dickson engine —
`√(trace 1)`, the trace of `(−1)^{1/4}`, `|1 + i|`, the bare `√NT`.  The
`P`-orbit (the `5 = NS+NT` engine) lives on a different residue, which is
why it cannot produce `√2`.  Two engines, two residues: `P` re-enters its
own `5`; the unit re-enters its own `√2`.  The exception is the diagonal
shadow of the identity.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Tower.UnitResidueRootTwo

open E213.Lib.Physics.Simplex.Counts
open E213.Lib.Math.Algebra.CayleyDickson.Tower.TypeOOctahedral
open E213.Lib.Math.Algebra.CayleyDickson.Tower.TypeEIcosian
open E213.Lib.Math.Algebra.CayleyDickson.Tower.ExceptionalTraceSeed
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI

/-- **`√2` is the square root of the unit's trace.**  `trace(g₈)² =
    trace(1) = NT`.  The identity quaternion `1 = ⟨2,0,0,0⟩` has trace
    `2 = NT`, and the order-`8` octahedral trace squares exactly to it. -/
theorem root_two_is_sqrt_unit_trace :
    octaTrace g8 * octaTrace g8 = (Octahedral.one).q0
    ∧ (Octahedral.one).q0 = (⟨(NT : Int), 0⟩ : ZRt2) := by decide

/-- **And uniquely so.**  `√5` is *not* the square root of the unit
    trace: `trace(g₅)² ≠ trace(1)`.  Only `√2` among the exceptional
    seeds is `√(trace 1)`. -/
theorem root_five_is_not_sqrt_unit_trace :
    icosTrace g5 * icosTrace g5 ≠ (Icosian.one).q0 := by decide

/-- **The dyadic self-square-root tower of the unit.**  `g₈² = i` (the
    order-`4` unit, trace `0`) and `g₈⁴ = −1` (trace `−2`): orders
    `2⁰,2¹,2²,2³`, traces `2, −2, 0, √2`.  `g₈ = (−1)^{1/4}`, so
    `trace(g₈)² = 2 + trace(g₈²) = 2 + 0 = NT`. -/
theorem dyadic_root_tower_of_unit :
    -- g₈⁴ = −1 (the unique order-2 element; trace −2).
    (g8 * g8 * g8 * g8 = ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩)
    -- g₈² = i (the order-4 unit): trace 0, imaginary coordinate NT.
    ∧ ((g8 * g8).q0 = (⟨0, 0⟩ : ZRt2) ∧ (g8 * g8).q1 = (⟨(NT : Int), 0⟩ : ZRt2)) := by decide

/-- **`√2 = |1 + i|`, the ramified prime over `NT`.**  In `ℤ[i]`:
    `(1+i)² = 2i` and `N(1+i) = (1+i)·conj(1+i) = NT`.  `2` ramifies as
    `(1+i)²`; `1 + i =` unit `+` first distinction, norm `NT`,
    magnitude `√2`. -/
theorem root_two_is_ramification :
    -- (1+i)² = 2i   (the square of "unit + first distinction").
    (ZI.mul ⟨1, 1⟩ ⟨1, 1⟩ = (⟨0, 2⟩ : ZI))
    -- N(1+i) = (1+i)·conj(1+i) = NT.
    ∧ (ZI.mul ⟨1, 1⟩ (ZI.conj ⟨1, 1⟩) = (⟨(NT : Int), 0⟩ : ZI))
    ∧ (ZI.normSq ⟨1, 1⟩ = (NT : Int)) := by decide

/-- **Bare vs golden.**  `trace(g₈) = √2` satisfies the *bare* polynomial
    `x² − NT = 0` (no linear term).  `trace(g₅) = φ−1` satisfies the
    *golden* polynomial `x² + x − 1 = 0` (with a linear shift), and
    `(φ−1)² = 2 − φ` is irrational.  `√2` is the unique bare
    square-root seed. -/
theorem bare_versus_golden :
    -- √2 : x² − NT = 0   (balanced, bare).
    (octaTrace g8 * octaTrace g8 - (⟨(NT : Int), 0⟩ : ZRt2) = ⟨0, 0⟩)
    -- φ−1 : x² + x − 1 = 0   (golden, linear term present).
    ∧ (icosTrace g5 * icosTrace g5 + icosTrace g5 - (⟨1, 0⟩ : ZPhi) = ⟨0, 0⟩)
    ∧ (icosTrace g5 * icosTrace g5 = (⟨2, -1⟩ : ZPhi)) := by decide

/-- ★★★ **`√2` is the morphological residue of the unit itself.**  It is
    `√(trace 1) = √NT` (uniquely among the seeds, `root_five_…` fails);
    the trace of `(−1)^{1/4}` on the dyadic `2`-power tower of the unit;
    the magnitude `|1 + i|` of the ramified prime over `NT`; and the
    unique *bare* square-root seed (`x² − NT`, no shift).  The `P`-orbit
    re-enters its own `5 = NS+NT`; the unit re-enters its own `√2`.  `E₇`
    is the diagonal shadow of the identity, which is exactly why the
    `P`-engine cannot reproduce it. -/
theorem unit_morphological_residue :
    -- √2 = √(trace 1) = √NT, and √5 is not √(trace 1).
    (octaTrace g8 * octaTrace g8 = (Octahedral.one).q0)
    ∧ (icosTrace g5 * icosTrace g5 ≠ (Icosian.one).q0)
    -- the dyadic tower: g₈⁴ = −1, g₈² = i (trace 0).
    ∧ (g8 * g8 * g8 * g8 = ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩)
    ∧ ((g8 * g8).q0 = (⟨0, 0⟩ : ZRt2))
    -- the ramified prime: N(1+i) = NT.
    ∧ (ZI.normSq ⟨1, 1⟩ = (NT : Int))
    -- the bare minimal polynomial x² − NT.
    ∧ (octaTrace g8 * octaTrace g8 - (⟨(NT : Int), 0⟩ : ZRt2) = ⟨0, 0⟩) := by
  refine ⟨?_, root_five_is_not_sqrt_unit_trace, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.Algebra.CayleyDickson.Tower.UnitResidueRootTwo
