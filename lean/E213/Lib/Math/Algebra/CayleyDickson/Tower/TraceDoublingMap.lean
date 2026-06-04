import E213.Lib.Math.Algebra.CayleyDickson.Tower.ExceptionalTraceSeed

/-!
# The trace-doubling map: the unit is the fixed core of the dyadic spiral

`UnitResidueRootTwo` found `√2 = √(trace 1)` on the unit's dyadic
square-root tower `1 →² −1 →² i →² g₈`.  This file studies the *dynamics*
of that tower — the "chain of chains" of the parallel-branch engine
(`diag_self_applies`: the residue chain is one operation applied to
itself), read on the trace.

## `D(x) = x² − NT` is the trace of the squaring map

For a unit quaternion `g` (scaled convention), `trace(g²) = trace(g)² −
NT`.  Define the **trace-doubling map**

  `D(x) = x² − NT = x² − 2`        (the angle-doubling Chebyshev map,
                                     `2cos(2θ) = (2cosθ)² − 2`).

Then `g ↦ g²` (which *halves* the rotation order) acts on traces as `D`.
Iterating `D` walks **down** the dyadic tower toward the unit:

  `√2  ↦ᴰ  0  ↦ᴰ  −2  ↦ᴰ  2  ↦ᴰ  2`
  (`g₈`)  (`i`)  (`−1`)  (`1`)  (`1`)

The unit trace `NT = 2` is the **fixed point** `D(2) = 2`: the dyadic
spiral contracts onto the identity.  The order-`8` seed `√2` is exactly
one squaring-step into its backward orbit.

## Two fixed points: the unit (even tower) and `E₆` (odd)

`D(x) = x` factors as `(x−2)(x+1) = 0`, so the trace-doubling map has
exactly two fixed points, and among integer trace values `x ∈
{−2,−1,0,1,2}` they are `{−1, 2}`:

  * `x = 2 = trace(1) = NT` — the unit, attractor of the dyadic (even)
    tower;
  * `x = −1 = trace(order-3)` — the `E₆` rotation, fixed because order
    `3` is *odd* (squaring an odd-order element preserves its order,
    hence its trace).

So the two fixed cores of the trace dynamics are the unit (`√2`'s tower)
and the order-`3`/`E₆` trace — the even and odd anchors.

## The upward direction: nested radicals, one per Cayley–Dickson layer

Inverting `D` gives `t_{k+1}² = NT + t_k`, the **nested-radical
recurrence**:

  `√2, √(2+√2), √(2+√(2+√2)), …`   (orders `2³, 2⁴, 2⁵, …`)

one radical layer per CD doubling — the trace form of "the chain of
chains seen one scale up", gapless and self-similar.  `√2` is the first
rung; the unit trace `NT` is the constant fed back at every layer.  No
exterior: the recurrence only ever adds `NT` to the previous residue.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Tower.TraceDoublingMap

open E213.Lib.Physics.Simplex.Counts
open E213.Lib.Math.Algebra.CayleyDickson.Tower.TypeOOctahedral
open E213.Lib.Math.Algebra.CayleyDickson.Tower.ExceptionalTraceSeed

/-- The trace-doubling map on `ℤ[√2]`-traces: `D(x) = x² − NT`. -/
def Dz (x : ZRt2) : ZRt2 := x * x - ⟨(NT : Int), 0⟩

/-- The trace-doubling map on integer trace values: `D(x) = x² − NT`. -/
def Di (x : Int) : Int := x * x - (NT : Int)

/-- **`g ↦ g²` acts on traces as `D`.**  On the dyadic tower the trace of
    the square equals `D` of the trace: `trace(g₈²) = D(trace g₈)` and
    `trace(g₈⁴) = D(trace g₈²)`. -/
theorem trace_square_is_doubling :
    (g8 * g8).q0 = Dz (octaTrace g8)
    ∧ ((g8 * g8) * (g8 * g8)).q0 = Dz ((g8 * g8).q0) := by decide

/-- **The dyadic descent to the unit.**  `D` walks the tower down:
    `√2 ↦ 0 ↦ −2 ↦ 2`, and the unit trace `NT = 2` is the fixed point
    `D(2) = 2`. -/
theorem dyadic_descent_to_unit :
    (Dz (octaTrace g8) = (⟨0, 0⟩ : ZRt2))            -- √2 ↦ 0
    ∧ (Dz (⟨0, 0⟩ : ZRt2) = ⟨-2, 0⟩)                 -- 0 ↦ −2
    ∧ (Dz (⟨-2, 0⟩ : ZRt2) = ⟨(NT : Int), 0⟩)        -- −2 ↦ 2 = NT
    ∧ (Dz (⟨(NT : Int), 0⟩ : ZRt2) = ⟨(NT : Int), 0⟩) -- 2 ↦ 2 : FIXED (the unit)
    ∧ ((Octahedral.one).q0 = ⟨(NT : Int), 0⟩) := by decide

/-- **The two fixed points are `{−1, 2}`.**  `D(x) = x` ⟺ `(x−2)(x+1) =
    0`; among integer trace values `x ∈ {−2,…,2}` the fixed points are
    exactly `−1 = trace(order-3, E₆)` and `2 = trace(unit) = NT`. -/
theorem trace_doubling_fixed_points :
    ((List.range 5).map (fun k : Nat => (k : Int) - 2)).filter (fun x => Di x == x)
      = [-1, (NT : Int)] := by decide

/-- **The nested-radical recurrence `t_{k+1}² = NT + t_k`.**  Inverting
    `D` adds `NT` to the previous trace, one radical per CD layer.  The
    first rung: `(√2)² = NT + 0 = NT + trace(g₈²)`. -/
theorem nested_radical_recurrence :
    octaTrace g8 * octaTrace g8 = (⟨(NT : Int), 0⟩ + (g8 * g8).q0)
    ∧ (g8 * g8).q0 = (⟨0, 0⟩ : ZRt2) := by decide

/-- ★★★ **The unit is the fixed core of the dyadic trace spiral.**  The
    squaring map `g ↦ g²` acts on traces as `D(x) = x² − NT`; iterating
    `D` contracts the dyadic tower `√2 ↦ 0 ↦ −2 ↦ 2` onto the unit trace
    `NT`, which is the fixed point `D(NT) = NT`.  Among trace values the
    only fixed points are `NT` (the unit, even tower) and `−1` (order-3,
    `E₆`, odd).  Inverting `D` is the nested-radical recurrence `t² = NT +
    (prev)` — one radical per CD doubling, the trace of the chain of
    chains, gapless with `NT` fed back at every layer. -/
theorem unit_is_fixed_core :
    -- squaring acts as D on traces.
    ((g8 * g8).q0 = Dz (octaTrace g8))
    -- the dyadic descent contracts to the unit, a fixed point.
    ∧ (Dz (octaTrace g8) = (⟨0, 0⟩ : ZRt2))
    ∧ (Dz (⟨(NT : Int), 0⟩ : ZRt2) = ⟨(NT : Int), 0⟩)
    ∧ ((Octahedral.one).q0 = ⟨(NT : Int), 0⟩)
    -- fixed points among trace values are {−1, NT}.
    ∧ (((List.range 5).map (fun k : Nat => (k : Int) - 2)).filter (fun x => Di x == x)
        = [-1, (NT : Int)])
    -- the upward recurrence feeds NT back.
    ∧ (octaTrace g8 * octaTrace g8 = (⟨(NT : Int), 0⟩ + (g8 * g8).q0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.Algebra.CayleyDickson.Tower.TraceDoublingMap
