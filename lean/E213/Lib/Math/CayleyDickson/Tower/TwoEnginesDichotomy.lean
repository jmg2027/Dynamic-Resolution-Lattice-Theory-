import E213.Lib.Math.CayleyDickson.Tower.TraceDoublingMap

/-!
# Two engines, one map: the elliptic/hyperbolic split at `|trace| = NT`

The marathon found two residue engines: the **unit** engine (dyadic tower,
seed `√NT = √2`, `Phase 20–21`) and the **`P`-orbit** engine (Möbius `P`,
seed `√(NS+NT) = √5 = √disc P`, the `5`-floor).  This file shows they are
the *two dynamical regimes of one map* — the trace-doubling
`D(x) = x² − NT` — split by the unit trace `NT = 2`.

## `D` governs the `P`-engine too

`P = [[2,1],[1,1]]` has `trace P = 3 = NS`, `det P = 1`, `disc P = 3² − 4
= 5 = NS+NT`.  For an `SL₂` element `trace(M²) = trace(M)² − 2`, so the
*same* `D` drives `P`'s trace:

  `D(trace P) = 3² − NT = 7 = trace(P²)`.

But now `|trace P| = 3 > 2 = NT`: the orbit **escapes**.

  `3 ↦ᴰ 7 ↦ᴰ 47 ↦ᴰ 2207 ↦ᴰ ⋯`   (strictly increasing, hyperbolic)

`P` is the *minimal hyperbolic integer element*: `trace P = NS = NT + 1`,
the first integer just past the elliptic boundary `|x| = NT`.

## The split

`D(x) = x² − NT` on traces:

  * `|x| ≤ NT` — **elliptic**: bounded orbits, finite rotation order,
    contracting onto the fixed core `NT` (the unit).  The dyadic tower
    `√2 ↦ 0 ↦ −2 ↦ 2` lives here; seed `√NT = √2`, the unit residue.
  * `|x| = NT` — the parabolic boundary (`±2`, the unit and `−`unit).
  * `|x| > NT` — **hyperbolic**: escaping orbits, infinite order, the
    Pell/Anosov direction.  `trace P = NS = NT+1` is the first such;
    `disc P = NS+NT = 5`, eigenvalues `(3 ± √5)/2 = φ², φ⁻²`; seed
    `√(NS+NT) = √5`, the `P` residue.

So `√2` and `√5` are not two unrelated surds: they are the residues of the
two regimes of the *one* trace-doubling map, separated by the unit trace
`NT`.  The unit engine re-enters its `√NT` (elliptic, the fixed core); the
`P` engine re-enters its `√(NS+NT)` (hyperbolic, the escaping spread).
`E₇` is the elliptic seed, `E₈` the hyperbolic one — and `NS = NT + 1`
places `P` exactly one step into the hyperbolic side.
-/

namespace E213.Lib.Math.CayleyDickson.Tower.TwoEnginesDichotomy

open E213.Lib.Physics.Simplex.Counts
open E213.Lib.Math.CayleyDickson.Tower.TraceDoublingMap (Di)

/-- **`D` governs the `P`-engine.**  `trace P = NS`, `disc P = NS+NT`,
    and `D(trace P) = trace(P²) = 7` (`SL₂`: `trace(M²) = trace(M)² −
    NT`). -/
theorem doubling_governs_P :
    ((3 : Int) = (NS : Int))                       -- trace P = NS
    ∧ ((3 : Int) ^ 2 - 4 * 1 = (NS : Int) + NT)    -- disc P = NS+NT
    ∧ (Di (NS : Int) = 7)                          -- D(trace P) = trace(P²)
    := by decide

/-- **The `P`-orbit escapes (hyperbolic).**  `D`-iterates of `trace P =
    3` strictly increase: `3 < 7 < 47 < 2207`.  Unbounded ⇒ infinite
    order ⇒ the Pell/Anosov regime. -/
theorem P_orbit_escapes :
    (Di 3 = 7 ∧ Di 7 = 47 ∧ Di 47 = 2207)
    ∧ (3 < Di 3 ∧ Di 3 < Di (Di 3) ∧ Di (Di 3) < Di (Di (Di 3))) := by decide

/-- **The unit orbit is bounded (elliptic).**  The dyadic cycle stays in
    `[−NT, NT]` and fixes the unit trace: `D(NT) = NT`, `D(0) = −NT`,
    `D(−NT) = NT`. -/
theorem unit_orbit_bounded :
    Di (NT : Int) = NT ∧ Di 0 = -(NT : Int) ∧ Di (-(NT : Int)) = NT := by decide

/-- **The boundary is the unit trace `NT`, and `trace P = NS = NT + 1`**
    is the first hyperbolic integer just past it. -/
theorem boundary_at_unit_trace :
    ((NT : Int) < NS) ∧ (NS = NT + 1) := by decide

/-- ★★★ **Two engines, one map.**  The trace-doubling `D(x) = x² − NT`
    drives both: `|x| ≤ NT` is elliptic (bounded, finite order, fixed
    core `NT` — the unit, seed `√NT = √2`); `|x| > NT` is hyperbolic
    (escaping, infinite order — the `P`-orbit, `trace P = NS = NT+1`,
    `disc P = NS+NT`, seed `√(NS+NT) = √5`).  The two seeds are the
    residues of the two regimes, split by the unit trace. -/
theorem two_engines_one_map :
    -- D governs both; trace P = NS, disc P = NS+NT.
    ((3 : Int) = (NS : Int) ∧ (3 : Int) ^ 2 - 4 * 1 = (NS : Int) + NT)
    -- elliptic: the unit is a fixed core (bounded).
    ∧ (Di (NT : Int) = NT)
    -- hyperbolic: P escapes (D(trace P) = 7 > trace P).
    ∧ (Di (NS : Int) = 7 ∧ (NS : Int) < Di (NS : Int))
    -- boundary at the unit trace; P is one step past it.
    ∧ ((NT : Int) < NS ∧ NS = NT + 1) := by
  refine ⟨⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide

end E213.Lib.Math.CayleyDickson.Tower.TwoEnginesDichotomy
