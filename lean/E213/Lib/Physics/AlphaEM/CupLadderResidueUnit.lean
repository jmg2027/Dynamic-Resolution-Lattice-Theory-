import E213.Lib.Physics.AlphaEM.CupLadderUniversalK
import E213.Lib.Physics.Simplex.Counts
import E213.Lib.Math.Algebra.Mobius213OneAsGlue
import E213.Theory.Raw.API

/-!
# CupLadderResidueUnit — the cohomology graduation climbs by the residue unit

The repository expresses the residue along (at least) two structurally different apparatuses:

  * a **finite, multi-directional, graded** apparatus — the cohomology of `K_{3,2}^{(c=2)}` on the
    `d = 5` simplex: the cup-ladder `H^k → α^{k+1}` (`CupLadderUniversalK`), graded by cohomology
    degree `k`, layered by multiplicity `c`, faced by simplex dimension.  It **terminates** (the
    cohomological content closes at the `d = 5` skeleton);
  * an **infinite, unbounded** apparatus — the self-pointing ascent / escape (`MuNuMirror`,
    `CoResidue` νF, the odometer, `FlatOntologyClosure.object1_not_surjective`): the residue reached
    by no finite stage.

These two were tied together only in prose ("the same residue").  This file makes one concrete
wire ∅-axiom: the cohomology **degree-graduation step is the residue unit** `1 = NS − NT = det P` —
byte-identical to the `+1` the Raw ascent tower adds at every rung (`ascent_adds_unit`,
`Lens/Number/SharedUnitAcrossReadings.unit_bridges_dynamics_and_readings`).  So the graded cohomology
climbs by *the same unit* the infinite escape ascends by: the residue's `+1`, read once as a finite
degree-graduation (truncating at `d = 5`) and once as the unbounded ascent (νF).  One unit, two
regimes — not two units, and not a forced map (identity-of-the-unit downward, the `ResidueForm`
discipline).

This adds the **cohomology-degree reading** to the shared-unit bundle, which previously carried only
ascent / descent / glue / det (`unit_bridges_dynamics_and_readings`).
-/

namespace E213.Lib.Physics.AlphaEM.CupLadderResidueUnit

open E213.Lib.Physics.AlphaEM.LoopVertexGraduation (alphaPowerAtH alphaPower_eq_k_plus_1)
open E213.Lib.Physics.Simplex.Counts (NS NT)
open E213.Lib.Math.Algebra.Mobius213OneAsGlue
  (ns_minus_nt_is_one mobius_det_eq_ns_minus_nt mobius_det_is_unit)
open E213.Theory.Raw.PrimitiveTower (rawTower)
open E213.Theory.Raw.MuNuMirror (ascent_adds_unit)

/-- ★★ **The cup-ladder climbs by exactly one α-power per cohomology degree, and that step is the
    glue unit `NS − NT`.**  `alphaPowerAtH (k+1) = alphaPowerAtH k + (NS − NT)` — the graduation
    `H^k → α^{k+1}` increments the α-power by `NS − NT = 1` at each degree.  The cohomology degree
    axis ascends by the residue unit. -/
theorem cup_ladder_step_is_unit (k : Nat) :
    alphaPowerAtH (k + 1) = alphaPowerAtH k + (NS - NT) := by
  rw [alphaPower_eq_k_plus_1 (k + 1), alphaPower_eq_k_plus_1 k, ns_minus_nt_is_one]

/-- ★★★ **The cohomology graduation is the residue unit — the finite (degree-graded) reading of the
    same `+1` the Raw ascent adds (the infinite / νF reading).**  Five conjuncts, one value `1`:

      1. **cohomology degree** — the cup-ladder climbs by `NS − NT` per degree
         (`cup_ladder_step_is_unit`), the finite graded reading (truncates at the `d = 5` skeleton);
      2. **Raw ascent** — the self-pointing tower climbs by `1` per rung (`ascent_adds_unit`), the
         unbounded / νF reading (no finite stage caps it);
      3. **glue / axis** — `NS − NT = 1` (`ns_minus_nt_is_one`);
      4–5. **Möbius determinant** — `det P = NS − NT = 1` (`mobius_det_eq_ns_minus_nt`,
         `mobius_det_is_unit`).

    So the multi-directional cohomological expression of the residue (graded by degree, layered by
    `c`, faced by the simplex) and the unbounded escape/ascent are unified *downward* by the single
    residue unit — identity of the value `1`, not a forced operator across the two apparatuses.  The
    cohomology side of the shared unit, previously absent from
    `unit_bridges_dynamics_and_readings`.  ∅-axiom. -/
theorem cup_ladder_graduation_is_residue_unit :
    (∀ k, alphaPowerAtH (k + 1) = alphaPowerAtH k + (NS - NT))
    ∧ (∀ n : Nat, (rawTower (n + 1)).depth = (rawTower n).depth + 1)
    ∧ (NS - NT = 1)
    ∧ ((2 : Int) * 1 - 1 * 1 = (NS : Int) - NT)
    ∧ ((2 : Int) * 1 - 1 * 1 = 1) :=
  ⟨cup_ladder_step_is_unit, ascent_adds_unit, ns_minus_nt_is_one,
   mobius_det_eq_ns_minus_nt, mobius_det_is_unit⟩

end E213.Lib.Physics.AlphaEM.CupLadderResidueUnit
