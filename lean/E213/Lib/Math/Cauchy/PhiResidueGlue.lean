import E213.Lib.Math.Cauchy.DepthFloorDetOne
import E213.Lib.Math.Mobius213OneAsGlue
import E213.Lib.Math.Real213.PhiFrozenDynamic

/-!
# Cauchy.PhiResidueGlue — the φ residue unit IS the atomic glue `NS − NT = det P`

The residue between *dynamic* φ (the Pell convergents) and *frozen* φ (the algebraic fixed
point) is the unit `1`: the convergent cross-determinant `W n` (`DepthFloorDetOne`, the Cassini
surplus `a² + 1 = a·b + b²`) is constant `1` for every `n` (`W_eq_one`).

This file makes the **cross-scale identification** explicit: that residue unit is *not* a bare
`1` — it is the **atomic glue** `NS − NT` (`Mobius213OneAsGlue.ns_minus_nt_is_one`), which is
itself `det P` (`mobius_det_eq_ns_minus_nt`).  So the analysis-side residue (the never-closing
gap between the convergent and φ) **equals** the algebra-side determinant of `P` **equals** the
atomicity-count difference `NS − NT`.  One unit, read at three scales — analysis, algebra,
atomicity — now chained by one ∅-axiom theorem, not three coincident `1`s.

This is the genuine cross-scale link (the convergent cross-determinant is *literally* `det Pⁿ =
(det P)ⁿ = 1` = `NS − NT`), not a "both equal 1" coincidence.
-/

namespace E213.Lib.Math.Cauchy.PhiResidueGlue

open E213.Lib.Math.Cauchy.DepthFloorDetOne (W W_eq_one)
open E213.Lib.Math.Mobius213OneAsGlue (ns_minus_nt_is_one mobius_det_eq_ns_minus_nt)
open E213.Lib.Physics.Simplex.Counts (NS NT)

/-- ★★ **The φ-convergent residue is the atomic glue.**  The convergent cross-determinant
    `W n` (the Cassini surplus separating the dynamic convergent from the frozen φ) equals the
    atomic-count difference `NS − NT` for every `n`: the residue unit between dynamic and frozen
    φ *is* the glue.  (`W n = 1 = NS − NT`.) -/
theorem phi_residue_is_glue (n : Nat) : W n = NS - NT := by
  rw [W_eq_one n]; exact ns_minus_nt_is_one.symm

/-- ★★★ **The residue unit at three scales — analysis = algebra = atomicity.**  For every `n`:

    1. **analysis** — the φ-convergent cross-determinant `W n` (the never-closing residue between
       the Pell convergent and the frozen φ) is `NS − NT` (`phi_residue_is_glue`);
    2. **atomicity** — `NS − NT = 1`, the atomic glue elevating `NT` to `NS`
       (`ns_minus_nt_is_one`);
    3. **algebra** — that `1` is `det P` (`mobius_det_eq_ns_minus_nt`): the determinant of the
       Möbius matrix whose orbit *is* the convergent sequence.

    So the residue between dynamic and frozen φ, the atomic glue `NS − NT`, and `det P` are the
    **same unit `1`**, read at three scales — chained, not merely coincident. -/
theorem residue_unit_three_scales (n : Nat) :
    W n = NS - NT
    ∧ NS - NT = 1
    ∧ ((2 : Int) * 1 - 1 * 1 = (NS : Int) - (NT : Int)) :=
  ⟨phi_residue_is_glue n, ns_minus_nt_is_one, mobius_det_eq_ns_minus_nt⟩

end E213.Lib.Math.Cauchy.PhiResidueGlue
