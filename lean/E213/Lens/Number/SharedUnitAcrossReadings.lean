import E213.Lib.Math.Mobius213OneAsGlue
import E213.Lib.Math.CassiniUnimodular
import E213.Lens.Number.Nat213.Tower.NatPairToQPos

/-!
# SharedUnitAcrossReadings — the number axes are unified by one unit, not one operator

The number-axis readings — count/difference (`ℤ`), ratio (`ℚ`), the Cassini/Möbius
determinant — look like separate constructions, and one is tempted to unify them *upward*,
as words in an operator algebra ("a monoid of construction moves").  That is the wrong
direction: the readings live on different codomains, and a forced common map across them is
the category error `theory/essays/the_form_of_the_residue.md` warns against ("the honest
unity is the *shared unit*, not a single map").

This file states the honest unification *downward*: the unit **`1`** is one value across
the readings.

  * **count-difference** — the glue `NS − NT = 1` (`Mobius213OneAsGlue.ns_minus_nt_is_one`);
  * **Möbius/ratio determinant** — `det P = NS − NT` and `det P = 1`
    (`mobius_det_eq_ns_minus_nt`, `mobius_det_is_unit`): the convergent matrix's
    unimodular determinant, the coprimality datum of `ℚ`;
  * **Cassini oscillation** — `det toggle 0 = 1` (`CassiniUnimodular.toggle_det_unit`): the
    period-2 orbit's conserved cross-determinant;
  * **reciprocal** — `x · (1/x) = 1` (`NatPairToQPos.qpair_mul_swap_eq_qOne`): the
    multiplicative inverse law, the unit class `qOne`.

Four readings, one value `1`.  (The companion *residue of size `NT = 2`* — the two atoms,
the `{±1}` of the determinant, the period-2 swap — is the other shared constant, pinned by
`PairCompletion.swap_order_eq_NT`.)  The axes are unified by *identity of the unit*, not by
a composition algebra of operators — "one orbit, many readings, one unit."

All theorems ∅-axiom.
-/

namespace E213.Lens.Number.SharedUnitAcrossReadings

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lib.Physics.Simplex.Counts (NS NT)
open E213.Lib.Math.Mobius213OneAsGlue
  (ns_minus_nt_is_one mobius_det_eq_ns_minus_nt mobius_det_is_unit)
open E213.Lib.Math.CassiniUnimodular (det toggle toggle_det_unit)
open E213.Lens.Number.Nat213.Tower.NatPairToQPos
  (QPair qpairEquiv qPairMul qSwap qOne qpair_mul_swap_eq_qOne)

/-- ★★★ **The unit `1` is one value across the number-axis readings.**  The count-difference
    glue `NS − NT`, the Möbius/ratio determinant `det P` (the coprimality datum of `ℚ`), the
    Cassini oscillation's conserved cross-determinant, and the reciprocal law `x · (1/x)` all
    equal the unit `1`.  This is the honest unification of the axis-readings — *identity of
    the unit*, downward to one value, not a forced common map across the readings (which the
    `the_form_of_the_residue` discipline names a category error) and not an operator monoid
    (which has no shared carrier, `Tower.PairCompletion`).  One orbit, many readings, one
    unit. -/
theorem the_unit_is_one_across_readings :
    (NS - NT = 1)
    ∧ ((2 : Int) * 1 - 1 * 1 = (NS : Int) - (NT : Int))
    ∧ ((2 : Int) * 1 - 1 * 1 = 1)
    ∧ (det toggle 0 = 1)
    ∧ (∀ p : QPair, qpairEquiv (qPairMul p (qSwap p)) qOne) :=
  ⟨ns_minus_nt_is_one, mobius_det_eq_ns_minus_nt, mobius_det_is_unit,
   toggle_det_unit, qpair_mul_swap_eq_qOne⟩

end E213.Lens.Number.SharedUnitAcrossReadings
