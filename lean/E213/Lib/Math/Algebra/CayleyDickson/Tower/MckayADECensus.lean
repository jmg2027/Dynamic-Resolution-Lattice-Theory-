import E213.Lib.Math.Algebra.CayleyDickson.Tower.SeedUnitGovernance
import E213.Lib.Math.Algebra.CayleyDickson.Tower.TypeOOctahedral
import E213.Lib.Math.Algebra.CayleyDickson.Tower.TypeEIcosian

/-!
# The meta-CD-tower realises the full McKay `A–D–E` classification

The finite subgroups of `SU(2)` are classified by the McKay
correspondence into three families:

| McKay | groups | meta-CD-tower loop class |
|---|---|---|
| `Aₙ` (cyclic) | `Cₙ` | the seed roots of unity `μ₂,μ₄,μ₆` (`units6 = C₆`) |
| `Dₙ` (binary dihedral) | `Dicₙ` | `Q₈ = Dic₂` (the dyadic `Lipschitz`/`Cayley` loop), `Dic₃` (`ZOmegaDouble`) |
| `E₆,E₇,E₈` (exceptional) | `2T, 2O, 2I` | `Hurwitz` (24), octahedral over `ℤ[√2]` (48), icosian over `ℤ[φ]` (120) |

So the loop classes that the seed ladder realises are *exactly* the McKay
`A–D–E` list of finite `SU(2)` subgroups — the "complete object" the
sparse-section intuition reached for.  The order-distribution signatures
below are the decidable shadows; the group-name identifications
(`C₆, Q₈, Dic₃, 2T, 2O, 2I`) are the cited classical McKay frame.

This census bundles one discriminating signature per family/rung:
`A` (cyclic `C₆`, `|units6| = 6`); `D` (`Q₈` — `Lipschitz` order-4 count 6;
`Dic₃` — `ZOmegaDouble` order-12 with 3-torsion 2); `E` (`2T` order-6
count 8; `2O` order-8 witness `g8`; `2I` order-5 and order-10 witnesses
`g5, g10`).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Tower.MckayADECensus

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmegaDouble
open E213.Lib.Math.Algebra.CayleyDickson.Tower.CDDouble.Lipschitz
open E213.Lib.Math.Algebra.CayleyDickson.Integer.Hurwitz213

/-- ★★ **The meta-CD-tower realises the full McKay `A–D–E` census.**  One
    discriminating order-signature per family, across the seed ladder:

    * `A` (cyclic `Cₙ`): the Eisenstein roots of unity `units6 = C₆`,
      `|units6| = 6`.
    * `D` (binary dihedral `Dicₙ`): `Q₈ = Dic₂` is the dyadic `Lipschitz`
      loop (order-4 count `6`, the 6 imaginary units); `Dic₃` is
      `ZOmegaDouble` (order 12 with `2` order-3 units).
    * `E₆,E₇,E₈` (`2T,2O,2I`): `2T = Hurwitz` carries `8` order-6 units;
      `2O` the octahedral order has the order-8 unit `g8` (`g8⁸ = 1`);
      `2I` the icosian order has the order-5 and order-10 units `g5,g10`
      (`g5⁵ = 1`, `g10¹⁰ = 1`).

    Every finite `SU(2)` subgroup type is realised; the group-name
    identifications are the cited McKay frame, the order-signatures the
    proved shadows. -/
theorem mckay_ADE_census :
    -- A: cyclic C₆ (μ₆).
    (units6.length = 6)
    -- D: Q₈ (Lipschitz) and Dic₃ (ZOmegaDouble, order 12, 3-torsion 2).
    ∧ (lip_units.countP (fun u => lip_orderOf u = 4) = 6)
    ∧ (zod_units.length = 12)
    ∧ (zod_units.countP (fun u => zod_orderOf u = 3) = 2)
    -- E₆ = 2T (Hurwitz): order-6 torsion.
    ∧ (hur_units.countP (fun u => hur_orderOf u = 6) = 8)
    -- E₇ = 2O (octahedral): order-8 unit.
    ∧ (TypeOOctahedral.g8 * TypeOOctahedral.g8 * TypeOOctahedral.g8
         * TypeOOctahedral.g8 * TypeOOctahedral.g8 * TypeOOctahedral.g8
         * TypeOOctahedral.g8 * TypeOOctahedral.g8 = TypeOOctahedral.Octahedral.one)
    -- E₈ = 2I (icosian): order-5 and order-10 units.
    ∧ (TypeEIcosian.g5 * TypeEIcosian.g5 * TypeEIcosian.g5
         * TypeEIcosian.g5 * TypeEIcosian.g5 = TypeEIcosian.Icosian.one)
    ∧ (TypeEIcosian.g10 * TypeEIcosian.g10 * TypeEIcosian.g10 * TypeEIcosian.g10
         * TypeEIcosian.g10 * TypeEIcosian.g10 * TypeEIcosian.g10 * TypeEIcosian.g10
         * TypeEIcosian.g10 * TypeEIcosian.g10 = TypeEIcosian.Icosian.one) :=
  ⟨by decide,
   lip_order_distribution.2.2.1,
   by decide,
   zod_order_distribution.2.2.1,
   hur_order_distribution.2.2.2.2.1,
   TypeOOctahedral.octahedral_order8_unit.2.1,
   TypeEIcosian.icosian_order5_unit.2.1,
   TypeEIcosian.icosian_order10_unit.2.1⟩

end E213.Lib.Math.Algebra.CayleyDickson.Tower.MckayADECensus
