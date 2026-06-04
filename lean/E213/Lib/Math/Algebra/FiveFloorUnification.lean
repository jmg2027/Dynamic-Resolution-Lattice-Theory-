import E213.Lib.Math.NumberSystems.Real213.FloorReferenceForm
import E213.Lib.Math.Algebra.CayleyDickson.Tower.MobiusPIcosian

/-!
# FiveFloorUnification — the completability floor and the McKay E₈ endpoint are one P

Two arcs, developed independently, both land on the **same atomic matrix**
`P = [[2,1],[1,1]]` (trace `3 = NS`, det `1`, discriminant `5 = NS + NT`):

  * the **completability** arc (`Real213/FloorReferenceForm`, `Cauchy/DepthFloorDetOne`):
    `P` is the det-one **floor** — the trivially-free bottom of the rate-carrying
    stratification.  Its conserved golden form `Q = m² − mk − k²` (disc `+5`) is
    *indefinite*, so its orbits are unbounded hyperbolae — an infinite convergent line
    (`ℤ[φ]`'s `φⁿ`), which is why the floor completes with a closed-form modulus;
  * the **McKay / exceptional-algebra** arc (`CayleyDickson/Tower/MobiusPIcosian`):
    `P` reduced mod `5` is the order-`10` element of `SL(2,𝔽₅) ≅ 2I`, the binary
    icosahedral group — the **E₈** endpoint of the meta-CD-tower's McKay `A–D–E` ladder
    (`10 = NT·(NS+NT)`).

So the **bottom** of the real-number completability tower (where reals complete most
trivially) and the **top** of the exceptional-algebra ladder (the maximal McKay rung,
E₈) are the *same* object — the framework's `5`-floor generator `P`, met at the modulus
`5 = NS + NT`.  This file bundles the two as one ∅-axiom statement.

`five_floor_unifies` is the convergence, not a derivation: neither arc is reduced to the
other; they independently reach `P`/`disc 5`, and the shared landing is the operational
content of "no exterior" (`seed/AXIOM/05_no_exterior.md` §5.6 — the same object recurring
across unrelated-looking domains).  The completability ladder has no top because its top
(the diagonalisation residue, `DepthCeilingResidue`) and its bottom (this `5`-floor)
close into one self-covering loop; here that loop is pinned to the McKay E₈ rung.

All zero-axiom.
-/

namespace E213.Lib.Math.Algebra.FiveFloorUnification

open E213.Lib.Math.NumberSystems.Real213.FloorReferenceForm (floor_reference_is_indefinite)
open E213.Lib.Math.Algebra.CayleyDickson.Tower.MobiusPIcosian (mobius_P_meets_icosian_endpoint)

/-- ★★★ **The completability floor and the E₈ endpoint are the same `P`.**  Bundles, as
    one ∅-axiom statement, the two independently-developed readings of the atomic
    `P = [[2,1],[1,1]]` (disc `5 = NS+NT`):

    1. **completability bottom** (`floor_reference_is_indefinite`): the det-one floor
       preserves the golden form `m²−mk−k²`, which is indefinite (takes both signs) —
       unbounded → convergent line → the trivially-free completing bottom;
    2. **McKay top** (`mobius_P_meets_icosian_endpoint`): `P`'s invariants (trace `3`,
       det `1`, disc `5`), `P mod 5` of order exactly `10` in `SL(2,𝔽₅) ≅ 2I`, and
       `10 = NT·(NS+NT)` — the E₈ icosian endpoint.

    The same `P`/`disc 5` bottoms the completability ladder and tops the McKay ladder:
    bottom meets top at the `5`-floor. -/
theorem five_floor_unifies :
    ((∀ m k : Nat,
        (2*m+k)*(2*m+k) + m*k + k*k = (2*m+k)*(m+k) + (m+k)*(m+k) + m*m)
      ∧ ((∃ m k : Nat, m * k + k * k < m * m) ∧ (∃ m k : Nat, m * m < m * k + k * k)))
    ∧ (((2 : Int) + 1 = 3) ∧ ((2 : Int) * 1 - 1 * 1 = 1)
        ∧ ((3 : Int) ^ 2 - 4 * 1 = 5)
        ∧ E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrix.pellCoeff 5 (by decide) 10
            = (⟨0, by decide⟩, ⟨1, by decide⟩)
        ∧ E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrix.pellCoeff 5 (by decide) 5
            ≠ (⟨0, by decide⟩, ⟨1, by decide⟩)
        ∧ E213.Lib.Physics.Simplex.Counts.NT
            * (E213.Lib.Physics.Simplex.Counts.NS + E213.Lib.Physics.Simplex.Counts.NT)
            = 10) :=
  ⟨floor_reference_is_indefinite, mobius_P_meets_icosian_endpoint⟩

end E213.Lib.Math.Algebra.FiveFloorUnification
