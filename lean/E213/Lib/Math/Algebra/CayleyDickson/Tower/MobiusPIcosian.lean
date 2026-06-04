import E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrix
import E213.Lib.Physics.Simplex.Counts

/-!
# The Möbius generator `P` meets the icosian endpoint

The framework's atomic Möbius matrix `P = [[2,1],[1,1]]` (trace `3 = NS`,
det `1`, disc `3²-4 = 5 = NS+NT` — the `5`-floor) reduces mod `5` to an
element of `SL(2,𝔽₅)`.  Since `SL(2,𝔽₅) ≅ 2I` (the binary icosahedral
group, the `E₈` McKay rung — a cited classical fact), `P mod 5` is an
element of the same `2I` whose order-5/10 torsion the icosian units
`g5`, `g10` witness over `ℤ[φ]`.

This file proves the executable shadow: **`P mod 5` has matrix order
exactly `10`** — via the Cayley–Hamilton coefficient detector
`pellCoeff` for `M = [[2,1],[1,1]]` (trace 3, det 1).  `P¹⁰ ≡ I`, while
`P¹, P², P⁵ ≢ I`, so the order divides 10 and equals neither 1, 2, nor 5
— hence is exactly 10.  Since `det P = 1` (so `P mod 5 ∈ SL(2,𝔽₅)`) and
`10 = NT·(NS+NT)`, this is the order-10 conjugacy class of the icosian
endpoint: the seed/McKay ladder's `E₈` rung and the DRLT atomic
`P`-orbit (`disc P = 5 = NS+NT`) meet at this order-10 element.

(The group isomorphism `SL(2,𝔽₅) ≅ 2I` and the conjugacy of `P mod 5`
with `g10` are the cited frame; what is *proved* here is `P mod 5`'s
matrix order and its `SL(2,𝔽₅)` membership via `det = 1`.)
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Tower.MobiusPIcosian

open E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrix
open E213.Lib.Physics.Simplex.Counts

/-- ★ **`P = [[2,1],[1,1]]` reduced mod 5 has matrix order exactly 10.**
    `pellCoeff 5 · k` is the Cayley–Hamilton coefficient pair `(a_k,b_k)`
    with `Pᵏ = a_k·P + b_k·I` over `𝔽₅`; `Pᵏ = I ⟺ (a_k,b_k) = (0,1)`.
    `P¹⁰ = I` while `P¹,P²,P⁵ ≠ I` ⇒ order divides 10, is not 1/2/5,
    hence is exactly 10 — the order-10 element of `SL(2,𝔽₅) ≅ 2I`. -/
theorem P_mod5_order_exactly_10 :
    pellCoeff 5 (by decide) 10 = (⟨0, by decide⟩, ⟨1, by decide⟩)
    ∧ pellCoeff 5 (by decide) 1 ≠ (⟨0, by decide⟩, ⟨1, by decide⟩)
    ∧ pellCoeff 5 (by decide) 2 ≠ (⟨0, by decide⟩, ⟨1, by decide⟩)
    ∧ pellCoeff 5 (by decide) 5 ≠ (⟨0, by decide⟩, ⟨1, by decide⟩) := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> decide

/-- ★★ **The Möbius `P`-orbit meets the icosian `E₈` endpoint.**  Bundles
    the bridge: `P`'s atomic invariants (trace `3 = NS`, det `1`,
    disc `5 = NS+NT` — the floor), its order-10 reduction mod 5 (an
    element of `SL(2,𝔽₅) ≅ 2I`), and `10 = NT·(NS+NT)` — the order-10
    icosian torsion.  The `5`-floor generator of the whole framework is
    the order-10 element of the seed ladder's binary-icosahedral
    endpoint. -/
theorem mobius_P_meets_icosian_endpoint :
    -- P atomic invariants: the 5-floor.
    ((2 : Int) + 1 = 3) ∧ ((2 : Int) * 1 - 1 * 1 = 1)
    ∧ ((3 : Int) ^ 2 - 4 * 1 = 5)
    -- P mod 5 has order exactly 10 in SL(2,𝔽₅).
    ∧ pellCoeff 5 (by decide) 10 = (⟨0, by decide⟩, ⟨1, by decide⟩)
    ∧ pellCoeff 5 (by decide) 5 ≠ (⟨0, by decide⟩, ⟨1, by decide⟩)
    -- 10 = NT·(NS+NT) = the icosian / E₈ order-10 torsion.
    ∧ NT * (NS + NT) = 10 := by
  refine ⟨by decide, by decide, by decide, rfl, by decide, by decide⟩

end E213.Lib.Math.Algebra.CayleyDickson.Tower.MobiusPIcosian
