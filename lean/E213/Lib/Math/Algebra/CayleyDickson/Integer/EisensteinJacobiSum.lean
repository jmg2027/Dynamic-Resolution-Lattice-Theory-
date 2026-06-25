import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum
import E213.Lib.Math.NumberTheory.FourSquareSeed
import E213.Meta.Nat.NatRing213

/-!
# The cubic Jacobi sum `J(χ,χ) = Σ_t χ_ω(t)·χ_ω(1−t)` as a concrete `ℤ[ω]` element (∅-axiom, Phase A2)

With the computable `ℤ[ω]`-valued cubic character `χ_ω` (`EisensteinCubicCharFp.chiOmega`), the Jacobi
sum of cubic reciprocity is the **concrete finite sum**

  `J(χ,χ) = Σ_{t=0}^{p-1} χ_ω(t) · χ_ω((1 − t) mod p)`,

where `(1 − t) mod p` is written `(1 + (p − t)) % p` to stay in `ℕ`.  This file *defines* `jacobiSum`
and records its structural identities — `χ_ω(0) = 0` (`chiOmega_zero`), and the vanishing of the two
boundary terms `t = 0` (`χ_ω(0) = 0`) and `t = 1` (`χ_ω(1−1) = χ_ω(0) = 0`).  So `J` is effectively a
sum over the `p − 2` interior residues `t ∈ {2, …, p−1}`, all of whose factors are genuine cube roots
of unity.

The norm law `N(J) = J·J̄ = p` (Phase A3) — via `𝔽_p` character orthogonality `Σ_t χ_ω(t) = 0` and the
collapsing double sum — is the open frontier (`research-notes/frontiers/higher_reciprocity_roadmap.md`).
∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum (sumRange sumRange_succ sum_congr)
open E213.Lib.Math.NumberTheory.FourSquareSeed (mod_zero_of_dvd)
open E213.Meta.Algebra213.Ring213 (zero_mul mul_zero)
open E213.Meta.Nat.NatRing213 (nat_sub_add_cancel)
open E213.Meta.Nat.AddMod213 (mod_self)

/-- ★★ **`χ_ω(t) = 0` when `p ∣ t`** — in particular `χ_ω(0) = 0`.  The `t % p = 0` branch. -/
theorem chiOmega_zero_of_dvd (p m x t : Nat) (h : p ∣ t) : chiOmega p m x t = 0 := by
  show (if t % p = 0 then (0 : ZOmega) else _) = 0
  rw [if_pos (mod_zero_of_dvd t p h)]

/-- The cubic Jacobi sum `J(χ,χ) = Σ_{t<p} χ_ω(t)·χ_ω((1−t) mod p)` as a concrete `ℤ[ω]` element. -/
def jacobiSum (p m x : Nat) : ZOmega :=
  sumRange (fun t => chiOmega p m x t * chiOmega p m x ((1 + (p - t)) % p)) p

/-- ★★ **The `t = 0` summand vanishes** — `χ_ω(0)·χ_ω(1) = 0` (the first factor `χ_ω(0) = 0`). -/
theorem jacobi_term_zero (p m x : Nat) :
    chiOmega p m x 0 * chiOmega p m x ((1 + (p - 0)) % p) = 0 := by
  rw [chiOmega_zero_of_dvd p m x 0 (⟨0, rfl⟩), zero_mul]

/-- ★★★ **The `t = 1` summand vanishes** — `χ_ω(1)·χ_ω(0) = 0` (the second factor: `(1 − 1) mod p =
    0`, so `χ_ω(0) = 0`).  Uses `1 + (p − 1) = p` and `p % p = 0`. -/
theorem jacobi_term_one (p m x : Nat) (hp : 1 ≤ p) :
    chiOmega p m x 1 * chiOmega p m x ((1 + (p - 1)) % p) = 0 := by
  have hp0 : (1 + (p - 1)) % p = 0 := by
    rw [Nat.add_comm 1 (p - 1), nat_sub_add_cancel hp, mod_self]
  rw [hp0, chiOmega_zero_of_dvd p m x 0 (⟨0, rfl⟩), mul_zero]

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum
