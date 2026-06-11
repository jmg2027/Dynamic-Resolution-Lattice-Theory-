import E213.Lib.Math.NumberTheory.PrimeValuation
import E213.Lib.Math.NumberTheory.ModArith.ValuationAlg

/-!
# FTALite — the prime-valuation divisibility criterion, ∅-axiom

`(∀ prime p, vₚ a ≤ vₚ b) → a ∣ b` (`a, b > 0`) — "FTA-lite": a number divides
another iff it loses the per-prime valuation race at no prime.  This is the exact
contrapositive of `ModArith.ValuationAlg.exists_prime_vp_gt` (`a ∤ b → ∃ prime q,
vₚ a > vₚ b`), with the `a ∣ b` decision taken purely through `a % b = 0` (the
`Decidable (·∣·)` instance carries `propext`).

It is the criterion the ζ(3) lcm-bound brick's key-divisibility step (forthcoming)
closes through: compare the two sides' `vₚ` per prime via `legendre` (factorials)
and `LcmGrowthChebyshev.vp_lcmUpTo` (lcm), folded by `count30`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.FTALite

open E213.Meta.Nat.Valuation (vp mod_zero_of_dvd)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Lib.Math.NumberTheory.ModArith.ValuationAlg (exists_prime_vp_gt)

/-- ★★★ **FTA-lite**: if at every prime `p` the valuation `vₚ a ≤ vₚ b`, then
    `a ∣ b` (`a, b > 0`).  The contrapositive of `exists_prime_vp_gt`; the divide
    decision runs through `b % a = 0` (pure `decEq`). -/
theorem dvd_of_forall_prime_vp_le {a b : Nat} (ha : 0 < a) (hb : 0 < b)
    (h : ∀ q, Prime213 q → vp q a ≤ vp q b) : a ∣ b := by
  by_cases hm : b % a = 0
  · exact dvd_of_mod_eq_zero hm
  · exfalso
    obtain ⟨q, hq1, hqpr, hgt⟩ :=
      exists_prime_vp_gt a b ha hb (fun hab => hm (mod_zero_of_dvd ha hab))
    exact absurd (h q ⟨hq1, hqpr⟩) (Nat.not_le.mpr hgt)

end E213.Lib.Math.NumberTheory.FTALite
