import E213.Lib.Math.NumberTheory.PrimePowFactorization
import E213.Meta.Nat.PowBasic

/-!
# Central binomial coefficient — explicit prime factorization (∅-axiom)

Combining the explicit FTA product form (`prod_prime_pow_eq`) with the Kummer
prime-power bound (`prime_pow_vp_central_binom_le`: `p^{vₚ(C(2n,n))} ≤ 2n`) gives
the explicit prime factorization of the central binomial coefficient over the
fixed index set of primes `≤ 2n`:

  `C(2n,n) = ∏_{p ≤ 2n, prime} p^{vₚ(C(2n,n))}`   (`central_binom_factorization`).

This is the object the Erdős proof of Bertrand's postulate **upper-bounds** by
splitting the index list `primesIn 0 (2n)` by the size of `p` (via
`primePowProd_append` + `primesIn_split`) and bounding each range.  The key input
beyond the FTA form is that every prime factor of `C(2n,n)` is `≤ 2n`
(`central_binom_prime_factors_le`), which is exactly what pins the index set.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.CentralBinomFactorization

open E213.Lib.Math.NumberTheory.PrimePowFactorization (primePowProd prod_prime_pow_eq)
open E213.Lens.Number.Nat213.MultSystem (binom)
open E213.Lens.Number.Nat213.MultSystemValue (central_binom_pos primesIn)
open E213.Lens.Number.Nat213.ChebyshevLower (prime_pow_vp_central_binom_le)
open E213.Meta.Nat.VpMul (IsPrime213)
open E213.Meta.Nat.Valuation (vp)
open E213.Meta.Nat.VpSeparation (dvd_iff_one_le_vp)
open E213.Meta.Nat.PowBasic (one_le_pow)

/-- **Every prime factor of `C(2n,n)` is `≤ 2n`.**  If `q ∣ C(2n,n)` then
    `1 ≤ vₚ(C)`, so `q = q¹ ≤ q^{vₚ(C)} ≤ 2n` (`prime_pow_vp_central_binom_le`).
    Pins the index set for the explicit factorization. -/
theorem central_binom_prime_factors_le {q n : Nat} (hq : IsPrime213 q) (hn : 1 ≤ n)
    (hdvd : q ∣ binom (2 * n) n) : q ≤ 2 * n := by
  have hcpos : 0 < binom (2 * n) n := central_binom_pos n
  have hk : 1 ≤ vp q (binom (2 * n) n) := (dvd_iff_one_le_vp hq hcpos).mp hdvd
  have hbound : q ^ vp q (binom (2 * n) n) ≤ 2 * n := prime_pow_vp_central_binom_le hq hn
  have hqpos : 0 < q := Nat.lt_of_lt_of_le (by decide) hq.two_le
  have hqle : q ≤ q ^ vp q (binom (2 * n) n) := by
    obtain ⟨k, hk2⟩ : ∃ k, vp q (binom (2 * n) n) = k + 1 := by
      cases hvp : vp q (binom (2 * n) n) with
      | zero => rw [hvp] at hk; exact absurd hk (by decide)
      | succ k => exact ⟨k, rfl⟩
    rw [hk2]
    have h1 : 1 ≤ q ^ k := one_le_pow (Nat.le_trans (by decide) hq.two_le) k
    calc q = 1 * q := (Nat.one_mul q).symm
      _ ≤ q ^ k * q := Nat.mul_le_mul_right q h1
      _ = q ^ (k + 1) := rfl
  exact Nat.le_trans hqle hbound

/-- ★★★ **Explicit prime factorization of the central binomial coefficient.**
    `C(2n,n) = ∏_{p ≤ 2n, prime} p^{vₚ(C(2n,n))}` — the FTA product form
    (`prod_prime_pow_eq`) instantiated at `m = C(2n,n)`, `B = 2n`, with the index
    set pinned by `central_binom_prime_factors_le`.  The object Erdős upper-bounds
    by size-ranges (`primePowProd_append` over `primesIn_split`).  ∅-axiom. -/
theorem central_binom_factorization (n : Nat) (hn : 1 ≤ n) :
    binom (2 * n) n
      = primePowProd (fun p => vp p (binom (2 * n) n)) (primesIn 0 (2 * n)) :=
  prod_prime_pow_eq (central_binom_pos n)
    (fun _q hq hd => central_binom_prime_factors_le hq hn hd)

end E213.Lib.Math.NumberTheory.CentralBinomFactorization
