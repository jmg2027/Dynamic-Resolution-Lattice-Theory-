import E213.Lib.Math.DyadicFSM.BinetBridge
import E213.Lib.Math.ModArith.UniversalFLT
/-!
# Universal Phase 3.2 closure (Bezout-based)

End-to-end universal Phase 3.2 closure:
  · Universal FLT (Part 31) for phi and psi at split primes
  · Universal ModInverse via Bezout (Part 30) for the sqrt5 witness s
  · Binet bridges (Parts 25-26) for F_{p-1} ≡ 0 and F_{p-3} ≡ -1
  · phase_3_2_closure (Part 13) for the matrix-order claim

All declarations PURE.
-/

namespace E213.Lib.Math.DyadicFSM.UniversalSplit

open E213.Lib.Math.DyadicFSM.PhiMod5 (phi phi_lt phi_pow_eq_fibLike fibLike)
open E213.Lib.Math.DyadicFSM.PsiMod5 (psi psi_lt fibLike_pow)
open E213.Lib.Math.DyadicFSM.PellMatrix (pellCoeff)
open E213.Lib.Math.DyadicFSM.PellFibBridge (fibFst phase_3_2_closure)
open E213.Lib.Math.DyadicFSM.BinetBridge
  (binet_F_p_minus_1_zero binet_F_p_minus_3_plus_one_zero
   mod_eq_p_minus_one_of_succ_mod_zero)
open E213.Lib.Math.DyadicFSM.MulOrderPigeonhole (ModInverse)
open E213.Lib.Math.ModArith.ModBezout (modBezout)
open E213.Lib.Math.ModArith.ModBezoutInvariant (modInverseFromBezout)
open E213.Lib.Math.ModArith.UniversalFLT (universal_flt_main)

/-- ★★★★★★★★ **Universal Phase 3.2 closure** at split primes.

    Universal hypotheses:
      · `hp : 1 < p`, `hpo : p % 2 = 1`
      · `s` — sqrt5 witness with `hs : s * s % p = 5 % p`
      · `h_prime_gcd` — primality as gcd-coprimality (decidable per p)

    Per-prime decidable hypotheses:
      · `h_phi_pos`, `h_psi_pos`, `h_phi_eq_psi_plus_s`
      · `h_phi_pow_psi`, `h_psi_pow_phi` — phi^(2N') and psi^(2N')
        characterizations (decidable per prime via decide)
      · `h_psi_sq` — psi recurrence (decidable per prime)
      · Index identities `h_idx_2N'_2 : 2*N' + 2 = p - 1`

    Conclusion: `pellCoeff p hp (N' + 1) = pellCoeff p hp 0`.

    PURE. -/
theorem universal_split_case
    (p : Nat) (hp : 1 < p) (hpo : p % 2 = 1)
    (s : Nat) (hs_lt : s < p) (hs_pos : 0 < s)
    (h_sqrt5 : s * s % p = 5 % p)
    (N' : Nat)
    (h_idx_2N'_2 : 2 * N' + 2 = p - 1)
    (h_prime_gcd : ∀ m, 0 < m → m < p → (modBezout m p).1 = 1)
    (h_phi_pos : 0 < phi p s)
    (h_psi_pos : 0 < psi p s)
    (h_phi_eq_psi_plus_s : (phi p s) % p = (psi p s + s) % p)
    (h_phi_pow_psi : (phi p s)^(2 * N') % p = (psi p s + 1) % p)
    (h_psi_pow_phi : (psi p s)^(2 * N') % p = (phi p s + 1) % p)
    (h_psi_sq : (psi p s * psi p s) % p = (psi p s + 1) % p) :
    pellCoeff p hp (N' + 1) = pellCoeff p hp 0 := by
  have hp_pos : 0 < p := Nat.lt_of_succ_lt hp
  -- 1. Universal FLT for phi and psi at index (p - 1)
  have h_phi_flt : (phi p s)^(p - 1) % p = 1 % p :=
    universal_flt_main (phi p s) p hp h_phi_pos
      (phi_lt p s hp_pos) h_prime_gcd
  have h_psi_flt : (psi p s)^(p - 1) % p = 1 % p :=
    universal_flt_main (psi p s) p hp h_psi_pos
      (psi_lt p s hp_pos) h_prime_gcd
  -- 2. ModInverse for s via Bezout
  have h_s_gcd : (modBezout s p).1 = 1 := h_prime_gcd s hs_pos hs_lt
  let mi_s : ModInverse p s := modInverseFromBezout s p hp_pos h_s_gcd
  -- 3. Fibonacci expansion at index (p - 1) for both phi and psi
  have h_phi_pow_fib_pm1 : (phi p s)^(p - 1) % p
            = ((fibLike (p - 1)).1 * phi p s + (fibLike (p - 1)).2) % p :=
    phi_pow_eq_fibLike p s hp hpo h_sqrt5 (p - 1)
  have h_psi_pow_fib_pm1 : (psi p s)^(p - 1) % p
            = ((fibLike (p - 1)).1 * psi p s + (fibLike (p - 1)).2) % p :=
    fibLike_pow p (psi p s) h_psi_sq (p - 1)
  -- 4. Binet F_{p-1} ≡ 0 via universal FLT
  have h_F_pm1_zero : (fibLike (p - 1)).1 % p = 0 :=
    binet_F_p_minus_1_zero p s hp_pos
      (fibLike (p - 1)).1 (fibLike (p - 1)).2
      h_phi_pow_fib_pm1 h_psi_pow_fib_pm1 h_phi_flt h_psi_flt
      h_phi_eq_psi_plus_s mi_s
  -- 5. Convert to fibFst (2*N' + 2) form via h_idx_2N'_2
  have h_F_top : fibFst (2 * N' + 2) % p = 0 := by
    show (fibLike (2 * N' + 2)).1 % p = 0
    rw [h_idx_2N'_2]
    exact h_F_pm1_zero
  -- 6. Fibonacci expansion at index (2 * N') for binet_F_p_minus_3
  have h_phi_pow_fib_2N' : (phi p s)^(2 * N') % p
            = ((fibLike (2 * N')).1 * phi p s + (fibLike (2 * N')).2) % p :=
    phi_pow_eq_fibLike p s hp hpo h_sqrt5 (2 * N')
  have h_psi_pow_fib_2N' : (psi p s)^(2 * N') % p
            = ((fibLike (2 * N')).1 * psi p s + (fibLike (2 * N')).2) % p :=
    fibLike_pow p (psi p s) h_psi_sq (2 * N')
  -- Combine with h_phi_pow_psi etc. to get the (psi + 1) / (phi + 1) forms
  have h_phi_pow_form : ((fibLike (2 * N')).1 * phi p s
                          + (fibLike (2 * N')).2) % p = (psi p s + 1) % p :=
    h_phi_pow_fib_2N'.symm.trans h_phi_pow_psi
  have h_psi_pow_form : ((fibLike (2 * N')).1 * psi p s
                          + (fibLike (2 * N')).2) % p = (phi p s + 1) % p :=
    h_psi_pow_fib_2N'.symm.trans h_psi_pow_phi
  -- 7. Binet F_{p-3} ≡ -1 (i.e., (F + 1) % p = 0)
  have h_F_low_plus_one : ((fibLike (2 * N')).1 + 1) % p = 0 :=
    binet_F_p_minus_3_plus_one_zero p s hp_pos
      (fibLike (2 * N')).1 (fibLike (2 * N')).2
      h_phi_pow_form h_psi_pow_form h_phi_eq_psi_plus_s mi_s
  -- 8. Convert to fibFst (2*N') % p = p - 1
  have h_F_low : fibFst (2 * N') % p = p - 1 :=
    mod_eq_p_minus_one_of_succ_mod_zero p (fibFst (2 * N')) hp h_F_low_plus_one
  -- 9. Apply phase_3_2_closure
  exact phase_3_2_closure p hp N' h_F_top h_F_low

/-! ## Per-prime smoke applications

Universal Phase 3.2 closure applied at specific split primes,
demonstrating that all hypotheses are decidable per prime.
-/

open E213.Lib.Math.ModArith.UniversalFLT (prime_gcd_11)

/-- ★★★★★★★★★ **Phase 3.2 at p=11 via UNIVERSAL closure**:
    `pellCoeff 11 _ 5 = pellCoeff 11 _ 0` derived through the
    universal end-to-end framework (Parts 11-32).

    No `decide` shortcut on FLT or matrix-order — every step
    structural via Universal FLT + Bezout + Binet. -/
theorem phase_3_2_at_11_universal :
    pellCoeff 11 (by decide) 5 = pellCoeff 11 (by decide) 0 :=
  universal_split_case 11 (by decide) (by decide)
    4 (by decide) (by decide) (by decide)
    4 (by decide) prime_gcd_11
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/- Smoke note: per-prime instantiation at p=19 would mirror p=11
   with `prime_gcd_19` (enumeration over m ∈ [1, 18]).  Mechanical
   follow-up. -/

end E213.Lib.Math.DyadicFSM.UniversalSplit
