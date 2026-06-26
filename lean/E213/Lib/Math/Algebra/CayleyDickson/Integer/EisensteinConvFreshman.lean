import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvBinomial
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFreshman

/-!
# The convolution freshman's dream in `R[C_p]` — `(f⊕g)^{⋆q} ≡ f^{⋆q} ⊕ g^{⋆q} (mod q)` (Phase B2e.3)

★★★★★ `convPow_add_pow_modEq_prime` : the Frobenius endomorphism of the group ring, coefficient-wise:

  `(f ⊕ g)^{⋆q}(k) ≡ f^{⋆q}(k) + g^{⋆q}(k)   (mod ofInt q)`   for prime `q`, `k < p`.

The convolution binomial theorem `convPow_add_pow` expands the `q`-th `⋆`-power; the two endpoints
give `g^{⋆q}(k)` (`j=0`, `e_0 ⋆ g^{⋆q}`) and `f^{⋆q}(k)` (`j=q`, `f^{⋆q} ⋆ e_0`), and every interior
coefficient `binom q j` (`0<j<q`) is `q`-divisible (`BinomPrime.prime_dvd_binom`), so the whole
interior sum vanishes mod `ofInt q`.  The `⋆`-analog of `EisensteinFreshman.add_pow_modEq_prime` —
the engine of the Gauss-sum Frobenius `g(χ)^{⋆q} ≡ χ̄(q)·g(χ) (mod q)` (Phase B2).

Carries `propext` (allowed-not-target) from `convPow_add_pow`; the divisibility core is PURE.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvFreshman

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq refl add_compat)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing (conv)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvPow
  (convPow convPow_zero convOne_left convOne_right)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvBinomial (convPow_add_pow)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinBinomial
  (cz cz_zero cz_diag sumRange_succ_bottom)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFreshman
  (dvd_mul_of_dvd_left ofInt_dvd dvd_sumRange)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum (sumRange sumRange_succ)
open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.NumberTheory.BinomPrime (prime_dvd_binom)
open E213.Lib.Math.NumberTheory.PolyRoot (nat_dvd_to_int)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (one_mul)
open E213.Meta.Algebra213.Ring213 (add_zero add_comm)

/-- `-(0 : ZOmega) = 0`. -/
private theorem neg_zero_zomega : (-(0 : ZOmega)) = 0 := by decide

/-- `d ∣ x ⟹ ModEq d x 0`. -/
private theorem modEq_zero_of_dvd {d x : ZOmega} (h : d ∣ x) : ModEq d x 0 := by
  show d ∣ (x + -0)
  rw [neg_zero_zomega, add_zero]; exact h

/-- ★★★★★ **The convolution freshman's dream** — `(f⊕g)^{⋆q}(k) ≡ f^{⋆q}(k) + g^{⋆q}(k) (mod ofInt q)`
    for a prime `q` and `k < p`.  The convolution binomial expansion's two endpoints survive; every
    interior term is `q`-divisible (interior `binom q j`), so the interior sum is `≡ 0`.  The
    Frobenius endomorphism of `R[C_p]` mod `q`.  ∅-axiom up to allowed `propext`. -/
theorem convPow_add_pow_modEq_prime (p : Nat) (f g : Nat → ZOmega) (q : Nat) (hq : 1 < q)
    (hqr : ∀ e, e ∣ q → e = 1 ∨ e = q) {k : Nat} (hk : k < p) :
    ModEq (ofInt ((q : Nat) : Int)) (convPow p (fun i => f i + g i) q k)
      (convPow p f q k + convPow p g q k) := by
  rcases q with _ | Q
  · exact absurd hq (by decide)
  · have hdecomp : convPow p (fun i => f i + g i) (Q + 1) k
        = (convPow p g (Q + 1) k
            + sumRange (fun j => cz (Q + 1) (j + 1)
                * conv p (convPow p f (j + 1)) (convPow p g ((Q + 1) - (j + 1))) k) Q)
          + convPow p f (Q + 1) k := by
      rw [convPow_add_pow p f g (Q + 1) k hk,
          sumRange_succ
            (fun j => cz (Q + 1) j * conv p (convPow p f j) (convPow p g ((Q + 1) - j)) k) (Q + 1),
          sumRange_succ_bottom
            (fun j => cz (Q + 1) j * conv p (convPow p f j) (convPow p g ((Q + 1) - j)) k) Q,
          show cz (Q + 1) (Q + 1)
                 * conv p (convPow p f (Q + 1)) (convPow p g ((Q + 1) - (Q + 1))) k
            = convPow p f (Q + 1) k by
            rw [Nat.sub_self, cz_diag, convPow_zero, convOne_right p (convPow p f (Q + 1)) hk,
                one_mul],
          show cz (Q + 1) 0 * conv p (convPow p f 0) (convPow p g ((Q + 1) - 0)) k
            = convPow p g (Q + 1) k by
            rw [Nat.sub_zero, cz_zero, convPow_zero, convOne_left p (convPow p g (Q + 1)) hk,
                one_mul]]
    -- interior terms are q-divisible
    have hterm : ∀ j, j < Q → ofInt ((Q + 1 : Nat) : Int) ∣
        (cz (Q + 1) (j + 1) * conv p (convPow p f (j + 1)) (convPow p g ((Q + 1) - (j + 1))) k) :=
      fun j hj => by
        have hnat : (Q + 1) ∣ binom (Q + 1) (j + 1) :=
          prime_dvd_binom (Q + 1) (j + 1) hq hqr (Nat.succ_le_succ (Nat.zero_le j))
            (Nat.succ_lt_succ hj)
        have hint : ((Q + 1 : Nat) : Int) ∣ ((binom (Q + 1) (j + 1) : Nat) : Int) :=
          nat_dvd_to_int (Q + 1) ((binom (Q + 1) (j + 1) : Nat) : Int)
            (by rw [Int.natAbs_ofNat]; exact hnat)
        exact dvd_mul_of_dvd_left (ofInt_dvd hint) _
    have hM : ModEq (ofInt ((Q + 1 : Nat) : Int))
        (sumRange (fun j => cz (Q + 1) (j + 1)
            * conv p (convPow p f (j + 1)) (convPow p g ((Q + 1) - (j + 1))) k) Q) 0 :=
      modEq_zero_of_dvd (dvd_sumRange _ Q hterm)
    rw [hdecomp]
    have h1 : ModEq (ofInt ((Q + 1 : Nat) : Int))
        ((convPow p g (Q + 1) k
            + sumRange (fun j => cz (Q + 1) (j + 1)
                * conv p (convPow p f (j + 1)) (convPow p g ((Q + 1) - (j + 1))) k) Q)
          + convPow p f (Q + 1) k)
        ((convPow p g (Q + 1) k + 0) + convPow p f (Q + 1) k) :=
      add_compat (add_compat (refl _ (convPow p g (Q + 1) k)) hM)
        (refl _ (convPow p f (Q + 1) k))
    have h2 : (convPow p g (Q + 1) k + 0) + convPow p f (Q + 1) k
        = convPow p f (Q + 1) k + convPow p g (Q + 1) k := by rw [add_zero, add_comm]
    rw [h2] at h1
    exact h1

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvFreshman
