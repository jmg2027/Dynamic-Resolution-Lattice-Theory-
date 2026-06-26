import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinBinomial
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplit
import E213.Lib.Math.NumberTheory.PolyRoot.IntEuclid

/-!
# The freshman's dream in `ℤ[ω]` — `(a+b)^q ≡ a^q + b^q (mod q)` for prime `q` (∅-axiom)

★★★★★ `add_pow_modEq_prime` : for a rational prime `q`, the Frobenius endomorphism in `ℤ[ω]`:

  `(a + b)^q ≡ a^q + b^q   (mod ofInt q)`.

The binomial theorem `add_pow` expands `(a+b)^q = Σ_{k=0}^{q} binom q k · a^k · b^{q−k}`; the two
endpoints give `b^q` (`k=0`) and `a^q` (`k=q`), and every **interior** coefficient `binom q k`
(`0<k<q`) is divisible by `q` (`BinomPrime.prime_dvd_binom`), so the whole interior sum vanishes mod
`ofInt q`.  This is the Frobenius (`x ↦ x^q`) ring-endomorphism-mod-`q`, the engine of the
cubic-reciprocity Frobenius congruence `g(χ)^q ≡ χ̄(q)·g(χ) (mod q)` (Phase B2).

Carries `propext` (allowed-not-target) only from the `add_pow` cast bookkeeping; the divisibility
core is PURE.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFreshman

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq refl trans add_compat)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinBinomial
  (cz cz_zero cz_diag bterm add_pow sumRange_succ_bottom)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplit (ofInt_mul)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality
  (pow pow_zero pow_succ one_mul mul_one)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum
  (sumRange sumRange_zero sumRange_succ)
open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.NumberTheory.BinomPrime (prime_dvd_binom)
open E213.Lib.Math.NumberTheory.PolyRoot (nat_dvd_to_int)
open E213.Meta.Algebra213.Ring213 (add_zero add_comm mul_add mul_assoc mul_zero)

/-- `d ∣ x → d ∣ y → d ∣ (x+y)` in `ℤ[ω]`. -/
theorem dvd_add {d x y : ZOmega} (hx : d ∣ x) (hy : d ∣ y) : d ∣ (x + y) := by
  obtain ⟨c1, hc1⟩ := hx
  obtain ⟨c2, hc2⟩ := hy
  exact ⟨c1 + c2, by rw [hc1, hc2, mul_add]⟩

/-- `d ∣ x → d ∣ (x·y)` in `ℤ[ω]`. -/
theorem dvd_mul_of_dvd_left {d x : ZOmega} (hx : d ∣ x) (y : ZOmega) : d ∣ (x * y) := by
  obtain ⟨c, hc⟩ := hx
  exact ⟨c * y, by rw [hc, mul_assoc]⟩

/-- The `ℤ → ℤ[ω]` embedding preserves divisibility: `a ∣ b → ofInt a ∣ ofInt b`. -/
theorem ofInt_dvd {a b : Int} (h : a ∣ b) : ofInt a ∣ ofInt b := by
  obtain ⟨c, hc⟩ := h
  exact ⟨ofInt c, by rw [hc, ofInt_mul]⟩

/-- `-(0 : ZOmega) = 0`. -/
private theorem neg_zero_zomega : (-(0 : ZOmega)) = 0 := by decide

/-- `d ∣ x ⟹ ModEq d x 0` — package a divisibility as a congruence to `0`. -/
private theorem modEq_zero_of_dvd {d x : ZOmega} (h : d ∣ x) : ModEq d x 0 := by
  show d ∣ (x + -0)
  rw [neg_zero_zomega, add_zero]; exact h

/-- Divisibility passes through a finite sum: if `d ∣ f k` for all `k < n`, then `d ∣ Σ_{k<n} f k`. -/
theorem dvd_sumRange {d : ZOmega} (f : Nat → ZOmega) :
    ∀ n, (∀ k, k < n → d ∣ f k) → d ∣ sumRange f n
  | 0, _ => ⟨0, by show (0 : ZOmega) = d * 0; rw [mul_zero]⟩
  | n + 1, h => by
      rw [sumRange_succ]
      exact dvd_add (dvd_sumRange f n (fun k hk => h k (Nat.lt_succ_of_lt hk)))
                    (h n (Nat.lt_succ_self n))

/-- **An interior binomial term is divisible by `ofInt q`** — for a prime `q` and `1 ≤ t < q`,
    `ofInt q ∣ bterm a b q t`, because `q ∣ binom q t` (`prime_dvd_binom`) lifts to
    `ofInt q ∣ cz q t`, the coefficient factor of `bterm`. -/
theorem ofIntq_dvd_bterm (a b : ZOmega) {q t : Nat} (hq : 1 < q)
    (hqr : ∀ e, e ∣ q → e = 1 ∨ e = q) (ht1 : 1 ≤ t) (htq : t < q) :
    ofInt ((q : Nat) : Int) ∣ bterm a b q t := by
  have hnat : q ∣ binom q t := prime_dvd_binom q t hq hqr ht1 htq
  have hint : ((q : Nat) : Int) ∣ ((binom q t : Nat) : Int) :=
    nat_dvd_to_int q ((binom q t : Nat) : Int) (by rw [Int.natAbs_ofNat]; exact hnat)
  show ofInt ((q : Nat) : Int) ∣ cz q t * (pow a t * pow b (q - t))
  exact dvd_mul_of_dvd_left (ofInt_dvd hint) (pow a t * pow b (q - t))

/-- ★★★★★ **The freshman's dream in `ℤ[ω]`** — `(a+b)^q ≡ a^q + b^q (mod ofInt q)` for a prime `q`.
    The binomial expansion's two endpoints survive; every interior term is `q`-divisible
    (`ofIntq_dvd_bterm`), so their sum is `≡ 0`.  The Frobenius endomorphism mod `q`.  ∅-axiom up to
    allowed `propext` (from `add_pow`). -/
theorem add_pow_modEq_prime (a b : ZOmega) (q : Nat) (hq : 1 < q)
    (hqr : ∀ e, e ∣ q → e = 1 ∨ e = q) :
    ModEq (ofInt ((q : Nat) : Int)) (pow (a + b) q) (pow a q + pow b q) := by
  rcases q with _ | Q
  · exact absurd hq (by decide)
  · have hdecomp : pow (a + b) (Q + 1)
        = (pow b (Q + 1) + sumRange (fun k => bterm a b (Q + 1) (k + 1)) Q) + pow a (Q + 1) := by
      rw [add_pow a b (Q + 1),
          sumRange_succ (fun k => bterm a b (Q + 1) k) (Q + 1),
          sumRange_succ_bottom (fun k => bterm a b (Q + 1) k) Q,
          show bterm a b (Q + 1) (Q + 1) = pow a (Q + 1) by
            show cz (Q + 1) (Q + 1) * (pow a (Q + 1) * pow b ((Q + 1) - (Q + 1))) = pow a (Q + 1)
            rw [Nat.sub_self, cz_diag, pow_zero, mul_one, one_mul],
          show bterm a b (Q + 1) 0 = pow b (Q + 1) by
            show cz (Q + 1) 0 * (pow a 0 * pow b ((Q + 1) - 0)) = pow b (Q + 1)
            rw [Nat.sub_zero, cz_zero, pow_zero, one_mul, one_mul]]
    have hM : ModEq (ofInt ((Q + 1 : Nat) : Int))
        (sumRange (fun k => bterm a b (Q + 1) (k + 1)) Q) 0 :=
      modEq_zero_of_dvd (dvd_sumRange _ Q (fun k hk =>
        ofIntq_dvd_bterm a b hq hqr (Nat.succ_le_succ (Nat.zero_le k)) (Nat.succ_lt_succ hk)))
    rw [hdecomp]
    have h1 : ModEq (ofInt ((Q + 1 : Nat) : Int))
        ((pow b (Q + 1) + sumRange (fun k => bterm a b (Q + 1) (k + 1)) Q) + pow a (Q + 1))
        ((pow b (Q + 1) + 0) + pow a (Q + 1)) :=
      add_compat (add_compat (refl _ (pow b (Q + 1))) hM) (refl _ (pow a (Q + 1)))
    have h2 : (pow b (Q + 1) + 0) + pow a (Q + 1) = pow a (Q + 1) + pow b (Q + 1) := by
      rw [add_zero, add_comm]
    rw [h2] at h1
    exact h1

/-- `pow (0 : ZOmega) q = 0` for `q ≥ 1`. -/
private theorem pow_zero_base_pos {q : Nat} (hq : 1 < q) : pow (0 : ZOmega) q = 0 := by
  have hq0 : q ≠ 0 := by intro h; rw [h] at hq; exact absurd hq (by decide)
  obtain ⟨Q, hQ⟩ := Nat.exists_eq_succ_of_ne_zero hq0
  rw [hQ, pow_succ, mul_zero]

/-- ★★★★★ **The multinomial freshman's dream in `ℤ[ω]`** — the `n`-ary Frobenius:

      `(Σ_{i<n} f i)^q ≡ Σ_{i<n} (f i)^q   (mod ofInt q)`   for prime `q`.

    Iterating the two-term dream (`add_pow_modEq_prime`) over the finite sum: each `succ` step peels
    `f n` and applies the binary dream plus the inductive congruence under `+`.  The coefficient-ring
    template for the group-ring (Gauss-sum) Frobenius.  ∅-axiom up to allowed `propext`. -/
theorem sum_pow_modEq_prime (f : Nat → ZOmega) {q : Nat} (hq : 1 < q)
    (hqr : ∀ e, e ∣ q → e = 1 ∨ e = q) (n : Nat) :
    ModEq (ofInt ((q : Nat) : Int)) (pow (sumRange f n) q)
      (sumRange (fun i => pow (f i) q) n) := by
  induction n with
  | zero =>
      show ModEq (ofInt ((q : Nat) : Int)) (pow (0 : ZOmega) q) (0 : ZOmega)
      rw [pow_zero_base_pos hq]; exact refl _ 0
  | succ n ih =>
      show ModEq (ofInt ((q : Nat) : Int)) (pow (sumRange f n + f n) q)
        (sumRange (fun i => pow (f i) q) n + pow (f n) q)
      exact trans (add_pow_modEq_prime (sumRange f n) (f n) q hq hqr)
        (add_compat ih (refl _ (pow (f n) q)))

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFreshman
