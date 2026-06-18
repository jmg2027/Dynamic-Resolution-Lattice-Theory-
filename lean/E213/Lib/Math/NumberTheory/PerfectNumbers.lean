import E213.Lib.Math.NumberTheory.MobiusDivisorSum
import E213.Lib.Math.NumberTheory.DivisorMultiplicative
import E213.Lib.Math.NumberTheory.DirichletIdentities
import E213.Lib.Math.NumberTheory.FactorialLcmDvd
import E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative
import E213.Lib.Math.NumberTheory.MobiusBridge
import E213.Meta.Int213.PolyIntMTactic

/-!
# Perfect numbers + Euclid's theorem (∅-axiom)

`N` is **perfect** iff `σ(N) = 2·N`.

★★★ **Euclid's theorem**: if `q = 2^(k+1) − 1` is prime then `N = 2^k · q` is
perfect.  Proof: `gcd(2^k, q) = 1` (q odd) ⇒ `σ(N) = σ(2^k)·σ(q)`
(`sigma_mul`); `σ(2^k) = 2^(k+1) − 1 = q` (geometric sum, via the prime-power
divisor reindex); `σ(q) = q + 1 = 2^(k+1)`; so
`σ(N) = q·2^(k+1) = 2·(2^k·q) = 2·N`.

Built entirely on the corpus σ-framework:
  * `sigma`, `sigma_mul` (σ multiplicative over coprime products).
  * `divisorSumZ_prime_pow_reindex` : `divisorSumZ (pᵏ) g = Σ_{i≤k} g(pⁱ)`.
  * `sigma_eq_id_conv_one` / `castSumTo` bridge : `(σ n : Int) = divisorSumZ n id`.
  * `coprime_pow_left`, `prime2`, `prime_coprime_of_not_dvd`.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.PerfectNumbers

open E213.Lib.Math.NumberTheory.SumOfDivisors (sigma)
open E213.Lib.Math.NumberTheory.DivisorMultiplicative (sigma_mul)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213 prime_coprime_of_not_dvd)
open E213.Lib.Math.NumberTheory.MobiusFunction (divisorSumZ)
open E213.Lib.Math.NumberTheory.MobiusDivisorSum (sumPowZ divisorSumZ_prime_pow_reindex)
open E213.Lib.Math.NumberTheory.DirichletConvolution (dconv dconv_one_right)
open E213.Lib.Math.NumberTheory.DirichletIdentities (sigma_eq_id_conv_one)
open E213.Lib.Math.NumberTheory.FactorialLcmDvd (prime2)
open E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative (coprime_pow_left)
open E213.Tactic.NatHelper (gcd213)

/-- `N` is **perfect** iff `σ(N) = 2·N`. -/
def Perfect (n : Nat) : Prop := sigma n = 2 * n

/-! ## §1 — `(σ n : Int) = divisorSumZ n (fun d => (d : Int))` -/

/-- Bridge: the Nat σ, cast to `Int`, equals the Int divisor sum of the identity. -/
theorem sigma_cast_eq_divisorSumZ (n : Nat) (hn : 0 < n) :
    (sigma n : Int) = divisorSumZ n (fun d => (d : Int)) := by
  have h := sigma_eq_id_conv_one n hn
  rw [dconv_one_right (fun d => (d : Int)) n] at h
  exact h.symm

/-! ## §2 — `σ(pᵏ) = Σ_{i≤k} pⁱ` as an Int identity, and the closed form for p=2 -/

/-- Nat doubling of a power of two: `2^(k+2) = 2^(k+1) + 2^(k+1)`. -/
theorem two_pow_double (k : Nat) :
    (2 : Nat) ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := by
  rw [Nat.pow_succ]
  show 2 ^ (k + 1) * 2 = 2 ^ (k + 1) + 2 ^ (k + 1)
  rw [Nat.mul_two]

/-- `sumPowZ (fun d => (d:Int)) 2 k + 1 = (2^(k+1) : Nat)` (cast to Int): the geometric
    sum `Σ_{i≤k} 2ⁱ = 2^(k+1) − 1`, kept subtraction-free as `Σ + 1 = 2^(k+1)`.
    Everything stays a Nat-cast power, so no Int `^` enters.  Induction on `k`. -/
theorem sumPowZ_two_succ (k : Nat) :
    sumPowZ (fun d => (d : Int)) 2 k + 1 = (((2 : Nat) ^ (k + 1) : Nat) : Int) := by
  induction k with
  | zero =>
      show (((2 : Nat) ^ 0 : Nat) : Int) + 1 = (((2 : Nat) ^ 1 : Nat) : Int)
      decide
  | succ k ih =>
      show (sumPowZ (fun d => (d : Int)) 2 k + (((2 : Nat) ^ (k + 1) : Nat) : Int)) + 1
          = (((2 : Nat) ^ (k + 2) : Nat) : Int)
      rw [two_pow_double k, Int.ofNat_add]
      -- goal: (S + A) + 1 = A + A, with S + 1 = A from ih
      have hA : (((2 : Nat) ^ (k + 1) : Nat) : Int) = sumPowZ (fun d => (d : Int)) 2 k + 1 :=
        ih.symm
      rw [hA]; ring_intZ

/-- ★★ **σ(2ᵏ) + 1 = 2^(k+1)** (Int form, subtraction-free): the divisor sum of `2ᵏ`
    is the geometric sum `Σ_{i≤k} 2ⁱ`. -/
theorem sigma_two_pow_succ_int (k : Nat) :
    (sigma (2 ^ k) : Int) + 1 = (((2 : Nat) ^ (k + 1) : Nat) : Int) := by
  have hpos : 0 < 2 ^ k := Nat.pos_pow_of_pos k (by decide)
  rw [sigma_cast_eq_divisorSumZ (2 ^ k) hpos,
      divisorSumZ_prime_pow_reindex prime2 k (fun d => (d : Int))]
  exact sumPowZ_two_succ k

/-- ★★ **σ(2ᵏ) + 1 = 2^(k+1)** (Nat form): de-cast of `sigma_two_pow_succ_int`. -/
theorem sigma_two_pow_succ (k : Nat) :
    sigma (2 ^ k) + 1 = 2 ^ (k + 1) := by
  apply Int.ofNat.inj
  show ((sigma (2 ^ k) : Int)) + ((1 : Nat) : Int) = (((2 : Nat) ^ (k + 1) : Nat) : Int)
  rw [show ((1 : Nat) : Int) = (1 : Int) from rfl]
  exact sigma_two_pow_succ_int k

/-! ## §3 — `σ(q) = q + 1` for `q` prime (q = q¹, the k=1 reindex) -/

/-- ★★ **σ(prime) = prime + 1** (Int form): a prime `q` has divisor sum `1 + q`. -/
theorem sigma_prime_cast {q : Nat} (hq : Prime213 q) :
    (sigma q : Int) = (q : Int) + 1 := by
  have hq0 : 0 < q := Nat.lt_of_lt_of_le (by decide) hq.1
  have hq1 : q = q ^ 1 := (Nat.pow_one q).symm
  rw [hq1, sigma_cast_eq_divisorSumZ (q ^ 1) (hq1 ▸ hq0),
      divisorSumZ_prime_pow_reindex hq 1 (fun d => (d : Int))]
  show (((q ^ 0 : Nat) : Int) + ((q ^ 1 : Nat) : Int)) = ((q ^ 1 : Nat) : Int) + 1
  rw [Nat.pow_zero, Nat.pow_one]
  show ((1 : Nat) : Int) + (q : Int) = (q : Int) + 1
  rw [show ((1 : Nat) : Int) = (1 : Int) from rfl]
  ring_intZ

/-- ★★ **σ(prime) = prime + 1** (Nat form): de-cast of `sigma_prime_cast`. -/
theorem sigma_prime {q : Nat} (hq : Prime213 q) : sigma q = q + 1 := by
  apply Int.ofNat.inj
  show ((sigma q : Int)) = (q : Int) + ((1 : Nat) : Int)
  rw [show ((1 : Nat) : Int) = (1 : Int) from rfl]
  exact sigma_prime_cast hq

/-! ## §4 — coprimality `gcd(2ᵏ, q) = 1` for `q` odd -/

/-- `q + 1 = 2^(k+1)` ⇒ `2 ∤ q` (q is odd, being a Mersenne number `2ᵐ − 1`).
    From `2 ∣ q` and `2 ∣ q+1` we get `2 ∣ (q+1) − q = 1`, contradiction. -/
theorem two_not_dvd_mersenne {k q : Nat} (hk : q + 1 = 2 ^ (k + 1)) : ¬ 2 ∣ q := by
  intro hdq
  have h2pow : (2 : Nat) ∣ 2 ^ (k + 1) := ⟨2 ^ k, by rw [Nat.pow_succ, Nat.mul_comm]⟩
  have h2q1 : (2 : Nat) ∣ q + 1 := hk ▸ h2pow
  have hle : q ≤ q + 1 := Nat.le_succ q
  have hdvd1 : (2 : Nat) ∣ (q + 1) - q :=
    E213.Meta.Nat.Gcd213.dvd_sub_213 q (q + 1) 2 hle hdq h2q1
  rw [E213.Tactic.NatHelper.succ_sub q] at hdvd1
  -- `2 ∣ 1` forces `2 = 1` (`eq_one_of_dvd_one`), impossible.
  have h21 : (2 : Nat) = 1 := E213.Lib.Math.NumberTheory.MobiusBridge.eq_one_of_dvd_one hdvd1
  exact absurd h21 (by decide)

/-- `gcd(2ᵏ, q) = 1` for a Mersenne-prime `q` (q odd ⇒ coprime to every power of 2). -/
theorem coprime_two_pow_mersenne {k q : Nat} (hk : q + 1 = 2 ^ (k + 1)) :
    gcd213 (2 ^ k) q = 1 := by
  have h2q : gcd213 2 q = 1 := prime_coprime_of_not_dvd prime2 (two_not_dvd_mersenne hk)
  exact coprime_pow_left h2q k

/-! ## §5 — ★★★ Euclid's perfect-number theorem (general k) -/

/-- ★★★ **Euclid's theorem**: if `q = 2^(k+1) − 1` is prime, then `N = 2ᵏ·q` is perfect,
    i.e. `σ(N) = 2·N`.

    `gcd(2ᵏ,q)=1` (q odd) ⇒ `σ(N) = σ(2ᵏ)·σ(q)` (`sigma_mul`).  `σ(2ᵏ) = 2^(k+1)−1 = q`
    (`sigma_two_pow_succ` + the Mersenne hypothesis), `σ(q) = q+1 = 2^(k+1)`
    (`sigma_prime`).  So `σ(N) = q·(q+1) = (q+1)·q = 2^(k+1)·q = 2·(2ᵏ·q) = 2·N`.
    Worked in `ℕ`, subtraction-free: `q + 1 = 2^(k+1)` carried as a hypothesis,
    and `σ(2ᵏ) = q` recovered by Nat `add_right_cancel` (both `+1` equal `2^(k+1)`). -/
theorem euclid_perfect {k q : Nat} (hq : Prime213 q) (hk : q + 1 = 2 ^ (k + 1)) :
    Perfect (2 ^ k * q) := by
  have hq0 : 0 < q := Nat.lt_of_lt_of_le (by decide) hq.1
  have hpos : 0 < 2 ^ k := Nat.pos_pow_of_pos k (by decide)
  have hcop : gcd213 (2 ^ k) q = 1 := coprime_two_pow_mersenne hk
  -- σ(2ᵏ) = q : both `+1` equal `2^(k+1)`, cancel the `+1`.
  have hσ2q : sigma (2 ^ k) = q := by
    have h1 : sigma (2 ^ k) + 1 = q + 1 := (sigma_two_pow_succ k).trans hk.symm
    exact E213.Tactic.NatHelper.add_right_cancel h1
  -- σ(q) = q + 1.
  have hσq : sigma q = q + 1 := sigma_prime hq
  -- assemble.
  show sigma (2 ^ k * q) = 2 * (2 ^ k * q)
  rw [sigma_mul hcop hpos hq0, hσ2q, hσq]
  -- goal: q * (q + 1) = 2 * (2^k * q)
  -- RHS: 2 * (2^k * q) = (2 * 2^k) * q = 2^(k+1) * q = (q+1) * q
  have hrhs : 2 * (2 ^ k * q) = (q + 1) * q := by
    have h2 : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2]
    calc 2 * (2 ^ k * q) = (2 * 2 ^ k) * q := by rw [E213.Tactic.NatHelper.mul_assoc]
      _ = 2 ^ (k + 1) * q := by rw [h2]
      _ = (q + 1) * q := by rw [hk]
  rw [hrhs]
  -- q * (q + 1) = (q + 1) * q
  exact Nat.mul_comm q (q + 1)

/-! ## §6 — concrete perfect-number smokes (the first three perfect numbers) -/

/-- `Prime213` of a concrete `q` via the `√q`-bounded primality check: a small factor
    `d` (`2 ≤ d`, `d*d ≤ q`) satisfies `d < B`, and a `decide` over `d < B` rules out
    `q % d = 0`. -/
theorem prime_of_bounded {q B : Nat} (h2 : 2 ≤ q) (hB : B * B > q)
    (hcheck : ∀ d, d < B → 2 ≤ d → q % d = 0 → False) : Prime213 q := by
  refine ⟨h2, E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor.prime_of_no_small_factor q h2 ?_⟩
  intro d hd2 hdsq hdvd
  obtain ⟨c, hc⟩ := hdvd
  have hmod : q % d = 0 := by rw [hc]; exact E213.Tactic.NatHelper.mul_mod_right d c
  rcases Nat.lt_or_ge d B with hlt | hge
  · exact hcheck d hlt hd2 hmod
  · exact absurd hdsq (Nat.not_le_of_lt (Nat.lt_of_lt_of_le hB (Nat.mul_le_mul hge hge)))

theorem prime3  : Prime213 3  := prime_of_bounded (by decide) (B := 2) (by decide) (by decide)
theorem prime7  : Prime213 7  := prime_of_bounded (by decide) (B := 3) (by decide) (by decide)
theorem prime31 : Prime213 31 := prime_of_bounded (by decide) (B := 6) (by decide) (by decide)

/-- The first three perfect numbers `6 = 2¹·3`, `28 = 2²·7`, `496 = 2⁴·31`
    (Mersenne primes `3, 7, 31`) via `euclid_perfect` at general `k = 1, 2, 4`. -/
theorem perfect_6   : Perfect (2 ^ 1 * 3)  := euclid_perfect (k := 1) prime3  (by decide)
theorem perfect_28  : Perfect (2 ^ 2 * 7)  := euclid_perfect (k := 2) prime7  (by decide)
theorem perfect_496 : Perfect (2 ^ 4 * 31) := euclid_perfect (k := 4) prime31 (by decide)

set_option maxRecDepth 8000 in
/-- σ values of the first three perfect numbers (closed, by `decide`):
    σ(6)=12, σ(28)=56, σ(496)=992. -/
theorem perfect_sigma_table :
    sigma 6 = 12 ∧ sigma 28 = 56 ∧ sigma 496 = 992 := by decide


/-! ## Abundant / deficient classification -/

/-- `n` is **abundant** if `σ(n) > 2n` (its proper divisors exceed it). -/
def Abundant (n : Nat) : Prop := 2 * n < sigma n
/-- `n` is **deficient** if `σ(n) < 2n`. -/
def Deficient (n : Nat) : Prop := sigma n < 2 * n

/-- ★★ **Perfect/abundant/deficient trichotomy**: every `n` is exactly one of perfect
    (`σ=2n`), abundant (`σ>2n`), or deficient (`σ<2n`).  Completes the classification around
    the Euclid/Euler perfect-number work. -/
theorem perfect_abundant_deficient_trichotomy (n : Nat) :
    Perfect n ∨ Abundant n ∨ Deficient n := by
  rcases Nat.lt_trichotomy (sigma n) (2 * n) with h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- ★ **Primes are deficient**: `σ(q) = q+1 < 2q` for a prime `q` (`q ≥ 2`). -/
theorem prime_deficient {q : Nat} (hq : Prime213 q) : Deficient q := by
  show sigma q < 2 * q
  rw [sigma_prime hq, Nat.two_mul]
  exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le (by decide) hq.1) q


/-- ★ Concrete classification: `12, 18, 20, 24` are abundant; `8, 9, 10` are deficient. -/
theorem abundant_12 : Abundant 12 := by show 2 * 12 < sigma 12; decide
theorem abundant_18 : Abundant 18 := by show 2 * 18 < sigma 18; decide
theorem abundant_20 : Abundant 20 := by show 2 * 20 < sigma 20; decide
theorem deficient_8 : Deficient 8 := by show sigma 8 < 2 * 8; decide
theorem deficient_9 : Deficient 9 := by show sigma 9 < 2 * 9; decide
theorem deficient_10 : Deficient 10 := by show sigma 10 < 2 * 10; decide


/-- ★★ **Euclid perfect numbers are triangular**: `2 · N = m·(m+1)` with `m = 2^{k+1}−1`,
    i.e. `N = 2^k·(2^{k+1}−1)` is the `m`-th triangular number `T_m = m(m+1)/2`.  (Every even
    perfect number is triangular.) -/
theorem even_perfect_triangular (k : Nat) :
    2 * (2 ^ k * (2 ^ (k + 1) - 1)) = (2 ^ (k + 1) - 1) * ((2 ^ (k + 1) - 1) + 1) := by
  have hm1 : (2 ^ (k + 1) - 1) + 1 = 2 ^ (k + 1) :=
    E213.Tactic.NatHelper.sub_one_add_one (Nat.ne_of_gt (Nat.pos_pow_of_pos _ (by decide)))
  rw [hm1, ← E213.Tactic.NatHelper.mul_assoc, Nat.mul_comm 2 (2 ^ k), ← Nat.pow_succ,
      Nat.mul_comm (2 ^ (k + 1)) (2 ^ (k + 1) - 1)]

end E213.Lib.Math.NumberTheory.PerfectNumbers
