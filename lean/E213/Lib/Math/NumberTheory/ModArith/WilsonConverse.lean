import E213.Lib.Math.NumberTheory.FactorialLcmDvd
import E213.Lib.Math.Combinatorics.Permutations
import E213.Lib.Math.NumberTheory.PrimeValuation
import E213.Meta.Nat.VpSeparation
import E213.Meta.Nat.VpMul
import E213.Meta.Nat.NatRing213

/-!
# Wilson's converse `(n−1)! ≡ 0 (mod n)` for composite `n > 4`  (∅-axiom)

★★★ `wilson_converse (hn : 4 < n) (hcomp : ¬ Prime213 n) : fact (n−1) % n = 0`.

For composite `n > 4`, `n ∣ (n−1)!`.  Complements Wilson's theorem
(`WilsonTheorem.wilson`, `(p−1)! ≡ −1 mod p` for primes).

Proof: a composite `n` (`2 ≤ n`, not prime) has a nontrivial factor `a` with
`1 < a < n` and cofactor `b = n/a`, `1 < b < n`, `a·b = n`.
- `a ≠ b`: `a`, `b` are distinct factors in `{1,…,n−1}`, so `a·b = n` divides
  `(n−1)!` via `mul_dvd_factorial`.
- `a = b` (`n = a²`, so `a ≥ 3` since `n > 4`): `a` and `2a` are distinct and
  `< n = a²` (as `2 < a`), so `a·(2a) = 2a² ∣ (n−1)!`, hence `a² = n ∣ (n−1)!`.
The excluded `n = 4 = 2²` is exactly Wilson's converse's exception.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.WilsonConverse

open E213.Lib.Math.Combinatorics.Permutations (fact)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial (factorial factorial_succ)
open E213.Lib.Math.NumberTheory.FactorialLcmDvd (dvd_factorial mul_dvd_factorial le_of_dvd_pos)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Meta.Nat.VpSeparation (exists_prime_factor)
open E213.Meta.Nat.VpMul (IsPrime213)
open E213.Meta.Nat.NatRing213 (nat_mul_lt_mul_right nat_mul_lt_mul_left)

/-! ## §0 — `fact = factorial` bridge (both are `0↦1`, `n+1 ↦ (n+1)·_`) -/

theorem fact_eq_factorial : ∀ n, fact n = factorial n
  | 0     => rfl
  | n + 1 => by
    show (n + 1) * fact n = (n + 1) * factorial n
    rw [fact_eq_factorial n]

/-! ## §1 — composite ⟹ nontrivial factor -/

/-- A composite `n` (`2 ≤ n`, `¬ Prime213 n`) has a divisor `a` with `a ≠ 1`, `a ≠ n`.
    Take any prime factor `q ∣ n` (`exists_prime_factor`): `q ≠ 1` (prime ⟹ `2 ≤ q`)
    and `q ≠ n` (else `IsPrime213 n = Prime213 n`, contradicting `¬ Prime213 n`).
    `Classical`-free: the prime factor is built by bounded search, not negation. -/
theorem exists_nontrivial_factor {n : Nat} (hn2 : 2 ≤ n) (hcomp : ¬ Prime213 n) :
    ∃ a, a ∣ n ∧ a ≠ 1 ∧ a ≠ n := by
  obtain ⟨q, hqpr, hqn⟩ := exists_prime_factor n n (Nat.le_refl n) hn2
  refine ⟨q, hqn, ?_, ?_⟩
  · -- q ≠ 1 (primes are ≥ 2)
    intro he
    have : (2 : Nat) ≤ 1 := he ▸ hqpr.1
    exact absurd this (by decide)
  · -- q ≠ n (else n prime)
    intro he
    -- IsPrime213 q with q = n gives IsPrime213 n; defeq to Prime213 n
    have hpn : Prime213 n := he ▸ hqpr
    exact hcomp hpn

/-! ## §2 — bounds on the factor -/

/-- A nontrivial divisor `a` of `n > 1` satisfies `1 < a < n` (with witness cofactor). -/
theorem factor_bounds {n a : Nat} (hn2 : 2 ≤ n) (hd : a ∣ n) (ha1 : a ≠ 1) (han : a ≠ n) :
    1 < a ∧ a < n := by
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) hn2
  -- a ≠ 0 (else 0 ∣ n forces n = 0)
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · exfalso
      rcases hd with ⟨c, hc⟩
      rw [h0, Nat.zero_mul] at hc
      exact absurd (hc ▸ hnpos) (Nat.lt_irrefl 0)
    · exact hpos
  -- 1 < a: a > 0 and a ≠ 1
  have h1a : 1 < a := by
    rcases Nat.lt_or_ge 1 a with h | h
    · exact h
    · -- a ≤ 1 and a > 0 ⟹ a = 1, contra
      have : a = 1 := Nat.le_antisymm h ha0
      exact absurd this ha1
  -- a ≤ n, a ≠ n ⟹ a < n
  have hale : a ≤ n := le_of_dvd_pos hnpos hd
  have han' : a < n := by
    rcases Nat.lt_or_ge a n with h | h
    · exact h
    · have : a = n := Nat.le_antisymm hale h
      exact absurd this han
  exact ⟨h1a, han'⟩

/-! ## §3 — Wilson's converse -/

/-- ★★★ **Wilson's converse.**  For composite `n > 4`, `(n−1)! ≡ 0 (mod n)`,
    i.e. `n ∣ (n−1)!`.  Stated as `fact (n−1) % n = 0` (corpus Wilson shape). -/
theorem wilson_converse {n : Nat} (hn : 4 < n) (hcomp : ¬ Prime213 n) :
    fact (n - 1) % n = 0 := by
  have hn2 : 2 ≤ n := Nat.le_of_lt (Nat.lt_of_le_of_lt (by decide) hn)
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) hn2
  -- get a nontrivial factor a, cofactor b with n = a * b
  obtain ⟨a, hd, ha1, han⟩ := exists_nontrivial_factor hn2 hcomp
  obtain ⟨h1a, han'⟩ := factor_bounds hn2 hd ha1 han
  obtain ⟨b, hab⟩ := hd          -- n = a * b
  -- bounds on b: 1 < b < n  (b is also a nontrivial divisor: n = b * a)
  have hdb : b ∣ n := ⟨a, by rw [hab, Nat.mul_comm]⟩
  have hb1 : b ≠ 1 := by
    intro he
    rw [he, Nat.mul_one] at hab
    exact absurd hab.symm han   -- a = n contra a ≠ n
  have hbn : b ≠ n := by
    intro he
    -- n = a * n with a > 1 ⟹ n < a * n, contradiction (n > 0)
    rw [he] at hab
    -- hab : n = a * n
    have : n < a * n := by
      have h2a : 2 ≤ a := h1a
      calc n = 1 * n := (Nat.one_mul n).symm
        _ < a * n := nat_mul_lt_mul_right hnpos h1a
    rw [← hab] at this
    exact absurd this (Nat.lt_irrefl n)
  obtain ⟨h1b, hbn'⟩ := factor_bounds hn2 hdb hb1 hbn
  -- both a, b ≤ n - 1
  have ha0 : 0 < a := Nat.lt_of_lt_of_le (by decide) h1a
  have hb0 : 0 < b := Nat.lt_of_lt_of_le (by decide) h1b
  have ha_le : a ≤ n - 1 := Nat.le_pred_of_lt han'
  have hb_le : b ≤ n - 1 := Nat.le_pred_of_lt hbn'
  -- The divisibility `n ∣ fact (n-1)`, proved per case.
  have hdvd_fact : n ∣ factorial (n - 1) := by
    rcases Nat.lt_trichotomy a b with hlt | heq | hgt
    · -- a < b: distinct factors, a*b = n divides (n-1)!
      have : a * b ∣ factorial (n - 1) := mul_dvd_factorial ha0 hlt hb_le
      rw [← hab] at this; exact this
    · -- a = b: n = a²
      -- a ≥ 3 since n = a² > 4
      have heqn : n = a * a := by rw [hab, heq]
      have ha3 : 3 ≤ a := by
        -- a ≤ 2 ⟹ a*a ≤ 4 ⟹ n ≤ 4, contra n > 4
        rcases Nat.lt_or_ge a 3 with hlt3 | hge3
        · exfalso
          -- a ≤ 2 ; with 1 < a, a = 2, so n = 4, contra
          have ha2 : a = 2 := Nat.le_antisymm (Nat.le_of_lt_succ hlt3) h1a
          rw [ha2] at heqn
          -- n = 4
          rw [heqn] at hn
          exact absurd hn (by decide)
        · exact hge3
      -- 2a < a*a = n  (since 2 < a)
      have h2a_lt : 2 * a < a * a := by
        -- 2 < a ⟹ 2 * a < a * a
        have h2lt : 2 < a := Nat.lt_of_lt_of_le (by decide) ha3
        exact nat_mul_lt_mul_right ha0 h2lt
      have h2a_ltn : 2 * a < n := by rw [heqn]; exact h2a_lt
      have h2a_le : 2 * a ≤ n - 1 := Nat.le_pred_of_lt h2a_ltn
      -- a < 2a  (a > 0)
      have ha_lt_2a : a < 2 * a := by
        have h12 : (1 : Nat) < 2 := by decide
        have : 1 * a < 2 * a := nat_mul_lt_mul_right ha0 h12
        rw [Nat.one_mul] at this; exact this
      -- a * (2a) ∣ (n-1)!
      have hpair : a * (2 * a) ∣ factorial (n - 1) :=
        mul_dvd_factorial ha0 ha_lt_2a h2a_le
      -- n = a*a ∣ a*(2a) = 2*(a*a)
      have hsplit : a * (2 * a) = (a * a) * 2 := by ring_nat
      have hndvd : n ∣ a * (2 * a) := by
        rw [hsplit, ← heqn]
        exact ⟨2, rfl⟩
      -- transitivity by hand (Nat.dvd_trans carries propext)
      obtain ⟨c1, hc1⟩ := hndvd        -- a*(2a) = n * c1
      obtain ⟨c2, hc2⟩ := hpair        -- factorial (n-1) = a*(2a) * c2
      exact ⟨c1 * c2, by rw [hc2, hc1]; ring_nat⟩
    · -- a > b: symmetric, b < a, b*a = n
      have hba : n = b * a := by rw [hab, Nat.mul_comm]
      have : b * a ∣ factorial (n - 1) := mul_dvd_factorial hb0 hgt ha_le
      rw [← hba] at this; exact this
  -- conclude `fact (n-1) % n = 0`
  rw [fact_eq_factorial]
  obtain ⟨c, hc⟩ := hdvd_fact
  rw [hc]
  exact E213.Meta.Nat.NatDiv213.mul_mod_self_pure n c

end E213.Lib.Math.NumberTheory.ModArith.WilsonConverse
