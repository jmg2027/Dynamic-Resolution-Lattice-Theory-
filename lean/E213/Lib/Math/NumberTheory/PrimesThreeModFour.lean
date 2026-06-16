import E213.Lib.Math.NumberTheory.PrimeFactorization
import E213.Meta.Nat.VpMul
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.NatDiv213

/-!
# Infinitely many primes ≡ 3 (mod 4) — computed Euclid witness (∅-axiom)

Vein-B forcing: the classical proof assumes a *finite* exhaustive list of
primes `≡ 3 (mod 4)` and derives a contradiction (LEM + finiteness).  Here,
given any bound `N`, we **construct** a witness prime `> N`, `≡ 3 (mod 4)`.

Keystone `exists_prime_factor_3mod4`: any `m ≡ 3 (mod 4)` has a prime factor
`≡ 3 (mod 4)` — computed as a `minFac`/quotient descent, not extracted from a
minimal counterexample.

Witness: `M = 4·(N!) + 3 ≡ 3 (mod 4)`; its `3 mod 4` prime factor `q` cannot
divide `N!` (else `q ∣ 3`, and `3 ∣ N!` for `N ≥ 3`), so `q > N`.
-/

namespace E213.Lib.Math.NumberTheory.PrimesThreeModFour

open E213.Lib.Math.NumberTheory.PrimeFactorization
  (minFac minFac_prime minFac_div prodL le_of_dvd_pos)
open E213.Meta.Nat.Gcd213 (dvd_sub_213)
open E213.Meta.Nat.VpMul (IsPrime213 euclid_lemma)
open E213.Meta.Nat.Valuation (dtrans mod_zero_of_dvd)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero add_mod_gen mod_mod_of_dvd)
open E213.Meta.Nat.MulMod213 (mul_mod_pure)
open E213.Meta.Nat.NatDiv213 (mul_div_cancel_left_pure mul_mod_self_pure)
open E213.Meta.Nat.PureNat (mul_assoc)

/-! ## §0 — `Prime213` and `IsPrime213` coincide (definitionally identical bodies) -/

/-- `minFac_prime` produces `Prime213`; its body is identical to `IsPrime213`. -/
theorem minFac_isPrime {n : Nat} (hn : 2 ≤ n) : IsPrime213 (minFac n) :=
  minFac_prime hn

/-! ## §1 — local factorial (PURE, minimal deps) -/

def fact : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos : ∀ n, 0 < fact n
  | 0     => by decide
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

/-- Every `1 ≤ m ≤ n` divides `fact n`. -/
theorem dvd_fact (m n : Nat) (h : 1 ≤ m) (hmn : m ≤ n) : m ∣ fact n := by
  induction n with
  | zero => exact absurd (Nat.le_trans h hmn) (Nat.not_succ_le_zero 0)
  | succ k ih =>
    by_cases hkm : m ≤ k
    · have hdvd : m ∣ fact k := ih hkm
      obtain ⟨q, hq⟩ := hdvd
      refine ⟨(k + 1) * q, ?_⟩
      show (k + 1) * fact k = m * ((k + 1) * q)
      rw [hq, Nat.mul_comm (k + 1) (m * q), mul_assoc m q (k + 1),
          Nat.mul_comm q (k + 1), ← mul_assoc m (k + 1) q]
    · have hmk1 : m = k + 1 := Nat.le_antisymm hmn (Nat.lt_of_not_le hkm)
      show m ∣ (k + 1) * fact k
      rw [hmk1]
      exact ⟨fact k, rfl⟩

/-! ## §2 — mod-4 reductions on the residues `{0,1,2,3}` -/

/-- `(a % 4) % 4 = a % 4`. -/
theorem mod4_mod4 (a : Nat) : (a % 4) % 4 = a % 4 :=
  Nat.mod_eq_of_lt (Nat.mod_lt a (by decide))

/-- If `(q * a) % 4 = 3` and `q % 4 = 1` then `a % 4 = 3`. -/
theorem cancel_mod4_one {q a : Nat} (hq : q % 4 = 1) (h : (q * a) % 4 = 3) :
    a % 4 = 3 := by
  have key : (q * a) % 4 = (a % 4) % 4 := by
    rw [mul_mod_pure q a 4, hq, Nat.one_mul]
  rw [key, mod4_mod4] at h
  exact h

/-! ## §3 — oddness helpers -/

/-- `m % 4 = 3 ⟹ m % 2 = 1` (`2 ∣ 4`). -/
theorem mod4_three_odd {m : Nat} (h : m % 4 = 3) : m % 2 = 1 := by
  have key : m % 4 % 2 = m % 2 := mod_mod_of_dvd m (⟨2, rfl⟩ : (2 : Nat) ∣ 4)
  rw [h] at key
  -- key : 3 % 2 = m % 2, and 3 % 2 = 1
  have : (3 : Nat) % 2 = 1 := by decide
  rw [this] at key
  exact key.symm

/-- `m % 4 = 3 ⟹ 2 ≤ m` (so `minFac` applies). -/
theorem mod4_three_ge_two {m : Nat} (h : m % 4 = 3) : 2 ≤ m := by
  rcases Nat.lt_or_ge m 2 with hlt | hge
  · -- m < 2 ≤ 4 ⟹ m % 4 = m, so m = 3, contradicting m < 2
    exfalso
    have hm4 : m % 4 = m := Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt (by decide))
    rw [hm4] at h
    rw [h] at hlt
    exact absurd hlt (by decide)
  · exact hge

/-- `q % 2 = 1 ⟹ q % 4 = 1 ∨ q % 4 = 3` (odd residues mod 4). -/
theorem odd_mod4 {q : Nat} (h : q % 2 = 1) : q % 4 = 1 ∨ q % 4 = 3 := by
  have hlt : q % 4 < 4 := Nat.mod_lt q (by decide)
  have hpar : q % 4 % 2 = 1 := by
    rw [mod_mod_of_dvd q (⟨2, rfl⟩ : (2 : Nat) ∣ 4)]; exact h
  -- case on q % 4 ∈ {0,1,2,3}; only 1 and 3 have odd parity
  rcases Nat.lt_or_ge (q % 4) 1 with h0 | h1
  · -- q%4 = 0 : parity 0, contra
    exfalso
    have : q % 4 = 0 := Nat.le_antisymm (Nat.le_of_lt_succ h0) (Nat.zero_le _)
    rw [this] at hpar; exact absurd hpar (by decide)
  · rcases Nat.lt_or_ge (q % 4) 2 with h1' | h2
    · -- q%4 = 1
      exact Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ h1') h1)
    · rcases Nat.lt_or_ge (q % 4) 3 with h2' | h3
      · -- q%4 = 2 : parity 0, contra
        exfalso
        have : q % 4 = 2 := Nat.le_antisymm (Nat.le_of_lt_succ h2') h2
        rw [this] at hpar; exact absurd hpar (by decide)
      · -- q%4 = 3
        exact Or.inr (Nat.le_antisymm (Nat.le_of_lt_succ hlt) h3)

/-! ## §4 — the keystone: `m ≡ 3 (mod 4)` has a prime factor `≡ 3 (mod 4)`

Strong induction on `m`.  `q = minFac m` is prime and divides `m`; `m` is odd so
`q` is odd, hence `q % 4 ∈ {1,3}`.  If `q % 4 = 3`, `q` is the witness.  If
`q % 4 = 1`, then `m / q ≡ 3 (mod 4)` and `m / q < m` — recurse. -/

theorem exists_prime_factor_3mod4 :
    ∀ m : Nat, m % 4 = 3 → ∃ q, IsPrime213 q ∧ q ∣ m ∧ q % 4 = 3 := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hm
    have hm2 : 2 ≤ m := mod4_three_ge_two hm
    have hmodd : m % 2 = 1 := mod4_three_odd hm
    -- q = minFac m
    have hqprime : IsPrime213 (minFac m) := minFac_isPrime hm2
    obtain ⟨hprod, hqlt⟩ := minFac_div hm2   -- minFac m * (m / minFac m) = m, quotient < m
    have hqdvd : minFac m ∣ m := ⟨m / minFac m, hprod.symm⟩
    -- minFac m is odd: else 2 ∣ minFac m ∣ m ⟹ m even
    have hqpos : 0 < minFac m := Nat.lt_of_lt_of_le (by decide) hqprime.two_le
    have hqodd : minFac m % 2 = 1 := by
      rcases E213.Meta.Nat.AddMod213.mod_two_zero_or_one (minFac m) with he | ho
      · exfalso
        -- 2 ∣ minFac m ∣ m ⟹ m % 2 = 0, contra hmodd
        have h2q : (2 : Nat) ∣ minFac m := dvd_of_mod_eq_zero he
        have h2m : (2 : Nat) ∣ m := dtrans h2q hqdvd
        have : m % 2 = 0 := mod_zero_of_dvd (by decide) h2m
        rw [this] at hmodd; exact absurd hmodd (by decide)
      · exact ho
    rcases odd_mod4 hqodd with hq1 | hq3
    · -- q % 4 = 1 : recurse on m / minFac m
      have hquo3 : (m / minFac m) % 4 = 3 := by
        -- m = minFac m * (m / minFac m), m % 4 = 3, q % 4 = 1
        have hmeq : (minFac m * (m / minFac m)) % 4 = 3 := by rw [hprod]; exact hm
        exact cancel_mod4_one hq1 hmeq
      obtain ⟨q, hqp, hqd, hq34⟩ := ih (m / minFac m) hqlt hquo3
      have hquodvd : (m / minFac m) ∣ m := ⟨minFac m, by rw [Nat.mul_comm]; exact hprod.symm⟩
      exact ⟨q, hqp, dtrans hqd hquodvd, hq34⟩
    · -- q % 4 = 3 : witness is minFac m
      exact ⟨minFac m, hqprime, hqdvd, hq3⟩

/-! ## §5 — the witness `M = 4·N! − 1` and the infinitude wrapper

`M = 4·(fact N) − 1 ≡ 3 (mod 4)`.  Every `2 ≤ d ≤ N` divides `fact N` hence
`4·fact N = M + 1`, so a prime factor `q ≤ N` of `M` would divide both `M` and
`M + 1`, hence `1` — impossible (`q ≥ 2`).  So the computed `3 mod 4` prime
factor of `M` exceeds `N`. -/

/-- `M + 1 = 4 · fact N` where `M = 4 · fact N − 1` (since `4 · fact N ≥ 1`). -/
theorem witness_succ (N : Nat) : (4 * fact N - 1) + 1 = 4 * fact N := by
  have hpos : 1 ≤ 4 * fact N :=
    Nat.le_trans (by decide : (1:Nat) ≤ 4) (Nat.le_mul_of_pos_right 4 (fact_pos N))
  exact E213.Meta.Nat.NatRing213.nat_sub_add_cancel hpos

/-- `(M+1) % 4 = 0 ⟹ M % 4 = 3` (residue case table on `M % 4 ∈ {0,1,2,3}`). -/
theorem mod4_three_of_succ_zero {M : Nat} (h : (M + 1) % 4 = 0) : M % 4 = 3 := by
  have hkey : (M % 4 + 1) % 4 = 0 := by
    have he := add_mod_gen M 1 4
    rw [he] at h
    have h14 : (1:Nat) % 4 = 1 := by decide
    rw [h14] at h; exact h
  have hlt : M % 4 < 4 := Nat.mod_lt M (by decide)
  rcases Nat.lt_or_ge (M % 4) 3 with hlo | hge
  · exfalso
    rcases Nat.lt_or_ge (M % 4) 1 with h0 | h1
    · have : M % 4 = 0 := Nat.le_antisymm (Nat.le_of_lt_succ h0) (Nat.zero_le _)
      rw [this] at hkey; exact absurd hkey (by decide)
    · rcases Nat.lt_or_ge (M % 4) 2 with h1' | h2
      · have : M % 4 = 1 := Nat.le_antisymm (Nat.le_of_lt_succ h1') h1
        rw [this] at hkey; exact absurd hkey (by decide)
      · have : M % 4 = 2 := Nat.le_antisymm (Nat.le_of_lt_succ hlo) h2
        rw [this] at hkey; exact absurd hkey (by decide)
  · exact Nat.le_antisymm (Nat.le_of_lt_succ hlt) hge

/-- `M = 4 · fact N − 1` satisfies `M % 4 = 3`. -/
theorem witness_mod4 (N : Nat) : (4 * fact N - 1) % 4 = 3 := by
  apply mod4_three_of_succ_zero
  rw [witness_succ N]
  exact mul_mod_self_pure 4 (fact N)

/-- ★★★ **Infinitely many primes ≡ 3 (mod 4)** (cofinal / constructive form):
    for every bound `N`, a prime `> N` congruent to `3 mod 4` exists and is
    computed (least `3 mod 4` prime factor of `M = 4·N! − 1`). -/
theorem infinitely_many_primes_3mod4 :
    ∀ N : Nat, ∃ p : Nat, N < p ∧ IsPrime213 p ∧ p % 4 = 3 := by
  intro N
  have hsucc : (4 * fact N - 1) + 1 = 4 * fact N := witness_succ N
  have hMmod : (4 * fact N - 1) % 4 = 3 := witness_mod4 N
  obtain ⟨q, hqp, hqd, hq34⟩ := exists_prime_factor_3mod4 (4 * fact N - 1) hMmod
  refine ⟨q, ?_, hqp, hq34⟩
  -- show N < q.  Suppose q ≤ N; then q ∣ fact N ⟹ q ∣ 4·fact N = M+1, with q ∣ M ⟹ q ∣ 1
  rcases Nat.lt_or_ge N q with hlt | hge
  · exact hlt
  · exfalso
    have hq2 : 2 ≤ q := hqp.two_le
    have hq1 : 1 ≤ q := Nat.le_trans (by decide) hq2
    have hqfact : q ∣ fact N := dvd_fact q N hq1 hge
    have hq4f : q ∣ 4 * fact N := dtrans hqfact (⟨4, Nat.mul_comm 4 (fact N)⟩)
    have hqMp1 : q ∣ ((4 * fact N - 1) + 1) := by rw [hsucc]; exact hq4f
    -- q ∣ M and q ∣ M+1 ⟹ q ∣ (M+1)-M = 1
    have hq1' : q ∣ (((4 * fact N - 1) + 1) - (4 * fact N - 1)) :=
      dvd_sub_213 (4 * fact N - 1) ((4 * fact N - 1) + 1) q (Nat.le_succ _) hqd hqMp1
    have hsub1 : ((4 * fact N - 1) + 1) - (4 * fact N - 1) = 1 := by
      rw [Nat.add_comm (4 * fact N - 1) 1]
      exact E213.Tactic.NatHelper.add_sub_cancel_right 1 (4 * fact N - 1)
    rw [hsub1] at hq1'
    -- q ∣ 1 ⟹ q ≤ 1, contra q ≥ 2
    have hqle1 : q ≤ 1 := le_of_dvd_pos (by decide) hq1'
    exact absurd (Nat.le_trans hq2 hqle1) (by decide)

/-! ## §6 — concrete smokes: the witness `M = 4·N! − 1` computes -/

-- N = 1: M = 4·1 − 1 = 3, minFac 3 = 3, 3 % 4 = 3 (prime witness > 1)
example : 4 * fact 1 - 1 = 3 := by decide
example : minFac (4 * fact 1 - 1) = 3 := by decide
-- N = 3: M = 4·6 − 1 = 23, minFac 23 = 23, 23 > 3, 23 % 4 = 3
example : 4 * fact 3 - 1 = 23 := by decide
example : minFac (4 * fact 3 - 1) = 23 := by decide
example : (23 : Nat) % 4 = 3 := by decide

end E213.Lib.Math.NumberTheory.PrimesThreeModFour
