import E213.Lib.Math.NumberTheory.PerfectNumbers
import E213.Meta.Nat.ModPow213
import E213.Meta.Nat.AddMod213

/-!
# σ(n) parity — companion to `TauParity.lean`  (∅-axiom, FALLBACK partials)

Target: σ(n) odd ⟺ n is a perfect square or twice a perfect square.

The GENERAL ⟺ requires a 2-adic odd-part decomposition `n = 2^a · odd` plus a
`square ⟺ all odd-prime-valuations even` characterization and a chaining of
`sigma_mul` over the full prime factorization — none of which the corpus
exposes (no `oddPart`, no `isSquare_iff_all_vp_even`, no general
`sigma`-over-factorization).  This file delivers the tractable PURE partials
that the general proof would build on:

  * `sigma_two_pow_odd k : sigma (2^k) % 2 = 1`     (general k)
  * `sigma_odd_prime_pow_parity : sigma (p^k) % 2 = (k+1) % 2`  (odd prime p, general k)
  * `sigma_parity_table` — n=1..30, σ(n)%2 matches the square-or-twice-square indicator
  * square / twice-square smoke directions via `sigma_mul`.
-/

namespace E213.Lib.Math.NumberTheory.SigmaParity

open E213.Lib.Math.NumberTheory.SumOfDivisors (sigma)
open E213.Lib.Math.NumberTheory.PerfectNumbers
  (sigma_two_pow_succ sigma_cast_eq_divisorSumZ)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Lib.Math.NumberTheory.MobiusFunction (divisorSumZ)
open E213.Lib.Math.NumberTheory.MobiusDivisorSum (sumPowZ divisorSumZ_prime_pow_reindex)
open E213.Meta.Nat.AddMod213 (add_mod_gen mod_mod)
open E213.Meta.Nat.ModPow213 (pow_mod_base)

/-! ## §1 — σ(2ᵏ) is always odd -/

/-- ★ **σ(2ᵏ) is odd** (general k): `σ(2ᵏ) = 2^(k+1) − 1`, carried subtraction-free as
    `σ(2ᵏ) + 1 = 2^(k+1)` (corpus `sigma_two_pow_succ`).  `2^(k+1)` is even, so
    `σ(2ᵏ)` is odd. -/
theorem sigma_two_pow_odd (k : Nat) : sigma (2 ^ k) % 2 = 1 := by
  have hk : sigma (2 ^ k) + 1 = 2 ^ (k + 1) := sigma_two_pow_succ k
  -- 2^(k+1) % 2 = 0
  have heven : (2 ^ (k + 1)) % 2 = 0 := by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2]
    exact E213.Meta.Nat.NatDiv213.mul_mod_self_pure 2 (2 ^ k)
  -- so (σ + 1) % 2 = 0
  have hsum : (sigma (2 ^ k) + 1) % 2 = 0 := by rw [hk]; exact heven
  -- (σ % 2 + 1) % 2 = 0 ⇒ σ % 2 = 1
  rw [add_mod_gen (sigma (2 ^ k)) 1 2] at hsum
  rcases E213.Meta.Nat.AddMod213.mod_two_zero_or_one (sigma (2 ^ k)) with h0 | h1
  · rw [h0] at hsum; exact absurd hsum (by decide)
  · exact h1

/-! ## §2 — σ(pᵏ) parity for an odd prime p -/

/-- For odd `p` (`p % 2 = 1`), every power `pⁱ` is odd: `pⁱ % 2 = 1`. -/
theorem odd_pow_mod_two {p : Nat} (hp : p % 2 = 1) (i : Nat) : p ^ i % 2 = 1 := by
  rw [pow_mod_base p 2 i, hp, Nat.one_pow]

/-- The Nat geometric sum `Σ_{i≤k} pⁱ` (mirrors corpus `sumPowZ` over `Int`). -/
def sumPowN (p : Nat) : Nat → Nat
  | 0     => p ^ 0
  | k + 1 => sumPowN p k + p ^ (k + 1)

/-- `(sumPowN p k : Int) = sumPowZ (fun d => (d:Int)) p k`: the Nat sum casts to the
    corpus Int sum used by `divisorSumZ_prime_pow_reindex`. -/
theorem sumPowN_cast (p : Nat) :
    ∀ k, ((sumPowN p k : Nat) : Int) = sumPowZ (fun d => (d : Int)) p k
  | 0 => by
      show ((p ^ 0 : Nat) : Int) = (fun d => (d : Int)) (p ^ 0)
      rfl
  | k + 1 => by
      show ((sumPowN p k + p ^ (k + 1) : Nat) : Int)
          = sumPowZ (fun d => (d : Int)) p k + ((p ^ (k + 1) : Nat) : Int)
      rw [Int.ofNat_add, sumPowN_cast p k]

/-- ★ **σ(pᵏ) = Σ_{i≤k} pⁱ** (Nat) for a prime `p`: de-cast of the corpus prime-power
    divisor reindex. -/
theorem sigma_prime_pow_eq_sumPowN {p : Nat} (hp : Prime213 p) (k : Nat) :
    sigma (p ^ k) = sumPowN p k := by
  apply Int.ofNat.inj
  show ((sigma (p ^ k) : Nat) : Int) = ((sumPowN p k : Nat) : Int)
  have hpos : 0 < p ^ k := Nat.pos_pow_of_pos k (Nat.lt_of_lt_of_le (by decide) hp.1)
  rw [sigma_cast_eq_divisorSumZ (p ^ k) hpos,
      divisorSumZ_prime_pow_reindex hp k (fun d => (d : Int)),
      sumPowN_cast p k]

/-- The parity of `Σ_{i≤k} pⁱ` for odd `p`: it is the parity of the number of terms,
    `(k+1) % 2` — each `pⁱ` is odd, so the sum's parity flips with each term. -/
theorem sumPowN_mod_two_odd {p : Nat} (hp : p % 2 = 1) :
    ∀ k, sumPowN p k % 2 = (k + 1) % 2
  | 0 => by
      show p ^ 0 % 2 = 1 % 2
      rw [odd_pow_mod_two hp 0]
  | k + 1 => by
      show (sumPowN p k + p ^ (k + 1)) % 2 = (k + 2) % 2
      rw [add_mod_gen (sumPowN p k) (p ^ (k + 1)) 2,
          sumPowN_mod_two_odd hp k, odd_pow_mod_two hp (k + 1)]
      -- ((k+1)%2 + 1) % 2 = (k+2) % 2
      rw [← add_mod_gen (k + 1) 1 2]

/-- ★★ **σ(pᵏ) parity for an odd prime**: `σ(pᵏ) % 2 = (k+1) % 2`.  Hence `σ(pᵏ)` is
    odd ⟺ `k` is even.  (General `k`, general odd prime `p`.) -/
theorem sigma_odd_prime_pow_parity {p : Nat} (hp : Prime213 p) (hodd : p % 2 = 1) (k : Nat) :
    sigma (p ^ k) % 2 = (k + 1) % 2 := by
  rw [sigma_prime_pow_eq_sumPowN hp k, sumPowN_mod_two_odd hodd k]

/-! ## §3 — concrete corollaries of the odd-prime-power parity -/

/-- `σ(3ᵏ)` is odd ⟺ k even — the smallest odd prime, via `sigma_odd_prime_pow_parity`. -/
theorem sigma_three_pow_parity (k : Nat) : sigma (3 ^ k) % 2 = (k + 1) % 2 := by
  have hp : Prime213 3 :=
    E213.Lib.Math.NumberTheory.PerfectNumbers.prime_of_bounded (q := 3)
      (by decide) (B := 2) (by decide) (by decide)
  exact sigma_odd_prime_pow_parity hp (by decide) k

/-! ## §4 — parity table matching the square-or-twice-square indicator -/

set_option maxRecDepth 4000 in
/-- ★ **σ-parity table (n = 1..30)**: `σ(n) % 2 = 1` exactly at
    `n ∈ {1,2,4,8,9,16,18,25}` — the squares (`1,4,9,16,25`) and twice-squares
    (`2,8,18`) up to 30.  Closed numerics, axiom-clean (`decide`). -/
theorem sigma_parity_table :
    sigma 1 % 2 = 1 ∧ sigma 2 % 2 = 1 ∧ sigma 4 % 2 = 1 ∧ sigma 8 % 2 = 1
    ∧ sigma 9 % 2 = 1 ∧ sigma 16 % 2 = 1 ∧ sigma 18 % 2 = 1 ∧ sigma 25 % 2 = 1
    ∧ sigma 3 % 2 = 0 ∧ sigma 5 % 2 = 0 ∧ sigma 6 % 2 = 0 ∧ sigma 7 % 2 = 0
    ∧ sigma 10 % 2 = 0 ∧ sigma 12 % 2 = 0 ∧ sigma 15 % 2 = 0 ∧ sigma 30 % 2 = 0 := by
  decide

/-! ## §5 — square / twice-square smoke directions

For the "odd" direction `n = r² ⇒ σ(n) odd` we'd chain `sigma_mul` over the prime
factorization (corpus-unsupported in general).  We give the concrete prime-power
square cases that DO close from the general lemmas above. -/

/-- `σ(2^(2j))` is odd: a power-of-two square is a square, σ odd (`sigma_two_pow_odd`). -/
theorem sigma_two_pow_sq_odd (j : Nat) : sigma (2 ^ (2 * j)) % 2 = 1 :=
  sigma_two_pow_odd (2 * j)

/-- `σ(3^(2j))` is odd: an odd-prime *even* power has `σ` odd
    (`sigma_odd_prime_pow_parity`, exponent `2j` even ⇒ `(2j+1)%2 = 1`). -/
theorem sigma_three_pow_sq_odd (j : Nat) : sigma (3 ^ (2 * j)) % 2 = 1 := by
  rw [sigma_three_pow_parity (2 * j)]
  -- (2j + 1) % 2 = 1
  rw [add_mod_gen (2 * j) 1 2, E213.Meta.Nat.NatDiv213.mul_mod_self_pure 2 j]

/-- Concrete square smokes: σ(r²) odd for r = 1..6 (via the corpus σ table / `decide`). -/
theorem sigma_square_smoke :
    sigma (1 * 1) % 2 = 1 ∧ sigma (2 * 2) % 2 = 1 ∧ sigma (3 * 3) % 2 = 1
    ∧ sigma (4 * 4) % 2 = 1 ∧ sigma (5 * 5) % 2 = 1 ∧ sigma (6 * 6) % 2 = 1 := by
  decide

/-- Concrete twice-square smokes: σ(2r²) odd for r = 1..3. -/
theorem sigma_twice_square_smoke :
    sigma (2 * (1 * 1)) % 2 = 1 ∧ sigma (2 * (2 * 2)) % 2 = 1
    ∧ sigma (2 * (3 * 3)) % 2 = 1 := by
  decide

end E213.Lib.Math.NumberTheory.SigmaParity
