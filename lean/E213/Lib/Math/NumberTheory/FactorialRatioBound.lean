import E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTwoVar
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChooseFactorial
import E213.Meta.Nat.PolyNatMTactic

/-!
# FactorialRatioBound — Brick 1 step 3: the Chebyshev factorial-ratio bound, ∅-axiom

`(30m)!·m!·6^{6m}·15^{15m}·10^{10m} ≤ (6m+1)·(15m)!(10m)!(6m)!·30^{30m}`, i.e.
`(30m)!·m!/((15m)!(10m)!(6m)!) ≤ (6m+1)·α₃₀^m` with `α₃₀ = 30³⁰/(6⁶15¹⁵10¹⁰)`.

The decomposition (rediscovered): pick the prime-spread `30 = 2·15 = 3·10 = 5·6`.

  * **B1** (two single-term binomial bounds): `(30m)!·15^{15m}·10^{10m}·5^{5m} ≤
    30^{30m}·(15m)!(10m)!(5m)!` — from `(15+15)^{30m}` and `(10+5)^{15m}` single terms.
  * **B2** (one max-term bound, unimodal at `k=m`): `6^{6m}·m!·(5m)! ≤
    (6m+1)·5^{5m}·(6m)!` — `(1+5)^{6m}=Σ_k C(6m,k)5^{6m-k} ≤ (6m+1)·[k=m term]`.

`B1 · B2`, cancelling `5^{5m}·(5m)!`, is exactly the deliverable (`step3`).

This file builds the single-term machinery + **B1**; B2 (the unimodal max-term) and
the assembly follow.  All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.FactorialRatioBound

open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial (factorial factorial_pos)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChooseFactorial (choose_mul_factorials)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTwoVar (binomSum2 binom2_theorem)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem (sumTo_term_le)

/-! ## §1 — the single-term binomial bound, in factorial form -/

/-- A single term of the binomial expansion is `≤` the whole: `C(n,k)·aᵏ·bⁿ⁻ᵏ ≤
    (a+b)ⁿ` (`k ≤ n`).  `binom2_theorem` + `sumTo_term_le`. -/
theorem binom_term_le (a b n k : Nat) (hk : k ≤ n) :
    choose n k * a ^ k * b ^ (n - k) ≤ (a + b) ^ n := by
  rw [binom2_theorem a b n]
  show choose n k * a ^ k * b ^ (n - k)
    ≤ sumTo (n + 1) (fun j => choose n j * a ^ j * b ^ (n - j))
  exact sumTo_term_le (n + 1) (fun j => choose n j * a ^ j * b ^ (n - j)) k
    (Nat.lt_succ_of_le hk)

/-- Factorial form: `(k+j)!·aᵏ·bʲ ≤ (a+b)^{k+j}·(k!·j!)`.  (`binom_term_le` × `k!j!`,
    using `choose(k+j) k · k!j! = (k+j)!`.) -/
theorem fact_binom_bound (a b k j : Nat) :
    factorial (k + j) * a ^ k * b ^ j ≤ (a + b) ^ (k + j) * (factorial k * factorial j) := by
  have hb := binom_term_le a b (k + j) k (Nat.le_add_right k j)
  rw [Nat.add_sub_cancel_left] at hb
  have h2 := Nat.mul_le_mul_right (factorial k * factorial j) hb
  rw [show choose (k + j) k * a ^ k * b ^ j * (factorial k * factorial j)
        = choose (k + j) k * (factorial k * factorial j) * (a ^ k * b ^ j) from by ring_nat,
      choose_mul_factorials k j,
      show factorial (k + j) * (a ^ k * b ^ j) = factorial (k + j) * a ^ k * b ^ j from by
        ring_nat] at h2
  exact h2

/-! ## §2 — pure right-cancellation (core analogues carry `propext`/full axioms) -/

private theorem mul_lt_mul_right_pure {a b k : Nat} (hk : 0 < k) (h : b < a) : b * k < a * k :=
  Nat.lt_of_lt_of_le
    (by rw [Nat.succ_mul]; exact Nat.lt_add_of_pos_right hk)
    (Nat.mul_le_mul_right k (Nat.succ_le_of_lt h))

private theorem le_of_mul_le_mul_right' {a b k : Nat} (hk : 0 < k) (h : a * k ≤ b * k) :
    a ≤ b := by
  rcases Nat.lt_or_ge b a with hba | hab
  · exact absurd h (Nat.not_le.mpr (mul_lt_mul_right_pure hk hba))
  · exact hab

/-! ## §3 — B1: the two-single-term lower bound on `30^{30m}` -/

/-- ★★ **B1**: `(30m)!·15^{15m}·10^{10m}·5^{5m} ≤ 30^{30m}·(15m)!(10m)!(5m)!`.
    `(15+15)^{30m}` and `(10+5)^{15m}` single terms, combined and `15^{15m}`-cancelled. -/
theorem B1 (m : Nat) :
    factorial (30 * m) * 15 ^ (15 * m) * 10 ^ (10 * m) * 5 ^ (5 * m)
    ≤ 30 ^ (30 * m) * (factorial (15 * m) * factorial (10 * m) * factorial (5 * m)) := by
  have b1a : factorial (30 * m) * 15 ^ (15 * m) * 15 ^ (15 * m)
      ≤ 30 ^ (30 * m) * (factorial (15 * m) * factorial (15 * m)) := by
    have h := fact_binom_bound 15 15 (15 * m) (15 * m)
    rw [show 15 * m + 15 * m = 30 * m from by ring_nat, show (15 : Nat) + 15 = 30 from rfl] at h
    exact h
  have b1b : factorial (15 * m) * 10 ^ (10 * m) * 5 ^ (5 * m)
      ≤ 15 ^ (15 * m) * (factorial (10 * m) * factorial (5 * m)) := by
    have h := fact_binom_bound 10 5 (10 * m) (5 * m)
    rw [show 10 * m + 5 * m = 15 * m from by ring_nat, show (10 : Nat) + 5 = 15 from rfl] at h
    exact h
  -- combine then cancel one 15^{15m}
  have key :
      (factorial (30 * m) * 15 ^ (15 * m) * 10 ^ (10 * m) * 5 ^ (5 * m)) * 15 ^ (15 * m)
      ≤ (30 ^ (30 * m) * (factorial (15 * m) * factorial (10 * m) * factorial (5 * m)))
          * 15 ^ (15 * m) :=
    calc (factorial (30 * m) * 15 ^ (15 * m) * 10 ^ (10 * m) * 5 ^ (5 * m)) * 15 ^ (15 * m)
        = (factorial (30 * m) * 15 ^ (15 * m) * 15 ^ (15 * m)) * (10 ^ (10 * m) * 5 ^ (5 * m)) := by
          ring_nat
      _ ≤ (30 ^ (30 * m) * (factorial (15 * m) * factorial (15 * m)))
            * (10 ^ (10 * m) * 5 ^ (5 * m)) := Nat.mul_le_mul_right _ b1a
      _ = 30 ^ (30 * m) * factorial (15 * m)
            * (factorial (15 * m) * 10 ^ (10 * m) * 5 ^ (5 * m)) := by ring_nat
      _ ≤ 30 ^ (30 * m) * factorial (15 * m)
            * (15 ^ (15 * m) * (factorial (10 * m) * factorial (5 * m))) :=
          Nat.mul_le_mul_left _ b1b
      _ = (30 ^ (30 * m) * (factorial (15 * m) * factorial (10 * m) * factorial (5 * m)))
            * 15 ^ (15 * m) := by ring_nat
  exact le_of_mul_le_mul_right' (Nat.pos_pow_of_pos _ (by decide)) key

end E213.Lib.Math.NumberTheory.FactorialRatioBound
