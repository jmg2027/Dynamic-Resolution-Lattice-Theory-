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
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose choose_succ_succ
  choose_one_right choose_zero_right choose_eq_zero_of_lt)
open E213.Tactic.NatHelper (add_mul sub_add_cancel add_right_cancel le_sub_of_add_le)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChooseFactorial (choose_mul_factorials)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTwoVar (binomSum2 binom2_theorem)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem (sumTo_term_le)
open E213.Tactic.NatHelper (add_sub_cancel_right)

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
  rw [show k + j - k = j from
        (congrArg (· - k) (Nat.add_comm k j)).trans (add_sub_cancel_right j k)] at hb
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

/-! ## §4 — B2: the absorption identity and the term-ratio bounds -/

/-- `N - k = (N - (k+1)) + 1` for `k+1 ≤ N`. -/
private theorem sub_succ_add_one {N k : Nat} (hk : k + 1 ≤ N) :
    N - k = (N - (k + 1)) + 1 := by
  have hk' : k ≤ N := Nat.le_trans (Nat.le_succ k) hk
  have e1 : (N - (k + 1)) + 1 + k = N := by
    rw [Nat.add_assoc, Nat.add_comm 1 k]; exact sub_add_cancel hk
  have e2 : (N - k) + k = N := sub_add_cancel hk'
  exact (add_right_cancel (e1.trans e2.symm)).symm

/-- The inductive-step coefficient identity for `choose_absorb` (when the binomial
    factor is nonzero, i.e. `k+1 ≤ N`). -/
private theorem coeff_shift {N k : Nat} (hk : k + 1 ≤ N) :
    (k + 2) + (N - (k + 1)) = (k + 1) + (N - k) := by
  rw [sub_succ_add_one hk]; ring_nat

/-- ★★ **Absorption**: `(k+1)·C(N,k+1) = (N−k)·C(N,k)`.  Induction on `N` + Pascal;
    the step coefficient identity holds where `C N (k+1) ≠ 0`, else both sides `·0`. -/
theorem choose_absorb : ∀ N k, (k + 1) * choose N (k + 1) = (N - k) * choose N k
  | 0, k => by
      rw [show choose 0 (k + 1) = 0 from rfl, Nat.mul_zero, Nat.zero_sub, Nat.zero_mul]
  | N + 1, 0 => by
      show 1 * choose (N + 1) 1 = (N + 1 - 0) * choose (N + 1) 0
      rw [choose_one_right, choose_zero_right, Nat.one_mul, Nat.sub_zero, Nat.mul_one]
  | N + 1, k + 1 => by
      have ih1 := choose_absorb N k
      have ih2 := choose_absorb N (k + 1)
      show (k + 2) * choose (N + 1) (k + 2) = (N + 1 - (k + 1)) * choose (N + 1) (k + 1)
      rw [choose_succ_succ N (k + 1), choose_succ_succ N k, Nat.succ_sub_succ,
          Nat.mul_add, Nat.mul_add, ih2, ← ih1]
      by_cases hc : choose N (k + 1) = 0
      · rw [hc, Nat.mul_zero, Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
      · have hkN : k + 1 ≤ N :=
          Nat.not_lt.mp (fun hlt => hc (choose_eq_zero_of_lt N (k + 1) hlt))
        rw [← add_mul, ← add_mul, coeff_shift hkN]

/-- For `k < m`: `5·C(6m,k) ≤ C(6m,k+1)` (the up-ratio, `6m−k ≥ 5(k+1)`). -/
theorem chooseRatioUp (m k : Nat) (hk : k < m) :
    5 * choose (6 * m) k ≤ choose (6 * m) (k + 1) := by
  have hab := choose_absorb (6 * m) k
  have hge : 5 * (k + 1) ≤ 6 * m - k :=
    le_sub_of_add_le (by
      calc 5 * (k + 1) + k = 6 * k + 5 := by ring_nat
        _ ≤ 6 * k + 6 := Nat.add_le_add_left (by decide) _
        _ = 6 * (k + 1) := by ring_nat
        _ ≤ 6 * m := Nat.mul_le_mul_left 6 hk)
  have h1 : 5 * (k + 1) * choose (6 * m) k ≤ (6 * m - k) * choose (6 * m) k :=
    Nat.mul_le_mul_right _ hge
  rw [← hab] at h1
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.succ_pos k)
  calc (k + 1) * (5 * choose (6 * m) k)
      = 5 * (k + 1) * choose (6 * m) k := by ring_nat
    _ ≤ (k + 1) * choose (6 * m) (k + 1) := h1

/-- For `m ≤ k`: `C(6m,k+1) ≤ 5·C(6m,k)` (the down-ratio, `6m−k ≤ 5(k+1)`). -/
theorem chooseRatioDown (m k : Nat) (hk : m ≤ k) :
    choose (6 * m) (k + 1) ≤ 5 * choose (6 * m) k := by
  have hab := choose_absorb (6 * m) k
  have h6 : 6 * m ≤ 5 * (k + 1) + k := by
    calc 6 * m ≤ 6 * k := Nat.mul_le_mul_left 6 hk
      _ ≤ 5 * (k + 1) + k := by
        rw [show 5 * (k + 1) + k = 6 * k + 5 from by ring_nat]; exact Nat.le_add_right _ _
  have hle : 6 * m - k ≤ 5 * (k + 1) := by
    calc 6 * m - k ≤ (5 * (k + 1) + k) - k := Nat.sub_le_sub_right h6 k
      _ = 5 * (k + 1) := add_sub_cancel_right (5 * (k + 1)) k
  have h1 : (6 * m - k) * choose (6 * m) k ≤ 5 * (k + 1) * choose (6 * m) k :=
    Nat.mul_le_mul_right _ hle
  rw [← hab] at h1
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.succ_pos k)
  calc (k + 1) * choose (6 * m) (k + 1) ≤ 5 * (k + 1) * choose (6 * m) k := h1
    _ = (k + 1) * (5 * choose (6 * m) k) := by ring_nat

end E213.Lib.Math.NumberTheory.FactorialRatioBound
