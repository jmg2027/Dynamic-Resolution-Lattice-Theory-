import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
import E213.Meta.Nat.PolyNatMTactic

/-!
# General two-variable binomial theorem `(a+b)ⁿ = Σ_{k≤n} C(n,k) aᵏ bⁿ⁻ᵏ` (∅-axiom)

**Marathon T5 core**.  The b=1 case (`binom_theorem_b_eq_one`) extended to general `b`, mirroring
its `binomSum_step` induction but tracking `bⁿ⁻ᵏ`.  The inductive step reduces both
`(a+b)·binomSum2 a b n` and `binomSum2 a b (n+1)` to the common form `bⁿ⁺¹ + A + thirdterm`, via
`sumTo_split_first` + Pascal (`choose_succ_succ`) + `sumTo_add_func`, with the `b`-exponent
congruences `n+1−(k+1)=n−k` (`Nat.succ_sub_succ`) and `n−(k+1)+1=n−k` (`k<n`).

This is the engine behind `exp(a+b)=exp(a)·exp(b)`: cross-multiplying the Taylor Cauchy product by
`n!` turns it into this identity via `choose_mul_factorials`.  All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTwoVar

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_zero_right choose_succ_succ choose_eq_zero_of_lt)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
  (sumTo_mul_left sumTo_add_func sumTo_split_first sumTo_congr)

/-- `binomSum2 a b n = Σ_{k=0}^{n} C(n,k) · aᵏ · bⁿ⁻ᵏ`. -/
def binomSum2 (a b n : Nat) : Nat :=
  sumTo (n + 1) (fun k => choose n k * a ^ k * b ^ (n - k))

theorem binomSum2_zero (a b : Nat) : binomSum2 a b 0 = 1 := by
  show 0 + choose 0 0 * a ^ 0 * b ^ (0 - 0) = 1
  rw [choose_zero_right]; rfl

/-- `b`-exponent shift: `n − (k+1) + 1 = n − k` for `k < n`. -/
private theorem bexp_shift (n k : Nat) (h : k < n) : n - (k + 1) + 1 = n - k :=
  E213.Tactic.NatHelper.sub_one_add_one
    (fun h0 => absurd (h0 ▸ E213.Tactic.NatHelper.sub_pos_of_lt h) (Nat.lt_irrefl 0))

/-- `a · binomSum2 a b n = Σ C(n,k) · a^{k+1} · bⁿ⁻ᵏ`. -/
theorem a_mul_binomSum2 (a b n : Nat) :
    a * binomSum2 a b n = sumTo (n + 1) (fun k => choose n k * a ^ (k + 1) * b ^ (n - k)) := by
  unfold binomSum2
  rw [sumTo_mul_left a (n + 1) (fun k => choose n k * a ^ k * b ^ (n - k))]
  refine sumTo_congr (n + 1) _ _ (fun k _ => ?_)
  show a * (choose n k * a ^ k * b ^ (n - k)) = choose n k * a ^ (k + 1) * b ^ (n - k)
  have hp : a ^ (k + 1) = a ^ k * a := Nat.pow_succ a k
  rw [hp]; ring_nat

/-- `b · binomSum2 a b n = Σ C(n,k) · aᵏ · b^{n−k+1}`. -/
theorem b_mul_binomSum2 (a b n : Nat) :
    b * binomSum2 a b n = sumTo (n + 1) (fun k => choose n k * a ^ k * b ^ (n - k + 1)) := by
  unfold binomSum2
  rw [sumTo_mul_left b (n + 1) (fun k => choose n k * a ^ k * b ^ (n - k))]
  refine sumTo_congr (n + 1) _ _ (fun k _ => ?_)
  show b * (choose n k * a ^ k * b ^ (n - k)) = choose n k * a ^ k * b ^ (n - k + 1)
  have hp : b ^ (n - k + 1) = b ^ (n - k) * b := Nat.pow_succ b (n - k)
  rw [hp]; ring_nat

/-- RHS reduction: `binomSum2 a b (n+1) = bⁿ⁺¹ + (A + thirdterm)`. -/
theorem rhs_to_common (a b n : Nat) :
    binomSum2 a b (n + 1)
      = b ^ (n + 1)
        + (sumTo (n + 1) (fun k => choose n k * a ^ (k + 1) * b ^ (n - k))
          + sumTo (n + 1) (fun k => choose n (k + 1) * a ^ (k + 1) * b ^ (n - k))) := by
  show sumTo (n + 2) (fun k => choose (n + 1) k * a ^ k * b ^ (n + 1 - k)) = _
  rw [sumTo_split_first (n + 1) (fun k => choose (n + 1) k * a ^ k * b ^ (n + 1 - k))]
  have htail :
      sumTo (n + 1) (fun k => choose (n + 1) (k + 1) * a ^ (k + 1) * b ^ (n + 1 - (k + 1)))
      = sumTo (n + 1) (fun k => choose n k * a ^ (k + 1) * b ^ (n - k))
        + sumTo (n + 1) (fun k => choose n (k + 1) * a ^ (k + 1) * b ^ (n - k)) := by
    rw [sumTo_add_func (n + 1)
          (fun k => choose n k * a ^ (k + 1) * b ^ (n - k))
          (fun k => choose n (k + 1) * a ^ (k + 1) * b ^ (n - k))]
    refine sumTo_congr (n + 1) _ _ (fun k _ => ?_)
    show choose (n + 1) (k + 1) * a ^ (k + 1) * b ^ (n + 1 - (k + 1))
        = choose n k * a ^ (k + 1) * b ^ (n - k) + choose n (k + 1) * a ^ (k + 1) * b ^ (n - k)
    have hs : n + 1 - (k + 1) = n - k := Nat.succ_sub_succ n k
    rw [hs, choose_succ_succ]; ring_nat
  -- head term + htail
  show choose (n + 1) 0 * a ^ 0 * b ^ (n + 1 - 0)
        + sumTo (n + 1) (fun k => choose (n + 1) (k + 1) * a ^ (k + 1) * b ^ (n + 1 - (k + 1)))
      = b ^ (n + 1) + _
  rw [htail, choose_zero_right]
  show 1 * a ^ 0 * b ^ (n + 1 - 0) + _ = b ^ (n + 1) + _
  rw [show n + 1 - 0 = n + 1 from rfl, Nat.pow_zero, Nat.mul_one, Nat.one_mul]

/-- `B`-sum reduction: `Σ C(n,k) aᵏ b^{n−k+1} = bⁿ⁺¹ + thirdterm`. -/
theorem b_sum_to_common (a b n : Nat) :
    sumTo (n + 1) (fun k => choose n k * a ^ k * b ^ (n - k + 1))
      = b ^ (n + 1)
        + sumTo (n + 1) (fun k => choose n (k + 1) * a ^ (k + 1) * b ^ (n - k)) := by
  rw [sumTo_split_first n (fun k => choose n k * a ^ k * b ^ (n - k + 1))]
  -- drop the vanishing last term of thirdterm
  have hlast :
      sumTo (n + 1) (fun k => choose n (k + 1) * a ^ (k + 1) * b ^ (n - k))
      = sumTo n (fun k => choose n (k + 1) * a ^ (k + 1) * b ^ (n - k)) := by
    rw [sumTo_succ, choose_eq_zero_of_lt n (n + 1) (Nat.lt_succ_self n),
        Nat.zero_mul, Nat.zero_mul, Nat.add_zero]
  have htail :
      sumTo n (fun k => choose n (k + 1) * a ^ (k + 1) * b ^ (n - (k + 1) + 1))
      = sumTo n (fun k => choose n (k + 1) * a ^ (k + 1) * b ^ (n - k)) := by
    refine sumTo_congr n _ _ (fun k hk => ?_)
    show choose n (k + 1) * a ^ (k + 1) * b ^ (n - (k + 1) + 1)
        = choose n (k + 1) * a ^ (k + 1) * b ^ (n - k)
    rw [bexp_shift n k hk]
  show choose n 0 * a ^ 0 * b ^ (n - 0 + 1)
        + sumTo n (fun k => choose n (k + 1) * a ^ (k + 1) * b ^ (n - (k + 1) + 1))
      = b ^ (n + 1) + _
  rw [htail, hlast, choose_zero_right,
      show n - 0 + 1 = n + 1 from rfl, Nat.pow_zero, Nat.mul_one, Nat.one_mul]

/-- ★★★ **Binomial theorem step**: `(a+b) · binomSum2 a b n = binomSum2 a b (n+1)`. -/
theorem binomSum2_step (a b n : Nat) :
    (a + b) * binomSum2 a b n = binomSum2 a b (n + 1) := by
  rw [E213.Tactic.NatHelper.add_mul, a_mul_binomSum2, b_mul_binomSum2,
      b_sum_to_common, rhs_to_common]
  ring_nat

/-- ★★★★ **General binomial theorem**: `(a+b)ⁿ = Σ_{k=0}^{n} C(n,k) · aᵏ · bⁿ⁻ᵏ`. -/
theorem binom2_theorem (a b : Nat) : ∀ n, (a + b) ^ n = binomSum2 a b n
  | 0 => (binomSum2_zero a b).symm
  | n + 1 => by
    show (a + b) ^ n * (a + b) = binomSum2 a b (n + 1)
    rw [binom2_theorem a b n, Nat.mul_comm, binomSum2_step]

end E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTwoVar
