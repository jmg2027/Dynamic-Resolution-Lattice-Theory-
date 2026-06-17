import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem

/-!
# The two-variable (homogeneous) binomial theorem `(b+d)ⁿ = Σ C(n,k) b^{n−k} dᵏ` (∅-axiom)

The repo's `binomSum` proves only the `b = 1` form `(a+1)ⁿ = Σ C(n,k) aᵏ`.  This module proves the
full homogeneous version

> `(b + d)ⁿ = Σ_{k=0}^{n} C(n,k) · b^{n−k} · dᵏ`   (`binom2`).

Same Pascal-induction architecture as `binomSum_step` (reduce `(b+d)·binom2 n` and `binom2 (n+1)`
to a common 4-term form), with the extra wrinkle of the truncated exponent `b^{n−k}` handled by the
pure `nat_succ_sub` (`(n+1)−k = (n−k)+1` for `k ≤ n`).

Needed for the lifting-the-exponent prime-power kernel: `(b+d)ᵖ − bᵖ = p·b^{p−1}·d + R` with the
binomial tail `R` whose terms carry `p ∣ C(p,k)`.  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.BinomialTwoVar

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_succ_succ choose_self choose_zero_right)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
  (sumTo_split_first sumTo_congr sumTo_add_func sumTo_mul_left)
open E213.Meta.Nat.NatRing213 (nat_succ_sub)
open E213.Meta.Nat.PureNat (add_mul)

/-- The homogeneous binomial sum `Σ_{k=0}^{n} C(n,k) · b^{n−k} · dᵏ`. -/
def binom2 (b d n : Nat) : Nat := sumTo (n + 1) (fun k => choose n k * b ^ (n - k) * d ^ k)

/-- `b · binom2 n` raises the `b`-exponent: `Σ C(n,k) b^{(n+1)−k} dᵏ`. -/
theorem b_mul_binom2 (b d n : Nat) :
    b * binom2 b d n = sumTo (n + 1) (fun k => choose n k * b ^ ((n + 1) - k) * d ^ k) := by
  show b * sumTo (n + 1) (fun k => choose n k * b ^ (n - k) * d ^ k)
     = sumTo (n + 1) (fun k => choose n k * b ^ ((n + 1) - k) * d ^ k)
  rw [sumTo_mul_left b (n + 1) (fun k => choose n k * b ^ (n - k) * d ^ k)]
  exact sumTo_congr (n + 1) _ _ (fun k hk => by
    have hkn : k ≤ n := Nat.le_of_lt_succ hk
    rw [nat_succ_sub hkn, Nat.pow_succ]; ring_nat)

/-- `d · binom2 n` raises the `d`-exponent: `Σ C(n,k) b^{n−k} d^{k+1}`. -/
theorem d_mul_binom2 (b d n : Nat) :
    d * binom2 b d n = sumTo (n + 1) (fun k => choose n k * b ^ (n - k) * d ^ (k + 1)) := by
  show d * sumTo (n + 1) (fun k => choose n k * b ^ (n - k) * d ^ k)
     = sumTo (n + 1) (fun k => choose n k * b ^ (n - k) * d ^ (k + 1))
  rw [sumTo_mul_left d (n + 1) (fun k => choose n k * b ^ (n - k) * d ^ k)]
  exact sumTo_congr (n + 1) _ _ (fun k _ => by rw [Nat.pow_succ]; ring_nat)

/-- 4-term rearrange: `(P + S1) + (S2 + Q) = P + S2 + S1 + Q`. -/
private theorem rearrange4 (P S1 S2 Q : Nat) : (P + S1) + (S2 + Q) = P + S2 + S1 + Q := by
  rw [Nat.add_assoc P S1 (S2 + Q), ← Nat.add_assoc S1 S2 Q, Nat.add_comm S1 S2,
      Nat.add_assoc S2 S1 Q, ← Nat.add_assoc P S2 (S1 + Q), Nat.add_assoc (P + S2) S1 Q]

/-- LHS reduction: `(b+d) · binom2 n` → the common 4-term form. -/
private theorem lhs_to_common (b d n : Nat) :
    (b + d) * binom2 b d n
      = b ^ (n + 1)
        + sumTo n (fun k => choose n k * b ^ (n - k) * d ^ (k + 1))
        + sumTo n (fun k => choose n (k + 1) * b ^ (n - k) * d ^ (k + 1))
        + d ^ (n + 1) := by
  rw [add_mul, b_mul_binom2 b d n, d_mul_binom2 b d n]
  -- b-part: split first term (k=0) → b^(n+1) + Σ_{k<n} C(n,k+1) b^{n−k} d^{k+1}
  rw [sumTo_split_first n (fun k => choose n k * b ^ ((n + 1) - k) * d ^ k)]
  -- d-part: extract last term (k=n) → Σ_{k<n} C(n,k) b^{n−k} d^{k+1} + d^(n+1)
  rw [show sumTo (n + 1) (fun k => choose n k * b ^ (n - k) * d ^ (k + 1))
        = sumTo n (fun k => choose n k * b ^ (n - k) * d ^ (k + 1))
          + choose n n * b ^ (n - n) * d ^ (n + 1) from rfl]
  -- evaluate the boundary terms
  have hb0 : choose n 0 * b ^ ((n + 1) - 0) * d ^ 0 = b ^ (n + 1) := by
    rw [choose_zero_right, Nat.sub_zero, Nat.pow_zero]; ring_nat
  have hdn : choose n n * b ^ (n - n) * d ^ (n + 1) = d ^ (n + 1) := by
    rw [choose_self, Nat.sub_self, Nat.pow_zero]; ring_nat
  rw [hb0, hdn]
  -- the b-part shifted sum: C(n,k+1) b^{(n+1)−(k+1)} d^{k+1} = C(n,k+1) b^{n−k} d^{k+1}
  rw [sumTo_congr n
        (fun k => choose n (k + 1) * b ^ ((n + 1) - (k + 1)) * d ^ (k + 1))
        (fun k => choose n (k + 1) * b ^ (n - k) * d ^ (k + 1))
        (fun k _ => by
          show choose n (k + 1) * b ^ ((n + 1) - (k + 1)) * d ^ (k + 1)
             = choose n (k + 1) * b ^ (n - k) * d ^ (k + 1)
          rw [Nat.succ_sub_succ])]
  -- now reorder: (b^(n+1) + S1) + (S2 + d^(n+1)) = b^(n+1) + S2 + S1 + d^(n+1)
  exact rearrange4 (b ^ (n + 1))
    (sumTo n (fun k => choose n (k + 1) * b ^ (n - k) * d ^ (k + 1)))
    (sumTo n (fun k => choose n k * b ^ (n - k) * d ^ (k + 1)))
    (d ^ (n + 1))

/-- RHS reduction: `binom2 (n+1)` → the same common 4-term form. -/
private theorem rhs_to_common (b d n : Nat) :
    binom2 b d (n + 1)
      = b ^ (n + 1)
        + sumTo n (fun k => choose n k * b ^ (n - k) * d ^ (k + 1))
        + sumTo n (fun k => choose n (k + 1) * b ^ (n - k) * d ^ (k + 1))
        + d ^ (n + 1) := by
  show sumTo (n + 2) (fun k => choose (n + 1) k * b ^ ((n + 1) - k) * d ^ k)
     = b ^ (n + 1)
       + sumTo n (fun k => choose n k * b ^ (n - k) * d ^ (k + 1))
       + sumTo n (fun k => choose n (k + 1) * b ^ (n - k) * d ^ (k + 1))
       + d ^ (n + 1)
  -- extract last (k=n+1): C(n+1,n+1) b^0 d^(n+1) = d^(n+1)
  rw [show sumTo (n + 2) (fun k => choose (n + 1) k * b ^ ((n + 1) - k) * d ^ k)
        = sumTo (n + 1) (fun k => choose (n + 1) k * b ^ ((n + 1) - k) * d ^ k)
          + choose (n + 1) (n + 1) * b ^ ((n + 1) - (n + 1)) * d ^ (n + 1) from rfl]
  have hlast : choose (n + 1) (n + 1) * b ^ ((n + 1) - (n + 1)) * d ^ (n + 1) = d ^ (n + 1) := by
    rw [choose_self, Nat.sub_self, Nat.pow_zero]; ring_nat
  rw [hlast]
  -- split first (k=0): C(n+1,0) b^(n+1) d^0 = b^(n+1)
  rw [sumTo_split_first n (fun k => choose (n + 1) k * b ^ ((n + 1) - k) * d ^ k)]
  have hfirst : choose (n + 1) 0 * b ^ ((n + 1) - 0) * d ^ 0 = b ^ (n + 1) := by
    rw [choose_zero_right, Nat.sub_zero, Nat.pow_zero]; ring_nat
  rw [hfirst]
  -- the shifted middle sum: C(n+1,k+1) b^{(n+1)−(k+1)} d^{k+1}, Pascal-split
  rw [sumTo_congr n
        (fun k => choose (n + 1) (k + 1) * b ^ ((n + 1) - (k + 1)) * d ^ (k + 1))
        (fun k => choose n k * b ^ (n - k) * d ^ (k + 1)
                  + choose n (k + 1) * b ^ (n - k) * d ^ (k + 1))
        (fun k _ => by
          show choose (n + 1) (k + 1) * b ^ ((n + 1) - (k + 1)) * d ^ (k + 1)
             = choose n k * b ^ (n - k) * d ^ (k + 1)
               + choose n (k + 1) * b ^ (n - k) * d ^ (k + 1)
          rw [Nat.succ_sub_succ, choose_succ_succ n k]; ring_nat)]
  rw [← sumTo_add_func n
        (fun k => choose n k * b ^ (n - k) * d ^ (k + 1))
        (fun k => choose n (k + 1) * b ^ (n - k) * d ^ (k + 1))]
  -- associativity: b^(n+1) + (S2 + S1) + d^(n+1) = b^(n+1) + S2 + S1 + d^(n+1)
  rw [← Nat.add_assoc (b ^ (n + 1)) _ _]

/-- Inductive step: `(b+d) · binom2 n = binom2 (n+1)`. -/
theorem binom2_step (b d n : Nat) : (b + d) * binom2 b d n = binom2 b d (n + 1) :=
  (lhs_to_common b d n).trans (rhs_to_common b d n).symm

/-- ★★★★ **Two-variable binomial theorem**: `(b + d)ⁿ = Σ_{k=0}^{n} C(n,k) · b^{n−k} · dᵏ`. -/
theorem add_pow (b d : Nat) : ∀ n, (b + d) ^ n = binom2 b d n
  | 0 => rfl
  | n + 1 => by rw [Nat.pow_succ, add_pow b d n, Nat.mul_comm, binom2_step]

/-- Smoke: `(2+3)² = 25 = C(2,0)·4 + C(2,1)·2·3 + C(2,2)·9`. -/
theorem add_pow_smoke : (2 + 3) ^ 2 = binom2 2 3 2 := by decide

end E213.Lib.Math.NumberTheory.BinomialTwoVar
