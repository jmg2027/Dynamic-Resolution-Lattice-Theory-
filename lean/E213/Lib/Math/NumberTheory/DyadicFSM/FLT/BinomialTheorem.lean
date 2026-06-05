import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Meta.Tactic.NatHelper
/-!
# Σ helpers for the binomial theorem — FLT prerequisite

Three Σ manipulation lemmas needed for the binomial-theorem inductive
proof:

  · `sumTo_mul_left`     : `a · Σ f = Σ (a · f)`
  · `sumTo_add_func`     : `Σ f + Σ g = Σ (f + g)` (pointwise add)
  · `sumTo_split_first`  : `Σ_{k=0}^{n} f(k) = f(0) + Σ_{k=0}^{n-1} f(k+1)`

Plus the binomSum definition (Σ form of `(a+1)^n`) for use by the
next-session binomial theorem proof.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose choose_zero_right)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_zero sumTo_succ)

/-! ## Σ helpers -/

/-- Factor scalar out of Σ:  `a · Σ_n f = Σ_n (a · f)`. -/
theorem sumTo_mul_left (a : Nat) :
    ∀ (n : Nat) (f : Nat → Nat),
      a * sumTo n f = sumTo n (fun k => a * f k)
  | 0, _ => by
    show a * 0 = sumTo 0 _
    rw [Nat.mul_zero]
    rfl
  | n + 1, f => by
    show a * (sumTo n f + f n) = sumTo n (fun k => a * f k) + a * f n
    rw [Nat.mul_add, sumTo_mul_left a n f]

/-- Σ distributes over pointwise add:  `Σ_n f + Σ_n g = Σ_n (f + g)`. -/
theorem sumTo_add_func :
    ∀ (n : Nat) (f g : Nat → Nat),
      sumTo n f + sumTo n g = sumTo n (fun k => f k + g k)
  | 0, _, _ => rfl
  | n + 1, f, g => by
    show (sumTo n f + f n) + (sumTo n g + g n)
       = sumTo n (fun k => f k + g k) + (f n + g n)
    rw [← sumTo_add_func n f g]
    -- Goal: (sumTo n f + f n) + (sumTo n g + g n)
    --     = (sumTo n f + sumTo n g) + (f n + g n)
    rw [Nat.add_assoc (sumTo n f) (f n) (sumTo n g + g n)]
    rw [← Nat.add_assoc (f n) (sumTo n g) (g n)]
    rw [Nat.add_comm (f n) (sumTo n g)]
    rw [Nat.add_assoc (sumTo n g) (f n) (g n)]
    rw [← Nat.add_assoc (sumTo n f) (sumTo n g) (f n + g n)]

/-- Σ extract first + shift:
    `sumTo (n+1) f = f 0 + sumTo n (fun k => f (k+1))`. -/
theorem sumTo_split_first :
    ∀ (n : Nat) (f : Nat → Nat),
      sumTo (n + 1) f = f 0 + sumTo n (fun k => f (k + 1))
  | 0, f => by
    show 0 + f 0 = f 0 + 0
    rw [Nat.zero_add, Nat.add_zero]
  | n + 1, f => by
    show sumTo (n + 1) f + f (n + 1)
       = f 0 + (sumTo n (fun k => f (k + 1)) + f (n + 1))
    rw [sumTo_split_first n f]
    -- Goal: (f 0 + sumTo n (fun k => f (k+1))) + f (n+1)
    --     = f 0 + (sumTo n (fun k => f (k+1)) + f (n+1))
    rw [Nat.add_assoc]

/-- Σ congruence: if `f k = g k` for all `k < n`, then `Σ f = Σ g`.
    PURE alternative to `funext` (which pulls `Quot.sound`).  By
    induction on `n`. -/
theorem sumTo_congr :
    ∀ (n : Nat) (f g : Nat → Nat),
      (∀ k, k < n → f k = g k) → sumTo n f = sumTo n g
  | 0, _, _, _ => rfl
  | n + 1, f, g, h => by
    show sumTo n f + f n = sumTo n g + g n
    rw [sumTo_congr n f g (fun k hk => h k (Nat.lt_succ_of_lt hk))]
    rw [h n (Nat.lt_succ_self n)]

/-! ## binomSum: Σ-form of (a + 1)^n

The binomial theorem `(a+1)^n = binomSum a n` is the multi-step
deferred.  This file commits the
infrastructure (helpers + def + zero case + smokes).
-/

/-- Binomial expansion: `binomSum a n = Σ_{k=0}^{n} C(n, k) · a^k`. -/
def binomSum (a n : Nat) : Nat := sumTo (n + 1) (fun k => choose n k * a^k)

/-- `binomSum a 0 = 1`. -/
theorem binomSum_zero (a : Nat) : binomSum a 0 = 1 := by
  show sumTo 1 (fun k => choose 0 k * a^k) = 1
  show 0 + choose 0 0 * a^0 = 1
  rw [choose_zero_right, Nat.one_mul, Nat.zero_add]
  rfl

/-- Smoke: `binomSum 2 3 = (2+1)^3 = 27`. -/
theorem binomSum_2_3 : binomSum 2 3 = 27 := by decide

/-- Smoke: `binomSum 3 4 = (3+1)^4 = 256`. -/
theorem binomSum_3_4 : binomSum 3 4 = 256 := by decide

/-- Smoke: `binomSum 1 5 = 2^5 = 32`. -/
theorem binomSum_1_5 : binomSum 1 5 = 32 := by decide

/-! ## Binomial theorem inductive step

Both LHS = `(a + 1) · binomSum a n` and RHS = `binomSum a (n + 1)`
reduce to a common form:

  `1 + sumTo n (fun k => C n k · a^(k+1))
     + sumTo n (fun k => C n (k+1) · a^(k+1))
     + a^(n+1)`

via the Σ helpers + Pascal applied pointwise.
-/

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose_zero_succ choose_succ_succ choose_self)
open E213.Tactic.NatHelper (mul_assoc add_mul)

/-- Helper: `a · (C n k · a^k) = C n k · a^(k+1)`. -/
private theorem mul_pow_step (a n k : Nat) :
    a * (choose n k * a^k) = choose n k * a^(k + 1) := by
  rw [← mul_assoc, Nat.mul_comm a (choose n k), mul_assoc,
      Nat.mul_comm a (a^k)]
  rfl

/-- Helper: `a · binomSum a n = sumTo (n+1) (fun k => C n k · a^(k+1))`. -/
private theorem a_mul_binomSum (a n : Nat) :
    a * binomSum a n = sumTo (n + 1) (fun k => choose n k * a^(k + 1)) := by
  show a * sumTo (n + 1) (fun k => choose n k * a^k)
     = sumTo (n + 1) (fun k => choose n k * a^(k + 1))
  rw [sumTo_mul_left a (n + 1) (fun k => choose n k * a^k)]
  exact sumTo_congr (n + 1)
    (fun k => a * (choose n k * a^k))
    (fun k => choose n k * a^(k + 1))
    (fun k _ => mul_pow_step a n k)

/-- Helper: split first term of binomSum.
    `binomSum a n = 1 + sumTo n (fun k => C n (k+1) · a^(k+1))`. -/
private theorem binomSum_split (a n : Nat) :
    binomSum a n = 1 + sumTo n (fun k => choose n (k + 1) * a^(k + 1)) := by
  show sumTo (n + 1) (fun k => choose n k * a^k)
     = 1 + sumTo n (fun k => choose n (k + 1) * a^(k + 1))
  rw [sumTo_split_first n (fun k => choose n k * a^k)]
  show choose n 0 * a^0 + _ = 1 + _
  rw [choose_zero_right, Nat.one_mul]
  rfl

/-- 4-term Nat-add rearrange: `(A + B) + (C + D) = C + A + D + B`. -/
private theorem rearrange_4 (A B C D : Nat) :
    (A + B) + (C + D) = C + A + D + B := by
  -- (A + B) + (C + D) = A + B + C + D = A + (B + C) + D = A + (C + B) + D
  --                  = A + C + B + D = C + A + B + D = C + A + (B + D)
  --                  = C + A + (D + B) = C + A + D + B
  rw [Nat.add_assoc A B (C + D)]
  rw [← Nat.add_assoc B C D]
  rw [Nat.add_comm B C]
  rw [Nat.add_assoc C B D]
  rw [Nat.add_comm B D]
  rw [← Nat.add_assoc C D B]
  rw [← Nat.add_assoc A (C + D) B]
  rw [Nat.add_comm A (C + D)]
  rw [Nat.add_assoc C D A]
  rw [Nat.add_comm D A]
  rw [← Nat.add_assoc C A D]

/-- LHS reduction.  `(a + 1) · binomSum a n` reduces to common form. -/
private theorem lhs_to_common (a n : Nat) :
    (a + 1) * binomSum a n
      = 1 + sumTo n (fun k => choose n k * a^(k + 1))
          + sumTo n (fun k => choose n (k + 1) * a^(k + 1))
          + a^(n + 1) := by
  rw [add_mul, Nat.one_mul]
  -- Goal: a * binomSum a n + binomSum a n = ...
  rw [a_mul_binomSum a n, binomSum_split a n]
  -- Goal: sumTo (n+1) (..a^(k+1)) + (1 + sumTo n (..a^(k+1))) = ...
  -- Extract last from first sum
  show sumTo n (fun k => choose n k * a^(k + 1))
         + choose n n * a^(n + 1)
       + (1 + sumTo n (fun k => choose n (k + 1) * a^(k + 1)))
     = 1 + sumTo n (fun k => choose n k * a^(k + 1))
         + sumTo n (fun k => choose n (k + 1) * a^(k + 1))
         + a^(n + 1)
  rw [choose_self, Nat.one_mul]
  -- Goal: (sumTo n .. + a^(n+1)) + (1 + sumTo n ..) = 1 + sumTo n .. + sumTo n .. + a^(n+1)
  -- Use rearrange_4 with A = sumTo n .. (first), B = a^(n+1), C = 1, D = sumTo n .. (second)
  rw [rearrange_4 (sumTo n (fun k => choose n k * a^(k + 1)))
        (a^(n + 1)) 1 (sumTo n (fun k => choose n (k + 1) * a^(k + 1)))]

/-- RHS reduction.  `binomSum a (n + 1)` reduces to common form. -/
private theorem rhs_to_common (a n : Nat) :
    binomSum a (n + 1)
      = 1 + sumTo n (fun k => choose n k * a^(k + 1))
          + sumTo n (fun k => choose n (k + 1) * a^(k + 1))
          + a^(n + 1) := by
  show sumTo (n + 2) (fun k => choose (n + 1) k * a^k)
     = 1 + sumTo n (fun k => choose n k * a^(k + 1))
         + sumTo n (fun k => choose n (k + 1) * a^(k + 1))
         + a^(n + 1)
  -- Extract last
  show sumTo (n + 1) (fun k => choose (n + 1) k * a^k)
       + choose (n + 1) (n + 1) * a^(n + 1)
     = 1 + sumTo n (fun k => choose n k * a^(k + 1))
         + sumTo n (fun k => choose n (k + 1) * a^(k + 1))
         + a^(n + 1)
  rw [choose_self, Nat.one_mul]
  -- Split first on the remaining sum
  rw [sumTo_split_first n (fun k => choose (n + 1) k * a^k)]
  show choose (n + 1) 0 * a^0
       + sumTo n (fun k => choose (n + 1) (k + 1) * a^(k + 1))
       + a^(n + 1)
     = 1 + sumTo n (fun k => choose n k * a^(k + 1))
         + sumTo n (fun k => choose n (k + 1) * a^(k + 1))
         + a^(n + 1)
  rw [choose_zero_right, Nat.one_mul]
  show 1 + sumTo n (fun k => choose (n + 1) (k + 1) * a^(k + 1)) + a^(n + 1)
     = 1 + sumTo n (fun k => choose n k * a^(k + 1))
         + sumTo n (fun k => choose n (k + 1) * a^(k + 1))
         + a^(n + 1)
  -- Apply Pascal pointwise inside the sum, then split via sumTo_add_func.
  -- Use `sumTo_congr` to avoid `funext` (Quot.sound).
  rw [sumTo_congr n
        (fun k => choose (n + 1) (k + 1) * a^(k + 1))
        (fun k => choose n k * a^(k + 1) + choose n (k + 1) * a^(k + 1))
        (fun k _ => by
          show choose (n + 1) (k + 1) * a^(k + 1)
             = choose n k * a^(k + 1) + choose n (k + 1) * a^(k + 1)
          rw [choose_succ_succ n k, add_mul])]
  -- Goal: 1 + sumTo n (fun k => C n k * a^(k+1) + C n (k+1) * a^(k+1)) + a^(n+1)
  --     = 1 + sumTo n (fun k => C n k * a^(k+1))
  --         + sumTo n (fun k => C n (k+1) * a^(k+1)) + a^(n+1)
  -- Backward sumTo_add_func: sumTo (f + g) = sumTo f + sumTo g
  rw [← sumTo_add_func n (fun k => choose n k * a^(k + 1))
        (fun k => choose n (k + 1) * a^(k + 1))]
  -- Final associativity: 1 + (A + B) + C = (1 + A) + B + C
  rw [← Nat.add_assoc 1 _ _]

/-- ★★★ **Binomial theorem inductive step**:
    `(a + 1) · binomSum a n = binomSum a (n + 1)`.  PURE. -/
theorem binomSum_step (a n : Nat) :
    (a + 1) * binomSum a n = binomSum a (n + 1) :=
  (lhs_to_common a n).trans (rhs_to_common a n).symm

/-- ★★★★ **Binomial theorem at b = 1**:
    `(a + 1)^n = binomSum a n = Σ_{k=0}^{n} C(n, k) · a^k`.

    By induction on `n`, using `binomSum_step` for the inductive step.
    PURE. -/
theorem binom_theorem_b_eq_one (a : Nat) :
    ∀ n, (a + 1)^n = binomSum a n
  | 0 => (binomSum_zero a).symm
  | n + 1 => by
    -- Nat.pow def: a^(n+1) = a^n * a
    show (a + 1)^n * (a + 1) = binomSum a (n + 1)
    rw [binom_theorem_b_eq_one a n, Nat.mul_comm, binomSum_step]

/-- ★★★ **Pascal row sum**: `Σ_{k=0}^{n} C(n, k) = 2ⁿ`.  The binomial theorem at `a = 1`
    (`(1+1)ⁿ = Σ C(n,k)·1ᵏ`), with `1ᵏ = 1`. -/
theorem pascal_row_sum (n : Nat) : sumTo (n + 1) (fun k => choose n k) = 2 ^ n := by
  rw [show (2 : Nat) = 1 + 1 from rfl, binom_theorem_b_eq_one 1 n]
  show sumTo (n + 1) (fun k => choose n k) = sumTo (n + 1) (fun k => choose n k * 1 ^ k)
  exact sumTo_congr (n + 1) (fun k => choose n k) (fun k => choose n k * 1 ^ k)
    (fun k _ => by show choose n k = choose n k * 1 ^ k; rw [Nat.one_pow, Nat.mul_one])

/-- A single term is `≤` the whole sum (all terms `Nat`-nonneg). -/
theorem sumTo_term_le : ∀ (m : Nat) (f : Nat → Nat) (k : Nat), k < m → f k ≤ sumTo m f
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, f, k, h => by
    rw [sumTo_succ]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with hlt | heq
    · exact Nat.le_trans (sumTo_term_le m f k hlt) (Nat.le_add_right _ _)
    · subst heq; exact Nat.le_add_left _ _

/-- ★★ **Binomial bound**: `C(n, k) ≤ 2ⁿ` — each binomial coefficient is at most the
    Pascal row sum.  (For `k ≤ n` it is one term of `Σ C(n,j) = 2ⁿ`; for `k > n` it is `0`.) -/
theorem choose_le_two_pow (n k : Nat) : choose n k ≤ 2 ^ n := by
  rcases Nat.lt_or_ge k (n + 1) with h | h
  · rw [← pascal_row_sum n]
    exact sumTo_term_le (n + 1) (fun j => choose n j) k h
  · rw [E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial.choose_eq_zero_of_lt n k h]
    exact Nat.zero_le _

end E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
