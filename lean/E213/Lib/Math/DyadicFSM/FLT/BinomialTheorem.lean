import E213.Lib.Math.DyadicFSM.FLT.Binomial
import E213.Lib.Math.DyadicFSM.FLT.Sum
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

namespace E213.Lib.Math.DyadicFSM.FLT.BinomialTheorem

open E213.Lib.Math.DyadicFSM.FLT.Binomial (choose choose_zero_right)
open E213.Lib.Math.DyadicFSM.FLT.Sum (sumTo sumTo_zero sumTo_succ)

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

/-! ## binomSum: Σ-form of (a + 1)^n

The binomial theorem `(a+1)^n = binomSum a n` is the multi-step
deliverable for the next session.  This Part 17 commits the
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

end E213.Lib.Math.DyadicFSM.FLT.BinomialTheorem
