import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.Order
import E213.Meta.Int213.Bound

/-!
# Finite Cauchy–Schwarz via Lagrange's identity (∅-axiom)

Headline `cauchy_schwarz`:
  `(Σ_{k<n} a k · b k)^2 ≤ (Σ_{k<n} a k^2)·(Σ_{k<n} b k^2)`.

Engine `lagrange_identity`:
  `(Σ a²)·(Σ b²) − (Σ a·b)^2 = Σ_{0≤i<j<n} (a i · b j − a j · b i)^2`.

The slack is *computed*, not asserted via a quadratic-positivity / inner-product
argument: it is the explicit cross-square double-sum, manifestly `≥ 0`.
-/

namespace E213.Lib.Math.Analysis.CauchySchwarz

open E213.Meta.Int213
open E213.Meta.Int213.PolyIntM

/-! ## §1  Finite `Int`-valued range sum -/

/-- `sumI f n = Σ_{k<n} f k`. -/
def sumI (f : Nat → Int) : Nat → Int
  | 0     => 0
  | n + 1 => sumI f n + f n

@[simp] theorem sumI_zero (f : Nat → Int) : sumI f 0 = 0 := rfl
theorem sumI_succ (f : Nat → Int) (n : Nat) : sumI f (n + 1) = sumI f n + f n := rfl

/-- Pointwise-equal summands give equal sums (no `funext`: induction on `n`). -/
theorem sumI_congr {f g : Nat → Int} (n : Nat) (h : ∀ k, f k = g k) :
    sumI f n = sumI g n := by
  induction n with
  | zero => rfl
  | succ m ih => rw [sumI_succ, sumI_succ, ih, h m]

/-- A sum of pointwise-nonnegative summands is nonnegative. -/
theorem sumI_nonneg {f : Nat → Int} (n : Nat) (h : ∀ k, (0 : Int) ≤ f k) :
    (0 : Int) ≤ sumI f n := by
  induction n with
  | zero => exact Order.le_refl 0
  | succ m ih =>
      rw [sumI_succ]
      exact add_nonneg ih (h m)

/-! ## §2  The per-step cross-square lemma

For fixed `x y : Int` (which will become `a n`, `b n`):
  `Σ_{i<n} (a i · y − x · b i)^2
     = y²·Σ a² + x²·Σ b² − 2·x·y·Σ (a·b)`. -/
theorem cross_square_sum (a b : Nat → Int) (x y : Int) (n : Nat) :
    sumI (fun i => (a i * y - x * b i) * (a i * y - x * b i)) n
      = y * y * sumI (fun i => a i * a i) n
        + x * x * sumI (fun i => b i * b i) n
        - (x * y + x * y) * sumI (fun i => a i * b i) n := by
  induction n with
  | zero =>
      show (0 : Int)
        = y * y * (0 : Int) + x * x * (0 : Int) - (x * y + x * y) * (0 : Int)
      rw [Int.mul_zero, Int.mul_zero, Int.mul_zero, Int.add_zero]
      show (0 : Int) = (0 : Int) - 0
      rw [Order.sub_zero]
  | succ m ih =>
      rw [sumI_succ, sumI_succ, sumI_succ, sumI_succ, ih]
      ring_intZ

/-! ## §3  The cross double-sum `Σ_{0≤i<j<n}` -/

/-- Inner sum: `Σ_{i<j} (a i · b j − a j · b i)^2`. -/
def innerCross (a b : Nat → Int) (j : Nat) : Int :=
  sumI (fun i => (a i * b j - a j * b i) * (a i * b j - a j * b i)) j

/-- Outer sum: `Σ_{j<n} Σ_{i<j} (a i · b j − a j · b i)^2`. -/
def crossSum (a b : Nat → Int) (n : Nat) : Int :=
  sumI (innerCross a b) n

theorem crossSum_succ (a b : Nat → Int) (n : Nat) :
    crossSum a b (n + 1) = crossSum a b n + innerCross a b n := rfl

/-- Each inner cross term is nonnegative (sum of squares). -/
theorem innerCross_nonneg (a b : Nat → Int) (j : Nat) :
    (0 : Int) ≤ innerCross a b j :=
  sumI_nonneg j (fun i => int_sq_nonneg _)

/-- The full cross double-sum is nonnegative. -/
theorem crossSum_nonneg (a b : Nat → Int) (n : Nat) :
    (0 : Int) ≤ crossSum a b n :=
  sumI_nonneg n (fun j => innerCross_nonneg a b j)

/-! ## §4  Lagrange's identity -/

/-- ★ **Lagrange's identity.**
  `(Σ a²)·(Σ b²) − (Σ a·b)^2 = Σ_{0≤i<j<n} (a i · b j − a j · b i)^2`. -/
theorem lagrange_identity (a b : Nat → Int) (n : Nat) :
    sumI (fun k => a k * a k) n * sumI (fun k => b k * b k) n
        - sumI (fun k => a k * b k) n * sumI (fun k => a k * b k) n
      = crossSum a b n := by
  induction n with
  | zero => rfl
  | succ m ih =>
      rw [crossSum_succ, ← ih]
      -- expand the three outer sums at `m`
      rw [sumI_succ (fun k => a k * a k),
          sumI_succ (fun k => b k * b k),
          sumI_succ (fun k => a k * b k)]
      -- rewrite the inner cross sum at `m` via the per-step lemma
      show _ =
        (sumI (fun k => a k * a k) m * sumI (fun k => b k * b k) m
          - sumI (fun k => a k * b k) m * sumI (fun k => a k * b k) m)
        + innerCross a b m
      unfold innerCross
      rw [cross_square_sum a b (a m) (b m) m]
      ring_intZ

/-! ## §5  Cauchy–Schwarz (headline) -/

/-- ★★ **Finite Cauchy–Schwarz.**
  `(Σ a·b)^2 ≤ (Σ a²)·(Σ b²)` — the slack is the cross-square double-sum. -/
theorem cauchy_schwarz (a b : Nat → Int) (n : Nat) :
    sumI (fun k => a k * b k) n * sumI (fun k => a k * b k) n
      ≤ sumI (fun k => a k * a k) n * sumI (fun k => b k * b k) n := by
  -- `(Σ a²)(Σ b²) = (Σ a·b)² + crossSum`, with `crossSum ≥ 0`.
  have hid : sumI (fun k => a k * a k) n * sumI (fun k => b k * b k) n
      = sumI (fun k => a k * b k) n * sumI (fun k => a k * b k) n
        + crossSum a b n := by
    have h := lagrange_identity a b n
    -- h : A*B - C*C = crossSum  ⟹  A*B = C*C + crossSum
    rw [← h]; ring_intZ
  rw [hid]
  -- `C² ≤ C² + crossSum` since `0 ≤ crossSum`.
  apply Order.le_of_sub_nonneg
  rw [show (sumI (fun k => a k * b k) n * sumI (fun k => a k * b k) n + crossSum a b n)
        - sumI (fun k => a k * b k) n * sumI (fun k => a k * b k) n
        = crossSum a b n by ring_intZ]
  exact Order.sub_zero (crossSum a b n) ▸ crossSum_nonneg a b n

/-! ## §6  Non-vacuous smokes (closed numerals) -/

/-- `a = (1,2,3)`, `b = (4,5,6)`.  `Σ a·b = 32`, `Σ a² = 14`, `Σ b² = 77`.
    `32² = 1024 ≤ 14·77 = 1078`.  Slack `= 1078 − 1024 = 54`. -/
def aS : Nat → Int := fun k => match k with | 0 => 1 | 1 => 2 | _ => 3
def bS : Nat → Int := fun k => match k with | 0 => 4 | 1 => 5 | _ => 6

theorem smoke_cs : sumI (fun k => aS k * bS k) 3 * sumI (fun k => aS k * bS k) 3
      ≤ sumI (fun k => aS k * aS k) 3 * sumI (fun k => bS k * bS k) 3 := by
  decide

theorem smoke_slack :
    sumI (fun k => aS k * aS k) 3 * sumI (fun k => bS k * bS k) 3
      - sumI (fun k => aS k * bS k) 3 * sumI (fun k => aS k * bS k) 3
      = crossSum aS bS 3 := by
  decide

/-- The slack is exactly the explicit cross-square sum, numerically `54`. -/
theorem smoke_slack_value : crossSum aS bS 3 = 54 := by decide

end E213.Lib.Math.Analysis.CauchySchwarz
