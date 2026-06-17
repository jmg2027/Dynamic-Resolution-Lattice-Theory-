import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.Order
import E213.Meta.Int213.OrderMul
import E213.Meta.Int213.Bound

/-!
# Chebyshev's sum inequality via a computed doubled slack (∅-axiom)

Headline `chebyshev_sum`:  for `a b : Nat → Int` **similarly sorted**,
  `(Σ_{k<n} a k)·(Σ_{k<n} b k)  ≤  n · Σ_{k<n} (a k · b k)`.

Engine `chebyshev_identity`:
  `2·(n·Σ a·b − Σa·Σb) = Σ_{i<n} Σ_{j<n} (a i − a j)·(b i − b j)`.

The slack is *computed*, not asserted via a rearrangement / pairing argument:
it is the explicit double-difference sum, manifestly `≥ 0` term-by-term because
both sequences are sorted the same way (matched signs of the two factors).

Mirrors `Lib/Math/Analysis/CauchySchwarz.lean` (`sumI`, `ring_intZ` kernel,
nested-sum / Lagrange-identity induction, `Int213` ordering toolkit).
-/

namespace E213.Lib.Math.Analysis.ChebyshevSumInequality

open E213.Meta.Int213
open E213.Meta.Int213.PolyIntM

/-! ## §1  Finite `Int`-valued range sum (mirror of CauchySchwarz) -/

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

/-- A sum over `k < n` of summands nonnegative *on that range* is nonnegative.
    (Only the in-range indices are evaluated by `sumI`.) -/
theorem sumI_nonneg_lt {f : Nat → Int} (n : Nat) (h : ∀ k, k < n → (0 : Int) ≤ f k) :
    (0 : Int) ≤ sumI f n := by
  induction n with
  | zero => exact Order.le_refl 0
  | succ m ih =>
      rw [sumI_succ]
      refine add_nonneg (ih (fun k hk => h k (Nat.lt_succ_of_lt hk))) (h m (Nat.lt_succ_self m))

/-! ## §2  Matched-sign product positivity

If `x` and `y` have the same sign (both `≤ 0` or both `≥ 0`), then `0 ≤ x·y`.
This is the term-by-term nonnegativity of the slack. -/

/-- `neg·neg ≥ 0`: from `x ≤ 0`, `y ≤ 0` we get `0 ≤ (−x)·(−y) = x·y`. -/
theorem mul_nonneg_of_nonpos_nonpos {x y : Int} (hx : x ≤ 0) (hy : y ≤ 0) :
    (0 : Int) ≤ x * y := by
  have hnx : (0 : Int) ≤ -x :=
    Order.le_zero_of_nonneg (Order.zero_sub x ▸ Order.sub_nonneg_of_le hx)
  have hny : (0 : Int) ≤ -y :=
    Order.le_zero_of_nonneg (Order.zero_sub y ▸ Order.sub_nonneg_of_le hy)
  have h : (0 : Int) ≤ (-x) * (-y) := mul_nonneg hnx hny
  rwa [show (-x) * (-y) = x * y from by ring_intZ] at h

/-- **Matched-sign product is nonnegative.** -/
theorem prod_nonneg_of_same_sign {x y : Int}
    (h : (x ≤ 0 ∧ y ≤ 0) ∨ (0 ≤ x ∧ 0 ≤ y)) : (0 : Int) ≤ x * y := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact mul_nonneg_of_nonpos_nonpos hx hy
  · exact mul_nonneg hx hy

/-- From `u ≤ v`, the difference `u − v ≤ 0`. -/
theorem sub_nonpos_of_le {u v : Int} (h : u ≤ v) : u - v ≤ 0 :=
  Order.le_of_sub_nonneg
    (show (0 - (u - v)).NonNeg from
      (show (0 : Int) - (u - v) = v - u from by
        rw [Order.zero_sub]; ring_intZ) ▸ Order.sub_nonneg_of_le h)

/-- From `u ≤ v`, the difference `0 ≤ v − u`. -/
theorem sub_nonneg_of_le' {u v : Int} (h : u ≤ v) : (0 : Int) ≤ v - u :=
  Order.le_zero_of_nonneg (Order.sub_nonneg_of_le h)

/-! ## §3  Similar sortedness and term-by-term slack positivity -/

/-- `mono a n`: `a` is nondecreasing on the first `n` indices. -/
def mono (a : Nat → Int) (n : Nat) : Prop :=
  ∀ i j, i ≤ j → i < n → j < n → a i ≤ a j

/-- The difference of two sorted-the-same-way sequences gives a matched-sign
    pair, hence a nonnegative product:
    `0 ≤ (a i − a j)·(b i − b j)` for any `i, j < n`. -/
theorem diff_prod_nonneg {a b : Nat → Int} {n : Nat}
    (ha : mono a n) (hb : mono b n) {i j : Nat} (hi : i < n) (hj : j < n) :
    (0 : Int) ≤ (a i - a j) * (b i - b j) := by
  rcases Nat.le_total i j with hij | hji
  · -- i ≤ j: a i ≤ a j and b i ≤ b j, so both differences ≤ 0.
    exact prod_nonneg_of_same_sign
      (Or.inl ⟨sub_nonpos_of_le (ha i j hij hi hj), sub_nonpos_of_le (hb i j hij hi hj)⟩)
  · -- j ≤ i: a j ≤ a i and b j ≤ b i, so both differences ≥ 0.
    exact prod_nonneg_of_same_sign
      (Or.inr ⟨sub_nonneg_of_le' (ha j i hji hj hi), sub_nonneg_of_le' (hb j i hji hj hi)⟩)

/-! ## §4  Per-row inner sum and the doubled-slack identity -/

/-- Inner sum for row `i`: `Σ_{j<n} (a i − a j)·(b i − b j)`. -/
def innerDiff (a b : Nat → Int) (i n : Nat) : Int :=
  sumI (fun j => (a i - a j) * (b i - b j)) n

/-- Outer (double) sum: `Σ_{i<n} Σ_{j<n} (a i − a j)·(b i − b j)`. -/
def doubleSum (a b : Nat → Int) (n : Nat) : Int :=
  sumI (fun i => innerDiff a b i n) n

/-- Each inner row is nonnegative (sum of matched-sign products over `j < n`). -/
theorem innerDiff_nonneg {a b : Nat → Int} {n : Nat}
    (ha : mono a n) (hb : mono b n) (i : Nat) (hi : i < n) :
    (0 : Int) ≤ innerDiff a b i n :=
  sumI_nonneg_lt n (fun j hj => diff_prod_nonneg ha hb hi hj)

/-- The full double-sum slack is nonnegative. -/
theorem doubleSum_nonneg {a b : Nat → Int} {n : Nat}
    (ha : mono a n) (hb : mono b n) : (0 : Int) ≤ doubleSum a b n :=
  sumI_nonneg_lt n (fun i hi => innerDiff_nonneg ha hb i hi)

/-! ## §5  Linearity of `sumI` over the expanded row, with fixed constants

The expanded row `f i = N·(aᵢ·bᵢ) − A·bᵢ − B·aᵢ + S` (with `N, A, B, S` fixed)
sums to `N·Σ(a·b) − A·Σb − B·Σa + (range)·S`.  We prove this generic linearity
over a range `r`, keeping the constants free, so the outer-sum induction never
disturbs the inner full-`n` sums. -/

theorem sumI_row_split (a b : Nat → Int) (N A B S : Int) (r : Nat) :
    sumI (fun k => N * (a k * b k) - A * b k - B * a k + S) r
      = N * sumI (fun k => a k * b k) r
        - A * sumI b r
        - B * sumI a r
        + (r : Int) * S := by
  induction r with
  | zero =>
      show (0 : Int)
        = N * (0 : Int) - A * (0 : Int) - B * (0 : Int) + (0 : Int) * S
      rw [Int.mul_zero, Int.mul_zero, Int.mul_zero, zero_mul]
      show (0 : Int) = (0 : Int) - 0 - 0 + 0
      rw [Order.sub_zero, Order.sub_zero, Int.add_zero]
  | succ m ih =>
      rw [sumI_succ, ih, sumI_succ (fun k => a k * b k), sumI_succ b, sumI_succ a]
      show _ = N * _ - A * _ - B * _ + ((m : Nat) + 1 : Int) * S
      rw [show (((m : Nat) + 1 : Int)) = (m : Int) + 1 from rfl]
      ring_intZ

/-! ## §6  Per-row expansion of the inner sum -/

/-- **Per-row expansion** of the inner sum:
  `Σ_{j<n} (a i − a j)(b i − b j)
     = n·(a i·b i) − b i·Σa − a i·Σb + Σ(a·b)`. -/
theorem innerDiff_expand (a b : Nat → Int) (i n : Nat) :
    innerDiff a b i n
      = (n : Int) * (a i * b i)
        - b i * sumI a n
        - a i * sumI b n
        + sumI (fun k => a k * b k) n := by
  unfold innerDiff
  induction n with
  | zero =>
      show (0 : Int)
        = (0 : Int) * (a i * b i) - b i * (0 : Int) - a i * (0 : Int) + (0 : Int)
      rw [zero_mul, Int.mul_zero, Int.mul_zero]
      show (0 : Int) = (0 : Int) - 0 - 0 + 0
      rw [Order.sub_zero, Order.sub_zero, Int.add_zero]
  | succ m ih =>
      rw [sumI_succ, ih, sumI_succ a, sumI_succ b, sumI_succ (fun k => a k * b k)]
      show _ = (((m : Nat) + 1 : Int)) * (a i * b i) - _ - _ + _
      rw [show (((m : Nat) + 1 : Int)) = (m : Int) + 1 from rfl]
      ring_intZ

/-! ## §7  The doubled-slack identity (★ engine) -/

/-- ★ **Chebyshev doubled-slack identity.**
  `2·(n·Σ(a·b) − Σa·Σb) = Σ_{i<n} Σ_{j<n} (a i − a j)·(b i − b j)`. -/
theorem chebyshev_identity (a b : Nat → Int) (n : Nat) :
    2 * ((n : Int) * sumI (fun k => a k * b k) n - sumI a n * sumI b n)
      = doubleSum a b n := by
  unfold doubleSum
  -- Each row `innerDiff a b k n` expands into the linear form
  -- `N·(aₖbₖ) − A·bₖ − B·aₖ + S` with `N = ↑n`, `A = sumI a n`, `B = sumI b n`,
  -- `S = Σ a·b` all constant across the outer (`i`) sum.
  have hrow : ∀ k,
      innerDiff a b k n
        = (n : Int) * (a k * b k)
          - sumI a n * b k - sumI b n * a k + sumI (fun t => a t * b t) n :=
    fun k => by
      rw [innerDiff_expand a b k n,
          show b k * sumI a n = sumI a n * b k from mul_comm _ _,
          show a k * sumI b n = sumI b n * a k from mul_comm _ _]
  rw [sumI_congr n hrow]
  rw [sumI_row_split a b (n : Int) (sumI a n) (sumI b n)
        (sumI (fun t => a t * b t) n) n]
  ring_intZ

/-! ## §8  Chebyshev's sum inequality (★★ headline) -/

/-- `0 ≤ 2·x  ⟹  0 ≤ x`, via `2·x = x + x` and `nonneg_of_add_self`. -/
theorem nonneg_of_two_mul_nonneg {x : Int} (h : (0 : Int) ≤ 2 * x) : (0 : Int) ≤ x :=
  nonneg_of_add_self (show (0 : Int) ≤ x + x from
    (show (2 : Int) * x = x + x from by ring_intZ) ▸ h)

/-- ★★ **Chebyshev's sum inequality.**
  For `a`, `b` similarly sorted (`mono`):
  `(Σ a)·(Σ b) ≤ n · Σ (a·b)` — the slack is the explicit double-difference
  sum, nonnegative term-by-term by matched sortedness. -/
theorem chebyshev_sum {a b : Nat → Int} {n : Nat}
    (ha : mono a n) (hb : mono b n) :
    sumI a n * sumI b n ≤ (n : Int) * sumI (fun k => a k * b k) n := by
  -- `2·slack = doubleSum ≥ 0`, hence `slack ≥ 0`.
  have hds : (0 : Int) ≤ doubleSum a b n := doubleSum_nonneg ha hb
  have h2 : (0 : Int) ≤ 2 *
      ((n : Int) * sumI (fun k => a k * b k) n - sumI a n * sumI b n) :=
    (chebyshev_identity a b n).symm ▸ hds
  have hslack : (0 : Int) ≤
      (n : Int) * sumI (fun k => a k * b k) n - sumI a n * sumI b n :=
    nonneg_of_two_mul_nonneg h2
  exact Order.le_of_sub_nonneg (Order.nonneg_of_le_zero hslack)

/-! ## §9  Non-vacuous smoke (closed numerals) -/

/-- `a = (1,2,3)`, `b = (4,5,6)`, both sorted.
    `Σa·Σb = 6·15 = 90 ≤ 3·(4+10+18) = 3·32 = 96`. -/
def aS : Nat → Int := fun k => match k with | 0 => 1 | 1 => 2 | _ => 3
def bS : Nat → Int := fun k => match k with | 0 => 4 | 1 => 5 | _ => 6

theorem smoke_ch :
    sumI aS 3 * sumI bS 3 ≤ (3 : Int) * sumI (fun k => aS k * bS k) 3 := by
  decide

/-- The doubled slack is exactly the double-difference sum (numerically `12`):
    `2·(96 − 90) = 12 = doubleSum`. -/
theorem smoke_ch_identity :
    2 * ((3 : Int) * sumI (fun k => aS k * bS k) 3 - sumI aS 3 * sumI bS 3)
      = doubleSum aS bS 3 := by
  decide

theorem smoke_ch_slack_value : doubleSum aS bS 3 = 12 := by decide

-- ∅-axiom probes (should print "does not depend on any axioms")
#print axioms chebyshev_identity
#print axioms chebyshev_sum

end E213.Lib.Math.Analysis.ChebyshevSumInequality

