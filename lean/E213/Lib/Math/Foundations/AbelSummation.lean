import E213.Lib.Math.Foundations.CauchySchwarzGeneral

/-!
# Abel summation / summation by parts over `Int` (∅-axiom)

General-`n` discrete integration-by-parts, built on the `sumZ` toolkit of
`Foundations/CauchySchwarzGeneral.lean`.

  * ★★ `telescope` — `Σ_{i<n} (f (i+1) − f i) = f n − f 0` (the discrete FTC).
  * ★★★ `summation_by_parts` — discrete integration by parts:
    `Σ aᵢ(b_{i+1}−bᵢ) = a_n b_n − a₀ b₀ − Σ (a_{i+1}−aᵢ) b_{i+1}`.
  * ★★ `partial_summation` — Abel's partial-summation corollary with prefix sums.

All by induction on `n` + `ring_intZ` (generalize-first where the tail/prefix
sums appear).  Genuinely absent (only the *specific* `FactorialSum.fact_telescope`
and the Casoratian one-step law existed).  All ∅-axiom.
-/

namespace E213.Lib.Math.Foundations.AbelSummation

open E213.Lib.Math.Foundations.CauchySchwarzGeneral
open E213.Meta.Int213

/-! ## Telescoping (discrete fundamental theorem of calculus) -/

/-- ★★ **Telescoping sum**: `Σ_{i<n} (f (i+1) − f i) = f n − f 0`. -/
theorem telescope (f : Nat → Int) (n : Nat) :
    sumZ n (fun i => f (i + 1) - f i) = f n - f 0 := by
  induction n with
  | zero => show (0 : Int) = f 0 - f 0; rw [Order.sub_self_zero]
  | succ m ih =>
    rw [sumZ_succ, ih]
    show (f m - f 0) + (f (m + 1) - f m) = f (m + 1) - f 0
    ring_intZ

/-! ## Summation by parts (Abel) -/

/-- ★★★ **Summation by parts**:
    `Σ_{i<n} a i · (b (i+1) − b i) = a n·b n − a 0·b 0 − Σ_{i<n} (a (i+1) − a i)·b (i+1)`. -/
theorem summation_by_parts (a b : Nat → Int) (n : Nat) :
    sumZ n (fun i => a i * (b (i + 1) - b i))
      = a n * b n - a 0 * b 0
        - sumZ n (fun i => (a (i + 1) - a i) * b (i + 1)) := by
  induction n with
  | zero =>
    show (0 : Int) = a 0 * b 0 - a 0 * b 0 - 0
    rw [Order.sub_self_zero, Order.sub_zero]
  | succ m ih =>
    rw [sumZ_succ, sumZ_succ, ih]
    show (a m * b m - a 0 * b 0 - sumZ m (fun i => (a (i + 1) - a i) * b (i + 1)))
         + a m * (b (m + 1) - b m)
       = a (m + 1) * b (m + 1) - a 0 * b 0
         - (sumZ m (fun i => (a (i + 1) - a i) * b (i + 1))
            + (a (m + 1) - a m) * b (m + 1))
    generalize sumZ m (fun i => (a (i + 1) - a i) * b (i + 1)) = S
    ring_intZ

/-! ## Partial summation (Abel's corollary) -/

/-- Prefix sum `A k = Σ_{j<k} a j`. -/
def prefixSum (a : Nat → Int) (k : Nat) : Int := sumZ k a

/-- `prefixSum a (k+1) − prefixSum a k = a k` (the prefix sum antidifferences `a`). -/
theorem prefixSum_diff (a : Nat → Int) (k : Nat) :
    prefixSum a (k + 1) - prefixSum a k = a k := by
  show (sumZ k a + a k) - sumZ k a = a k
  generalize sumZ k a = S
  ring_intZ

/-- ★★ **Abel partial summation**:
    `Σ_{i<n} a i · c i = A n · c n − Σ_{i<n} A (i+1)·(c (i+1) − c i)`, `A k = Σ_{j<k} a j`. -/
theorem partial_summation (a c : Nat → Int) (n : Nat) :
    sumZ n (fun i => a i * c i)
      = prefixSum a n * c n
        - sumZ n (fun i => prefixSum a (i + 1) * (c (i + 1) - c i)) := by
  induction n with
  | zero =>
    show (0 : Int) = prefixSum a 0 * c 0 - 0
    show (0 : Int) = sumZ 0 a * c 0 - 0
    rw [sumZ_zero]; show (0 : Int) = 0 * c 0 - 0
    rw [zero_mul, Order.sub_zero]
  | succ m ih =>
    rw [sumZ_succ, sumZ_succ, ih]
    have hd : a m = prefixSum a (m + 1) - prefixSum a m := (prefixSum_diff a m).symm
    rw [hd]
    show (prefixSum a m * c m
            - sumZ m (fun i => prefixSum a (i + 1) * (c (i + 1) - c i)))
         + (prefixSum a (m + 1) - prefixSum a m) * c m
       = prefixSum a (m + 1) * c (m + 1)
         - (sumZ m (fun i => prefixSum a (i + 1) * (c (i + 1) - c i))
            + prefixSum a (m + 1) * (c (m + 1) - c m))
    generalize sumZ m (fun i => prefixSum a (i + 1) * (c (i + 1) - c i)) = S
    generalize prefixSum a m = Am
    generalize prefixSum a (m + 1) = Am1
    ring_intZ

end E213.Lib.Math.Foundations.AbelSummation
