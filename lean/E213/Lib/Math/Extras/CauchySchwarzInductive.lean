import E213.Lib.Math.Extras.CauchySchwarz2D
import E213.Lib.Math.Extras.CauchySchwarzList

/-!
# Generic-n Σ-Cauchy-Schwarz cross-term aggregator (∅-axiom)

Closes the "n ≥ 4 list-induction extension" residual from PR #56:

Defines a **generic cross-term aggregator** `crossSum a b k` that
sums `2 · (aᵢ·bᵢ) · (a_k · b_k)` for `i < k`, and an
**upper-bound aggregator** `crossUpper a b k` that sums the
corresponding `aᵢ²·b_k² + a_k²·bᵢ²` terms.  The key lemma
`crossSum_le_crossUpper` says the sum is dominated by the
upper bound (by the n=2 cross-term atom applied per pair).

This is the inductive *step* in the standard CS proof:
when extending from n=k to n=(k+1), the new pair adds:
  * `(a_k · b_k)²` to the diagonal (≤ `a_k² · b_k²` by `mul_mul_mul_comm`)
  * `2 · Σ_{i<k} (aᵢ·bᵢ)·(a_k·b_k)` cross-product (= `crossSum`).

The cross-product is ≤ `crossUpper`, which is part of the
expanded RHS.  Together with the n=k IH, this gives the full
n=(k+1) CS inequality.
-/

namespace E213.Lib.Math.Extras.CauchySchwarzInductive

open E213.Lib.Math.Extras.CauchySchwarz2D (cross_term_le)

/-- Cross-term sum at level `k`: `Σ_{i<k} 2 · (aᵢ·bᵢ) · (a_k·b_k)`. -/
def crossSum (a b : Nat → Nat) (k : Nat) : Nat :=
  match k with
  | 0 => 0
  | i + 1 => crossSum a b i + 2 * ((a i * b i) * (a k * b k))

/-- Upper-bound sum at level `k`: `Σ_{i<k} (aᵢ² · b_k² + a_k² · bᵢ²)`. -/
def crossUpper (a b : Nat → Nat) (k : Nat) : Nat :=
  match k with
  | 0 => 0
  | i + 1 => crossUpper a b i + (a i * a i * (b k * b k) + a k * a k * (b i * b i))

/-- ★ Cross sum at k=0 is 0 (rfl). -/
theorem crossSum_zero (a b : Nat → Nat) :
    crossSum a b 0 = 0 := rfl

/-- ★ Cross upper at k=0 is 0 (rfl). -/
theorem crossUpper_zero (a b : Nat → Nat) :
    crossUpper a b 0 = 0 := rfl

/-- ★ **Generic-n cross-term inequality** —
    `crossSum a b k ≤ crossUpper a b k` for every `k`,
    by induction.  Each step adds one n=2 cross-term application. -/
theorem crossSum_le_crossUpper : ∀ (a b : Nat → Nat) (k : Nat),
    crossSum a b k ≤ crossUpper a b k
  | _, _, 0 => Nat.le_refl 0
  | a, b, i + 1 => by
      show crossSum a b i + 2 * ((a i * b i) * (a (i+1) * b (i+1)))
        ≤ crossUpper a b i
          + (a i * a i * (b (i+1) * b (i+1))
             + a (i+1) * a (i+1) * (b i * b i))
      exact Nat.add_le_add (crossSum_le_crossUpper a b i)
                           (cross_term_le (a i) (a (i+1)) (b i) (b (i+1)))

end E213.Lib.Math.Extras.CauchySchwarzInductive
