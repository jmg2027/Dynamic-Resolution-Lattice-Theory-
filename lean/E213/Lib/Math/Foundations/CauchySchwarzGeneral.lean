import E213.Meta.Int213.Core
import E213.Meta.Int213.Bound
import E213.Meta.Int213.Order
import E213.Meta.Int213.PolyIntMTactic

/-!
# General-`n` Lagrange identity + Cauchy–Schwarz over `Int` (∅-axiom)

Sequences `a b : Nat → Int`.  The fixed-`n` (n = 2,3,4) cases live in
`Lib/Math/Foundations/Positivity.lean`; this is the **general-`n` sequence**
version (the genuine extension).

  * ★★ `lagrange_identity` — `(Σ aᵢ²)(Σ bᵢ²) − (Σ aᵢbᵢ)² = Σ_{m<n} Σ_{i<m} (aᵢb_m − a_mbᵢ)²`.
  * ★★★ `cauchy_schwarz` — `(Σ aᵢbᵢ)² ≤ (Σ aᵢ²)(Σ bᵢ²)`.

Induction on `n` (`gap_succ` adds row `n`; the pure-algebra core `rowSq_expand` +
`cross_sq` close by `ring_intZ` after isolating compound atoms).  CS follows since
the gap equals the nonnegative strict-upper-triangular SOS `triSq`.  All ∅-axiom.
-/

namespace E213.Lib.Math.Foundations.CauchySchwarzGeneral

open E213.Meta.Int213

/-! ## Int-valued Σ toolkit -/

/-- `sumZ n f = f 0 + f 1 + ... + f (n-1)`. -/
def sumZ : Nat → (Nat → Int) → Int
  | 0,     _ => 0
  | n + 1, f => sumZ n f + f n

@[simp] theorem sumZ_zero (f : Nat → Int) : sumZ 0 f = 0 := rfl

@[simp] theorem sumZ_succ (n : Nat) (f : Nat → Int) :
    sumZ (n + 1) f = sumZ n f + f n := rfl

theorem sumZ_congr (n : Nat) (f g : Nat → Int) (h : ∀ k, k < n → f k = g k) :
    sumZ n f = sumZ n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumZ_succ, sumZ_succ, ih (fun k hk => h k (Nat.lt_succ_of_lt hk)),
        h m (Nat.lt_succ_self m)]

theorem sumZ_const_zero (n : Nat) : sumZ n (fun _ => (0 : Int)) = 0 := by
  induction n with
  | zero => rfl
  | succ m ih => rw [sumZ_succ, ih]; rfl

theorem sumZ_add_func (n : Nat) (f g : Nat → Int) :
    sumZ n f + sumZ n g = sumZ n (fun k => f k + g k) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    show (sumZ m f + f m) + (sumZ m g + g m)
       = sumZ m (fun k => f k + g k) + (f m + g m)
    rw [← ih]
    have : (sumZ m f + f m) + (sumZ m g + g m)
         = (sumZ m f + sumZ m g) + (f m + g m) := by ring_intZ
    rw [this]

theorem sumZ_mul_left (c : Int) (n : Nat) (f : Nat → Int) :
    c * sumZ n f = sumZ n (fun k => c * f k) := by
  induction n with
  | zero => show c * 0 = 0; rw [PolyIntM.mul_zeroZ]
  | succ m ih =>
    show c * (sumZ m f + f m) = sumZ m (fun k => c * f k) + c * f m
    rw [← ih]; ring_intZ

/-! ## Aggregates -/

/-- `Σ_{i<n} a i²`. -/
def ssq (a : Nat → Int) (n : Nat) : Int := sumZ n (fun i => a i * a i)

/-- `Σ_{i<n} a i · b i`. -/
def dot (a b : Nat → Int) (n : Nat) : Int := sumZ n (fun i => a i * b i)

/-- Cauchy–Schwarz gap `(Σ aᵢ²)(Σ bᵢ²) − (Σ aᵢbᵢ)²`. -/
def gap (a b : Nat → Int) (n : Nat) : Int := ssq a n * ssq b n - dot a b n * dot a b n

/-- Row sum at fixed outer index `m`: `Σ_{i<m} (aᵢ·b_m − a_m·bᵢ)²`. -/
def rowSq (a b : Nat → Int) (m : Nat) : Int :=
  sumZ m (fun i => (a i * b m - a m * b i) * (a i * b m - a m * b i))

/-- Strict-upper-triangular double sum `Σ_{m<n} Σ_{i<m} (aᵢ·b_m − a_m·bᵢ)²`. -/
def triSq (a b : Nat → Int) (n : Nat) : Int := sumZ n (fun m => rowSq a b m)

/-! ## The row-sum expansion (the key algebraic step) -/

/-- Pointwise square expansion (named to avoid in-lambda `generalize`). -/
theorem cross_sq (ai bi am bm : Int) :
    (ai * bm - am * bi) * (ai * bm - am * bi)
      = bm * bm * (ai * ai) + am * am * (bi * bi)
        + (- (2 * (am * bm))) * (ai * bi) := by
  ring_intZ

/-- `rowSq a b m = b_m²·ssq a m + a_m²·ssq b m − 2·a_m·b_m·dot a b m`. -/
theorem rowSq_expand (a b : Nat → Int) (m : Nat) :
    rowSq a b m
      = b m * b m * ssq a m + a m * a m * ssq b m
        - 2 * (a m * b m) * dot a b m := by
  show sumZ m (fun i => (a i * b m - a m * b i) * (a i * b m - a m * b i))
      = b m * b m * ssq a m + a m * a m * ssq b m
        - 2 * (a m * b m) * dot a b m
  rw [sumZ_congr m
        (fun i => (a i * b m - a m * b i) * (a i * b m - a m * b i))
        (fun i => b m * b m * (a i * a i) + a m * a m * (b i * b i)
                  + (- (2 * (a m * b m))) * (a i * b i))
        (fun i _ => cross_sq (a i) (b i) (a m) (b m))]
  rw [← sumZ_add_func m
        (fun i => b m * b m * (a i * a i) + a m * a m * (b i * b i))
        (fun i => (- (2 * (a m * b m))) * (a i * b i))]
  rw [← sumZ_add_func m
        (fun i => b m * b m * (a i * a i))
        (fun i => a m * a m * (b i * b i))]
  rw [← sumZ_mul_left (b m * b m) m (fun i => a i * a i)]
  rw [← sumZ_mul_left (a m * a m) m (fun i => b i * b i)]
  rw [← sumZ_mul_left (- (2 * (a m * b m))) m (fun i => a i * b i)]
  show b m * b m * ssq a m + a m * a m * ssq b m
       + (- (2 * (a m * b m))) * dot a b m
     = b m * b m * ssq a m + a m * a m * ssq b m
       - 2 * (a m * b m) * dot a b m
  generalize ssq a m = SA
  generalize ssq b m = SB
  generalize dot a b m = D
  generalize a m = am
  generalize b m = bm
  ring_intZ

/-! ## The induction step (pure algebra) -/

/-- `gap (n+1) = gap n + rowSq n`. -/
theorem gap_succ (a b : Nat → Int) (n : Nat) :
    gap a b (n + 1) = gap a b n + rowSq a b n := by
  rw [rowSq_expand a b n]
  show ssq a (n + 1) * ssq b (n + 1) - dot a b (n + 1) * dot a b (n + 1)
     = (ssq a n * ssq b n - dot a b n * dot a b n)
       + (b n * b n * ssq a n + a n * a n * ssq b n
          - 2 * (a n * b n) * dot a b n)
  show (ssq a n + a n * a n) * (ssq b n + b n * b n)
       - (dot a b n + a n * b n) * (dot a b n + a n * b n)
     = (ssq a n * ssq b n - dot a b n * dot a b n)
       + (b n * b n * ssq a n + a n * a n * ssq b n
          - 2 * (a n * b n) * dot a b n)
  generalize ssq a n = SA
  generalize ssq b n = SB
  generalize dot a b n = D
  generalize a n = an
  generalize b n = bn
  ring_intZ

/-! ## ★★ Lagrange identity (general `n`) -/

/-- ★★ **Lagrange identity** (general `n`, sequences over `Int`):
    `(Σ_{i<n} aᵢ²)(Σ_{i<n} bᵢ²) − (Σ_{i<n} aᵢbᵢ)²
      = Σ_{m<n} Σ_{i<m} (aᵢ·b_m − a_m·bᵢ)²`. -/
theorem lagrange_identity (a b : Nat → Int) (n : Nat) :
    gap a b n = triSq a b n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [gap_succ a b m, ih]
    show triSq a b m + rowSq a b m = triSq a b (m + 1)
    rfl

/-! ## ★★★ Cauchy–Schwarz (general `n`) -/

/-- A `sumZ` of squares is nonnegative: `0 ≤ Σ_{i<j} g i · g i`. -/
theorem sumZ_sq_nonneg (g : Nat → Int) : ∀ j, 0 ≤ sumZ j (fun i => g i * g i)
  | 0 => Order.le_refl 0
  | j + 1 => add_nonneg (sumZ_sq_nonneg g j) (int_sq_nonneg _)

/-- Each `rowSq` is a nonnegative sum of squares. -/
theorem rowSq_nonneg (a b : Nat → Int) (m : Nat) : 0 ≤ rowSq a b m :=
  sumZ_sq_nonneg (fun i => a i * b m - a m * b i) m

/-- `triSq ≥ 0` — a sum of nonnegative `rowSq` terms. -/
theorem triSq_nonneg (a b : Nat → Int) (n : Nat) : 0 ≤ triSq a b n := by
  show 0 ≤ sumZ n (fun m => rowSq a b m)
  induction n with
  | zero => exact Order.le_refl 0
  | succ k ih => exact add_nonneg ih (rowSq_nonneg a b k)

/-- ★★★ **Cauchy–Schwarz** (general `n`, sequences over `Int`):
    `(Σ_{i<n} aᵢbᵢ)² ≤ (Σ_{i<n} aᵢ²)(Σ_{i<n} bᵢ²)`.  Immediate from Lagrange. -/
theorem cauchy_schwarz (a b : Nat → Int) (n : Nat) :
    dot a b n * dot a b n ≤ ssq a n * ssq b n := by
  have hgap : 0 ≤ gap a b n := by
    rw [lagrange_identity a b n]; exact triSq_nonneg a b n
  exact Order.le_of_sub_nonneg (Order.nonneg_of_le_zero hgap)

end E213.Lib.Math.Foundations.CauchySchwarzGeneral
