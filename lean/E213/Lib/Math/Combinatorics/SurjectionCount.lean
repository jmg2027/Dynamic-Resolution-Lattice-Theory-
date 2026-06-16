import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.AlternatingBinomial
import E213.Lib.Math.Combinatorics.Permutations
import E213.Meta.Int213.PolyIntMTactic

/-!
# Surjection inclusion-exclusion sum (∅-axiom)

`surj m n := Σ_{k=0}^{n} (−1)^k · C(n,k) · (n−k)^m` = number of surjections [m]↠[n].

**Proven (general `n`, ∅-axiom — both must-have boundary identities)**:
  * `surj_zero_of_lt` — ★★★ **`surj m n = 0` for `m < n`**: the inclusion-
                        exclusion vanishing identity (the offset monomial
                        `(n−k)^m` has degree `m < n`, so its `n`-fold finite
                        difference is 0) — fewer cannot surject onto more.
  * `surj_diag`       — ★★★ **`surj n n = n!`**: the surjections [n]↠[n] are the
                        n! bijections.  Via the diagonal recurrence
                        `surj (n+1) (n+1) = (n+1)·surj n n` (`surj_diag_rec`).
  * `surj_base_col`   — ★ **`surj 0 0 = 1`, `surj (m+1) 0 = 0`** (`= [m = 0]`).

**Supporting machinery (all ∅-axiom)**:
  * `A_rec`           — the finite-difference recurrence `A (n+1) g = A n (Δg)`,
                        `Δg k = g k − g (k+1)`, via Pascal + reindexing (the
                        polynomial-weight alternating-sum machinery, built from
                        scratch; mirrors `alt_partial`).
  * `A_eq_diffIt`     — `A n g = (Δ^[n] g)(0)`.
  * `PolyLe` theory   — degree predicate closed under `+, −`, shift, `(s−k)·`;
                        `Δ^[d+1]` annihilates a degree-≤d function; `Δ^[n]` of a
                        degree-≤n function is constant (`diffIt_const`).
  * `choose_absorb`   — the absorption `(n+1−k)·C(n+1,k) = (n+1)·C(n,k)` (`k≤n`),
                        from `choose_succ_mul` + binomial symmetry.

The diagonal avoids needing the exact monomial top-difference (and the binomial
expansion the corpus lacks): the offset-shift invariance of the top difference
(`A_shift_eq`) plus the `choose` absorption close the `(n+1)·surj n n` recurrence
directly.  ∅-axiom throughout (no `funext`/`propext`/`Quot.sound`).
-/

namespace E213.Lib.Math.Combinatorics.SurjectionCount

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_zero_right choose_succ_succ choose_eq_zero_of_lt choose_self
   choose_succ_mul choose_symm_sum)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.AlternatingBinomial
  (sumZ sumZ_zero sumZ_succ powNegOne_succ)
open E213.Lib.Math.Combinatorics.Permutations (fact)
open E213.Meta.Int213.PolyIntM (powInt powInt_add one_mulZ mul_zeroZ)

/-- The weighted alternating sum `A n g = Σ_{k=0}^{n} (−1)^k C(n,k) g(k)` over `Int`. -/
def A (n : Nat) (g : Nat → Int) : Int :=
  sumZ (n + 1) (fun k => powInt (-1 : Int) k * (choose n k : Int) * g k)

/-- Backward difference `Δg k = g k − g (k+1)`. -/
def Δ (g : Nat → Int) : Nat → Int := fun k => g k - g (k + 1)

/-! ## `sumZ` helper lemmas (reproduced locally from `DerangementConvolution`) -/

/-- Split off the first term of an `Int` sum. -/
theorem sumZ_split_first : ∀ (n : Nat) (f : Nat → Int),
    sumZ (n + 1) f = f 0 + sumZ n (fun k => f (k + 1))
  | 0, f => by
      show (0 : Int) + f 0 = f 0 + 0
      rw [E213.Meta.Int213.zero_add, Int.add_zero]
  | n + 1, f => by
      show sumZ (n + 1) f + f (n + 1)
         = f 0 + (sumZ n (fun k => f (k + 1)) + f (n + 1))
      rw [sumZ_split_first n f, E213.Meta.Int213.add_assoc]

/-- `Int` sum distributes over pointwise add. -/
theorem sumZ_add_func : ∀ (n : Nat) (f g : Nat → Int),
    sumZ n f + sumZ n g = sumZ n (fun k => f k + g k)
  | 0, _, _ => by show (0 : Int) + 0 = 0; rw [Int.add_zero]
  | n + 1, f, g => by
      show (sumZ n f + f n) + (sumZ n g + g n)
         = sumZ n (fun k => f k + g k) + (f n + g n)
      rw [← sumZ_add_func n f g]
      rw [E213.Meta.Int213.add_assoc (sumZ n f) (f n) (sumZ n g + g n)]
      rw [← E213.Meta.Int213.add_assoc (f n) (sumZ n g) (g n)]
      rw [E213.Meta.Int213.add_comm (f n) (sumZ n g)]
      rw [E213.Meta.Int213.add_assoc (sumZ n g) (f n) (g n)]
      rw [← E213.Meta.Int213.add_assoc (sumZ n f) (sumZ n g) (f n + g n)]

/-- Factor a scalar out of an `Int` sum. -/
theorem sumZ_mul_left (a : Int) : ∀ (n : Nat) (f : Nat → Int),
    a * sumZ n f = sumZ n (fun k => a * f k)
  | 0, _ => by show a * 0 = (0 : Int); rw [mul_zeroZ]
  | n + 1, f => by
      show a * (sumZ n f + f n) = sumZ n (fun k => a * f k) + a * f n
      rw [E213.Meta.Int213.mul_add, sumZ_mul_left a n f]

/-- `Int`-sum congruence (no `funext`). -/
theorem sumZ_congr : ∀ (n : Nat) (f g : Nat → Int),
    (∀ k, k < n → f k = g k) → sumZ n f = sumZ n g
  | 0, _, _, _ => rfl
  | n + 1, f, g, h => by
      show sumZ n f + f n = sumZ n g + g n
      rw [sumZ_congr n f g (fun k hk => h k (Nat.lt_succ_of_lt hk))]
      rw [h n (Nat.lt_succ_self n)]

/-- The surjection inclusion-exclusion sum `Σ_{k=0}^{n} (−1)^k C(n,k) (n−k)^m`. -/
def surj (m n : Nat) : Int :=
  A n (fun k => powInt ((n : Int) - (k : Int)) m)

/-! ## The finite-difference recurrence `A (n+1) g = A n (Δ g)` -/

/-- A summand rewrite via Pascal + `(−1)^{k+1} = −(−1)^k`:
    `(−1)^{k+1} C(n+1,k+1) g(k+1)
      = (−1)^k C(n,k) (−g(k+1)) + (−1)^k C(n,k+1) (−g(k+1))`. -/
theorem arec_summand (n k : Nat) (g : Nat → Int) :
    powInt (-1 : Int) (k + 1) * (choose (n + 1) (k + 1) : Int) * g (k + 1)
      = powInt (-1 : Int) k * (choose n k : Int) * (- g (k + 1))
        + powInt (-1 : Int) k * (choose n (k + 1) : Int) * (- g (k + 1)) := by
  rw [choose_succ_succ n k,
      show ((choose n k + choose n (k + 1) : Nat) : Int)
        = (choose n k : Int) + (choose n (k + 1) : Int) from rfl,
      powNegOne_succ k]
  ring_intZ

/-- Key split: `Σ_{k=0}^{n} (−1)^k C(n,k) g k
    = g 0 − Σ_{k=0}^{n−1} (−1)^k C(n,k+1) g(k+1)`. -/
theorem S1_split (n : Nat) (g : Nat → Int) :
    sumZ (n + 1) (fun k => powInt (-1 : Int) k * (choose n k : Int) * g k)
      = g 0 - sumZ n (fun k => powInt (-1 : Int) k * (choose n (k + 1) : Int) * g (k + 1)) := by
  rw [sumZ_split_first n (fun k => powInt (-1 : Int) k * (choose n k : Int) * g k)]
  show powInt (-1 : Int) 0 * (choose n 0 : Int) * g 0
       + sumZ n (fun k => powInt (-1 : Int) (k + 1) * (choose n (k + 1) : Int) * g (k + 1))
     = g 0 - sumZ n (fun k => powInt (-1 : Int) k * (choose n (k + 1) : Int) * g (k + 1))
  rw [show powInt (-1 : Int) 0 = 1 from rfl, choose_zero_right,
      show ((1 : Nat) : Int) = (1 : Int) from rfl, one_mulZ, one_mulZ]
  rw [sumZ_congr n
        (fun k => powInt (-1 : Int) (k + 1) * (choose n (k + 1) : Int) * g (k + 1))
        (fun k => (-1 : Int) * (powInt (-1 : Int) k * (choose n (k + 1) : Int) * g (k + 1)))
        (fun k _ => by
          show powInt (-1 : Int) (k + 1) * (choose n (k + 1) : Int) * g (k + 1)
             = (-1 : Int) * (powInt (-1 : Int) k * (choose n (k + 1) : Int) * g (k + 1))
          rw [powNegOne_succ k]; ring_intZ)]
  rw [← sumZ_mul_left (-1 : Int) n
        (fun k => powInt (-1 : Int) k * (choose n (k + 1) : Int) * g (k + 1))]
  generalize sumZ n (fun k => powInt (-1 : Int) k * (choose n (k + 1) : Int) * g (k + 1)) = S
  ring_intZ

/-- ★★★ **Finite-difference recurrence** `A (n+1) g = A n (Δ g)`:
    `Σ_{k=0}^{n+1} (−1)^k C(n+1,k) g(k) = Σ_{k=0}^{n} (−1)^k C(n,k) (g k − g(k+1))`. -/
theorem A_rec (n : Nat) (g : Nat → Int) : A (n + 1) g = A n (Δ g) := by
  show sumZ (n + 2) (fun k => powInt (-1 : Int) k * (choose (n + 1) k : Int) * g k)
     = sumZ (n + 1) (fun k => powInt (-1 : Int) k * (choose n k : Int) * Δ g k)
  rw [sumZ_split_first (n + 1)
        (fun k => powInt (-1 : Int) k * (choose (n + 1) k : Int) * g k)]
  show powInt (-1 : Int) 0 * (choose (n + 1) 0 : Int) * g 0
       + sumZ (n + 1)
           (fun k => powInt (-1 : Int) (k + 1) * (choose (n + 1) (k + 1) : Int) * g (k + 1))
     = _
  rw [show powInt (-1 : Int) 0 = 1 from rfl, choose_zero_right,
      show ((1 : Nat) : Int) = (1 : Int) from rfl, one_mulZ, one_mulZ]
  rw [sumZ_congr (n + 1)
        (fun k => powInt (-1 : Int) (k + 1) * (choose (n + 1) (k + 1) : Int) * g (k + 1))
        (fun k => powInt (-1 : Int) k * (choose n k : Int) * (- g (k + 1))
                  + powInt (-1 : Int) k * (choose n (k + 1) : Int) * (- g (k + 1)))
        (fun k _ => arec_summand n k g)]
  rw [← sumZ_add_func (n + 1)
        (fun k => powInt (-1 : Int) k * (choose n k : Int) * (- g (k + 1)))
        (fun k => powInt (-1 : Int) k * (choose n (k + 1) : Int) * (- g (k + 1)))]
  have hdrop : sumZ (n + 1)
        (fun k => powInt (-1 : Int) k * (choose n (k + 1) : Int) * (- g (k + 1)))
      = sumZ n
        (fun k => powInt (-1 : Int) k * (choose n (k + 1) : Int) * (- g (k + 1))) := by
    rw [sumZ_succ n
          (fun k => powInt (-1 : Int) k * (choose n (k + 1) : Int) * (- g (k + 1)))]
    show sumZ n (fun k => powInt (-1 : Int) k * (choose n (k + 1) : Int) * (- g (k + 1)))
         + powInt (-1 : Int) n * (choose n (n + 1) : Int) * (- g (n + 1)) = _
    rw [choose_eq_zero_of_lt n (n + 1) (Nat.lt_succ_self n)]
    show _ + powInt (-1 : Int) n * ((0 : Nat) : Int) * (- g (n + 1)) = _
    rw [show ((0 : Nat) : Int) = 0 from rfl, mul_zeroZ,
        E213.Meta.Int213.zero_mul, Int.add_zero]
  rw [hdrop]
  rw [sumZ_congr (n + 1)
        (fun k => powInt (-1 : Int) k * (choose n k : Int) * Δ g k)
        (fun k => powInt (-1 : Int) k * (choose n k : Int) * g k
                  + powInt (-1 : Int) k * (choose n k : Int) * (- g (k + 1)))
        (fun k _ => by
          show powInt (-1 : Int) k * (choose n k : Int) * (g k - g (k + 1))
             = powInt (-1 : Int) k * (choose n k : Int) * g k
               + powInt (-1 : Int) k * (choose n k : Int) * (- g (k + 1))
          ring_intZ)]
  rw [← sumZ_add_func (n + 1)
        (fun k => powInt (-1 : Int) k * (choose n k : Int) * g k)
        (fun k => powInt (-1 : Int) k * (choose n k : Int) * (- g (k + 1)))]
  rw [S1_split n g]
  generalize hP : sumZ n (fun k => powInt (-1 : Int) k * (choose n (k + 1) : Int) * g (k + 1)) = P
  generalize hQ : sumZ (n + 1) (fun k => powInt (-1 : Int) k * (choose n k : Int) * (- g (k + 1))) = Q
  generalize hR : sumZ n (fun k => powInt (-1 : Int) k * (choose n (k + 1) : Int) * (- g (k + 1))) = R
  have hR1 : R = (-1 : Int) * P := by
    rw [← hR, ← hP, sumZ_mul_left (-1 : Int) n
          (fun k => powInt (-1 : Int) k * (choose n (k + 1) : Int) * g (k + 1))]
    apply sumZ_congr
    intro k _
    show powInt (-1 : Int) k * (choose n (k + 1) : Int) * (- g (k + 1))
       = (-1 : Int) * (powInt (-1 : Int) k * (choose n (k + 1) : Int) * g (k + 1))
    ring_intZ
  have hRP : R = - P := by rw [hR1]; ring_intZ
  rw [hRP]
  generalize g 0 = a
  ring_intZ

/-! ## Iterated difference and `A n g = Δ^[n] g (0)` -/

/-- `n`-fold backward difference. -/
def diffIt : Nat → (Nat → Int) → (Nat → Int)
  | 0,     g => g
  | n + 1, g => diffIt n (Δ g)

/-- `A 0 g = g 0`. -/
theorem A_zero (g : Nat → Int) : A 0 g = g 0 := by
  show sumZ 1 (fun k => powInt (-1 : Int) k * (choose 0 k : Int) * g k) = g 0
  show (0 : Int) + powInt (-1 : Int) 0 * (choose 0 0 : Int) * g 0 = g 0
  rw [show powInt (-1 : Int) 0 = 1 from rfl, show (choose 0 0 : Nat) = 1 from rfl,
      show ((1 : Nat) : Int) = (1 : Int) from rfl, one_mulZ, one_mulZ,
      E213.Meta.Int213.zero_add]

/-- ★ `A n g = (Δ^[n] g)(0)` — the alternating-binomial sum is the `n`-fold
    difference at 0.  Induction on `n` via `A_rec`. -/
theorem A_eq_diffIt : ∀ (n : Nat) (g : Nat → Int), A n g = diffIt n g 0
  | 0,     g => A_zero g
  | n + 1, g => by
      rw [A_rec n g]
      show A n (Δ g) = diffIt n (Δ g) 0
      exact A_eq_diffIt n (Δ g)

/-! ## Polynomial-degree predicate and finite-difference annihilation -/

/-- `PolyLe d g`: `g` behaves like a polynomial of degree ≤ `d` (its `d`-fold
    difference is constant — captured recursively via `Δ`). -/
def PolyLe : Nat → (Nat → Int) → Prop
  | 0,     g => ∀ k, g k = g 0
  | d + 1, g => PolyLe d (Δ g)

/-- `Δ` of a constant function is the zero function. -/
theorem Δ_const {g : Nat → Int} (h : ∀ k, g k = g 0) : ∀ k, Δ g k = 0 := by
  intro k
  show g k - g (k + 1) = 0
  rw [h k, h (k + 1)]
  exact E213.Meta.Int213.add_neg_cancel (g 0)

/-- Pointwise difference of pointwise-equal functions agrees (funext-free). -/
theorem Δ_congr {f g : Nat → Int} (h : ∀ k, f k = g k) : ∀ k, Δ f k = Δ g k := by
  intro k
  show f k - f (k + 1) = g k - g (k + 1)
  rw [h k, h (k + 1)]

/-- `PolyLe` respects pointwise equality (funext-free). -/
theorem PolyLe_congr : ∀ (d : Nat) {f g : Nat → Int},
    (∀ k, f k = g k) → PolyLe d f → PolyLe d g
  | 0, f, g, h, hf => by
      intro k
      show g k = g 0
      rw [← h k, ← h 0]; exact hf k
  | d + 1, f, g, h, hf => by
      show PolyLe d (Δ g)
      exact PolyLe_congr d (Δ_congr h) hf

/-- `PolyLe` is closed under (pointwise) subtraction. -/
theorem PolyLe_sub : ∀ (d : Nat) (f g : Nat → Int),
    PolyLe d f → PolyLe d g → PolyLe d (fun k => f k - g k)
  | 0, f, g, hf, hg => by
      intro k
      show f k - g k = f 0 - g 0
      rw [hf k, hg k]
  | d + 1, f, g, hf, hg => by
      show PolyLe d (Δ (fun k => f k - g k))
      refine PolyLe_congr d (f := fun k => Δ f k - Δ g k) ?_ (PolyLe_sub d (Δ f) (Δ g) hf hg)
      intro k
      show Δ f k - Δ g k = Δ (fun k => f k - g k) k
      show (f k - f (k + 1)) - (g k - g (k + 1))
         = (f k - g k) - (f (k + 1) - g (k + 1))
      ring_intZ

/-- `PolyLe` is closed under (pointwise) addition. -/
theorem PolyLe_add : ∀ (d : Nat) (f g : Nat → Int),
    PolyLe d f → PolyLe d g → PolyLe d (fun k => f k + g k)
  | 0, f, g, hf, hg => by
      intro k
      show f k + g k = f 0 + g 0
      rw [hf k, hg k]
  | d + 1, f, g, hf, hg => by
      show PolyLe d (Δ (fun k => f k + g k))
      refine PolyLe_congr d (f := fun k => Δ f k + Δ g k) ?_ (PolyLe_add d (Δ f) (Δ g) hf hg)
      intro k
      show (f k - f (k + 1)) + (g k - g (k + 1))
         = (f k + g k) - (f (k + 1) + g (k + 1))
      ring_intZ

/-- `PolyLe` is closed under the shift `g ↦ g ∘ succ`. -/
theorem PolyLe_shift : ∀ (d : Nat) (g : Nat → Int),
    PolyLe d g → PolyLe d (fun k => g (k + 1))
  | 0, g, hg => by
      intro k
      show g (k + 1) = g (0 + 1)
      rw [hg (k + 1), hg (0 + 1)]
  | d + 1, g, hg => by
      show PolyLe d (Δ (fun k => g (k + 1)))
      refine PolyLe_congr d (f := fun k => (Δ g) (k + 1)) ?_ (PolyLe_shift d (Δ g) hg)
      intro k; rfl

/-- Multiplying by `k` raises the degree bound by one:
    `PolyLe d g → PolyLe (d+1) (fun k => k · g k)`. -/
theorem PolyLe_mul_k : ∀ (d : Nat) (g : Nat → Int),
    PolyLe d g → PolyLe (d + 1) (fun k => (k : Int) * g k)
  | 0, g, hg => by
      -- g constant ⇒ Δ(k·g) k = -g 0 (constant)
      show PolyLe 0 (Δ (fun k => (k : Int) * g k))
      intro k
      show (k : Int) * g k - ((k : Int) + 1) * g (k + 1)
         = (0 : Int) * g 0 - ((0 : Int) + 1) * g (0 + 1)
      rw [hg k, hg (k + 1), hg 0, hg (0 + 1)]
      ring_intZ
  | d + 1, g, hg => by
      show PolyLe (d + 1) (Δ (fun k => (k : Int) * g k))
      have h1 : PolyLe (d + 1) (fun k => (k : Int) * (Δ g) k) :=
        PolyLe_mul_k d (Δ g) hg
      have h2 : PolyLe (d + 1) (fun k => g (k + 1)) :=
        PolyLe_shift (d + 1) g hg
      refine PolyLe_congr (d + 1)
        (f := fun (k : Nat) => (k : Int) * (Δ g) k - g (k + 1)) ?_
        (PolyLe_sub (d + 1) _ _ h1 h2)
      intro k
      show (k : Int) * (g k - g (k + 1)) - g (k + 1)
         = (k : Int) * g k - ((k : Int) + 1) * g (k + 1)
      ring_intZ

/-- Multiplying by an affine `(s − k)` raises the degree bound by one:
    `PolyLe d g → PolyLe (d+1) (fun k => (s − k)·g k)`. -/
theorem PolyLe_mul_affine (s : Int) : ∀ (d : Nat) (g : Nat → Int),
    PolyLe d g → PolyLe (d + 1) (fun (k : Nat) => (s - (k : Int)) * g k)
  | 0, g, hg => by
      show PolyLe 0 (Δ (fun (k : Nat) => (s - (k : Int)) * g k))
      intro k
      show (s - (k : Int)) * g k - (s - ((k : Int) + 1)) * g (k + 1)
         = (s - ((0 : Nat) : Int)) * g 0 - (s - (((0 : Nat) : Int) + 1)) * g (0 + 1)
      rw [hg k, hg (k + 1), hg 0, hg (0 + 1)]
      show (s - (k : Int)) * g 0 - (s - ((k : Int) + 1)) * g 0
         = (s - ((0 : Nat) : Int)) * g 0 - (s - (((0 : Nat) : Int) + 1)) * g 0
      rw [show (((0 : Nat) : Int)) = (0 : Int) from rfl]
      ring_intZ
  | d + 1, g, hg => by
      show PolyLe (d + 1) (Δ (fun (k : Nat) => (s - (k : Int)) * g k))
      have h1 : PolyLe (d + 1) (fun (k : Nat) => (s - (k : Int)) * (Δ g) k) :=
        PolyLe_mul_affine s d (Δ g) hg
      have h2 : PolyLe (d + 1) (fun (k : Nat) => g (k + 1)) :=
        PolyLe_shift (d + 1) g hg
      refine PolyLe_congr (d + 1)
        (f := fun (k : Nat) => (s - (k : Int)) * (Δ g) k + g (k + 1)) ?_
        (PolyLe_add (d + 1) _ _ h1 h2)
      intro k
      show (s - (k : Int)) * (g k - g (k + 1)) + g (k + 1)
         = (s - (k : Int)) * g k - (s - ((k : Int) + 1)) * g (k + 1)
      ring_intZ

/-- The offset monomial `fun k => (s − k)^m` has degree ≤ `m`. -/
theorem PolyLe_offset (s : Int) : ∀ m, PolyLe m (fun (k : Nat) => powInt (s - (k : Int)) m)
  | 0 => by intro k; rfl
  | m + 1 => by
      refine PolyLe_congr (m + 1)
        (f := fun (k : Nat) => (s - (k : Int)) * powInt (s - (k : Int)) m) ?_
        (PolyLe_mul_affine s m (fun (k : Nat) => powInt (s - (k : Int)) m)
          (PolyLe_offset s m))
      intro k
      show (s - (k : Int)) * powInt (s - (k : Int)) m
         = powInt (s - (k : Int)) (m + 1)
      show (s - (k : Int)) * powInt (s - (k : Int)) m
         = powInt (s - (k : Int)) m * (s - (k : Int))
      exact E213.Meta.Int213.mul_comm _ _

/-- A `PolyLe d` function's `(d+1)`-fold difference is pointwise zero. -/
theorem diffIt_polyLe_zero : ∀ (d : Nat) (g : Nat → Int),
    PolyLe d g → ∀ k, diffIt (d + 1) g k = 0
  | 0, g, hg, k => by
      show Δ g k = 0
      exact Δ_const hg k
  | d + 1, g, hg, k => by
      show diffIt (d + 1) (Δ g) k = 0
      exact diffIt_polyLe_zero d (Δ g) hg k

/-- `diffIt` peels one difference from the outside (pointwise):
    `diffIt (n+1) g k = Δ (diffIt n g) k`. -/
theorem diffIt_outer : ∀ (n : Nat) (g : Nat → Int) (k : Nat),
    diffIt (n + 1) g k = Δ (diffIt n g) k
  | 0, g, k => rfl
  | n + 1, g, k => by
      show diffIt (n + 1) (Δ g) k = Δ (diffIt n (Δ g)) k
      exact diffIt_outer n (Δ g) k

/-- Once a difference-iterate is pointwise zero, more iterates stay pointwise zero. -/
theorem diffIt_stays_zero (t : Nat) (g : Nat → Int)
    (ht : ∀ k, diffIt t g k = 0) :
    ∀ (j : Nat) (k : Nat), diffIt (t + j) g k = 0
  | 0,     k => ht k
  | j + 1, k => by
      have hstep : diffIt (t + (j + 1)) g k = Δ (diffIt (t + j) g) k := by
        show diffIt ((t + j) + 1) g k = Δ (diffIt (t + j) g) k
        exact diffIt_outer (t + j) g k
      rw [hstep]
      show diffIt (t + j) g k - diffIt (t + j) g (k + 1) = 0
      rw [diffIt_stays_zero t g ht j k, diffIt_stays_zero t g ht j (k + 1)]
      exact E213.Meta.Int213.add_neg_cancel 0

/-- ★★ **Vanishing**: if `g` is `PolyLe m` and `m < n`, then `A n g = 0`. -/
theorem A_polyLe_zero (m n : Nat) (g : Nat → Int) (hp : PolyLe m g) (hmn : m < n) :
    A n g = 0 := by
  rw [A_eq_diffIt n g]
  obtain ⟨j, hj⟩ : ∃ j, n = (m + 1) + j := ⟨n - (m + 1), by
    have hle : m + 1 ≤ n := hmn
    exact (E213.Tactic.NatHelper.add_sub_of_le hle).symm⟩
  rw [hj]
  exact diffIt_stays_zero (m + 1) g (fun k => diffIt_polyLe_zero m g hp k) j 0

/-! ## Diagonal `surj n n = n!` -/

/-- `a − b = 0 → b = a` over `Int` (∅-axiom). -/
theorem int_eq_of_sub_zero {a b : Int} (h : a - b = 0) : b = a := by
  have h1 : a + (- b) = 0 := h
  have h2 : (a + (- b)) + b = 0 + b := by rw [h1]
  rw [E213.Meta.Int213.add_assoc a (- b) b,
      E213.Meta.Int213.add_left_neg b, Int.add_zero,
      E213.Meta.Int213.zero_add] at h2
  exact h2.symm

/-- Pointwise congruence for `diffIt` (funext-free). -/
theorem diffIt_congr : ∀ (n : Nat) (f g : Nat → Int),
    (∀ k, f k = g k) → ∀ k, diffIt n f k = diffIt n g k
  | 0, f, g, h, k => h k
  | n + 1, f, g, h, k => by
      show diffIt n (Δ f) k = diffIt n (Δ g) k
      exact diffIt_congr n (Δ f) (Δ g) (Δ_congr h) k

/-- `diffIt` commutes with the argument-shift `succ`:
    `diffIt n (g ∘ succ) k = diffIt n g (k+1)`. -/
theorem diffIt_shift : ∀ (n : Nat) (g : Nat → Int) (k : Nat),
    diffIt n (fun j => g (j + 1)) k = diffIt n g (k + 1)
  | 0, g, k => rfl
  | n + 1, g, k => by
      show diffIt n (Δ (fun j => g (j + 1))) k = diffIt n (Δ g) (k + 1)
      -- Δ (g∘succ) = (Δ g)∘succ pointwise; bridge by diffIt_congr
      have hc : ∀ j, (Δ (fun j => g (j + 1))) j = (fun j => (Δ g) (j + 1)) j := by
        intro j; rfl
      rw [diffIt_congr n (Δ (fun j => g (j + 1))) (fun j => (Δ g) (j + 1)) hc k]
      exact diffIt_shift n (Δ g) k

/-- A `PolyLe n` function's `n`-fold difference is constant:
    `diffIt n g k = diffIt n g 0`. -/
theorem diffIt_const {n : Nat} {g : Nat → Int} (hp : PolyLe n g) :
    ∀ k, diffIt n g k = diffIt n g 0 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      -- diffIt n g (k+1) = diffIt n g k − Δ(diffIt n g) k = diffIt n g k − diffIt(n+1) g k
      have hΔ0 : diffIt (n + 1) g k = 0 := diffIt_polyLe_zero n g hp k
      have hstep : diffIt n g k - diffIt n g (k + 1) = 0 := by
        have := diffIt_outer n g k
        show diffIt n g k - diffIt n g (k + 1) = 0
        rw [show diffIt n g k - diffIt n g (k + 1) = Δ (diffIt n g) k from rfl,
            ← this]; exact hΔ0
      -- so diffIt n g (k+1) = diffIt n g k = diffIt n g 0
      have heq : diffIt n g (k + 1) = diffIt n g k := int_eq_of_sub_zero hstep
      rw [heq, ih]

/-- `A` respects pointwise equality (funext-free). -/
theorem A_congr (n : Nat) (f g : Nat → Int) (h : ∀ k, f k = g k) : A n f = A n g := by
  show sumZ (n + 1) (fun k => powInt (-1 : Int) k * (choose n k : Int) * f k)
     = sumZ (n + 1) (fun k => powInt (-1 : Int) k * (choose n k : Int) * g k)
  apply sumZ_congr
  intro k _
  show powInt (-1 : Int) k * (choose n k : Int) * f k
     = powInt (-1 : Int) k * (choose n k : Int) * g k
  rw [h k]

/-- `A n` agrees on a function and its argument-shift when the function is
    `PolyLe n`: `A n (fun k => g (k+1)) = A n g`. -/
theorem A_shift_eq {n : Nat} {g : Nat → Int} (hp : PolyLe n g) :
    A n (fun k => g (k + 1)) = A n g := by
  rw [A_eq_diffIt n (fun k => g (k + 1)), A_eq_diffIt n g]
  rw [diffIt_shift n g 0]
  exact diffIt_const hp 1

/-- **Key absorption (Nat)**: `(n+1−k)·C(n+1,k) = (n+1)·C(n,k)` for `k ≤ n`.
    Via `choose_succ_mul` + binomial symmetry. -/
theorem choose_absorb (n k : Nat) (hk : k ≤ n) :
    ((n + 1) - k) * choose (n + 1) k = (n + 1) * choose n k := by
  -- choose (n+1) k = choose (n+1) (n+1-k); with j = n-k, (j+1) = n+1-k
  have hsymm1 : choose (n + 1) k = choose (n + 1) ((n + 1) - k) :=
    choose_symm_sum (n + 1) k ((n + 1) - k) (E213.Tactic.NatHelper.add_sub_of_le
      (Nat.le_succ_of_le hk))
  have hjk : (n - k) + 1 = (n + 1) - k :=
    (E213.Meta.Nat.NatRing213.nat_succ_sub hk).symm
  have hcsm : ((n - k) + 1) * choose (n + 1) ((n - k) + 1) = (n + 1) * choose n (n - k) :=
    choose_succ_mul n (n - k)
  have hsymm2 : choose n (n - k) = choose n k :=
    choose_symm_sum n (n - k) k (by
      rw [Nat.add_comm]; exact E213.Tactic.NatHelper.add_sub_of_le hk)
  rw [hsymm1, ← hjk, hcsm, hsymm2]

/-- `x + b = a → x = a − b` over `Int` (∅-axiom). -/
theorem int_eq_sub_of_add_eq {x a b : Int} (h : x + b = a) : x = a - b := by
  rw [Int.sub_eq_add_neg]
  have h2 : (x + b) + (- b) = a + (- b) := by rw [h]
  rw [E213.Meta.Int213.add_assoc, E213.Meta.Int213.add_neg_cancel, Int.add_zero] at h2
  exact h2

/-- Cast of a Nat subtraction (`b ≤ a`): `((a−b:Nat):Int) = (a:Int) − (b:Int)`. -/
theorem ofNat_sub_cast {a b : Nat} (h : b ≤ a) :
    (((a - b : Nat)) : Int) = (a : Int) - (b : Int) := by
  apply int_eq_sub_of_add_eq
  rw [show (((a - b : Nat)) : Int) + (b : Int) = (((a - b) + b : Nat) : Int) from rfl,
      E213.Tactic.NatHelper.sub_add_cancel h]

/-- Int cast of the absorption: `((n+1:Int)−k)·C(n+1,k) = (n+1)·C(n,k)` for `k ≤ n`. -/
theorem choose_absorb_int (n k : Nat) (hk : k ≤ n) :
    (((n : Int) + 1) - (k : Int)) * (choose (n + 1) k : Int)
      = ((n : Int) + 1) * (choose n k : Int) := by
  have hN := choose_absorb n k hk
  have hcast : ((((n + 1) - k) * choose (n + 1) k : Nat) : Int)
             = (((n + 1) * choose n k : Nat) : Int) := by rw [hN]
  rw [show ((((n + 1) - k) * choose (n + 1) k : Nat) : Int)
        = (((n + 1) - k : Nat) : Int) * (choose (n + 1) k : Int) from rfl,
      show ((((n + 1) * choose n k : Nat)) : Int)
        = (((n + 1 : Nat)) : Int) * (choose n k : Int) from rfl] at hcast
  rw [ofNat_sub_cast (Nat.le_succ_of_le hk),
      show (((n + 1 : Nat)) : Int) = (n : Int) + 1 from rfl] at hcast
  exact hcast

/-- `0^(n+1) = 0` over `Int`. -/
theorem powInt_zero_succ (n : Nat) : powInt (0 : Int) (n + 1) = 0 := by
  show powInt (0 : Int) n * 0 = 0
  exact mul_zeroZ _

/-- ★★ **Diagonal recurrence** `surj (n+1) (n+1) = (n+1) · surj n n`.
    Absorption `(n+1−k)·C(n+1,k) = (n+1)·C(n,k)` + the offset-shift
    `A n (·^n at offset n+1) = A n (·^n at offset n)`. -/
theorem surj_diag_rec (n : Nat) :
    surj (n + 1) (n + 1) = ((n : Int) + 1) * surj n n := by
  show A (n + 1) (fun k => powInt (((n : Int) + 1) - (k : Int)) (n + 1))
     = ((n : Int) + 1) * surj n n
  show sumZ (n + 2)
        (fun k => powInt (-1 : Int) k * (choose (n + 1) k : Int)
                  * powInt (((n : Int) + 1) - (k : Int)) (n + 1))
     = ((n : Int) + 1) * surj n n
  rw [sumZ_succ (n + 1)
        (fun k => powInt (-1 : Int) k * (choose (n + 1) k : Int)
                  * powInt (((n : Int) + 1) - (k : Int)) (n + 1))]
  have htop : powInt (-1 : Int) (n + 1) * (choose (n + 1) (n + 1) : Int)
              * powInt (((n : Int) + 1) - ((n + 1 : Nat) : Int)) (n + 1) = 0 := by
    rw [show (((n : Int) + 1) - ((n + 1 : Nat) : Int)) = 0 from by
          rw [show ((n + 1 : Nat) : Int) = (n : Int) + 1 from rfl]
          exact E213.Meta.Int213.add_neg_cancel ((n : Int) + 1),
        powInt_zero_succ n, mul_zeroZ]
  rw [htop, Int.add_zero]
  rw [sumZ_congr (n + 1)
        (fun k => powInt (-1 : Int) k * (choose (n + 1) k : Int)
                  * powInt (((n : Int) + 1) - (k : Int)) (n + 1))
        (fun k => ((n : Int) + 1)
                  * (powInt (-1 : Int) k * (choose n k : Int)
                     * powInt (((n : Int) + 1) - (k : Int)) n))
        (fun k hk => by
          have hkn : k ≤ n := Nat.le_of_lt_succ hk
          show powInt (-1 : Int) k * (choose (n + 1) k : Int)
               * powInt (((n : Int) + 1) - (k : Int)) (n + 1)
             = ((n : Int) + 1)
               * (powInt (-1 : Int) k * (choose n k : Int)
                  * powInt (((n : Int) + 1) - (k : Int)) n)
          have hpow : powInt (((n : Int) + 1) - (k : Int)) (n + 1)
                    = powInt (((n : Int) + 1) - (k : Int)) n
                      * (((n : Int) + 1) - (k : Int)) := rfl
          rw [hpow]
          have habs := choose_absorb_int n k hkn
          rw [show powInt (-1 : Int) k * (choose (n + 1) k : Int)
                   * (powInt (((n : Int) + 1) - (k : Int)) n
                      * (((n : Int) + 1) - (k : Int)))
                 = powInt (-1 : Int) k
                   * ((((n : Int) + 1) - (k : Int)) * (choose (n + 1) k : Int))
                   * powInt (((n : Int) + 1) - (k : Int)) n from by ring_intZ]
          rw [habs]
          show powInt (-1 : Int) k * (((n : Int) + 1) * (choose n k : Int))
                * powInt (((n : Int) + 1) - (k : Int)) n
             = ((n : Int) + 1)
               * (powInt (-1 : Int) k * (choose n k : Int)
                  * powInt (((n : Int) + 1) - (k : Int)) n)
          ring_intZ)]
  rw [← sumZ_mul_left ((n : Int) + 1) (n + 1)
        (fun k => powInt (-1 : Int) k * (choose n k : Int)
                  * powInt (((n : Int) + 1) - (k : Int)) n)]
  -- inner sum = A n (offset-(n+1) monomial) = surj n n
  have hAshift : sumZ (n + 1)
        (fun k => powInt (-1 : Int) k * (choose n k : Int)
                  * powInt (((n : Int) + 1) - (k : Int)) n)
      = surj n n := by
    show A n (fun k => powInt (((n : Int) + 1) - (k : Int)) n) = surj n n
    have hp : PolyLe n (fun k => powInt (((n : Int) + 1) - (k : Int)) n) :=
      PolyLe_offset ((n : Int) + 1) n
    have hsh : A n (fun k => powInt (((n : Int) + 1) - ((k + 1 : Nat) : Int)) n)
             = A n (fun k => powInt (((n : Int) + 1) - (k : Int)) n) :=
      A_shift_eq hp
    -- A n (offset n+1 body at k+1) = A n (surj body) by pointwise congr
    have hcong : A n (fun k => powInt (((n : Int) + 1) - ((k + 1 : Nat) : Int)) n)
               = A n (fun k => powInt ((n : Int) - (k : Int)) n) :=
      A_congr n _ _ (fun k => by
        rw [show (((n : Int) + 1) - ((k + 1 : Nat) : Int)) = (n : Int) - (k : Int) from by
              rw [show ((k + 1 : Nat) : Int) = (k : Int) + 1 from rfl]; ring_intZ])
    -- combine: surj n n = A n (surj body) = A n (offset n+1 body @k+1) = A n (offset n+1)
    show A n (fun k => powInt (((n : Int) + 1) - (k : Int)) n) = surj n n
    rw [← hsh, hcong]
    rfl
  rw [hAshift]

/-- ★★★ **Diagonal boundary identity** `surj n n = n!`:
    `Σ_{k=0}^{n} (−1)^k C(n,k) (n−k)^n = n!` — the surjections [n]↠[n] are the
    n! bijections.  By induction via `surj_diag_rec`. -/
theorem surj_diag : ∀ n, surj n n = (fact n : Int)
  | 0     => by decide
  | n + 1 => by
      rw [surj_diag_rec n, surj_diag n]
      show ((n : Int) + 1) * (fact n : Int) = (fact (n + 1) : Int)
      rw [show (fact (n + 1) : Int) = (((n + 1) * fact n : Nat)) from rfl,
          show ((((n + 1) * fact n : Nat))) = (((n + 1 : Nat)) : Int) * (fact n : Int) from rfl,
          show (((n + 1 : Nat)) : Int) = (n : Int) + 1 from rfl]

/-! ## Boundary identity: `surj m n = 0` for `m < n` -/

/-- ★★★ **Vanishing boundary identity** `surj m n = 0` for `m < n`:
    `Σ_{k=0}^{n} (−1)^k C(n,k) (n−k)^m = 0` — there is no surjection from
    fewer elements onto more.  The genuine inclusion-exclusion content. -/
theorem surj_zero_of_lt {m n : Nat} (hmn : m < n) : surj m n = 0 := by
  show A n (fun k => powInt ((n : Int) - (k : Int)) m) = 0
  exact A_polyLe_zero m n (fun k => powInt ((n : Int) - (k : Int)) m)
    (PolyLe_offset (n : Int) m) hmn

/-- ★ **Base column** `surj (m+1) 0 = 0` and `surj 0 0 = 1` (= `[m = 0]`). -/
theorem surj_base_col : surj 0 0 = 1 ∧ ∀ m, surj (m + 1) 0 = 0 := by
  refine ⟨by decide, ?_⟩
  intro m
  show A 0 (fun k => powInt ((0 : Int) - (k : Int)) (m + 1)) = 0
  rw [A_zero (fun k => powInt ((0 : Int) - (k : Int)) (m + 1))]
  show powInt ((0 : Int) - ((0 : Nat) : Int)) (m + 1) = 0
  rw [show ((0 : Int) - ((0 : Nat) : Int)) = 0 from by
        rw [show ((0 : Nat) : Int) = (0 : Int) from rfl]
        exact E213.Meta.Int213.add_neg_cancel 0]
  exact powInt_zero_succ m

/-! ## Smoke tests (closed numeric `decide`) -/

/-- `surj 3 2 = 6`: surjections [3]↠[2] are 2³−2 = 6. -/
theorem surj_smoke_32 : surj 3 2 = 6 := by decide
/-- `surj 2 3 = 0`: no surjection [2]↠[3] (fewer onto more). -/
theorem surj_smoke_23 : surj 2 3 = 0 := by decide
/-- `surj 2 2 = 2!` and `surj 3 3 = 3!`: bijections. -/
theorem surj_smoke_diag : surj 2 2 = 2 ∧ surj 3 3 = 6 := by decide
/-- `surj 0 0 = 1`, `surj 1 0 = 0`: base column `[m = 0]`. -/
theorem surj_smoke_col0 : surj 0 0 = 1 ∧ surj 1 0 = 0 := by decide
/-- `surj 4 3 = 36`: surjections [4]↠[3]. -/
theorem surj_smoke_43 : surj 4 3 = 36 := by decide

end E213.Lib.Math.Combinatorics.SurjectionCount
