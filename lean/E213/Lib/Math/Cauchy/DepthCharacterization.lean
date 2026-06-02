import E213.Lib.Math.Cauchy.NewtonGregory
import E213.Lib.Math.Cauchy.FiniteDepthAlgebra
import E213.Lib.Math.Cauchy.PolynomialDepth

/-!
# DepthCharacterization — finite divergence depth ⟺ polynomial (the iff, over ℤ)

The capstone of the divergence-depth thread.  Two halves existed separately:

  * **⟹** `NewtonGregory.reconstruct`: `polyDepthZ d s ⟹ s n = Σ_{j≤d} C(n,j)·(Δʲs 0)`
    (a degree-`d` polynomial in the binomial / Newton basis);
  * **⟸** `PolynomialDepth.polyDepthZ_polySeq`: a degree-`d` *monomial* polynomial has depth
    `d` — but in the monomial basis, not the Newton basis `reconstruct` produces.

This file supplies the missing Newton-basis ⟸ and closes the loop into a single
**equivalence**.  The key new lemma is the **ℤ binomial-column depth**

  > `polyDepthZ_binomColZ` : `polyDepthZ k (fun n => (C(n,k) : ℤ))`

— each Newton column `C(·,k)` has divergence-depth exactly its index, because the ℤ forward
difference lowers the column by one (`diffZ_binomColZ`, the ℤ lift of Pascal's rule
`C(n+1,k+1) = C(n,k) + C(n,k+1)`).  Summing the columns (the finite-depth ring
`polyDepthZ_{add,smul}` + `polyDepthZ_mono`) gives `polyDepthZ d (newtonZ c d)` for any `c`;
combined with `reconstruct`:

  > ★★★ `finite_depthZ_iff` : `polyDepthZ d s ↔ ∃ c, ∀ n, s n = newtonZ c d n`
  > — **finite divergence depth = being a polynomial of degree ≤ d**, ∅-axiom over ℤ.

All zero-axiom.
-/

namespace E213.Lib.Math.Cauchy.DepthCharacterization

open E213.Lib.Math.Cauchy.NewtonGregory
  (diffZ liftKZ isConstZ polyDepthZ bsum newtonZ reconstruct bsum_pascal_aux)
open E213.Lib.Math.Cauchy.DepthPRecursiveInstances (binom binom_zero_right)
open E213.Lib.Math.Cauchy.FiniteDepthAlgebra
  (polyDepthZ_add polyDepthZ_smul liftKZ_diffZ_comm liftKZ_congrZ
   polyDepthZ_iff_vanish vanishZ)
open E213.Lib.Math.Cauchy.PolynomialDepth (polyDepthZ_mono)
open E213.Meta.Int213 (add_comm add_assoc add_neg_cancel zero_add mul_comm mul_one)

/-! ## §0 — small PURE Int + depth-transfer helpers -/

theorem add_zeroZ (a : Int) : a + 0 = a := (add_comm a 0).trans (zero_add a)

theorem add_sub_cancel_rightZ (a b : Int) : a + b - b = a := by
  show a + b + (-b) = a
  rw [add_assoc a b (-b), add_neg_cancel b, add_zeroZ a]

/-- `polyDepthZ` respects pointwise equality. -/
theorem polyDepthZ_congrZ {d : Nat} {u v : Nat → Int} (h : ∀ m, u m = v m)
    (hv : polyDepthZ d v) : polyDepthZ d u := by
  intro n
  rw [liftKZ_congrZ h d n, liftKZ_congrZ h d 0]
  exact hv n

/-- A difference drops the depth by one: `polyDepthZ k (Δs) → polyDepthZ (k+1) s`. -/
theorem polyDepthZ_succ_of_diff {k : Nat} {s : Nat → Int} (h : polyDepthZ k (diffZ s)) :
    polyDepthZ (k + 1) s := by
  intro n
  rw [← liftKZ_diffZ_comm s k n, ← liftKZ_diffZ_comm s k 0]
  exact h n

/-! ## §1 — the ℤ binomial columns have depth = index -/

/-- The `k`-th Newton column as a `ℤ`-sequence: `n ↦ C(n,k)`. -/
def binomColZ (k : Nat) : Nat → Int := fun n => Int.ofNat (binom n k)

/-- ★ **Pascal's rule as a ℤ forward difference**: `Δ C(·,k+1) = C(·,k)` — the column drops
    by one index, with no truncation (the `ℤ` lift of `binomCol_diff`). -/
theorem diffZ_binomColZ (k n : Nat) : diffZ (binomColZ (k + 1)) n = binomColZ k n := by
  show Int.ofNat (binom n k + binom n (k + 1)) - Int.ofNat (binom n (k + 1)) = Int.ofNat (binom n k)
  rw [show Int.ofNat (binom n k + binom n (k + 1))
        = Int.ofNat (binom n k) + Int.ofNat (binom n (k + 1)) from rfl]
  exact add_sub_cancel_rightZ (Int.ofNat (binom n k)) (Int.ofNat (binom n (k + 1)))

/-- ★★ **The `k`-th binomial column has divergence-depth `k`.** -/
theorem polyDepthZ_binomColZ : ∀ k, polyDepthZ k (binomColZ k)
  | 0     => by
      intro n
      show Int.ofNat (binom n 0) = Int.ofNat (binom 0 0)
      rw [binom_zero_right n, binom_zero_right 0]
  | k + 1 =>
      polyDepthZ_succ_of_diff
        (polyDepthZ_congrZ (fun n => diffZ_binomColZ k n) (polyDepthZ_binomColZ k))

/-! ## §2 — Newton-form polynomials have depth `d` (the ⟸ direction) -/

/-- ★★ **A Newton-basis polynomial `n ↦ Σ_{j≤d} C(n,j)·cⱼ` has divergence-depth `d`.**
    Columns of depth `j ≤ d` (`polyDepthZ_binomColZ` + `polyDepthZ_mono`), scaled
    (`polyDepthZ_smul`) and summed (`polyDepthZ_add`). -/
theorem polyDepthZ_newtonZ (c : Nat → Int) : ∀ d, polyDepthZ d (fun n => bsum n c d)
  | 0     => by
      intro n
      show (Int.ofNat (binom n 0)) * c 0 = (Int.ofNat (binom 0 0)) * c 0
      rw [binom_zero_right n, binom_zero_right 0]
  | d + 1 =>
      polyDepthZ_add
        (polyDepthZ_mono (Nat.le_succ d) (polyDepthZ_newtonZ c d))
        (polyDepthZ_congrZ (fun n => mul_comm (binomColZ (d + 1) n) (c (d + 1)))
          (polyDepthZ_smul (c (d + 1)) (polyDepthZ_binomColZ (d + 1))))

/-! ## §3 — the equivalence -/

/-- ★★★ **Finite divergence depth ⟺ polynomial (degree ≤ `d`), over ℤ.**
    `polyDepthZ d s ↔ ∃ c, ∀ n, s n = newtonZ c d n` — a sequence has faithful finite
    divergence depth `d` *iff* it is a degree-`≤d` polynomial (in the Newton/binomial basis).
    ⟹ is `reconstruct` (Newton coefficients `cⱼ = Δʲs 0`); ⟸ is `polyDepthZ_newtonZ`.  The
    complete ∅-axiom characterization closing the depth thread (`DivergenceDepth` … this
    file). -/
theorem finite_depthZ_iff {d : Nat} {s : Nat → Int} :
    polyDepthZ d s ↔ ∃ c : Nat → Int, ∀ n, s n = newtonZ c d n := by
  constructor
  · intro h
    exact ⟨fun i => liftKZ i s 0, fun n => reconstruct h n⟩
  · rintro ⟨c, hc⟩
    exact polyDepthZ_congrZ hc (polyDepthZ_newtonZ c d)

/-! ## §4 — exactness: depth is **exactly** the degree (top Newton coefficient ≠ 0) -/

theorem add_sub_cancel_leftZ (a b : Int) : a + b - a = b := by
  show a + b + (-a) = b
  rw [add_comm a b, add_assoc b a (-a), add_neg_cancel a, add_zeroZ b]

/-- The forward difference of a degree-`(d+1)` Newton form is the degree-`d` Newton form with
    the coefficients shifted up by one — `Δ (Σ_{j≤d+1} C(·,j)cⱼ) = Σ_{j≤d} C(·,j)c_{j+1}` —
    the ℤ `diff_newton`, from `bsum_pascal_aux`. -/
theorem diffZ_newtonZ (c : Nat → Int) (d n : Nat) :
    diffZ (fun m => bsum m c (d + 1)) n = bsum n (fun j => c (j + 1)) d := by
  show bsum (n + 1) c (d + 1) - bsum n c (d + 1) = bsum n (fun j => c (j + 1)) d
  rw [bsum_pascal_aux n c d]
  exact add_sub_cancel_leftZ (bsum n c (d + 1)) (bsum n (fun j => c (j + 1)) d)

/-- ★★ **The `d`-th difference of a degree-`d` Newton form is its top coefficient**:
    `Δ^d (Σ_{j≤d} C(·,j)cⱼ) = c_d` (constant).  Iterate `diffZ_newtonZ`. -/
theorem liftKZ_newtonZ_const (c : Nat → Int) : ∀ d n, liftKZ d (fun m => bsum m c d) n = c d
  | 0,     n => by
      show Int.ofNat (binom n 0) * c 0 = c 0
      rw [binom_zero_right n]
      exact (mul_comm 1 (c 0)).trans (mul_one (c 0))
  | d + 1, n => by
      rw [← liftKZ_diffZ_comm (fun m => bsum m c (d + 1)) d n,
          liftKZ_congrZ (fun m => diffZ_newtonZ c d m) d n]
      exact liftKZ_newtonZ_const (fun j => c (j + 1)) d n

/-- ★★★ **Exactness — a degree-`(e+1)` Newton form drops to depth `e` iff its top coefficient
    vanishes.**  `polyDepthZ e (Σ_{j≤e+1} C(·,j)cⱼ) ↔ c_{e+1} = 0`.  With `finite_depthZ_iff`,
    this pins divergence depth = degree *exactly*: a degree-`(e+1)` polynomial has depth `e+1`,
    not `e`, precisely when its leading Newton coefficient is non-zero. -/
theorem newtonZ_depth_drop (c : Nat → Int) (e : Nat) :
    polyDepthZ e (fun m => bsum m c (e + 1)) ↔ c (e + 1) = 0 := by
  constructor
  · intro hpd
    have h0 := (polyDepthZ_iff_vanish.mp hpd) 0
    rwa [liftKZ_newtonZ_const c (e + 1) 0] at h0
  · intro h
    refine polyDepthZ_iff_vanish.mpr (fun n => ?_)
    rw [liftKZ_newtonZ_const c (e + 1) n]; exact h

end E213.Lib.Math.Cauchy.DepthCharacterization
