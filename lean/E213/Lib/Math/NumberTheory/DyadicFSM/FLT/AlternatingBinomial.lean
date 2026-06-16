import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Meta.Int213.PolyIntMTactic

/-!
# Alternating binomial sum `Σ_{k=0}^{m} (−1)^k C(m,k) = 0` (m ≥ 1, ∅-axiom)

The signed alternating sum of a Pascal row vanishes (for `m ≥ 1`) — the `m`-th
case of `(1 + (−1))^m = 0`.  Genuinely absent (`(-1)^k · choose` had zero matches
in the corpus).

Rather than the binomial theorem, the proof goes through a sharper **telescoping
lemma** `alt_partial`: the alternating *partial* sum of a Pascal row collapses to
a single signed entry of the row above,
`Σ_{k=0}^{j} (−1)^k C(M+1,k) = (−1)^j C(M,j)` (Pascal + `powNegOne_succ`); taking
`M=n`, `j=n+1` and `C(n,n+1)=0` gives the full-row sum `0`.

An Int-valued fold `sumZ` is defined locally (the corpus `sumTo` is `Nat→Nat`).
All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.FLT.AlternatingBinomial

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_zero_right choose_succ_succ choose_eq_zero_of_lt)
open E213.Meta.Int213.PolyIntM (powInt mul_zeroZ)
open E213.Meta.Int213 (zero_add)

/-- Int-valued Σ over `[0, n)`. -/
def sumZ : Nat → (Nat → Int) → Int
  | 0,     _ => 0
  | n + 1, f => sumZ n f + f n

@[simp] theorem sumZ_zero (f : Nat → Int) : sumZ 0 f = 0 := rfl

@[simp] theorem sumZ_succ (n : Nat) (f : Nat → Int) :
    sumZ (n + 1) f = sumZ n f + f n := rfl

/-- `powInt (-1) (j+1) = - powInt (-1) j`. -/
theorem powNegOne_succ (j : Nat) :
    powInt (-1 : Int) (j + 1) = - powInt (-1 : Int) j := by
  show powInt (-1 : Int) j * (-1) = - powInt (-1 : Int) j
  ring_intZ

/-- ★ **Alternating partial sum** of a Pascal row = signed `choose` of the row above:
    `Σ_{k=0}^{j} (−1)^k C(M+1,k) = (−1)^j C(M,j)`.  Induction on `j` via Pascal. -/
theorem alt_partial (M : Nat) :
    ∀ j, sumZ (j + 1) (fun k => powInt (-1 : Int) k * (choose (M + 1) k : Int))
        = powInt (-1 : Int) j * (choose M j : Int) := by
  intro j
  induction j with
  | zero =>
      show (0 : Int) + powInt (-1 : Int) 0 * (choose (M + 1) 0 : Int)
          = powInt (-1 : Int) 0 * (choose M 0 : Int)
      rw [choose_zero_right, choose_zero_right, zero_add]
  | succ j ih =>
      show sumZ (j + 1) (fun k => powInt (-1 : Int) k * (choose (M + 1) k : Int))
            + powInt (-1 : Int) (j + 1) * (choose (M + 1) (j + 1) : Int)
          = powInt (-1 : Int) (j + 1) * (choose M (j + 1) : Int)
      rw [ih]
      rw [choose_succ_succ M j]
      show powInt (-1 : Int) j * (choose M j : Int)
            + powInt (-1 : Int) (j + 1) * ((choose M j + choose M (j + 1) : Nat) : Int)
          = powInt (-1 : Int) (j + 1) * (choose M (j + 1) : Int)
      rw [show ((choose M j + choose M (j + 1) : Nat) : Int)
            = (choose M j : Int) + (choose M (j + 1) : Int) from rfl]
      rw [powNegOne_succ j]
      ring_intZ

/-- ★★★ **Alternating binomial sum** `Σ_{k=0}^{m} (−1)^k C(m,k) = 0` for `m = n+1 ≥ 1`. -/
theorem alt_binom_sum (n : Nat) :
    sumZ (n + 2) (fun k => powInt (-1 : Int) k * (choose (n + 1) k : Int)) = 0 := by
  have h := alt_partial n (n + 1)
  rw [show choose n (n + 1) = 0 from choose_eq_zero_of_lt n (n + 1) (Nat.lt_succ_self n)] at h
  show sumZ ((n + 1) + 1) (fun k => powInt (-1 : Int) k * (choose (n + 1) k : Int)) = 0
  rw [h]
  show powInt (-1 : Int) (n + 1) * ((0 : Nat) : Int) = 0
  rw [show ((0 : Nat) : Int) = 0 from rfl, mul_zeroZ]

end E213.Lib.Math.NumberTheory.DyadicFSM.FLT.AlternatingBinomial
