import E213.Lib.Math.Combinatorics.EulerianNumbers
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.PolyNatMTactic

/-!
# Worpitzky's identity `xⁿ = Σ_k A(n,k)·C(x+k, n)` — fully general (∅-axiom)

★★★ Closes the open frontier recorded in `EulerianNumbers.lean` (the fully-general
`∀n, ∀x` Worpitzky; that file proved only n=1,2,3).

  * `worpitzky_succ (n x) : x^(n+1) = Σ_{k=0}^{n} A(n+1,k)·C(x+k, n+1)` (hypothesis-free).
  * `worpitzky (n x) (0<n) : xⁿ = Σ_{k<n} A(n,k)·C(x+k, n)`.

Induction on `n`; the coefficient bookkeeping closes via the additive upper-index
absorption `x·C(x+k,n) = (n−k)·C(x+k+1,n+1) + (k+1)·C(x+k,n+1)` (`absorb_shift`,
from `choose_succ_mul`), the reindex `Vsum_eq`, and matching the Eulerian recurrence
`A(n+2,k+1) = (k+2)A(n+1,k+1) + ((n+1)−k)A(n+1,k)` (`target_eq`).  `eulerian_diag_succ`
(`A(n+1,n+1)=0`) peels the vanishing top term.  All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.Worpitzky

open E213.Lib.Math.Combinatorics.Permutations (fact)
open E213.Lib.Math.Combinatorics.EulerianNumbers
  (eulerian eulerian_zero_above)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_zero sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
  (sumTo_split_first sumTo_add_func sumTo_congr sumTo_mul_left)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_one_right choose_succ_succ choose_zero_right choose_succ_mul)
open E213.Tactic.NatHelper (add_sub_of_le sub_add_cancel)

/-! ## Key absorption lemmas (the upper-index Pascal + the absorption) -/

/-- (i) Upper-index Pascal: `C(x+k+1, n+1) = C(x+k, n) + C(x+k, n+1)`. -/
theorem upper_pascal (x k n : Nat) :
    choose (x + k + 1) (n + 1) = choose (x + k) n + choose (x + k) (n + 1) :=
  choose_succ_succ (x + k) n

/-- (ii) Upper-index absorption (no subtraction):
    `(n+1)·C(x+k+1, n+1) = (x+k+1)·C(x+k, n)`. -/
theorem upper_absorb (x k n : Nat) :
    (n + 1) * choose (x + k + 1) (n + 1) = (x + k + 1) * choose (x + k) n :=
  choose_succ_mul (x + k) n

/-- (iii) Additive absorption (subtraction-free):
    `x·C(x+k,n) + (k+1)·C(x+k,n) = (n+1)·C(x+k,n) + (n+1)·C(x+k,n+1)`. -/
theorem add_absorb (x k n : Nat) :
    x * choose (x + k) n + (k + 1) * choose (x + k) n
      = (n + 1) * choose (x + k) n + (n + 1) * choose (x + k) (n + 1) := by
  have ha : (n + 1) * choose (x + k + 1) (n + 1) = (x + k + 1) * choose (x + k) n :=
    upper_absorb x k n
  rw [upper_pascal x k n] at ha
  -- ha : (n+1)*(C(x+k,n) + C(x+k,n+1)) = (x+k+1)*C(x+k,n)
  rw [Nat.mul_add] at ha
  -- ha : (n+1)*C(x+k,n) + (n+1)*C(x+k,n+1) = (x+k+1)*C(x+k,n)
  -- RHS: (x+k+1) = x + (k+1)
  rw [show x + k + 1 = x + (k + 1) from by rw [Nat.add_assoc],
      E213.Tactic.NatHelper.add_mul x (k + 1) (choose (x + k) n)] at ha
  -- ha : (n+1)*C(x+k,n) + (n+1)*C(x+k,n+1) = x*C(x+k,n) + (k+1)*C(x+k,n)
  exact ha.symm

/-- (iv) Pointwise absorption with the Eulerian weight `(n-k)` (for `k ≤ n`):
    `x·C(x+k,n) = (n-k)·C(x+k,n) + (n+1)·C(x+k,n+1)`. -/
theorem absorb_sub {x k n : Nat} (h : k ≤ n) :
    x * choose (x + k) n
      = (n - k) * choose (x + k) n + (n + 1) * choose (x + k) (n + 1) := by
  -- From add_absorb : x*C + (k+1)*C = (n+1)*C + (n+1)*C'
  have hab := add_absorb x k n
  -- Split (n+1)*C = (n-k)*C + (k+1)*C  via  (n-k) + (k+1) = n+1.
  have hsplit : (n + 1) * choose (x + k) n
      = ((n - k) + (k + 1)) * choose (x + k) n := by
    rw [show (n - k) + (k + 1) = n + 1 from by
          rw [← Nat.add_assoc, Nat.add_comm (n - k) k, add_sub_of_le h]]
  rw [hsplit, E213.Tactic.NatHelper.add_mul (n - k) (k + 1) (choose (x + k) n)] at hab
  -- hab : x*C + (k+1)*C = ((n-k)*C + (k+1)*C) + (n+1)*C'
  rw [Nat.add_assoc, Nat.add_comm ((k + 1) * choose (x + k) n)
        ((n + 1) * choose (x + k) (n + 1)), ← Nat.add_assoc] at hab
  -- hab : x*C + (k+1)*C = ((n-k)*C + (n+1)*C') + (k+1)*C
  exact E213.Tactic.NatHelper.add_right_cancel hab

/-- (v) Shifted pointwise absorption (additive, for `k ≤ n`):
    `x·C(x+k,n) = (n-k)·C(x+k+1,n+1) + (k+1)·C(x+k,n+1)`. -/
theorem absorb_shift {x k n : Nat} (h : k ≤ n) :
    x * choose (x + k) n
      = (n - k) * choose (x + k + 1) (n + 1) + (k + 1) * choose (x + k) (n + 1) := by
  rw [absorb_sub h]
  -- goal: (n-k)*C(x+k,n) + (n+1)*C(x+k,n+1)
  --     = (n-k)*C(x+k+1,n+1) + (k+1)*C(x+k,n+1)
  rw [upper_pascal x k n]   -- C(x+k+1,n+1) = C(x+k,n) + C(x+k,n+1)
  -- RHS: (n-k)*(C(x+k,n)+C(x+k,n+1)) + (k+1)*C(x+k,n+1)
  rw [Nat.mul_add]
  -- RHS: (n-k)*C(x+k,n) + (n-k)*C(x+k,n+1) + (k+1)*C(x+k,n+1)
  rw [Nat.add_assoc, ← E213.Tactic.NatHelper.add_mul (n - k) (k + 1) (choose (x + k) (n + 1))]
  -- RHS: (n-k)*C(x+k,n) + ((n-k)+(k+1))*C(x+k,n+1)
  rw [show (n - k) + (k + 1) = n + 1 from by
        rw [← Nat.add_assoc, Nat.add_comm (n - k) k, add_sub_of_le h]]

/-- Diagonal vanishes: `A(n+1, n+1) = 0` (max ascents of a perm of `n+1` is `n`). -/
theorem eulerian_diag_succ (n : Nat) : eulerian (n + 1) (n + 1) = 0 := by
  show (n + 2) * eulerian n (n + 1) + (n - n) * eulerian n n = 0
  rw [eulerian_zero_above (Nat.lt_succ_self n), Nat.mul_zero, Nat.zero_add,
      Nat.sub_self, Nat.zero_mul]

/-! ## Sum-level decomposition `x·(IH sum) = U + V` -/

/-- Abbreviations for the two target sub-sums.
    `Usum` uses the shifted upper index `C(x+k+1, n+1)` with weight `(n-k)`;
    `Vsum` uses `C(x+k, n+1)` with weight `(k+1)`. -/
def Usum (x n : Nat) : Nat :=
  sumTo n (fun k => (n - k) * eulerian n k * choose (x + k + 1) (n + 1))
def Vsum (x n : Nat) : Nat :=
  sumTo n (fun k => (k + 1) * eulerian n k * choose (x + k) (n + 1))

/-- Per-term: `A(n,k)·(x·C(x+k,n)) = (n-k)·A(n,k)·C(x+k+1,n+1) + (k+1)·A(n,k)·C(x+k,n+1)`
    for `k < n`. -/
theorem term_split {x k n : Nat} (h : k < n) :
    eulerian n k * (x * choose (x + k) n)
      = (n - k) * eulerian n k * choose (x + k + 1) (n + 1)
        + (k + 1) * eulerian n k * choose (x + k) (n + 1) := by
  rw [absorb_shift (Nat.le_of_lt h)]
  -- LHS: A * ((n-k)*C' + (k+1)*C'')
  generalize choose (x + k + 1) (n + 1) = a
  generalize choose (x + k) (n + 1) = b
  generalize eulerian n k = e
  generalize n - k = m
  ring_nat

/-- `x · (Σ_{k<n} A(n,k)·C(x+k,n)) = Usum x n + Vsum x n`. -/
theorem mul_ih_split (x n : Nat) :
    x * sumTo n (fun k => eulerian n k * choose (x + k) n)
      = Usum x n + Vsum x n := by
  rw [sumTo_mul_left x n (fun k => eulerian n k * choose (x + k) n)]
  -- Σ (x * (A * C))  →  rewrite each term to  A * (x * C)  then term_split
  rw [sumTo_congr n
        (fun k => x * (eulerian n k * choose (x + k) n))
        (fun k => (n - k) * eulerian n k * choose (x + k + 1) (n + 1)
                  + (k + 1) * eulerian n k * choose (x + k) (n + 1))
        (fun k hk => by
          show x * (eulerian n k * choose (x + k) n)
            = (n - k) * eulerian n k * choose (x + k + 1) (n + 1)
              + (k + 1) * eulerian n k * choose (x + k) (n + 1)
          rw [show x * (eulerian n k * choose (x + k) n)
                = eulerian n k * (x * choose (x + k) n) from by
                generalize choose (x + k) n = c
                generalize eulerian n k = e
                ring_nat]
          exact term_split hk)]
  rw [← sumTo_add_func n
        (fun k => (n - k) * eulerian n k * choose (x + k + 1) (n + 1))
        (fun k => (k + 1) * eulerian n k * choose (x + k) (n + 1))]
  show Usum x n + Vsum x n = Usum x n + Vsum x n
  rfl

/-- The target tail sum `Σ_{k<n} (k+2)·A(n,k+1)·C(x+k+1, n+1)`. -/
def Wsum (x n : Nat) : Nat :=
  sumTo n (fun k => (k + 2) * eulerian n (k + 1) * choose (x + k + 1) (n + 1))

/-- `Vsum x (n+1) = C(x, n+2) + Wsum x (n+1)`.  (Split off `k=0`, `A(n+1,0)=1`.) -/
theorem Vsum_eq (x n : Nat) :
    Vsum x (n + 1) = choose x (n + 2) + Wsum x (n + 1) := by
  show sumTo (n + 1) (fun k => (k + 1) * eulerian (n + 1) k * choose (x + k) (n + 2))
      = choose x (n + 2) + Wsum x (n + 1)
  rw [sumTo_split_first n (fun k => (k + 1) * eulerian (n + 1) k * choose (x + k) (n + 2))]
  -- = (0+1)*A(n+1,0)*C(x+0,n+2) + Σ_{k<n+1} (k+1+1)*A(n+1,k+1)*C(x+(k+1),n+2)
  show (0 + 1) * eulerian (n + 1) 0 * choose (x + 0) (n + 2)
        + sumTo n
            (fun k => (k + 1 + 1) * eulerian (n + 1) (k + 1) * choose (x + (k + 1)) (n + 2))
      = choose x (n + 2) + Wsum x (n + 1)
  rw [show eulerian (n + 1) 0 = 1 from rfl]
  rw [show (0 + 1) * 1 * choose (x + 0) (n + 2) = choose x (n + 2) from by
        rw [Nat.zero_add]
        rw [Nat.one_mul (1 : Nat)]
        rw [Nat.one_mul (choose (x + 0) (n + 2))]
        rw [Nat.add_zero x]]
  -- The tail (sumTo n) matches Wsum's lower n terms; Wsum's top term (k=n) is
  -- (n+2)·A(n+1,n+1)·C(...) = 0 since A(n+1,n+1)=0.
  rw [show Wsum x (n + 1)
        = sumTo n (fun k => (k + 2) * eulerian (n + 1) (k + 1) * choose (x + k + 1) (n + 2))
        from by
          show sumTo n (fun k => (k + 2) * eulerian (n + 1) (k + 1) * choose (x + k + 1) (n + 2))
                 + (n + 2) * eulerian (n + 1) (n + 1) * choose (x + n + 1) (n + 2)
               = sumTo n (fun k => (k + 2) * eulerian (n + 1) (k + 1) * choose (x + k + 1) (n + 2))
          rw [eulerian_diag_succ n]
          rw [Nat.mul_zero, Nat.zero_mul, Nat.add_zero]]
  rw [sumTo_congr n
        (fun k => (k + 1 + 1) * eulerian (n + 1) (k + 1) * choose (x + (k + 1)) (n + 2))
        (fun k => (k + 2) * eulerian (n + 1) (k + 1) * choose (x + k + 1) (n + 2))
        (fun k _ => by
          show (k + 1 + 1) * eulerian (n + 1) (k + 1) * choose (x + (k + 1)) (n + 2)
            = (k + 2) * eulerian (n + 1) (k + 1) * choose (x + k + 1) (n + 2)
          rw [show x + (k + 1) = x + k + 1 from by rw [Nat.add_assoc]])]

/-! ## Target decomposition `T = Usum + Vsum` -/

/-- `sumTo (n+2) (A(n+2,·)·C(x+·,n+2)) = Usum x (n+1) + Vsum x (n+1)`. -/
theorem target_eq (x n : Nat) :
    sumTo (n + 2) (fun k => eulerian (n + 2) k * choose (x + k) (n + 2))
      = Usum x (n + 1) + Vsum x (n + 1) := by
  rw [sumTo_split_first (n + 1) (fun k => eulerian (n + 2) k * choose (x + k) (n + 2))]
  -- = A(n+2,0)*C(x+0,n+2) + Σ_{k<n+1} A(n+2,k+1)*C(x+(k+1),n+2)
  show eulerian (n + 2) 0 * choose (x + 0) (n + 2)
        + sumTo (n + 1) (fun k => eulerian (n + 2) (k + 1) * choose (x + (k + 1)) (n + 2))
      = Usum x (n + 1) + Vsum x (n + 1)
  rw [show eulerian (n + 2) 0 = 1 from rfl]
  rw [show (1 : Nat) * choose (x + 0) (n + 2) = choose x (n + 2) from by
        rw [Nat.one_mul, Nat.add_zero]]
  -- Expand A(n+2,k+1) = (k+2)A(n+1,k+1) + ((n+1)-k)A(n+1,k), and shift x+(k+1)=x+k+1.
  rw [sumTo_congr (n + 1)
        (fun k => eulerian (n + 2) (k + 1) * choose (x + (k + 1)) (n + 2))
        (fun k => (k + 2) * eulerian (n + 1) (k + 1) * choose (x + k + 1) (n + 2)
                  + (n + 1 - k) * eulerian (n + 1) k * choose (x + k + 1) (n + 2))
        (fun k _ => by
          show eulerian (n + 2) (k + 1) * choose (x + (k + 1)) (n + 2)
            = (k + 2) * eulerian (n + 1) (k + 1) * choose (x + k + 1) (n + 2)
              + (n + 1 - k) * eulerian (n + 1) k * choose (x + k + 1) (n + 2)
          rw [show x + (k + 1) = x + k + 1 from by rw [Nat.add_assoc]]
          show ((k + 2) * eulerian (n + 1) (k + 1) + (n + 1 - k) * eulerian (n + 1) k)
                 * choose (x + k + 1) (n + 2)
            = (k + 2) * eulerian (n + 1) (k + 1) * choose (x + k + 1) (n + 2)
              + (n + 1 - k) * eulerian (n + 1) k * choose (x + k + 1) (n + 2)
          rw [E213.Tactic.NatHelper.add_mul])]
  -- Split the sum into Wsum + Usum.
  rw [← sumTo_add_func (n + 1)
        (fun k => (k + 2) * eulerian (n + 1) (k + 1) * choose (x + k + 1) (n + 2))
        (fun k => (n + 1 - k) * eulerian (n + 1) k * choose (x + k + 1) (n + 2))]
  -- Now: C(x,n+2) + (Wsum x (n+1) + Usum x (n+1)) = Usum x (n+1) + Vsum x (n+1)
  show choose x (n + 2) + (Wsum x (n + 1) + Usum x (n + 1))
      = Usum x (n + 1) + Vsum x (n + 1)
  rw [Vsum_eq x n]
  -- RHS: Usum + (C(x,n+2) + Wsum)
  generalize Usum x (n + 1) = U
  generalize Wsum x (n + 1) = W
  generalize choose x (n + 2) = c
  -- c + (W + U) = U + (c + W)
  rw [Nat.add_comm W U, ← Nat.add_assoc, Nat.add_comm c U, Nat.add_assoc]

/-! ## ★★★ Worpitzky's identity, general `n` and `x` -/

/-- ★★★ **Worpitzky's identity** (general `n`, general `x`):
    `x^(n+1) = Σ_{k=0}^{n} A(n+1,k)·C(x+k, n+1)`.
    Induction on `n`; step uses `mul_ih_split` (absorption) + `target_eq`
    (Eulerian recurrence reindex).  PURE. -/
theorem worpitzky_succ :
    ∀ (n x : Nat),
      x ^ (n + 1) = sumTo (n + 1) (fun k => eulerian (n + 1) k * choose (x + k) (n + 1))
  | 0, x => by
      -- x^1 = C(x,1) = x
      show x ^ 1 = (0 : Nat) + eulerian 1 0 * choose (x + 0) 1
      rw [show eulerian 1 0 = 1 from rfl, Nat.zero_add, Nat.one_mul, Nat.add_zero,
          choose_one_right, Nat.pow_one]
  | n + 1, x => by
      -- x^(n+2) = x · x^(n+1)
      rw [show x ^ (n + 2) = x * x ^ (n + 1) from by rw [Nat.pow_succ, Nat.mul_comm]]
      rw [worpitzky_succ n x]
      -- x * sumTo (n+1) (A(n+1,·)C(x+·,n+1)) = Usum x (n+1) + Vsum x (n+1)
      rw [mul_ih_split x (n + 1)]
      -- = target
      rw [← target_eq x n]

/-- ★★★ **Worpitzky's identity** in the `sumTo n` form matching `EulerianNumbers.lean`
    (`worpitzky_one/two/three`), for `n ≥ 1`. -/
theorem worpitzky (n x : Nat) (hn : 0 < n) :
    x ^ n = sumTo n (fun k => eulerian n k * choose (x + k) n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by
    cases n with
    | zero => exact absurd hn (Nat.lt_irrefl 0)
    | succ k => rfl⟩
  exact worpitzky_succ m x

/-! ## Smoke checks against the per-`n` results -/

theorem worp_check1 (x : Nat) :
    x ^ 1 = sumTo 1 (fun k => eulerian 1 k * choose (x + k) 1) := worpitzky_succ 0 x
theorem worp_check2 (x : Nat) :
    x ^ 2 = sumTo 2 (fun k => eulerian 2 k * choose (x + k) 2) := worpitzky_succ 1 x
theorem worp_check3 (x : Nat) :
    x ^ 3 = sumTo 3 (fun k => eulerian 3 k * choose (x + k) 3) := worpitzky_succ 2 x
theorem worp_check4 (x : Nat) :
    x ^ 4 = sumTo 4 (fun k => eulerian 4 k * choose (x + k) 4) := worpitzky_succ 3 x
theorem worp_check5 (x : Nat) :
    x ^ 5 = sumTo 5 (fun k => eulerian 5 k * choose (x + k) 5) := worpitzky_succ 4 x

end E213.Lib.Math.Combinatorics.Worpitzky
