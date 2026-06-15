import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
import E213.Lib.Math.Combinatorics.Catalan

/-!
# Motzkin numbers `M(n)` via the convolution recurrence (∅-axiom)

The Motzkin numbers (OEIS A001006) count lattice paths from `(0,0)` to `(n,0)`
using up `(1,1)`, down `(1,−1)`, and flat `(1,0)` steps never going below the
x-axis (equivalently: ways of drawing non-crossing chords between `n` points on a
circle).  Defined by the **two-term convolution recurrence**

  `M(0) = 1`,   `M(n+1) = M(n) + Σ_{k=0}^{n−1} M(k)·M(n−1−k)`.

  * ★ `motzkin_succ` — the defining recurrence (general `n`).
  * `motzkin_table` — `M(0..9) = 1,1,2,4,9,21,51,127,323,835`.
  * ★ `motzkin_catalan_table` — the Motzkin–Catalan relation
        `M(n) = Σ_k C(n,2k)·catalan(k)`, verified `n = 0..6` (kept small so the
        corpus finite `catalan` table — values up to `k = 3` — suffices).
  * `motzkin_three_term_recurrence` — the classical P-recurrence
        `(n+2)·M(n) = (2n+1)·M(n−1) + 3(n−1)·M(n−2)` in table form, `n = 2..9`.

`motzkin` is fuel-based (plain structural recursion on fuel + fuel-irrelevance via
`Nat.strongRecOn`), mirroring the corpus `bell` pattern.  All ∅-axiom.  Genuinely
absent (Motzkin numbers were not in the corpus).
-/

namespace E213.Lib.Math.Combinatorics.MotzkinNumbers

abbrev catalan := E213.Lib.Math.Combinatorics.Catalan.catalan

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem (sumTo_congr)

/-- Fuel-based Motzkin: `motzkinF fuel n = M n` whenever `fuel ≥ n` (fuel decreases
    structurally → plain structural recursion, PURE).
    `M(n+1) = M(n) + Σ_{k=0}^{n−1} M(k)·M(n−1−k)`, the convolution sum being
    `sumTo n (fun k => M k · M (n−1−k))` (exclusive upper bound). -/
def motzkinF : Nat → Nat → Nat
  | 0,     _     => 1
  | _ + 1, 0     => 1
  | f + 1, n + 1 => motzkinF f n + sumTo n (fun k => motzkinF f k * motzkinF f (n - 1 - k))

/-- Motzkin number via the convolution recurrence, fuel = index. -/
def motzkin (n : Nat) : Nat := motzkinF n n

/-- **Fuel irrelevance**: any two fuels `≥ n` agree.  Strong induction on `n`. -/
theorem motzkinF_eq : ∀ n f g, n ≤ f → n ≤ g → motzkinF f n = motzkinF g n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f g hf hg
    match n, f, g, hf, hg with
    | 0,     f,     g,     _,  _  => cases f <;> cases g <;> rfl
    | n + 1, f + 1, g + 1, hf, hg =>
      show motzkinF f n + sumTo n (fun k => motzkinF f k * motzkinF f (n - 1 - k))
         = motzkinF g n + sumTo n (fun k => motzkinF g k * motzkinF g (n - 1 - k))
      have hnf : n ≤ f := Nat.le_of_succ_le_succ hf
      have hng : n ≤ g := Nat.le_of_succ_le_succ hg
      have hhead : motzkinF f n = motzkinF g n :=
        ih n (Nat.lt_succ_self n) f g hnf hng
      have htail :
          sumTo n (fun k => motzkinF f k * motzkinF f (n - 1 - k))
            = sumTo n (fun k => motzkinF g k * motzkinF g (n - 1 - k)) := by
        refine sumTo_congr n _ _ ?_
        intro k hk
        have hkn  : k ≤ n := Nat.le_of_lt hk
        have hknm : n - 1 - k ≤ n := Nat.le_trans (Nat.sub_le (n - 1) k) (Nat.sub_le n 1)
        have hkf  : motzkinF f k = motzkinF g k :=
          ih k (Nat.lt_succ_of_lt hk) f g (Nat.le_trans hkn hnf) (Nat.le_trans hkn hng)
        have hkg  : motzkinF f (n - 1 - k) = motzkinF g (n - 1 - k) :=
          ih (n - 1 - k) (Nat.lt_succ_of_le hknm) f g
            (Nat.le_trans hknm hnf) (Nat.le_trans hknm hng)
        rw [hkf, hkg]
      rw [hhead, htail]

/-- `motzkinF f n = motzkin n` whenever `fuel ≥ n`. -/
theorem motzkinF_eq_motzkin (f n : Nat) (h : n ≤ f) : motzkinF f n = motzkin n :=
  motzkinF_eq n f n h (Nat.le_refl n)

/-- ★ **Defining recurrence**:
    `motzkin (n+1) = motzkin n + Σ_{k=0}^{n−1} motzkin k · motzkin (n−1−k)`. -/
theorem motzkin_succ (n : Nat) :
    motzkin (n + 1)
      = motzkin n + sumTo n (fun k => motzkin k * motzkin (n - 1 - k)) := by
  show motzkinF (n + 1) (n + 1)
      = motzkin n + sumTo n (fun k => motzkin k * motzkin (n - 1 - k))
  show motzkinF n n + sumTo n (fun k => motzkinF n k * motzkinF n (n - 1 - k))
      = motzkin n + sumTo n (fun k => motzkin k * motzkin (n - 1 - k))
  have hhead : motzkinF n n = motzkin n := motzkinF_eq_motzkin n n (Nat.le_refl n)
  have htail :
      sumTo n (fun k => motzkinF n k * motzkinF n (n - 1 - k))
        = sumTo n (fun k => motzkin k * motzkin (n - 1 - k)) := by
    refine sumTo_congr n _ _ ?_
    intro k hk
    have hkn  : k ≤ n := Nat.le_of_lt hk
    have hknm : n - 1 - k ≤ n := Nat.le_trans (Nat.sub_le (n - 1) k) (Nat.sub_le n 1)
    rw [motzkinF_eq_motzkin n k hkn, motzkinF_eq_motzkin n (n - 1 - k) hknm]
  rw [hhead, htail]

theorem motzkin_zero : motzkin 0 = 1 := rfl

/-- **Value table** `M(0..9) = 1,1,2,4,9,21,51,127,323,835` (OEIS A001006). -/
theorem motzkin_table :
    motzkin 0 = 1 ∧ motzkin 1 = 1 ∧ motzkin 2 = 2 ∧ motzkin 3 = 4
    ∧ motzkin 4 = 9 ∧ motzkin 5 = 21 ∧ motzkin 6 = 51 ∧ motzkin 7 = 127
    ∧ motzkin 8 = 323 ∧ motzkin 9 = 835 := by decide

/-- ★ **Motzkin–Catalan relation** `M(n) = Σ_k C(n,2k)·catalan(k)`, verified for
    `n = 0..6` (kept small so the corpus finite `catalan` table suffices; at `n = 6`
    the largest Catalan argument is `k = 3`). -/
theorem motzkin_catalan_table :
    motzkin 0 = choose 0 0 * catalan 0
    ∧ motzkin 1 = choose 1 0 * catalan 0
    ∧ motzkin 2 = choose 2 0 * catalan 0 + choose 2 2 * catalan 1
    ∧ motzkin 3 = choose 3 0 * catalan 0 + choose 3 2 * catalan 1
    ∧ motzkin 4 = choose 4 0 * catalan 0 + choose 4 2 * catalan 1
                    + choose 4 4 * catalan 2
    ∧ motzkin 5 = choose 5 0 * catalan 0 + choose 5 2 * catalan 1
                    + choose 5 4 * catalan 2
    ∧ motzkin 6 = choose 6 0 * catalan 0 + choose 6 2 * catalan 1
                    + choose 6 4 * catalan 2 + choose 6 6 * catalan 3 := by decide

/-- **Three-term recurrence** `(n+2)·M(n) = (2n+1)·M(n−1) + 3(n−1)·M(n−2)`, the
    classical P-recurrence (OEIS A001006), in table form for `n = 2..9`.  The
    general proof is a deeper induction (not attempted); each instance is a closed
    numeric identity. -/
theorem motzkin_three_term_recurrence :
    4 * motzkin 2 = 5 * motzkin 1 + 3 * 1 * motzkin 0
    ∧ 5 * motzkin 3 = 7 * motzkin 2 + 3 * 2 * motzkin 1
    ∧ 6 * motzkin 4 = 9 * motzkin 3 + 3 * 3 * motzkin 2
    ∧ 7 * motzkin 5 = 11 * motzkin 4 + 3 * 4 * motzkin 3
    ∧ 8 * motzkin 6 = 13 * motzkin 5 + 3 * 5 * motzkin 4
    ∧ 9 * motzkin 7 = 15 * motzkin 6 + 3 * 6 * motzkin 5
    ∧ 10 * motzkin 8 = 17 * motzkin 7 + 3 * 7 * motzkin 6
    ∧ 11 * motzkin 9 = 19 * motzkin 8 + 3 * 8 * motzkin 7 := by decide

end E213.Lib.Math.Combinatorics.MotzkinNumbers
