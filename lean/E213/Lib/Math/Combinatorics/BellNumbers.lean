import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
import E213.Lib.Math.Combinatorics.Stirling

/-!
# Bell numbers via the binomial recurrence (∅-axiom)

The Bell numbers `B_n` (count of set partitions) defined by the **binomial
recurrence** `B(n+1) = Σ_{k=0}^{n} C(n,k)·B(k)` — computing arbitrary `bell n`,
unlike the corpus `Stirling.bell` finite lookup table.  Genuinely new (the
recurrence-based definition + the proved recurrence theorem).

  * ★ `bell_succ` — the defining recurrence (general `n`).
  * `bell_table` — `B_0..B_6 = 1,1,2,5,15,52,203` (OEIS A000110).
  * ★ `bell_pos` — `bell n ≥ 1` (general; the `k=0` term is `1`).
  * `bell_eq_stirling_sum` — the Stirling connection `B_n = Σ_k S(n,k)` checked
    against the corpus `Stirling.stirling2` (n ≤ 5; the fully-general agreement of
    the two recurrences is a deeper induction, not attempted).

`bell` is fuel-based (plain structural recursion on fuel + fuel-irrelevance via
`Nat.strongRecOn`), avoiding well-founded recursion.  All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.BellNumbers

/-- Alias for the corpus second-kind Stirling numbers. -/
abbrev ST.stirling2 := E213.Lib.Math.Combinatorics.Stirling.stirling2

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose choose_zero_right choose_self)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_zero sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem (sumTo_congr sumTo_term_le)

/-- Fuel-based Bell: `bellF fuel n = B n` whenever `fuel ≥ n` (fuel decreases
    structurally → plain structural recursion, PURE). -/
def bellF : Nat → Nat → Nat
  | 0,     _ => 1
  | _ + 1, 0 => 1
  | f + 1, n + 1 => sumTo (n + 1) (fun k => choose n k * bellF f k)

/-- Bell number via the binomial recurrence, fuel = index. -/
def bell (n : Nat) : Nat := bellF n n

/-- **Fuel irrelevance**: any two fuels `≥ n` agree.  Strong induction on `n`. -/
theorem bellF_eq : ∀ n f g, n ≤ f → n ≤ g → bellF f n = bellF g n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f g hf hg
    match n, f, g, hf, hg with
    | 0,     f,     g,     _,  _  => cases f <;> cases g <;> rfl
    | n + 1, f + 1, g + 1, hf, hg =>
      show sumTo (n + 1) (fun k => choose n k * bellF f k)
         = sumTo (n + 1) (fun k => choose n k * bellF g k)
      have hnf : n ≤ f := Nat.le_of_succ_le_succ hf
      have hng : n ≤ g := Nat.le_of_succ_le_succ hg
      refine sumTo_congr (n + 1) _ _ ?_
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ hk
      rw [ih k hk f g (Nat.le_trans hkn hnf) (Nat.le_trans hkn hng)]

/-- `bellF f n = bell n` whenever `fuel ≥ n`. -/
theorem bellF_eq_bell (f n : Nat) (h : n ≤ f) : bellF f n = bell n :=
  bellF_eq n f n h (Nat.le_refl n)

/-- ★ **Defining recurrence**: `bell (n+1) = Σ_{k=0}^{n} C(n,k) · bell k`. -/
theorem bell_succ (n : Nat) :
    bell (n + 1) = sumTo (n + 1) (fun k => choose n k * bell k) := by
  show bellF (n + 1) (n + 1) = sumTo (n + 1) (fun k => choose n k * bell k)
  show sumTo (n + 1) (fun k => choose n k * bellF n k)
     = sumTo (n + 1) (fun k => choose n k * bell k)
  refine sumTo_congr (n + 1) _ _ ?_
  intro k hk
  rw [bellF_eq_bell n k (Nat.le_of_lt_succ hk)]

theorem bell_zero : bell 0 = 1 := rfl

/-- **Value table** `B_0..B_6 = 1,1,2,5,15,52,203` (OEIS A000110). -/
theorem bell_table :
    bell 0 = 1 ∧ bell 1 = 1 ∧ bell 2 = 2 ∧ bell 3 = 5
    ∧ bell 4 = 15 ∧ bell 5 = 52 ∧ bell 6 = 203 := by decide

/-- ★ **Positivity** `bell n ≥ 1` (general `n`): the `k=0` term of the recurrence
    is `C(n,0)·bell 0 = 1`, bounded above by the whole sum. -/
theorem bell_pos : ∀ n, 1 ≤ bell n
  | 0     => Nat.le_refl 1
  | n + 1 => by
    rw [bell_succ n]
    have hterm :
        (fun k => choose n k * bell k) 0
          ≤ sumTo (n + 1) (fun k => choose n k * bell k) :=
      sumTo_term_le (n + 1) (fun k => choose n k * bell k) 0 (Nat.succ_pos n)
    have hzero : (fun k => choose n k * bell k) 0 = 1 := by
      show choose n 0 * bell 0 = 1
      rw [choose_zero_right, bell_zero]
    rw [hzero] at hterm
    exact hterm

/-- **Stirling connection** `bell n = Σ_k S(n,k)` for `n = 0..5`, matching the
    corpus second-kind Stirling table — ties the binomial-recurrence Bell to the
    partition-counting Bell. -/
theorem bell_eq_stirling_sum :
    bell 0 = ST.stirling2 0 0
    ∧ bell 1 = ST.stirling2 1 0 + ST.stirling2 1 1
    ∧ bell 2 = ST.stirling2 2 0 + ST.stirling2 2 1 + ST.stirling2 2 2
    ∧ bell 3 = ST.stirling2 3 0 + ST.stirling2 3 1 + ST.stirling2 3 2 + ST.stirling2 3 3
    ∧ bell 4 = ST.stirling2 4 0 + ST.stirling2 4 1 + ST.stirling2 4 2
                + ST.stirling2 4 3 + ST.stirling2 4 4
    ∧ bell 5 = ST.stirling2 5 0 + ST.stirling2 5 1 + ST.stirling2 5 2
                + ST.stirling2 5 3 + ST.stirling2 5 4 + ST.stirling2 5 5 := by decide

end E213.Lib.Math.Combinatorics.BellNumbers
