import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem

/-!
# Schröder numbers — large `S(n)` and little `s(n)` (∅-axiom)

Large Schröder numbers (OEIS A006318): `1, 2, 6, 22, 90, 394, 1806, 8558, …`
via the **inclusive convolution recurrence**

  `S(0) = 1`,   `S(n+1) = S(n) + Σ_{k=0}^{n} S(k)·S(n−k)`.

Little Schröder (super-Catalan, OEIS A001003): `1, 1, 3, 11, 45, 197, …` with
`s(0) = 1` and `S(n) = 2·s(n)` for `n ≥ 1`.

  * ★ `schroder_succ` — the defining convolution recurrence (general `n`).
  * `schroder_table` — `S(0..7)`.
  * `schroder_three_term_recurrence` — the P-recurrence
    `(n+2)·S(n+1) = 3(2n+1)·S(n) − (n−1)·S(n−1)` (additive form, table n=1..6).
  * `littleSchroder` + `little_schroder_table` + `schroder_double_table`.

`schroder` is fuel-based (`Nat.strongRecOn` fuel-irrelevance, the `MotzkinNumbers`
pattern; the one difference is the *inclusive* convolution `sumTo (n+1)` with
`n−k`).  All ∅-axiom.  Genuinely absent (Schröder were not in the corpus).
-/

namespace E213.Lib.Math.Combinatorics.SchroderNumbers

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem (sumTo_congr)

/-- Fuel-based large Schröder: `schroderF fuel n = S n` whenever `fuel ≥ n`.
    `S(n+1) = S(n) + Σ_{k=0}^{n} S(k)·S(n−k)` (inclusive convolution). -/
def schroderF : Nat → Nat → Nat
  | 0,     _     => 1
  | _ + 1, 0     => 1
  | f + 1, n + 1 => schroderF f n + sumTo (n + 1) (fun k => schroderF f k * schroderF f (n - k))

/-- Large Schröder number via the convolution recurrence, fuel = index. -/
def schroder (n : Nat) : Nat := schroderF n n

/-- **Fuel irrelevance**: any two fuels `≥ n` agree.  Strong induction on `n`. -/
theorem schroderF_eq : ∀ n f g, n ≤ f → n ≤ g → schroderF f n = schroderF g n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f g hf hg
    match n, f, g, hf, hg with
    | 0,     f,     g,     _,  _  => cases f <;> cases g <;> rfl
    | n + 1, f + 1, g + 1, hf, hg =>
      show schroderF f n + sumTo (n + 1) (fun k => schroderF f k * schroderF f (n - k))
         = schroderF g n + sumTo (n + 1) (fun k => schroderF g k * schroderF g (n - k))
      have hnf : n ≤ f := Nat.le_of_succ_le_succ hf
      have hng : n ≤ g := Nat.le_of_succ_le_succ hg
      have hhead : schroderF f n = schroderF g n :=
        ih n (Nat.lt_succ_self n) f g hnf hng
      have htail :
          sumTo (n + 1) (fun k => schroderF f k * schroderF f (n - k))
            = sumTo (n + 1) (fun k => schroderF g k * schroderF g (n - k)) := by
        refine sumTo_congr (n + 1) _ _ ?_
        intro k hk
        have hkn  : k ≤ n := Nat.le_of_lt_succ hk
        have hknm : n - k ≤ n := Nat.sub_le n k
        have hkf  : schroderF f k = schroderF g k :=
          ih k (Nat.lt_succ_of_le hkn) f g (Nat.le_trans hkn hnf) (Nat.le_trans hkn hng)
        have hkg  : schroderF f (n - k) = schroderF g (n - k) :=
          ih (n - k) (Nat.lt_succ_of_le hknm) f g
            (Nat.le_trans hknm hnf) (Nat.le_trans hknm hng)
        rw [hkf, hkg]
      rw [hhead, htail]

/-- `schroderF f n = schroder n` whenever `fuel ≥ n`. -/
theorem schroderF_eq_schroder (f n : Nat) (h : n ≤ f) : schroderF f n = schroder n :=
  schroderF_eq n f n h (Nat.le_refl n)

/-- ★ **Defining recurrence**:
    `schroder (n+1) = schroder n + Σ_{k=0}^{n} schroder k · schroder (n−k)`. -/
theorem schroder_succ (n : Nat) :
    schroder (n + 1)
      = schroder n + sumTo (n + 1) (fun k => schroder k * schroder (n - k)) := by
  show schroderF (n + 1) (n + 1)
      = schroder n + sumTo (n + 1) (fun k => schroder k * schroder (n - k))
  show schroderF n n + sumTo (n + 1) (fun k => schroderF n k * schroderF n (n - k))
      = schroder n + sumTo (n + 1) (fun k => schroder k * schroder (n - k))
  have hhead : schroderF n n = schroder n := schroderF_eq_schroder n n (Nat.le_refl n)
  have htail :
      sumTo (n + 1) (fun k => schroderF n k * schroderF n (n - k))
        = sumTo (n + 1) (fun k => schroder k * schroder (n - k)) := by
    refine sumTo_congr (n + 1) _ _ ?_
    intro k hk
    have hkn  : k ≤ n := Nat.le_of_lt_succ hk
    have hknm : n - k ≤ n := Nat.sub_le n k
    rw [schroderF_eq_schroder n k hkn, schroderF_eq_schroder n (n - k) hknm]
  rw [hhead, htail]

theorem schroder_zero : schroder 0 = 1 := rfl

/-- **Value table** `S(0..7) = 1,2,6,22,90,394,1806,8558` (OEIS A006318). -/
theorem schroder_table :
    schroder 0 = 1 ∧ schroder 1 = 2 ∧ schroder 2 = 6 ∧ schroder 3 = 22
    ∧ schroder 4 = 90 ∧ schroder 5 = 394 ∧ schroder 6 = 1806 ∧ schroder 7 = 8558 := by
  decide

/-- **Three-term P-recurrence** `(n+2)·S(n+1) = 3(2n+1)·S(n) − (n−1)·S(n−1)`
    (OEIS A006318), additive `Nat` form `(n+2)·S(n+1) + (n−1)·S(n−1) = 3(2n+1)·S(n)`,
    table n=1..6.  General proof is a deeper induction (not attempted). -/
theorem schroder_three_term_recurrence :
    3 * schroder 2 + 0 * schroder 0 = 3 * 3 * schroder 1
    ∧ 4 * schroder 3 + 1 * schroder 1 = 3 * 5 * schroder 2
    ∧ 5 * schroder 4 + 2 * schroder 2 = 3 * 7 * schroder 3
    ∧ 6 * schroder 5 + 3 * schroder 3 = 3 * 9 * schroder 4
    ∧ 7 * schroder 6 + 4 * schroder 4 = 3 * 11 * schroder 5
    ∧ 8 * schroder 7 + 5 * schroder 5 = 3 * 13 * schroder 6 := by
  decide

/-- Little Schröder (super-Catalan, OEIS A001003): `s(0) = 1`, `s(n) = S(n)/2` (n≥1). -/
def littleSchroder : Nat → Nat
  | 0     => 1
  | n + 1 => schroder (n + 1) / 2

/-- **Little Schröder table** `s(0..7) = 1,1,3,11,45,197,903,4279` (OEIS A001003). -/
theorem little_schroder_table :
    littleSchroder 0 = 1 ∧ littleSchroder 1 = 1 ∧ littleSchroder 2 = 3
    ∧ littleSchroder 3 = 11 ∧ littleSchroder 4 = 45 ∧ littleSchroder 5 = 197
    ∧ littleSchroder 6 = 903 ∧ littleSchroder 7 = 4279 := by
  decide

/-- **Doubling relation** `S(n) = 2·s(n)` for `n ≥ 1`, table n=1..7 (the parity of
    `schroder` is a deeper general fact). -/
theorem schroder_double_table :
    schroder 1 = 2 * littleSchroder 1 ∧ schroder 2 = 2 * littleSchroder 2
    ∧ schroder 3 = 2 * littleSchroder 3 ∧ schroder 4 = 2 * littleSchroder 4
    ∧ schroder 5 = 2 * littleSchroder 5 ∧ schroder 6 = 2 * littleSchroder 6
    ∧ schroder 7 = 2 * littleSchroder 7 := by
  decide

end E213.Lib.Math.Combinatorics.SchroderNumbers
