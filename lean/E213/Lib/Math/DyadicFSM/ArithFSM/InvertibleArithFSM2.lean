import E213.Lib.Math.DyadicFSM.ArithFSM
import E213.Lib.Math.DyadicFSM.Forward.ForwardPeriodicity
/-!
# Invertible 2-state arithmetic FSMs — generic existential period

`InvertibleArithFSM2 n` augments `ArithFSM2 n` with a step-inverse
witness `stepInv` and a left-cancellation proof `stepInv (step v) = v`.

The two consequences captured here, both PURE:

  · **`run_translation`** — any coincidence `F.run i = F.run j` with
    `i ≤ j` produces a period `F.run (j - i) = F.run 0`.  By
    repeated application of `stepInv` to peel `min(i, j)` steps off
    both sides.
  · **`exists_period`** — combining `run_translation` with the
    constructive pigeonhole on `Fin (n² + 1) → Fin (n²)` (via
    `Forward.ForwardPeriodicity.pigeonhole_collision`), any
    invertible `ArithFSM2 n` (with `1 < n`) has a period
    `N ≤ n²` with `F.run N = F.run 0`.

This is the abstract version of the G119 Phase 2 existential Pisano
period closure for the Pell matrix C-H FSM.  Future invertible
2-state FSMs (Lucas / Fib companions / arbitrary `M ∈ SL_2(𝔽_n)`
recurrences) become 1-line corollaries: provide a `stepInv` + proof
of `stepInv (step v) = v` once, get the existential period for free.

All declarations PURE.
-/

namespace E213.Lib.Math.DyadicFSM.ArithFSM

/-- `ArithFSM2 n` augmented with a left-cancelling step inverse.
    The two-sided cancellation `step (stepInv v) = v` is NOT required;
    only the left cancellation is needed for the translation argument
    on the forward run sequence.  (In particular, `stepInv` does not
    need to be defined as a true inverse on states outside the orbit.) -/
structure InvertibleArithFSM2 (n : Nat) extends ArithFSM2 n where
  stepInv  : Fin n × Fin n → Fin n × Fin n
  inv_left : ∀ v, stepInv (step v) = v

end E213.Lib.Math.DyadicFSM.ArithFSM

namespace E213.Lib.Math.DyadicFSM.ArithFSM.InvertibleArithFSM2

/-- `stepInv` peels one step off the forward run sequence:
    `stepInv (F.run (k + 1)) = F.run k`.  PURE. -/
theorem stepInv_run_succ {n : Nat} (F : InvertibleArithFSM2 n) (k : Nat) :
    F.stepInv (F.run (k + 1)) = F.run k := by
  show F.stepInv (F.step (F.run k)) = F.run k
  exact F.inv_left (F.run k)

/-- ★ **Translation engine**: any coincidence in the forward run
    sequence (`F.run i = F.run j` with `i ≤ j`) produces a period
    `F.run (j - i) = F.run 0`.  PURE — induction on `i`, peeling
    `stepInv` from both sides at each step. -/
theorem run_translation {n : Nat} (F : InvertibleArithFSM2 n) :
    ∀ i j, i ≤ j → F.run i = F.run j → F.run (j - i) = F.run 0
  | 0, j, _, h => by rw [Nat.sub_zero]; exact h.symm
  | i+1, j, hij, h => by
    match j, hij, h with
    | m+1, hm1, h' =>
      have hstep : F.stepInv (F.run (i + 1)) = F.stepInv (F.run (m + 1)) :=
        congrArg _ h'
      rw [F.stepInv_run_succ i, F.stepInv_run_succ m] at hstep
      have him : i ≤ m := Nat.le_of_succ_le_succ hm1
      have hrec : F.run (m - i) = F.run 0 :=
        run_translation F i m him hstep
      show F.run (m + 1 - (i + 1)) = F.run 0
      rw [Nat.succ_sub_succ_eq_sub]
      exact hrec

/-- Pair-encode `F.run i.val ∈ Fin n × Fin n` into `Fin (n · n)` via
    `(a, b) ↦ a · n + b`.  Bound `(a + 1) · n ≤ n · n` from `a < n`. -/
def runEncode {n : Nat} (F : InvertibleArithFSM2 n)
    (i : Fin (n * n + 1)) : Fin (n * n) :=
  ⟨(F.run i.val).1.val * n + (F.run i.val).2.val, by
    have ha : (F.run i.val).1.val < n := (F.run i.val).1.isLt
    have hb : (F.run i.val).2.val < n := (F.run i.val).2.isLt
    calc (F.run i.val).1.val * n + (F.run i.val).2.val
        < (F.run i.val).1.val * n + n := Nat.add_lt_add_left hb _
      _ = ((F.run i.val).1.val + 1) * n := (Nat.succ_mul _ n).symm
      _ ≤ n * n := Nat.mul_le_mul_right n ha⟩

open E213.Lib.Math.DyadicFSM.Forward.ForwardPeriodicity
  (pigeonhole_collision collTest_imp_val_eq encode_inj)
open E213.Tactic.NatHelper (sub_pos_of_lt)

/-- ★ **Existential period** for any invertible 2-state FSM on
    `Fin n × Fin n` with `1 < n`: the forward run sequence returns
    to its initial value within `n²` steps.  Proven via
    constructive pigeonhole (`pigeonhole_collision`) + the
    translation engine (`run_translation`).  PURE. -/
theorem exists_period {n : Nat} (F : InvertibleArithFSM2 n) (hn : 1 < n) :
    ∃ N, 0 < N ∧ N ≤ n * n ∧ F.run N = F.run 0 := by
  have hn_pos : 0 < n := Nat.lt_of_succ_lt hn
  have hlt : n * n < n * n + 1 := Nat.lt_succ_self _
  obtain ⟨i, hi, j, hj, hij, hcoll⟩ :=
    pigeonhole_collision hlt F.runEncode
  have hval_eq : (F.runEncode ⟨i, hi⟩).val = (F.runEncode ⟨j, hj⟩).val :=
    collTest_imp_val_eq F.runEncode i j hi hj hcoll
  have hbi : (F.run i).2.val < n := (F.run i).2.isLt
  have hbj : (F.run j).2.val < n := (F.run j).2.isLt
  obtain ⟨ha_eq, hb_eq⟩ := encode_inj hn_pos
    (F.run i).1.val (F.run j).1.val
    (F.run i).2.val (F.run j).2.val
    hbi hbj hval_eq
  have hrun_eq : F.run i = F.run j :=
    Prod.ext (Fin.ext ha_eq) (Fin.ext hb_eq)
  have hpt : F.run (j - i) = F.run 0 :=
    run_translation F i j (Nat.le_of_lt hij) hrun_eq
  exact ⟨j - i, sub_pos_of_lt hij,
    Nat.le_trans (Nat.sub_le j i) (Nat.le_of_lt_succ hj), hpt⟩

end E213.Lib.Math.DyadicFSM.ArithFSM.InvertibleArithFSM2
