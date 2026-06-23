import E213.Lib.Math.Foundations.UniverseChain.RawRecurrence

/-!
# Generic Raw count for arbitrary atom count (∅-axiom)

Mingu's question: "is the structure the same even if we start from 3 points?" — yes,
recurrence form is **N-generic**:

  **|S_n| = N + C(|S_{n-1}|, 2)**, |S_0| = N

Sequences:

  N = 1: 1, 1, 1, …                (degenerate; no slash)
  N = 2: 2, 3, 5, 12, 68, …        (current 213; minimal)
  N = 3: 3, 6, 18, 156, …
  N = 4: 4, 10, 49, …
  N = 5: 5, 15, 110, …

213 picks N = 2 by minimality (`seed/AXIOM/03_form.md` §3.2):
  * N = 1: no distinction (vacuous)
  * N = 2: minimum for distinction
  * N ≥ 3: redundant

The recurrence itself doesn't care about N — only the *justification*
for picking N = 2 (atomicity + arity-2 forcing) does.
-/

namespace E213.Lib.Math.Foundations.UniverseChain.RawCountGeneric

open E213.Lib.Math.Foundations.UniverseChain.RawRecurrence (choose2)

/-- Generic Raw count: parameter N = atom count. -/
def rawCountG (atomCount : Nat) : Nat → Nat
  | 0 => atomCount
  | n + 1 => atomCount + choose2 (rawCountG atomCount n)

/-- ★ Recurrence step (definitional). -/
theorem rawCountG_succ (N n : Nat) :
    rawCountG N (n + 1) = N + choose2 (rawCountG N n) := rfl

/-- ★ N = 2 matches our `rawCount`. -/
theorem rawCountG_2 (n : Nat) :
    rawCountG 2 n = E213.Lib.Math.Foundations.UniverseChain.RawRecurrence.rawCount n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show 2 + choose2 (rawCountG 2 k)
       = 2 + choose2 (E213.Lib.Math.Foundations.UniverseChain.RawRecurrence.rawCount k)
    rw [ih]

/-- N = 3 sequence: 3, 6, 18, 156. -/
theorem rawCountG_3_values :
    rawCountG 3 0 = 3 ∧ rawCountG 3 1 = 6
    ∧ rawCountG 3 2 = 18 ∧ rawCountG 3 3 = 156 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- N = 4 sequence: 4, 10, 49. -/
theorem rawCountG_4_values :
    rawCountG 4 0 = 4 ∧ rawCountG 4 1 = 10 ∧ rawCountG 4 2 = 49 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- N = 5 sequence: 5, 15, 110. -/
theorem rawCountG_5_values :
    rawCountG 5 0 = 5 ∧ rawCountG 5 1 = 15 ∧ rawCountG 5 2 = 110 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- N = 1 is degenerate (constant 1). -/
theorem rawCountG_1_degenerate :
    rawCountG 1 0 = 1 ∧ rawCountG 1 1 = 1
    ∧ rawCountG 1 2 = 1 ∧ rawCountG 1 3 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- ★★★ **Capstone**: N-generic recurrence; 213 picks N = 2 by
    minimality.  Other N give same form but different sequences. -/
theorem rawCountG_capstone :
    (∀ N n, rawCountG N (n + 1) = N + choose2 (rawCountG N n))
    ∧ (∀ n, rawCountG 2 n
            = E213.Lib.Math.Foundations.UniverseChain.RawRecurrence.rawCount n)
    ∧ rawCountG 1 5 = 1
    ∧ rawCountG 3 3 = 156
    ∧ rawCountG 4 2 = 49
    ∧ rawCountG 5 2 = 110 :=
  ⟨rawCountG_succ, rawCountG_2,
   by decide, by decide, by decide, by decide⟩

end E213.Lib.Math.Foundations.UniverseChain.RawCountGeneric
