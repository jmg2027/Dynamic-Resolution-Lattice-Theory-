import E213.Lib.Math.Cohomology.Cup.Core
import E213.Lib.Math.Cohomology.Cochain.Core

/-!
# Cohomology — exact Grade-4 truncation of cup-power

The Δ⁴ cohomology ring is graded `0..4` (with a trivial top
`Cochain 5 5 = Fin 1 → Bool` and *empty* `Cochain 5 n` for `n ≥ 6`,
since `binom 5 n = 0`).

This file establishes the **structural truncation**: the `n`-fold
cup-power of a 1-cochain `α : Cochain 5 1` lives in `Cochain 5 n`,
which for `n ≥ 6` is the empty function `Fin 0 → Bool` — pointwise
provably zero.

There is no "convergence" or "modulus" here: the tail is *exactly*
zero by dimensional bound, recovered as a `False.elim` from
`i.isLt < binom 5 n = 0`.

This is the 213-native replacement for the deferred "Cauchy
convergence modulus" in the Probability extension's open follow-ups.
-/

namespace E213.Lib.Math.Cohomology.Bridge.CutExpFiniteTruncation

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Cup.Core (cup)
open E213.Lib.Physics.Simplex.Counts (binom)

/-- All-true cochain at top grade 0 (the "1" of the cohomology ring). -/
def one_5 : Cochain 5 0 := fun _ => true

/-- n-fold cup-power of a 1-cochain `α`.  Lives in `Cochain 5 n`. -/
def cupPow (α : Cochain 5 1) : (n : Nat) → Cochain 5 n
  | 0 => one_5
  | n + 1 => cup 5 n 1 (cupPow α n) α

/-- `binom 5 6 = 0` — the Grade-6 hard wall in Δ⁴.  Externally
    consumed by `Bridge/CutLog` and `ParadigmDomainGradedRing`. -/
theorem binom_5_6_zero : binom 5 6 = 0 := by decide

/-- ★ **Grade-6 nilpotency** ★ — `cupPow α 6 i` is provably `false`
    *pointwise*, because `i : Fin (binom 5 6) = Fin 0` is empty.
    Externally consumed by `Probability/Foundation/Capstone`. -/
theorem cupPow_grade_6_zero (α : Cochain 5 1) (i : Fin (binom 5 6)) :
    cupPow α 6 i = false :=
  False.elim (Nat.not_lt_zero i.val
    (Nat.lt_of_lt_of_eq i.isLt binom_5_6_zero))

/-- ★★ **General overflow nilpotency** ★★ — for *any* `n` with
    `binom 5 n = 0`, `cupPow α n` is the unique empty function
    (provably `false` at every index, vacuously).  Externally
    consumed by `Bridge/CutLog`. -/
theorem cupPow_zero_of_binom_zero (α : Cochain 5 1) (n : Nat)
    (h : binom 5 n = 0) (i : Fin (binom 5 n)) :
    cupPow α n i = false :=
  False.elim (Nat.not_lt_zero i.val (Nat.lt_of_lt_of_eq i.isLt h))

/-- ★ Truncation master — bundles the Δ⁴ grade-dim table
    (n = 0..5 non-trivial, n ≥ 6 vanishing) and grade-7/8 nilpotency
    (further overflow witnesses).

    The Grade-4 wall in Δ⁴ doesn't fully kick in until Grade 6
    (`Cochain 5 5 = Fin 1 → Bool` is non-trivial: the unique top
    form on Δ⁴).  Anything strictly above grade 5 is empty —
    *exact* truncation, no Cauchy modulus. -/
theorem truncation_master :
    -- Full grade-dim table for Δ⁴: n = 0..6
    binom 5 0 = 1 ∧ binom 5 1 = 5 ∧ binom 5 2 = 10
    ∧ binom 5 3 = 10 ∧ binom 5 4 = 5 ∧ binom 5 5 = 1
    ∧ binom 5 6 = 0
    -- Higher overflow zeros (grade 7, 8)
    ∧ binom 5 7 = 0 ∧ binom 5 8 = 0
    -- Pointwise nilpotency at grade 7, 8 (vacuous Fin 0)
    ∧ (∀ (α : Cochain 5 1) (i : Fin (binom 5 7)), cupPow α 7 i = false)
    ∧ (∀ (α : Cochain 5 1) (i : Fin (binom 5 8)), cupPow α 8 i = false) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | decide
    | (intro α i
       exact False.elim (Nat.not_lt_zero i.val
         (Nat.lt_of_lt_of_eq i.isLt (by decide))))

end E213.Lib.Math.Cohomology.Bridge.CutExpFiniteTruncation
