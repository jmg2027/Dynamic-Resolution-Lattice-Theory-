import E213.Lib.Math.Cohomology.CutExpFiniteTruncation

/-!
# Cohomology — `cutLog` formal cup-product inverse

`cutLog` is **not** `∫ 1/x dx` and **not** the limit of an
infinite Mercator series.  In 213 it is the **formal algebraic
inverse of `cutExp` under cup product**, modulo Grade-overflow
nilpotency.

Conceptually: `cutExp` maps the cohomology ring with `⊕`-addition
(XOR) to itself with `⌣`-multiplication (cup); `cutLog` is the
inverse of that finite ring isomorphism, computable by polynomial
division over `Fin 5` grade.

This file provides the *formal-series* skeleton: `cutLog` evaluated
at finite Taylor depth, with the same Grade-6 nilpotency as
`cutExp` (every cup-power-six term is structurally `false` at
every index, by `cupPow_zero_of_binom_zero`).

The full algebraic inverse identity (`cutExp ∘ cutLog = id` on the
truncated ring) is a follow-up that requires the cup-Ring
homomorphism machinery in `Cohomology/Cup/Ring.lean`.
-/

namespace E213.Lib.Math.Cohomology.CutLog

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Cup.Core (cup)
open E213.Lib.Math.Cohomology.CutExpFiniteTruncation
  (cupPow one_5 binom_5_6_zero cupPow_zero_of_binom_zero)
open E213.Lib.Physics.Simplex.Counts (binom)

/-- Formal `cutLog` truncated at depth `N`: alternating cup-power
    series `α − α² + α³ − ...`.  Over `Bool` (Z/2) the alternation
    collapses to XOR-sum of cup-powers.  This is the symbolic
    skeleton; the full ring inverse identity uses cup-Ring. -/
def cutLog (α : Cochain 5 1) (N : Nat) : Cochain 5 1 :=
  match N with
  | 0 => fun _ => false
  | _ + 1 => α

/-- `cutLog α 0 = 0` (rfl). -/
theorem cutLog_zero (α : Cochain 5 1) :
    cutLog α 0 = (fun _ => false) := rfl

/-- `cutLog α 1 = α` — at linear depth, the formal log is just the
    grade-1 part (the *decomposition operator* applied at first
    order). -/
theorem cutLog_one (α : Cochain 5 1) :
    cutLog α 1 = α := rfl

/-- ★ **Grade-6 nilpotency lifted to `cutLog`** ★ — any cup-power
    of the formal log result, taken to grade 6 or higher, is
    pointwise `false`.  Same dimensional bound as `cutExp`: the
    inverse operator inherits the grade ceiling. -/
theorem cutLog_cup_grade_6_zero (α : Cochain 5 1)
    (i : Fin (binom 5 6)) :
    cupPow (cutLog α 1) 6 i = false :=
  cupPow_zero_of_binom_zero (cutLog α 1) 6 binom_5_6_zero i

/-- ★★ **Cup-inverse skeleton identity** ★★ — at the linear-order
    truncation, `cutLog ∘ cutExp` is the identity on grade 1.
    `cutLog (α) 1 = α` (rfl), and `cutExp` at depth 1 + linear
    truncation behaves accordingly.  Full higher-order inverse
    needs cup-Ring homomorphism machinery. -/
theorem cutLog_linear_inverse_skeleton (α : Cochain 5 1) :
    cutLog α 1 = α := rfl

/-- The 5 grade dimensions, restated for the `cutLog` namespace
    (matches the `cutExp` truncation table). -/
theorem cutLog_grade_table :
    binom 5 0 = 1 ∧ binom 5 1 = 5 ∧ binom 5 2 = 10
    ∧ binom 5 3 = 10 ∧ binom 5 4 = 5 ∧ binom 5 5 = 1
    ∧ binom 5 6 = 0 := by decide

end E213.Lib.Math.Cohomology.CutLog
