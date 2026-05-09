/-!
# Type A residual closed form — pure dyadic recurrence

Empirical discovery (Rust probe + recurrence search, 2026-05-09):

Type A (ZI base, rank 0) Moufang fail rate residuals from asymptote
1/2, expressed as integer numerators a_n with denominator 2^(3n+7):

  L5: 43,  L6: 197,  L7: 841,  L8: 3473,  L9: 14113

These satisfy the **2nd-order linear inhomogeneous recurrence**:

  a_{n+2} = 6·a_{n+1} − 8·a_n + 3

Characteristic polynomial: x² − 6x + 8 = (x−2)(x−4). Eigenvalues 2, 4
(pure powers of 2 — no irrationals, no Pell/Fibonacci).

Closed form:  a_n = 56·4^n − 14·2^n + 1.

This pins the recurrence as ∅-axiom Lean theorems for finite n.
-/

namespace E213.Lib.Math.CayleyDickson.TypeAResidualClosedForm

/-- Closed form for Type A residual numerator at L_{n+5}. -/
def closed_form (n : Nat) : Int := 56 * (4 : Int)^n - 14 * (2 : Int)^n + 1

/-- ★ closed_form matches measured values for n = 0..4. -/
theorem closed_form_match :
    closed_form 0 = 43 ∧
    closed_form 1 = 197 ∧
    closed_form 2 = 841 ∧
    closed_form 3 = 3473 ∧
    closed_form 4 = 14113 := by decide

/-- ★ The 2nd-order linear recurrence holds for the closed form (n = 0..2). -/
theorem closed_form_recurrence_check :
    closed_form 2 = 6 * closed_form 1 - 8 * closed_form 0 + 3 ∧
    closed_form 3 = 6 * closed_form 2 - 8 * closed_form 1 + 3 ∧
    closed_form 4 = 6 * closed_form 3 - 8 * closed_form 2 + 3 := by decide

/-- ★ The recurrence holds for n = 0..3 (via decide).
    General-n proof requires Mathlib's `ring` tactic; here we keep
    finite-n verification, which is still ∅-axiom decidable. -/
theorem closed_form_recurrence_extended :
    closed_form 5 = 6 * closed_form 4 - 8 * closed_form 3 + 3 ∧
    closed_form 6 = 6 * closed_form 5 - 8 * closed_form 4 + 3 ∧
    closed_form 7 = 6 * closed_form 6 - 8 * closed_form 5 + 3 := by decide

end E213.Lib.Math.CayleyDickson.TypeAResidualClosedForm
