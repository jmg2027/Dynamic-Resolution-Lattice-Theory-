/-!
# Type A residual closed form — pure dyadic recurrence

Empirical discovery (Rust probe + recurrence search,):

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

namespace E213.Lib.Math.Algebra.CayleyDickson.Misc.TypeAResidualClosedForm

/-- Closed form for Type A residual numerator at L_{n+5}. -/
def closed_form (n : Nat) : Int := 56 * (4 : Int)^n - 14 * (2 : Int)^n + 1

/-- ★ closed_form agrees with the per-layer computed numerators for n = 0..4. -/
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

/-- ★ Extended decide check (n = 5..7). -/
theorem closed_form_recurrence_extended :
    closed_form 5 = 6 * closed_form 4 - 8 * closed_form 3 + 3 ∧
    closed_form 6 = 6 * closed_form 5 - 8 * closed_form 4 + 3 ∧
    closed_form 7 = 6 * closed_form 6 - 8 * closed_form 5 + 3 := by decide

/-- ★★★ Recurrence-defined version. ∅-axiom by `rfl`, no `ring` needed.

    Strategy: define the recurrence as the function definition itself.
    Then the recurrence theorem holds trivially.  Equivalence to the
    algebraic closed_form is verified pointwise via decide (finite n). -/
def rec_form : Nat → Int
  | 0     => 43
  | 1     => 197
  | n + 2 => 6 * rec_form (n + 1) - 8 * rec_form n + 3

/-- ★ The 2nd-order linear recurrence holds for all n by definition. -/
theorem rec_form_recurrence_general (n : Nat) :
    rec_form (n + 2) = 6 * rec_form (n + 1) - 8 * rec_form n + 3 := rfl

/-- ★ rec_form matches the algebraic closed form for n = 0..4. -/
theorem rec_form_matches_closed_form :
    rec_form 0 = closed_form 0 ∧
    rec_form 1 = closed_form 1 ∧
    rec_form 2 = closed_form 2 ∧
    rec_form 3 = closed_form 3 ∧
    rec_form 4 = closed_form 4 := by decide

/-- ★ rec_form matches measured residual numerators (n = 0..4). -/
theorem rec_form_matches_measured :
    rec_form 0 = 43 ∧ rec_form 1 = 197 ∧ rec_form 2 = 841 ∧
    rec_form 3 = 3473 ∧ rec_form 4 = 14113 := by decide

end E213.Lib.Math.Algebra.CayleyDickson.Misc.TypeAResidualClosedForm
