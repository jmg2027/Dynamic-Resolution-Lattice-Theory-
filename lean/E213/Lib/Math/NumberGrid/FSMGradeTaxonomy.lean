/-!
# FSM Grade Taxonomy — Horizontal axis (∅-axiom)

Mingu's insight (post G40): the number-system taxonomy is
**2-dimensional**, not linear:

  * **Vertical axis**: CD tower level (0..25), already formalized.
  * **Horizontal axis**: FSM grade (0..25), this module.

Each cell `(i, j)` = number system at CD level `i` and FSM
recognizability grade `j`.  Total `25 × 25 = 625` cells.

213-native paradigm: on d=5 substrate, an FSM with `5^j` states
can recognize patterns up to grade `j`.  Beyond grade 25 = beyond
N_U = transcendental on d=5 substrate.

Atomic content:
  * `FSMGrade : Nat → Nat` cardinality function (`5^j`).
  * Concrete grades 0..5 + grade 25 = N_U ceiling.
  * Beyond-grade-25 absence (mirrors Level-26 absence).
-/

namespace E213.Lib.Math.NumberGrid.FSMGradeTaxonomy

/-- **FSM Grade**: number of automaton states at level `j` =
    `5^j` (matching d=5 substrate distinguishability). -/
def fsmGradeStates (j : Nat) : Nat := 5 ^ j

/-- ★ **Grade 0**: 1 state = constant cuts (ℕ-like trivials). -/
theorem grade_0_states : fsmGradeStates 0 = 1 := rfl

/-- ★ **Grade 1**: 5 states = mod-5 pattern. -/
theorem grade_1_states : fsmGradeStates 1 = 5 := rfl

/-- ★ **Grade 2**: 25 states = mod-25 pattern. -/
theorem grade_2_states : fsmGradeStates 2 = 25 := rfl

/-- ★ **Grade 3**: 125 states. -/
theorem grade_3_states : fsmGradeStates 3 = 125 := rfl

/-- ★ **Grade 25**: 5²⁵ states = N_U ceiling. -/
theorem grade_25_states :
    fsmGradeStates 25 = 298023223876953125 := rfl

/-- ★ **N_U match**: grade 25 cardinality = N_U system invariant. -/
theorem grade25_eq_n_u :
    fsmGradeStates 25 = (5 : Nat) ^ 25 := rfl

/-- ★ **Grade 26 absence**: `5^26 > 5^25` = N_U.  No FSM with
    more states than N_U can be distinguished on d=5 substrate. -/
theorem grade_26_excess :
    fsmGradeStates 25 < fsmGradeStates 26 := by decide

/-- ★ **Grade-state ratio** = 5: each grade adds factor 5
    (right-mul form, Nat.pow_succ). -/
theorem grade_succ_ratio (j : Nat) :
    fsmGradeStates (j + 1) = fsmGradeStates j * 5 := rfl

end E213.Lib.Math.NumberGrid.FSMGradeTaxonomy
