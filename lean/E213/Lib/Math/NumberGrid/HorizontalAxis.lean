import E213.Lib.Math.NumberGrid.FSMGradeTaxonomy

/-!
# Horizontal Axis — Number Type Predicates (∅-axiom)

The horizontal axis of the number-system grid: classification of
cuts by FSM-recognizability grade, mapping to traditional number
type names.

| Grade | FSM States | Number Type Name |
|---|---|---|
| 0 | 1 (constant) | ℕ-like (terminating) |
| 1 | 5 | mod-5 patterns |
| 2 | 25 | mod-25 patterns (rational with small denom) |
| 3 | 125 | mod-125 patterns |
| ... | ... | ... |
| ~10 | 5^10 ≈ 10⁷ | finite-state rationals |
| ~15 | 5^15 ≈ 3·10¹⁰ | algebraic with small minimal poly |
| ~20 | 5^20 ≈ 10¹⁴ | high-grade algebraic |
| 25 | 5²⁵ = N_U | maximum on d=5 substrate |
| 26+ | beyond N_U | structurally absent |

213-native: traditional number-type names (ℕ, ℤ, ℚ, algebraic, ℝ)
correspond to *intervals* of FSM grades, not individual grades.
-/

namespace E213.Lib.Math.NumberGrid.HorizontalAxis

open E213.Lib.Math.NumberGrid.FSMGradeTaxonomy
  (fsmGradeStates grade_0_states grade_1_states grade_25_states)

/-- Number type name corresponding to grade range. -/
inductive NumberType where
  | natural        -- grade 0 (constant cuts)
  | integer        -- grade 0-1 (sign-extension)
  | rational       -- grade 2..~12 (eventually periodic)
  | algebraic      -- grade ~13..~24 (algebraic minimal poly)
  | substrateMax   -- grade 25 = N_U

/-- ★ Map a grade to its number-type classification. -/
def gradeToType (j : Nat) : NumberType :=
  if j = 0 then NumberType.natural
  else if j ≤ 1 then NumberType.integer
  else if j ≤ 12 then NumberType.rational
  else if j ≤ 24 then NumberType.algebraic
  else NumberType.substrateMax

/-- ★ Grade 0 → natural. -/
theorem grade0_natural : gradeToType 0 = NumberType.natural := rfl

/-- ★ Grade 1 → integer. -/
theorem grade1_integer : gradeToType 1 = NumberType.integer := rfl

/-- ★ Grade 5 → rational. -/
theorem grade5_rational : gradeToType 5 = NumberType.rational := rfl

/-- ★ Grade 20 → algebraic. -/
theorem grade20_algebraic :
    gradeToType 20 = NumberType.algebraic := rfl

/-- ★ Grade 25 → substrate maximum. -/
theorem grade25_substrate :
    gradeToType 25 = NumberType.substrateMax := rfl

/-- ★ Grade-25 cardinality matches substrate ceiling N_U. -/
theorem grade25_cardinality :
    fsmGradeStates 25 = 298023223876953125 := grade_25_states

end E213.Lib.Math.NumberGrid.HorizontalAxis
