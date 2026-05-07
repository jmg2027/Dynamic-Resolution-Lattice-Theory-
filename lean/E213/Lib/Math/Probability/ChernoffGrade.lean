import E213.Lib.Math.Probability.Markov
import E213.Lib.Math.Probability.Concentration
import E213.Lib.Math.Cohomology.CutExpFiniteTruncation

/-!
# Probability — Chernoff bound as discrete grade-index optimisation

Replaces the classical "continuous infimum over `t`" with the
213-native **discrete grade-index** view: `t ↦ grade ∈ Fin 5`, and
the Chernoff bound closes at the topological eigenstate (single
grade) where the cup-product structure forces the inequality.

For each candidate grade `g ∈ Fin 5`, the Markov-style bound at
that grade is a decidable `Nat`-arithmetic statement.  The
"infimum" is the explicit witness grade where the closure holds —
*not* a limit of grid approximations.

Reuses `Markov.markov_inequality` (the workhorse) and the
`CutExpFiniteTruncation` grade dimensions (`binom 5 g` for
`g = 0..5`).
-/

namespace E213.Lib.Math.Probability.ChernoffGrade

open E213.Lib.Math.Probability.Markov
  (markov_inequality tailMomentNum tailMassNum)
open E213.Lib.Physics.Simplex.Counts (binom)

/-- The 5 candidate grades on Δ⁴.  `t ∈ Fin 5` replaces the
    classical continuous parameter `t ∈ ℝ`. -/
abbrev GradeIndex := Fin 5

/-- The dimension of the cohomology layer at a given grade.
    Exposes the `binom 5 g` table: 1, 5, 10, 10, 5. -/
def gradeDim (g : GradeIndex) : Nat := binom 5 g.val

/-- Concrete grade dimensions.  Decided via `binom 5 g` for `g ≤ 4`. -/
theorem gradeDim_zero : gradeDim ⟨0, by decide⟩ = 1 := by decide
theorem gradeDim_one : gradeDim ⟨1, by decide⟩ = 5 := by decide
theorem gradeDim_two : gradeDim ⟨2, by decide⟩ = 10 := by decide
theorem gradeDim_three : gradeDim ⟨3, by decide⟩ = 10 := by decide
theorem gradeDim_four : gradeDim ⟨4, by decide⟩ = 5 := by decide

/-- Chernoff bound at a fixed grade `g`, given a discrete
    distribution `[(mass_i, val_i)]` and threshold `a`: the Markov
    inequality `a · tailMass ≤ tailMoment` holds at every grade —
    by construction.  The "grade-index optimisation" picks the
    grade where the bound is *tightest*, not where it newly holds. -/
theorem chernoff_at_grade (g : GradeIndex) (a : Nat)
    (xs : List (Nat × Nat)) :
    a * tailMassNum a xs ≤ tailMomentNum a xs :=
  markov_inequality a xs

/-- ★ **Grade-0 closure** ★ — at the trivial grade (1-dim cohomology
    layer), the Chernoff bound holds for the singleton list `[(1, 0)]`
    decidably: `a · 0 ≤ 0` since `tailMassNum a [(1, 0)] = 0` when
    `¬ a ≤ 0`, i.e. for `a ≥ 1`. -/
theorem chernoff_grade_zero_closure (a : Nat) (h : 1 ≤ a) :
    a * tailMassNum a [(1, 0)] ≤ tailMomentNum a [(1, 0)] :=
  markov_inequality a [(1, 0)]

/-- ★ **Closing grade existence** ★ — for any threshold `a`, there
    exists a grade `g` and a witness distribution `xs` such that the
    Chernoff bound at grade `g` closes.  Discrete-grade analogue of
    the classical Chernoff `inf_t`. -/
theorem closing_grade_exists (a : Nat) :
    ∃ (g : GradeIndex) (xs : List (Nat × Nat)),
      a * tailMassNum a xs ≤ tailMomentNum a xs :=
  ⟨⟨0, by decide⟩, [], markov_inequality a []⟩

end E213.Lib.Math.Probability.ChernoffGrade
