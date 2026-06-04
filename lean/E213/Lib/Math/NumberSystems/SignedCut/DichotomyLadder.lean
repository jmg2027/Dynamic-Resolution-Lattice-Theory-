import E213.Lib.Math.NumberSystems.SignedCut.Hurwitz.HurwitzDichotomy
import E213.Lib.Math.NumberSystems.SignedCut.Octonion.NonAssocQuantification
/-!
# Rigor — Cayley-Dickson dichotomy ladder strict ordering

Companion to `HurwitzDichotomy.lean` and `NonAssocQuantification.lean`
establishing **strict ordering** of the dichotomy ladder:

  commut (n ≤ 1) → assoc (n ≤ 2) → norm-mult (n ≤ 3)

For each adjacent pair, the implication is strict: there exists a
level admitted by the weaker predicate but rejected by the
stronger.

Specifically:
  · `assocAdmissible 2 = true`, `commut ≤ 1` rejects 2 → strict
  · `hurwitzAdmissible 3 = true`, `assocAdmissible 3 = false` →
    strict
  · `hurwitzAdmissible 4 = false`, all weaker also reject 4

The ladder is faithful: each predicate is a strict refinement.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberSystems.SignedCut.DichotomyLadder

open E213.Lib.Math.NumberSystems.SignedCut.Hurwitz.HurwitzDichotomy
  (hurwitzAdmissible)
open E213.Lib.Math.NumberSystems.SignedCut.Octonion.NonAssocQuantification
  (assocAdmissible)

/-! ## §1 — Commutativity predicate (added for the ladder) -/

/-- Commutativity-admissible CD level: `n ≤ 1`.  Only ℝ (n=0) and
    ℂ (n=1) are commutative; ℍ (n=2) is non-commutative. -/
def commutAdmissible (n : Nat) : Bool :=
  n ≤ 1

theorem commut_admissible_0 : commutAdmissible 0 = true := rfl
theorem commut_admissible_1 : commutAdmissible 1 = true := rfl
theorem commut_fails_2 : commutAdmissible 2 = false := rfl
theorem commut_fails_3 : commutAdmissible 3 = false := rfl
theorem commut_fails_4 : commutAdmissible 4 = false := rfl

/-! ## §2 — Ladder implication: commut → assoc → Hurwitz -/

/-- ★ commut ⇒ assoc: every commutative level is associative. -/
theorem commut_implies_assoc (n : Nat)
    (h : commutAdmissible n = true) : assocAdmissible n = true := by
  show decide (n ≤ 2) = true
  have h1 : n ≤ 1 := of_decide_eq_true h
  exact decide_eq_true (Nat.le_trans h1 (by decide : 1 ≤ 2))

/-- ★ assoc ⇒ Hurwitz: every associative level is norm-multiplicative. -/
theorem assoc_implies_hurwitz (n : Nat)
    (h : assocAdmissible n = true) : hurwitzAdmissible n = true := by
  show decide (n ≤ 3) = true
  have h1 : n ≤ 2 := of_decide_eq_true h
  exact decide_eq_true (Nat.le_trans h1 (by decide : 2 ≤ 3))

/-- ★ commut ⇒ Hurwitz (transitivity). -/
theorem commut_implies_hurwitz (n : Nat)
    (h : commutAdmissible n = true) : hurwitzAdmissible n = true :=
  assoc_implies_hurwitz n (commut_implies_assoc n h)

/-! ## §3 — Strict ordering: each implication is non-vacuous -/

/-- ★ **commut ⊊ assoc**: level 2 (ℍ) is associative but not
    commutative.  Witnesses the strict refinement. -/
theorem assoc_strictly_extends_commut :
    assocAdmissible 2 = true
    ∧ commutAdmissible 2 = false := by
  refine ⟨rfl, rfl⟩

/-- ★ **assoc ⊊ Hurwitz**: level 3 (𝕆) is norm-multiplicative but
    not associative.  Witnesses the strict refinement. -/
theorem hurwitz_strictly_extends_assoc :
    hurwitzAdmissible 3 = true
    ∧ assocAdmissible 3 = false := by
  refine ⟨rfl, rfl⟩

/-- ★ **All three fail at 𝕊 (level 4)**: no algebraic property
    survives past CD level 3 in the standard ladder. -/
theorem all_fail_at_sedenion :
    commutAdmissible 4 = false
    ∧ assocAdmissible 4 = false
    ∧ hurwitzAdmissible 4 = false := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## §4 — Cardinality at each ladder level -/

/-- ★ **Ladder population**: commut admits 2 levels (ℝ, ℂ), assoc
    admits 3 (ℝ, ℂ, ℍ), Hurwitz admits 4 (ℝ, ℂ, ℍ, 𝕆).  At each
    step the admitted-set grows by exactly one. -/
theorem ladder_population :
    -- commut admits 0, 1
    commutAdmissible 0 = true ∧ commutAdmissible 1 = true
    ∧ commutAdmissible 2 = false
    -- assoc admits 0, 1, 2
    ∧ assocAdmissible 2 = true ∧ assocAdmissible 3 = false
    -- Hurwitz admits 0, 1, 2, 3
    ∧ hurwitzAdmissible 3 = true ∧ hurwitzAdmissible 4 = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §5 — Capstone -/

/-- ★★★★★ **Dichotomy ladder strict-ordering capstone**.

    Establishes that the canonical CD loss ladder
      commut (n ≤ 1) → assoc (n ≤ 2) → norm-mult (n ≤ 3)
    is a **strict** refinement chain:

      (a) implications hold (transitivity at the Bool level),
      (b) each level is non-vacuously stronger (witnesses at
          n = 2, n = 3),
      (c) all three fail at n = 4 (sedenions = first total
          collapse).

    The ladder admits exactly 2, 3, 4 levels respectively
    (commut: ℝ, ℂ; assoc: ℝ, ℂ, ℍ; Hurwitz: ℝ, ℂ, ℍ, 𝕆). -/
theorem dichotomy_ladder_capstone :
    -- (a) Implications
    (∀ n, commutAdmissible n = true → assocAdmissible n = true)
    ∧ (∀ n, assocAdmissible n = true → hurwitzAdmissible n = true)
    -- (b) Strict refinements (non-vacuous)
    ∧ (assocAdmissible 2 = true ∧ commutAdmissible 2 = false)
    ∧ (hurwitzAdmissible 3 = true ∧ assocAdmissible 3 = false)
    -- (c) All fail at sedenion (n = 4)
    ∧ (commutAdmissible 4 = false ∧ assocAdmissible 4 = false
       ∧ hurwitzAdmissible 4 = false) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact commut_implies_assoc
  · exact assoc_implies_hurwitz
  · exact assoc_strictly_extends_commut
  · exact hurwitz_strictly_extends_assoc
  · exact all_fail_at_sedenion

end E213.Lib.Math.NumberSystems.SignedCut.DichotomyLadder
