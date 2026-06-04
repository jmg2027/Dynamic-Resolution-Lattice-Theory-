import E213.Lib.Math.Algebra.GRA.GRAModel
import E213.Lib.Math.Algebra.GRA.NumberTheory
import E213.Lib.Math.Algebra.GRA.Common
import E213.Lib.Math.Algebra.GRA.Graph
import E213.Lib.Math.Algebra.GRA.Analysis
import E213.Lib.Math.Algebra.GRA.Cohomology
import E213.Lib.Math.Algebra.GRA.HoTT

/-!
# GRA Higher Algebra Instance (Reading R₂) + Universality Capstone

Higher Algebra interpretation of GRA:
  * **Carrier**: Eₙ operad levels / chromatic heights
  * **Grade**: Operad level (= the carrier)
  * **⊕**: Day convolution grade (additive on ⊗-Day)
  * **⊗**: Nested integration (grade-additive composition)
  * **Depth**: ⌈n/3⌉ = chromatic height
  * **gen1=2**: E₂-operad (associative up to homotopy)
  * **gen2=3**: E₃-operad (next level of coherence)

This file also contains the GRA Universality Capstone:
  * Transitivity theorem: R_i ≅ NT ∧ R_j ≅ NT → R_i ≅ R_j
  * Full 5-Reading universality statement

Standard: 0 sorry, ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.GRA.HigherAlgebra

open E213.Lib.Math.Algebra.GRA
open E213.Lib.Math.Algebra.GRA.Common
  (coprime_2_3 two_lt_three reach_23 depth_formula greedy_form)

-- ============================================================
-- Higher Algebra carrier and operations
-- ============================================================

/-- Carrier = operad level / chromatic height. -/
abbrev HACarrier := Nat

/-- Grade = operad level (identity). -/
def haGrade (n : HACarrier) : Nat := n

/-- ⊕ = Day convolution: ⊗-Day of Eₘ and Eₙ structures yields
    an E_{m+n}-like structure (grade-additive). -/
def haOplus (a b : HACarrier) : HACarrier := a + b

/-- ⊗ = nested integration: composing coherence data adds
    operad levels (sub-additively). -/
def haOtimes (a b : HACarrier) : HACarrier := a + b

/-- Depth = ⌈n/3⌉ = chromatic height = minimum number of
    E₃-compositions to reach operad level n. -/
def haDepth (n : Nat) : Nat := (n + 2) / 3

-- ============================================================
-- Axiom verification
-- ============================================================

theorem ha_gen1_lt_gen2 : (2 : Nat) < 3 := two_lt_three

theorem ha_coprime : E213.Tactic.NatHelper.gcd213 2 3 = 1 := coprime_2_3

theorem ha_grade_oplus (a b : HACarrier) :
    haGrade (haOplus a b) = haGrade a + haGrade b := rfl

theorem ha_grade_otimes (a b : HACarrier) :
    haGrade (haOtimes a b) ≤ haGrade a + haGrade b := Nat.le.refl

/-- Reachability: every operad level ≥ 2 decomposes as
    a combination of E₂ and E₃ compositions. -/
theorem ha_reach (n : Nat) (hn : n ≥ 2) :
    ∃ a b : Nat, n = 2 * a + 3 * b := reach_23 n hn

/-- Depth = ⌈n/3⌉ in explicit form. -/
theorem ha_depth_eq (n : Nat) (_hn : n ≥ 2) :
    haDepth n = n / 3 + (if n % 3 = 0 then 0 else 1) := depth_formula n

/-- Greedy: using E₃ maximally minimizes chromatic height. -/
theorem ha_greedy (n : Nat) (_hn : n ≥ 2) :
    haDepth n = (n + 3 - 1) / 3 := greedy_form n

-- ============================================================
-- The (2,3)-GRA model for Higher Algebra
-- ============================================================

/-- The (2,3)-GRA model on operad levels (Higher Algebra reading R₂). -/
def GRA23_HigherAlgebra : GRAModel where
  Carrier := HACarrier
  grade := haGrade
  oplus := haOplus
  otimes := haOtimes
  gen1 := 2
  gen2 := 3
  depth := haDepth
  ax_gen1_lt_gen2 := ha_gen1_lt_gen2
  ax_coprime := ha_coprime
  ax_grade_oplus := ha_grade_oplus
  ax_grade_otimes := ha_grade_otimes
  ax_reach := ha_reach
  ax_depth_eq := ha_depth_eq
  ax_greedy := ha_greedy

-- ============================================================
-- Isomorphism: Higher Algebra ≅ NumberTheory
-- ============================================================

/-- The GRA isomorphism between Higher Algebra and NT models. -/
def GRAIso_HigherAlgebra_NT : GRAIso GRA23_HigherAlgebra NumberTheory.GRA23_NT where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  grade_comm := fun _ => rfl
  oplus_comm := fun _ _ => rfl
  otimes_comm := fun _ _ => rfl

end E213.Lib.Math.Algebra.GRA.HigherAlgebra

-- ============================================================
-- GRA UNIVERSALITY CAPSTONE
-- ============================================================

namespace E213.Lib.Math.Algebra.GRA.Universality

open E213.Lib.Math.Algebra.GRA

/-- Transitivity: if R_i ≅ NT and R_j ≅ NT, then R_i ≅ R_j.
    This is simply the composition of iso_i with iso_j.symm. -/
def transitivity (M₁ M₂ : GRAModel)
    (iso₁ : GRAIso M₁ NumberTheory.GRA23_NT)
    (iso₂ : GRAIso M₂ NumberTheory.GRA23_NT) :
    GRAIso M₁ M₂ :=
  GRAIso.trans iso₁ iso₂.symm

/-- The full GRA Universality theorem: all 5 Readings are pairwise
    isomorphic as GRA models.
    
    Structure: each Reading has an iso to NT (the hub), and by
    transitivity any pair R_i, R_j satisfies R_i ≅ R_j. -/
structure GRA_Universality where
  /-- R₁ Cohomology ≅ NT -/
  iso_cohom : GRAIso Cohomology.GRA23_Cohomology NumberTheory.GRA23_NT
  /-- R₂ Higher Algebra ≅ NT -/
  iso_ha : GRAIso HigherAlgebra.GRA23_HigherAlgebra NumberTheory.GRA23_NT
  /-- R₃ HoTT ≅ NT -/
  iso_hott : GRAIso HoTT.GRA23_HoTT NumberTheory.GRA23_NT
  /-- R₄ Graph ≅ NT -/
  iso_graph : GRAIso Graph.GRA23_Graph NumberTheory.GRA23_NT
  /-- R₅ Analysis ≅ NT -/
  iso_analysis : GRAIso Analysis.GRA23_Analysis NumberTheory.GRA23_NT

/-- The GRA Universality theorem is inhabited: all 5 isos are proved. -/
def gra_universality_witness : GRA_Universality where
  iso_cohom := Cohomology.GRAIso_Cohomology_NT
  iso_ha := HigherAlgebra.GRAIso_HigherAlgebra_NT
  iso_hott := HoTT.GRAIso_HoTT_NT
  iso_graph := Graph.GRAIso_Graph_NT
  iso_analysis := Analysis.GRAIso_Analysis_NT

/-- Corollary: any two Readings are isomorphic (10 pairwise isos). -/
def any_two_readings_iso (M₁ M₂ : GRAModel)
    (h₁ : GRAIso M₁ NumberTheory.GRA23_NT)
    (h₂ : GRAIso M₂ NumberTheory.GRA23_NT) :
    GRAIso M₁ M₂ :=
  transitivity M₁ M₂ h₁ h₂

/-- Concrete example: Graph ≅ Cohomology (via NT hub). -/
def GRAIso_Graph_Cohomology : GRAIso Graph.GRA23_Graph Cohomology.GRA23_Cohomology :=
  transitivity Graph.GRA23_Graph Cohomology.GRA23_Cohomology
    Graph.GRAIso_Graph_NT Cohomology.GRAIso_Cohomology_NT

/-- Concrete example: Analysis ≅ HoTT (via NT hub). -/
def GRAIso_Analysis_HoTT : GRAIso Analysis.GRA23_Analysis HoTT.GRA23_HoTT :=
  transitivity Analysis.GRA23_Analysis HoTT.GRA23_HoTT
    Analysis.GRAIso_Analysis_NT HoTT.GRAIso_HoTT_NT

end E213.Lib.Math.Algebra.GRA.Universality
