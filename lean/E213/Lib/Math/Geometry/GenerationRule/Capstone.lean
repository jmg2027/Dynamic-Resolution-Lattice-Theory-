import E213.Lib.Math.Geometry.GenerationRule.TriangleIteration
import E213.Lib.Math.Geometry.GenerationRule.GenerationCount
import E213.Lib.Math.Geometry.GenerationRule.OrthogonalDirection

/-!
# G46 Capstone — Generation Rule + Triangle Iteration (∅-axiom)

5 cluster witnesses + total bundle.

Three Mingu questions answered:
  1. `(2+3)²⁵`: 25 = orthogonal direction, 2/3 = binary choice
     per level (NOT separate axes).
  2. C(N_S, N_T) = C(3, 2) = 3 = SM generation count
     (already in `Counts.lean`).
  3. Triangle iteration `a_{n+1} = C(a_n, 2) + a_n = T(a_n)`
     starting from 2 generates 2, 3, 6, 21, 231, ... — first
     two terms are (N_T, N_S) = (2, 3) atomicity.
-/

namespace E213.Lib.Math.Geometry.GenerationRule.Capstone

open E213.Lib.Math.Geometry.GenerationRule.TriangleIteration
  (T triIter T_two T_three T_six T_twentyone
   triIter_2_0 triIter_2_1 triIter_2_2 atomicity_first_two)
open E213.Lib.Math.Geometry.GenerationRule.GenerationCount
  (binom binom_3_2 generation_count_witness no_4th_generation
   total_exterior)
open E213.Lib.Math.Geometry.GenerationRule.OrthogonalDirection
  (binomial_orthogonal_direction total_partitions
   partition_contribution_endpoints generation_count_match)

/-- ★ **Triangle iteration from 2** generates (2, 3, 6, 21, 231). -/
theorem triangle_iter_witness :
    triIter 2 0 = 2
    ∧ triIter 2 1 = 3
    ∧ triIter 2 2 = 6
    ∧ T 21 = 231 :=
  ⟨triIter_2_0, triIter_2_1, triIter_2_2, T_twentyone⟩

/-- ★ **Atomicity = first two terms**: (N_T, N_S) = (2, 3). -/
theorem atomicity_witness : triIter 2 0 = 2 ∧ triIter 2 1 = 3 :=
  atomicity_first_two

/-- ★ **C(3, 2) = 3 = SM generation count**. -/
theorem generation_witness :
    binom 3 2 = 3
    ∧ binom 4 2 = 6 :=
  ⟨binom_3_2, no_4th_generation.1⟩

/-- ★ **(2+3)²⁵ orthogonal direction witness**. -/
theorem orthogonal_witness :
    ((3 : Nat) + 2) ^ 25 = (5 : Nat) ^ 25
    ∧ (2 : Nat) ^ 25 = 33554432 :=
  ⟨binomial_orthogonal_direction, total_partitions⟩

/-- ★★★ **Total witness** ★★★ — triangle iteration + generation
    count + orthogonal direction. -/
theorem total_witness :
    triIter 2 1 = 3
    ∧ binom 3 2 = 3
    ∧ ((3 : Nat) + 2) ^ 25 = (5 : Nat) ^ 25
    ∧ binom 5 0 + binom 5 1 + binom 5 2 + binom 5 3
        + binom 5 4 + binom 5 5 = 32 :=
  ⟨triIter_2_1, binom_3_2, binomial_orthogonal_direction,
   total_exterior⟩

end E213.Lib.Math.Geometry.GenerationRule.Capstone
