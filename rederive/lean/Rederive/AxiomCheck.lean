/-
Rederive/AxiomCheck.lean — the zero-axiom contract, machine-checked.

Every theorem in the package is listed; every `#print axioms` line must
report "does not depend on any axioms".  Any non-empty output (propext,
Quot.sound, Classical.choice, …) is a contract violation.
-/

import Rederive.Tree
import Rederive.Object1
import Rederive.Grading

namespace Rederive

-- Tree.lean
#print axioms Tree.a_ne_b
#print axioms Tree.cmp_refl
#print axioms Tree.eq_of_cmp_eq
#print axioms Tree.cmp_oswap
#print axioms Tree.cmp_gt_of_lt
#print axioms Tree.cmp_lt_of_gt
#print axioms Tree.cmp_lt_or_gt_of_ne
#print axioms Tree.pairing_of_lt
#print axioms Tree.pairing_of_gt
#print axioms Tree.pairing_comm
#print axioms Tree.pairing_inj
#print axioms Tree.pairing_ne
#print axioms Tree.children_pairing
#print axioms Tree.pairing_ne_a
#print axioms Tree.pairing_ne_b

-- Object1.lean
#print axioms Tree.beq_refl
#print axioms Tree.eq_of_beq
#print axioms Tree.beq_eq_false_of_ne
#print axioms Tree.decEq
#print axioms object1_self
#print axioms object1_eq_true_iff
#print axioms object1_eq_false_of_ne
#print axioms object1_injective_ext
#print axioms object1_injective
#print axioms diag_ne
#print axioms object1_not_surjective
#print axioms diag_object1_eq_false
#print axioms inImageExt_of_eq
#print axioms inImageExt_iff_uniqueIndicator
#print axioms constFalse_not_inImageExt
#print axioms constFalse_ne_object1
#print axioms constTrue_not_inImageExt
#print axioms constTrue_ne_object1
#print axioms twoIndicator_not_inImageExt
#print axioms twoIndicator_ne_object1

-- Grading.lean — Nat mini-toolkit
#print axioms le_maxN_left
#print axioms le_maxN_right
#print axioms maxN_le
#print axioms zero_addN
#print axioms succ_addN
#print axioms add_left_cancelN

-- Grading.lean — folds
#print axioms Tree.and_eq_true_split
#print axioms Tree.and_eq_true_join
#print axioms Tree.inGen_iff
#print axioms Tree.gen_eq_depth

-- Grading.lean — fold divergence at level 3
#print axioms Grading.ladder_level2
#print axioms Grading.witness_diverges
#print axioms Grading.gen_witness
#print axioms Grading.reversal
#print axioms Grading.eStar_tree_facts

-- Grading.lean — no-rank theorem (finitized Theorem 4.1)
#print axioms Grading.heightOf_formula
#print axioms Grading.no_rank
#print axioms Grading.no_rank_exists
#print axioms Grading.covers_unit_except
#print axioms Grading.height_jump
#print axioms Grading.height_not_rank

-- Grading.lean — positive half (level-≤2 zone)
#print axioms Grading.height_is_rank_on_Z
#print axioms Grading.rank_on_Z_unique

end Rederive
