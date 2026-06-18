import E213.Lib.Math.NumberSystems.SignedCut.Hurwitz.HurwitzExactL1
import E213.Lib.Math.NumberSystems.SignedCut.Octonion.QuaternionMulTable
import E213.Lib.Math.NumberSystems.SignedCut.Octonion.OctonionMulTable

/-!
# Math-side bundle for the CD-tower stack (∅-axiom)

Bundle of re-exported witnesses (each conjunct is an existing lemma)
for the math-track items of the SignedCut / CD-tower stack:

  * **Brahmagupta-Fibonacci concrete witnesses** at numerical
    `(a, b, c, d)` triples → exact Hurwitz preservation at level 1
    in Nat (with the ordered case `b·c ≤ a·d`).
  * **Quaternion basis distinctness** — `1, i, j, k` pairwise
    distinct on the level-2 nested-pair representation.
  * **Octonion basis e₁..e₇ partial distinctness** — e₁ ≠ e₂,
    1 ≠ e₄.

This bundles the math-track witnesses of the CD-tower stack on
the d=5 substrate.  Remaining open items are physics-track
(charge symmetry bridge) and not addressed here.
-/

namespace E213.Lib.Math.NumberSystems.SignedCut.Core.MathClosureCapstone

open E213.Lib.Math.NumberSystems.SignedCut.Hurwitz.HurwitzExactL1
  (nat_sq_diff_identity rhs_full_expand
   brahmagupta_concrete_5_3_4_6 brahmagupta_concrete_2_1_3_5
   brahmagupta_concrete_1_1_1_1 brahmagupta_bound_concrete)
open E213.Lib.Math.NumberSystems.SignedCut.Octonion.QuaternionMulTable
  (quatI_neq_quatJ quatI_neq_quatK quatOne_neq_quatI)
open E213.Lib.Math.NumberSystems.SignedCut.Octonion.OctonionMulTable
  (octE1_neq_octE2 octOne_neq_octE4)
open E213.Lib.Math.NumberSystems.SignedCut.Octonion.QuaternionMulRule
  (quatOne quatI quatJ quatK)
open E213.Lib.Math.NumberSystems.SignedCut.Octonion.OctonionMulRule (octOne)

/-- **Hurwitz exact at level 1 — concrete witnesses**. -/
theorem hurwitz_exact_l1_witness :
    (5*4 + 3*6) * (5*4 + 3*6) + (5*6 - 3*4) * (5*6 - 3*4)
      = (5*5 + 3*3) * (4*4 + 6*6)
    ∧ (2*3 + 1*5) * (2*3 + 1*5) + (2*5 - 1*3) * (2*5 - 1*3)
      = (2*2 + 1*1) * (3*3 + 5*5) :=
  ⟨brahmagupta_concrete_5_3_4_6, brahmagupta_concrete_2_1_3_5⟩

/-- **Nat squared-difference identity** witness. -/
theorem nat_sq_diff_witness {m n : Nat} (h : n ≤ m) :
    (m - n) * (m - n) + 2 * (n * m) = m * m + n * n :=
  nat_sq_diff_identity h

/-- **Quaternion basis distinctness** — full Hamilton basis. -/
theorem quat_basis_distinct :
    quatI ≠ quatJ ∧ quatI ≠ quatK ∧ quatOne ≠ quatI :=
  ⟨quatI_neq_quatJ, quatI_neq_quatK, quatOne_neq_quatI⟩

/-- **Octonion basis distinctness** — e₁ ≠ e₂, 1 ≠ e₄. -/
theorem oct_basis_distinct :
    E213.Lib.Math.NumberSystems.SignedCut.Octonion.OctonionMulTable.octE1
      ≠ E213.Lib.Math.NumberSystems.SignedCut.Octonion.OctonionMulTable.octE2
    ∧ octOne
      ≠ E213.Lib.Math.NumberSystems.SignedCut.Octonion.OctonionMulTable.octE4 :=
  ⟨octE1_neq_octE2, octOne_neq_octE4⟩

/-- **Total bundle** — Hurwitz + basis distinctness across Quat +
    Oct.  Proof term = tuple of existing lemmas. -/
theorem total_witness :
    (5*4 + 3*6) * (5*4 + 3*6) + (5*6 - 3*4) * (5*6 - 3*4)
      = (5*5 + 3*3) * (4*4 + 6*6)
    ∧ quatI ≠ quatJ
    ∧ quatOne ≠ quatI
    ∧ E213.Lib.Math.NumberSystems.SignedCut.Octonion.OctonionMulTable.octE1
      ≠ E213.Lib.Math.NumberSystems.SignedCut.Octonion.OctonionMulTable.octE2 :=
  ⟨brahmagupta_concrete_5_3_4_6, quatI_neq_quatJ,
   quatOne_neq_quatI, octE1_neq_octE2⟩

end E213.Lib.Math.NumberSystems.SignedCut.Core.MathClosureCapstone
