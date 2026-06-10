import E213.Lib.Physics.Symmetry.AutAction
import E213.Lib.Physics.Symmetry.AutEdgeAction
import E213.Lib.Physics.Symmetry.AutEdgeActionGenerators
import E213.Lib.Physics.Symmetry.AutEdgeOrbits
import E213.Lib.Physics.Symmetry.AutKChiral
import E213.Lib.Physics.Symmetry.GluonChannelInterpretation
import E213.Lib.Physics.Symmetry.AutKSemidirectFull
import E213.Lib.Physics.Symmetry.C2_6MixedMatrices
import E213.Lib.Physics.Symmetry.Sym3BlockDiagonal

/-! Spec-as-code entry point for `E213.Lib.Physics.Symmetry`.

  Symmetry / automorphism / representation infrastructure for
 213-Algebra.  Step 1 of conjecture C3 (Aut(K) gauge group emergence):

  * `AutKChiral.lean` — Aut(K_{3,2}^{(c=2)}) group cardinality
    structure: |Aut| = 768 = NS! · NT! · 2^(NS·NT) decomposed into
    external (Sym(NS) × Sym(NT)) and internal (C_2^(NS·NT)) parts.

  * `GluonChannelInterpretation.lean` — eight-fold QCD-channel
    identification (user's session insight): b_1(K) = 8 = NS²−1 =
    adj SU(3) IS the 8 SU(3) gluon color-charge DOF.  Chains
    χ(K) = -7, b_1 = 8, adj SU(NS) = 8 into one ∅-axiom statement.

  Future files (once representation theory is formalized):

  * `AutAction.lean` — Aut acting on `Cochain n k`
  * `Irreps.lean`    — irreducible representation decomposition
  * `GaugeEmergence.lean` — full C3 conjecture closure
-/
