import E213.Lib.Physics.Symmetry.AutKChiral

/-! Spec-as-code entry point for `E213.Lib.Physics.Symmetry`.

  Symmetry / automorphism / representation infrastructure for
  213-Algebra (per `research-notes/G35_chiral_cup_ring_catalog.md`
  D7).  Currently a single file capturing Step 1 of conjecture C3
  (Aut(K) gauge group emergence):

  * `AutKChiral.lean` — Aut(K_{3,2}^{(c=2)}) group cardinality
    structure: |Aut| = 768 = NS! · NT! · 2^(NS·NT) decomposed into
    external (Sym(NS) × Sym(NT)) and internal (C_2^(NS·NT)) parts;
    adjoint SU dimensions; gauge-group emergence pointers.

  Future files (once representation theory is formalized):

  * `AutAction.lean` — Aut acting on `Cochain n k`
  * `Irreps.lean`    — irreducible representation decomposition
  * `GaugeEmergence.lean` — main C3 conjecture closure
-/
