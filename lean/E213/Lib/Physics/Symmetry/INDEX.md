# `Lib/Physics/Symmetry/` — automorphism + orbit symmetry + C3 chain

K_{3,2}^{(c=2)} automorphism group, edge action, orbits, chiral
structure, gluon-channel interpretation, and the **18-phase C3
chain** closing gauge emergence as Sym(3) F_2-irrep decomposition
of H¹(K).

**Narrative**: `theory/physics/symmetry/c3_chain.md` (promoted
2026-05-22).

## Companion files (substrate, 6)

  - `AutAction.lean`                 — automorphism action on Raw / lattice
  - `AutEdgeAction.lean`             — auto action on edges
  - `AutEdgeActionGenerators.lean`   — generators of the edge action
  - `AutEdgeOrbits.lean`             — edge orbit classification
  - `AutKChiral.lean`                — chiral auto-action on K
  - `GluonChannelInterpretation.lean` — gluon-channel physics reading
                                        (8 holes = 8 gluon channels)

## C3 chain (12 core phases)

  - `AutKType`                — Phase 1: Aut_K as Type, card 768
  - `Sym3OnKEdges`            — Phase 3: Sym(3) on K-edges
  - `Sym3OnH1K`               — Phase 4: descent to H¹(K)
  - `Sym3OnH1KMatrix`         — Phase 5: explicit 8×8 M_S01
  - `Sym3OnH1KCayley`         — Phase 6: ⟨s,t | s²=t²=(st)³=e⟩
  - `IotaKToDelta4`           — Phase 7: gluon octet = coker ι*
  - `IotaSym3Equivariance`    — Phase 8: ι is Sym(3)-equivariant
  - `Sym3IrrepDecomp`         — Phase 9: 2·trivial ⊕ 3·standard
  - `Sym3StandardReps`        — Phase 10: 2 explicit basis pairs
  - `Sym3Group`               — Phase 11: Sym(3) as proper Group
  - `AutKGroup`               — Phase 12: Aut(K) direct-product Group
  - ★ `C3ChainCapstone`       — `c3_chain_master` (12-conjunct)

Phase 2 (H¹(K) module) lives in `Cohomology/Bipartite/H1K.lean`.

## C3 chain extensions (Phases 13-18)

  - `C2_6OnH1K`               — Phase 13: C_2^6 trivial on coboundaries
  - `Sym3StandardRepThird`    — Phase 14: 3rd standard pair (full basis)
  - `AutKSemidirect`          — Phase 15: bit_perm twist sample
  - `C2_6MixedMatrices`       — Phase 16: 4 mixed C_2^6 H1K matrices
  - `Sym3BlockDiagonal`       — Phase 17: M_S01, M_S12 block-diagonal
  - `AutKSemidirectFull`      — Phase 18: full semidirect Group axioms

## Top-level

  - `Symmetry.lean` aggregator

## Where to add new files

  - Auto-action / orbits      → `Aut<...>` family
  - Generator catalog         → `AutEdgeAction<...>Generators`
  - Physics interpretation    → `<Channel>Interpretation.lean`
  - C3 chain extension        → next phase number, see capstone
