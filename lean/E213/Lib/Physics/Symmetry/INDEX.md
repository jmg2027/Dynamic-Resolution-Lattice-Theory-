# `Lib/Physics/Symmetry/` — automorphism + orbit symmetry + C3 chain

K_{NS,NT} automorphism group, edge action, orbits, chiral
structure, gluon-channel interpretation, and the **C3 chain**
closing gauge emergence as the Sym(3) 𝔽₂-irrep decomposition of the
colour octet.

The colour octet is the **SU(3) adjoint**, `dim = NS² − 1 = 8`,
sourced directly from `NS = 3` (`SpectrumComplete.alpha_3_channel`) —
not a graph `b₁`.  Its carrier is the abstract rank-8 𝔽₂-module
`OctetModule.Octet`.

**Narrative**: `theory/physics/symmetry/c3_chain.md`.

## Companion files (automorphism action / lattice)

  - `AutAction.lean`                 — automorphism action on Raw / lattice
  - `AutEdgeAction.lean`             — auto action on edges
  - `AutEdgeActionGenerators.lean`   — generators of the edge action
  - `AutEdgeOrbits.lean`             — edge orbit classification
  - `AutKChiral.lean`                — chiral auto-action
  - `GluonChannelInterpretation.lean` — gluon-channel physics reading
                                        (8 = NS²−1 adjoint channels)

## C3 chain (c-free core)

  - ★ `OctetModule`           — rank-8 𝔽₂ Sym(3)-rep, `rank = NS²−1 = 8`;
                                generators `M_S01`/`M_S12`, Coxeter
                                presentation `s²=t²=(st)³=e`, fixed
                                subspace (`fixedSize = 4`), decomposition
                                `2·trivial ⊕ 3·standard`, explicit
                                standard 2-rep pairs.  `octet_master`.
  - `Sym3Group`               — Sym(3) as a proper Group on `Fin 6`
  - `AutKType`                — `Aut_K` as Type, card `768 = 6·2·64`
  - `AutKGroup`               — Aut direct-product Group
  - `AutKSemidirect` / `AutKSemidirectFull` — semidirect refinement
  - ★ `C3ChainCapstone`       — `c3_chain_master` (c-free, ★★★★★)

`H¹(Δ⁴) = 0` (4-simplex contractibility) is taken from
`Cohomology/Examples/BettiKernel`.

## Top-level

  - `Symmetry.lean` aggregator

## Where to add new files

  - Auto-action / orbits      → `Aut<...>` family
  - Octet representation theory → `OctetModule`
  - Physics interpretation    → `<Channel>Interpretation.lean`
