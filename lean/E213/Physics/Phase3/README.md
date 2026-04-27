# Phase 3 — 213 Translation + Falsifier + Reframing

## Purpose

Building on Phase 1 (precision quantity reproduction) + Phase 2
(axiom viewpoint):
- Redescribe *all* areas of standard physics using 213 atomic primitives
- Formalize each key result as a Lean theorem
- Explicitly state falsifiers (discard if observation decides)
- Catalog the artifactual nature of SM/QM terminology

## 60 module structure

```
Phase3/
├── Manifesto.lean              operating principles
├── Capstone.lean               19-conjunct falsifier synthesis
├── UltraCapstone.lean          full integration (12-conjunct)
├── Phase3.lean (root)          single import of all modules
│
├── Falsifier (14): NoFourthGen, NeutrinoOrdering, ...
├── Deep-dive (8):  WhyValue derivations
├── Reframing (7):  StaticCouplings, Artifacts, ...
└── Translation/ (28): translation of modern physics
```

## Key Discovery — atomic integer multi-output

### Integer 6 = NS·NT (strongest pattern)
- Pauli ε_abc nonzero entries [QM]
- Lorentz SO(3,1) generators [SR]
- AB cross pair K_{3,2} [Phase 2]
- SU(NS) root count [Group]
- 3! permutation, AdS/CFT bulk

### Integer 8 = NS²-1
- 1/α_3, SU(3) adjoint, Cycle b_1
- Einstein 8π, Hawking 1/8
- Nuclear binding ~8 MeV
- Bell quantum², F_6 Fibonacci

### Integer 24 = d²-1
- SU(5) GUT adjoint
- α_2 prefactor 12·NT
- PMNS δ_CP, 4! permutation
- SM gauge sum (8+3+12+1)

## Guarantees

- 60 modules 0 sorry, ≤ propext + Quot.sound (most 0 axioms)
- `lake build E213.Physics` clean (198 modules)
- All capstones 0 axioms

## Operating Principles

- Only 213 axioms are fundamental. Everything else is Lens output.
- No words "observer/space/structure/relation/cognition" in axiom
  descriptions
- "running, energy scale, wave function, existence probability,
  interaction" all disappear
- Any falsifier violation → 213 abandoned
