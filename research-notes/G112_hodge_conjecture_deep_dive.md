# G112 — HodgeConjecture Tier-2 deep dive (961 decls)

**Date**: 2026-05-22  
**Branch**: `claude/analyze-lean4-ast-patterns-49Rh2`  
**Predecessor**: G111 (Cohomology), G108 (Real213/Analysis),
G110 (FluxMVT).  
**Context**: Cohomology's natural successor — HodgeConjecture
sits ON TOP of Cohomology's machinery and adds the Hodge-
conjecture-specific architecture (pairings, structure, motivic
bridge, physics applications).

---

## §1.  Scale + distribution

**961 decls** across 8 sub-areas:

| Sub-area | decls | Role |
|----------|------:|------|
| **Bridge**    | **447** | Physics + CS applications (Beilinson regulator, Ising, Potts, ML decoder, motive-etale, Galois, ...) |
| **Pairing**   | **319** | Hodge-Index + Hodge-Riemann pairing theorems on surfaces |
| Foundation    |  58 | Canonical / Complete / Conjecture / Filled / LensCata |
| Toolkit       |  58 | LensClassifier / Primitives / RoundTrip helpers |
| MotivicBridge |  28 | Beilinson-Lichtenbaum / Bloch-Beilinson / Chern / HodgeTate |
| Refinement    |  27 | Generalized Hodge / Lefschetz hyperplane / Voisin |
| Structure     |  23 | HardLefschetz / Map / PoincareDuality / Ring |
| API           |   1 | public surface |

**Bridge dominates** (47 % of decls) — HodgeConjecture is
primarily an **application layer**, applying Hodge structure to
physics + CS problems.  Pairing (33 %) is the second-largest —
Hodge-Index theorems specialised to specific surfaces.

### Marker analysis

| Marker | hits | % |
|--------|-----:|--:|
| `binom`    | **153** | 15.9 |
| `Cochain`  |  46 |  4.8 |
| `hodgeStar`|  19 |  2.0 |
| `cup` (lex)|  12 |  1.2 |
| `Bool.xor` |   6 |  0.6 |
| `delta`    |   3 |  0.3 |
| `cupAW`    |   0 |  0.0 |
| `Lens.view`|   0 |  0.0 |
| **Raw atom** | **0** | **0** |

**Critical observation**: HodgeConjecture uses Cochain (4.8 %)
and hodgeStar (2.0 %) but **NOT cupAW directly** (0 %).
Instead it operates at a HIGHER ABSTRACTION level — Hodge
Index, Hodge-Riemann, Hard Lefschetz, etc. — which were proven
in Cohomology and re-cited symbolically.

This makes HodgeConjecture a **second-order encapsulation**:
Cohomology encapsulates Raw/Lens; HodgeConjecture encapsulates
Cohomology's operations.

---

## §2.  Architecture

```
                    Layer 1: Foundation (58 decls)
                    Canonical / Complete / Conjecture
                    ConjectureLens / Filled / LensCata
                               │
                    Layer 2: Structure (23 decls)
                    HardLefschetz / Map / PoincareDuality / Ring
                               │
                    Layer 3: Pairing (319 decls) ← BIGGEST math
                    HodgeIndex {P¹², P², T², T²², T²ⁿ}
                    HodgeRiemann {T², T²²}
                    + Genus_g, TripleProduct, Hirzebruch, Kahler
                    + BalancedSignature, TensorSignature
                               │
                    Layer 4: MotivicBridge (28 decls)
                    Beilinson-Lichtenbaum / Bloch-Beilinson /
                    Chern / HodgeTate / MumfordTate / Tate
                               │
                    Layer 5: Refinement (27 decls)
                    GeneralizedHodge / Lefschetz(1,1) /
                    StandardConjectures / Voisin
                               │
                    Layer 6: Bridge (447 decls) ← BIGGEST overall
                    physics + CS applications
                               │
                    Layer 7: Toolkit (58 decls, orthogonal)
                    LensClassifier / Primitives / RoundTrip
                               │
                            Layer 8: API (1 decl)
```

---

## §3.  Layer 3 — Pairing (319 decls, math heart)

The structural-mathematical heart.  Per-surface Hodge Index +
Hodge-Riemann pairing theorems:

| Surface | Files | Result |
|---------|-------|--------|
| ℙ¹×ℙ¹ | `HodgeIndexP1Squared` | signature (2, 0), positive-definite |
| ℙ² | `HodgeIndexP2` | signature (1, 0) |
| T² | `HodgeIndexT2`, `HodgeRiemannT2` | signature (1, 1) |
| T²×T² | `HodgeIndexT2Squared`, `HodgeRiemannT2Squared` | signature (3, 3) |
| T²ⁿ | `T2nInductive`, `T2nPattern` | Künneth recursion |

Plus general-position results:
  · `GenusGSurface` — genus-g surface signature
  · `HirzebruchMultiplicative` — Hirzebruch class multiplicative
  · `KahlerGradeStructure` — Kähler grading
  · `BalancedSignature` — balanced signature data
  · `TensorSignature` — tensor product signature Künneth
  · `ProductSurfaceSignature` — product surface signature
  · `SignatureMetaTheorem` — meta-level signature claim
  · `SurfaceComparisonTheorem` — cross-surface comparison
  · `TripleProductSurface[Parametric]` — triple product
  · `HodgeIndexGradeStructure` — graded structure

**Pairing's core math**: take Cohomology's surface CW models →
apply Hodge Index / Hodge-Riemann theorems → produce
non-vacuous structure proofs that the ℤ/2 cohomology in
isolation can't generate.

### Heavy proofs in Pairing

  · `TensorSignature.tensor_signature_kunneth_master`: 23,816
    nodes — Künneth master theorem.
  · `GenusGSurface.genus_g_signature_master`: 14,169 nodes —
    genus-g signature.

---

## §4.  Layer 6 — Bridge (447 decls, application layer)

Physics + CS application bridges built on Hodge framework:

| Bridge | Topic | Heaviest |
|--------|-------|---------:|
| MLDecoder    | Machine learning decoder via Hodge | 94,835 |
| MotiveEtaleFusion | Motivic ⟷ étale fusion (cohomology) | 84,323 |
| BeilinsonRegulator | Beilinson regulator function | 38,975 |
| Potts        | Potts model (statistical physics) | 35,547 |
| Ising        | Ising model (statistical physics) | 34,811 |
| GaloisCounterfactual | Galois counterfactual | 17,285 |
| PhaseRouting | Phase routing | smaller |
| SpinGlass + SpinGlassGroundState | Spin glass + ground state | smaller |
| DiscreteGeometry | Discrete geometric bridges | smaller |
| G6Vacuity    | G6 vacuity check | smaller |

**Reading**: HodgeConjecture's Bridge directory carries DRLT's
**big physics ↔ math capstones** — `*_213_capstone` master
theorems for Potts, Ising, Beilinson regulator, ML decoder,
motive-étale fusion.

Each capstone is a substantial proof (30-90K nodes) showing the
213-native version of a classical physics/CS construction.

### MLDecoder.ml_decoder_capstone — biggest single HodgeConjecture proof

94,835 nodes.  Likely the most complex single proof in
HodgeConjecture.  Demonstrates that **ML decoding** (an
information-theoretic problem) has a 213-native realisation
via Hodge structure.

This is the kind of bridge that goes well beyond classical
Hodge theory — using the cohomological framework for problems
in machine learning + statistical physics + ML decoding.

---

## §5.  Layer 4 — MotivicBridge (28 decls)

The motivic-cohomology classical-side counterparts:

  · `BeilinsonLichtenbaum` — Beilinson-Lichtenbaum conjecture
  · `BlochBeilinson` — Bloch-Beilinson regulator
  · `ChernCharacter` — Chern character map (G109 CDI-2 member)
  · `HodgeTate` — Hodge-Tate decomposition
  · `MumfordTate` — Mumford-Tate group
  · `Tate` — Tate conjecture

These are the **classical-mathematics anchors** in the
HodgeConjecture sub.  Each provides a bridge between DRLT's
constructive cohomology and the classical motivic
conjectures.

---

## §6.  Cross-domain identifications (G109 cross-ref)

HodgeConjecture is a **major math-side anchor** in G109's
math↔physics bridges:

  · **CDI-1**: `b_1_eq_NS_sq_minus_one` —
    `Foundation.ConjectureLens` member, `Pairing.HodgeIndex.h1_dim_K32` member.
  · **CDI-2**: 5-way bridge —
    `MotivicBridge.ChernCharacter.ch_target_even_delta4` member.

HodgeConjecture is the **bridge between Cohomology (structural)
and Physics (constants)**.  Cohomology produces the Betti
numbers + Hodge structure; HodgeConjecture re-packages them
for physics applications via Bridge/.

---

## §7.  Heavy proof clusters

### Cluster I — Bridge capstones (5 sites, ~290K total)

  · `MLDecoder.ml_decoder_capstone`: 94,835
  · `MotiveEtaleFusion.motive_etale_fusion_capstone`: 84,323
  · `BeilinsonRegulator.beilinson_regulator_213_capstone`: 38,975
  · `Potts.potts_213_capstone`: 35,547
  · `Ising.ising_213_capstone`: 34,811

**Each capstone is a self-contained master theorem**.  Likely
NOT byte-identical (they prove different things), but share
overall structure (213-native realisation of a classical
construction).

### Cluster II — Pairing surface signatures

  · `TensorSignature.tensor_signature_kunneth_master`: 23,816
  · `GenusGSurface.genus_g_signature_master`: 14,169
  · Plus per-surface HodgeIndex / HodgeRiemann proofs.

### Cluster III — Structure Map theorem

  · `Structure.Map.hodgeStar_xor_5_1`: 17,709 nodes.
  · `Refinement.GeneralizedHodge.generalized_hodge_213`: 9,953.

---

## §8.  Action items from G112

### HC-1 — Bridge capstone structural pattern

5 `*_213_capstone` proofs (ML decoder, motive-étale fusion,
Beilinson regulator, Potts, Ising) likely share a templated
**capstone-structure pattern**: setup → Hodge framework
invocation → physics-side calculation → match.  If so,
investigate via shape-vector grouping (G103 method).

**Effort**: investigation (1-2 hours) to check for byte-shared
structure across the 5 capstones.

### HC-2 — Per-surface HodgeIndex/HodgeRiemann template

`HodgeIndexP1Squared`, `HodgeIndexP2`, `HodgeIndexT2`,
`HodgeIndexT2Squared` likely share Hodge-Index proof template
across surfaces.  Same for `HodgeRiemannT2`, `HodgeRiemannT2Squared`.

**Effort**: investigation + medium marathon if pattern
confirmed.

### HC-3 — MotivicBridge as classical-side anchor

The 6 motivic bridges are **the classical-math citation
surface** of DRLT.  Could be promoted into a dedicated
`classical-bridges.md` catalog for citing the classical
counterparts of DRLT's 213-native theorems.

**Effort**: short doc work.

---

## §9.  Research questions surfaced from G112

### HC-RES1 — Hodge Conjecture status check

`Foundation/Conjecture.lean` defines the conjecture statement.
`Refinement/StandardConjectures.lean` lists standard
conjectures.  **Question**: is the Hodge Conjecture itself
proven in DRLT-internal form?  Or only **bridged** (Hodge
structure → classical conjecture statement)?

If proven in some form (likely vacuously over ℤ/2 + non-
vacuously on surfaces), characterise the precise status.

**Effort**: 1-2 sessions investigating Foundation +
Refinement files.

### HC-RES2 — Bridge capstones unification

5 `*_213_capstone` master theorems are clearly templated.
**Question**: can they be unified under a single
`physics_213_capstone {model : PhysicsModel} {hodge_data :
HodgeStructure} : RealisationCorrect`?

Would require formalising what "PhysicsModel" and
"RealisationCorrect" mean — meta-theoretic work.

**Effort**: 3-5 sessions, doctrinal value.

### HC-RES3 — T²ⁿ inductive Hodge structure

`Pairing/T2nInductive.lean` + `T2nPattern.lean` claim general
T²ⁿ Künneth structure.  **Question**: is this proven ∀ n?  Or
only for low n?  If proven ∀ n, T²ⁿ-Hodge is a corpus-wide
universal.

**Effort**: 1 session investigation.

### HC-RES4 — Voisin + Lefschetz(1,1) status

`Refinement/Voisin.lean` and `Refinement/LefschetzHyperplane.lean`
(if exists) target the Voisin counter-example and Lefschetz
hyperplane theorem.  **Question**: in DRLT, do these proceed
constructively or are they framework-level statements?

**Effort**: 1 session.

---

## §10.  Significance for the meta-scan tree

### What G112 confirms

  · **Second-order encapsulation pattern**: HodgeConjecture
    encapsulates Cohomology's operations (uses Cochain +
    hodgeStar + cup-lex but NOT cupAW directly).
  · **Bridge-dominant architecture** (47 % of decls in Bridge
    sub) — HodgeConjecture is primarily an application layer.
  · **Math-side anchor for physics**: most physics-relevant
    capstones (Ising, Potts, ML decoder, Beilinson regulator)
    live here.

### What G112 newly surfaces

  · **Per-surface signature template** (HC-2) — multiple
    surfaces likely share HodgeIndex/HodgeRiemann proof shape.
  · **Bridge capstone template** (HC-1) — 5 `*_213_capstone`
    proofs likely templated.
  · **Classical-side citation surface** (HC-3) — MotivicBridge
    as DRLT's anchor for classical Hodge-conjecture-adjacent
    statements.

### What's still unexplored

  · `DyadicFSM/` (1,272 decls) — biggest remaining Tier-3.
  · `CayleyDickson/` (629 decls).
  · `Lib.Physics/` subtrees (Atomic, Hadron, Cosmology,
    Symmetry, etc.) — these were covered partially in G109
    via cross-domain bridges but not deeply analysed.
  · Inside HodgeConjecture: `Bridge/G6Vacuity.lean` (the G6
    vacuity check) deserves precise analysis given G6's
    role in atomicity (G87 §2).

---

## §11.  Updated executor priority (G108 + G110 + G111 + G112)

1. **L1 LeibnizAlgLift marathon** (G106) — biggest mass
2. **G111 COH-1 + COH-2 + COH-3 batch** (~90K nodes)
3. **G112 HC-1 capstone-template investigation** (1-2 hours)
4. **G110 FLUX-1** forward/backward parametric
5. **G108 REAL-1 + REAL-2** Cut iff consolidation
6. **G108 CutSumOne C template**
7. **G112 HC-2 per-surface HodgeIndex template** (medium)
8. **G113 DyadicFSM deep dive** (1-2 sessions)
9. **G114 CayleyDickson deep dive** (1-2 sessions)
10. **G115 Bishop comparison** (REAL-RES6)

**Doctrinal capstones (research)**:
  · COH-RES5 Pattern #17 framework
  · HC-RES2 Bridge capstones unification
  · HC-RES3 T²ⁿ inductive
  · COH-RES4 Bipartite+Fractal physics chain

---

## §12.  Artifacts

  · This document: `research-notes/G112_hodge_conjecture_deep_dive.md`
  · Source: G102 callgraph + G103 shape + source inspection.

Next Tier-2 candidates (G113-G115): DyadicFSM (1,272 decls),
CayleyDickson (629 decls), Lib.Physics subtrees.
