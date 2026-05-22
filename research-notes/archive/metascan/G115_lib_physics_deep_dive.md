# G115 — Lib.Physics Tier-2 deep dive (2,159 decls — largest single Library subtree)

**Date**: 2026-05-22  
**Branch**: `claude/analyze-lean4-ast-patterns-49Rh2`  
**Predecessor**: G108-G114 (Real213/Analysis, FluxMVT,
Cohomology, HodgeConjecture, DyadicFSM, CayleyDickson).  
**Context**: After 6 Math Tier-2 deep dives, Lib.Physics is the
remaining major subtree — and turns out to be the **single
largest** at 2,159 decls.

---

## §1.  Scale + distribution

**2,159 decls** in 16 top-level Physics sub-areas:

| Sub-area | decls | Role |
|----------|------:|------|
| **AlphaEM**     | **903** (42%) | Fine-structure constant α_em chain |
| Foundations     | 161 | Atomic constants, finite universe, Hop hypothesis |
| AtomicBase      | 153 | Phase 1/2 atomic structure + capstones |
| Atomic          | 149 | Hydrogen / Helium / IE / BondAngles / Screening |
| Hadron          | 131 | Hadron physics (proton-electron, neutron-proton) |
| Symmetry        | 125 | C3 chain — Aut(K)/Sym(3) gauge emergence |
| Couplings       | 111 | α₃ confinement, gauge couplings |
| Simplex         | 109 | Δ⁴ + K_{3,2}^{(c=2)} structure + generation count |
| Nuclear         |  72 | Magic numbers, deuteron, shells |
| Mixing          |  52 | PMNS / CKM neutrino-quark mixing |
| Basel           |  49 | Basel-sum width brackets |
| YangMills       |  49 | SU adjoint, WZ bosons |
| Higgs           |  36 | Higgs mass mechanism |
| Cosmology       |  28 | Hubble, Ω_Λ |
| Mass            |  25 | Mass ratios |
| Capstones       |   6 | Top-level physics-track capstones |

---

## §2.  Marker analysis (Raw / Math / Physics constants)

| Marker | hits | % | Role |
|--------|-----:|--:|------|
| `NS` (= 3) | 330 | 15.3 | atomicity S-vertex count |
| `d` (= 5) | 274 | 12.7 | atomicity dimension |
| `NT` (= 2) | 259 | 12.0 | atomicity T-vertex count |
| `binom`   | 114 |  5.3 | binomial coefficient |
| `cup`     |  16 |  0.7 | (lex-projection) |
| `hodgeStar` | 15 | 0.7 | Hodge dual |
| `Cochain` |  14 |  0.6 | Cochain type |
| `cupAW`   |   3 |  0.1 | Alexander-Whitney cup |
| **Raw atom** | **2** |  0.1 | direct Raw reference |
| **Lens.view** | **2** | 0.1 | Lens projection |
| **Cut / cutMul** | **0** | 0 | Real213 Cut function |
| **ZOmega** | **0** | 0 | CayleyDickson Eisenstein |

**Critical observations**:

  · **Atomicity constants (NS, NT, d) threaded heavily**: 40 %
    of decls touch at least one of NS / NT / d.  ~45 % including
    binom (which depends on these via type `Fin (binom n k)`
    with n = d = 5).
  · **Cohomology objects rarely directly referenced**:
    Cochain + cup + hodgeStar + cupAW combined < 3 %.  Physics
    cites the **values** (b₁ = NS²-1 = 8) but not the
    **operations** (cup product, Hodge star).
  · **Zero Real213 / ZOmega touch**: Physics does NOT use Cut
    function form or Eisenstein integer arithmetic directly.
    Even though G109 CDIs show math↔physics bridges via these
    structures, Physics's PROOF BODIES don't invoke them.

**Architectural reading**:

Lib.Physics is **maximally encapsulated from the math
infrastructure** at the Expr level.  It builds on (NS, NT, d)
atomicity numerics (which are Raw-derived structurally — G104
(β)) but operates in its own carriers (atomic constant brackets,
mass ratios, etc.) without re-invoking Cochain / Cut / ZOmega
machinery.

This is the **CDI bridge pattern at scale** (G109): physics
THEOREMS are byte-identical to math THEOREMS at the Expr
level, but each side uses its own NAMED carriers.  The cross-
domain identification surfaces only via shape-vector grouping,
not via direct citation.

---

## §3.  AlphaEM dominance (903 decls — 42 % of Physics)

`Lib/Physics/AlphaEM/` is the **single largest single subtree
in the entire Lib/Math + Lib/Physics combined**:

  · 23 files
  · 903 decls
  · ~3× the next largest (Foundations at 161)

### AlphaEM file architecture

| File | Topic |
|------|-------|
| `Bare`              | Bare α_em derivation |
| `Augmented`         | Augmented α_em (with corrections) |
| `Brackets`          | α_em ∈ DRLT-predicted bracket |
| `Capstone`          | α_em capstone master |
| `ChannelCohomologyLoss` | Cohomology channel loss formula |
| `CupChannelInventory` | Cup channel inventory (K_{3,2}^{(c=2)} edges) |
| `CupRingTrace`      | Cup ring trace |
| `FractalLevelLift`  | Fractal level lifting |
| `FractalLevelZeta{Bracket,CoeffSeq,Convergence,Modulus,Spectrum}` | 5 ζ-related files |
| `GradedDecomposition` | α_em graded decomposition |
| `GradedFormula{,Precision}` | Graded formula + precision |
| `GramHigherOrder`   | Higher-order Gram |
| `GramSelfConsistency` | Gram self-consistency |
| `LaplacianSpectrum` | Laplacian spectrum (≈ 19K nodes heavy) |
| `NResolutionCandidates` | N-resolution candidates |
| `PiFiveGap`         | π⁵ gap in α_em |
| `ProjectionRatios`  | Projection ratios |
| `StructuralGap`     | Structural gap = α_em precision |

AlphaEM is the framework's **most-elaborated single physics
claim** — α_em derivation through atomicity + Gram self-energy
+ Laplacian spectrum + fractal levels + ζ-sequences.

### Reading

α_em's atomic prediction within DRLT is **the headline physics
claim** that the corpus invests most effort in (903 decls vs
next largest 161).  The chain:

```
Atomicity (NS=3, NT=2, d=5)
  ↓
K_{3,2}^{(c=2)} cup channels (Cup channel inventory)
  ↓
Cohomology channel loss formula
  ↓
Gram self-consistency + higher-order
  ↓
Fractal level ζ-corrections
  ↓
α_em derived bracket (Augmented/Bare/Brackets/Capstone)
  ↓
α_em ≈ 1/137.036 (matched to observation)
```

---

## §4.  Symmetry — C3 gauge-emergence chain (125 decls)

`Lib/Physics/Symmetry/` hosts the parallel branch's C3 chain
work (per HANDOFF.md Part 1: "C3 chain (gauge emergence) —
12 phases + master").

Files:
  · `AutKType` — Aut(K) as Type, cardinality 768 (Phase 1)
  · `AutKGroup` — Aut(K) as Group structure
  · `AutKSemidirect{,Full}` — Sym(3) × Sym(2) ⋉ C₂⁶ structure
  · `AutAction`, `AutEdgeAction`, `AutEdgeActionGenerators`,
    `AutEdgeOrbits` — Aut(K) acting on K-edges
  · `AutKChiral` — chiral substructure
  · `C2_6{MixedMatrices,OnH1K}` — C₂⁶ on H¹(K)
  · `Sym3Group`, `Sym3OnH1K`, `Sym3OnH1KCayley`,
    `Sym3OnH1KMatrix`, `Sym3OnKEdges`, `Sym3IrrepDecomp`,
    `Sym3BlockDiagonal`, `Sym3StandardReps`,
    `Sym3StandardRepThird` — Sym(3) action + representations
  · `IotaKToDelta4`, `IotaSym3Equivariance` — ι* morphism
    H¹(Δ⁴) → H¹(K)
  · `C3ChainCapstone` — ★ master result
  · `GluonChannelInterpretation` — physical gluon interpretation

The C3 chain's **master**:
```
gluon octet := coker(ι*: H¹(Δ⁴) → H¹(K_{3,2}^{(c=2)}))
            =  H¹(K) / 0        (H¹(Δ⁴) = 0)
            ≃  (F_2)^8
            =  2·trivial ⊕ 3·standard  (over F_2)
```

`Symmetry.AutEdgeOrbits.aut_edge_orbits_master` is **35,621
nodes** — second heaviest in Lib.Physics.

This subtree is the **gauge-emergence narrative anchor** —
ties Cohomology + HodgeConjecture math machinery to physics
gauge groups via concrete K_{3,2}^{(c=2)} cocycle analysis.

---

## §5.  Heavy proof clusters

### Cluster I — Atomic constants foundations

| Nodes | Decl |
|------:|------|
| 46,831 | `Foundations.AtomicSuperCatalog.super_catalog` |
| 35,320 | `Foundations.AtomicConstantsParametricFull.mp_n_sq_le_msub1_nsub1` |
| 25,024 | `Foundations.AtomicConstantsParametricFull.msq_nsq_decomp` |
| 21,001 | `Foundations.DrltZeroParameters.drlt_zero_parameter_claim` |
| 17,485 | `Foundations.GoldenRatio.golden_ratio_atomic` |

**Foundations is the second-largest cluster by mass**.
`AtomicSuperCatalog` (47K) catalogues all atomic constant
relationships.  `DrltZeroParameters` (21K) is the structural
"zero free parameter" claim itself.

### Cluster II — Symmetry C3 chain

| Nodes | Decl |
|------:|------|
| 35,621 | `Symmetry.AutEdgeOrbits.aut_edge_orbits_master` |

The Sym(3) action on K-edges orbit analysis.

### Cluster III — AtomicBase phase capstones

| Nodes | Decl |
|------:|------|
| 23,481 | `AtomicBase.Existence.cosmos_existence_minimal` |
| 22,193 | `AtomicBase.Capstone.phase2_absolute` |

Phase 2 absolute capstone + minimal cosmos existence.

### Cluster IV — Specific physics predictions

| Nodes | Decl |
|------:|------|
| 33,597 | `Nuclear.MagicNumbersAtomic.nuclear_magic_atomic_capstone` |
| 18,949 | `Mixing.NeutrinoMixing.PMNS_simplicial_pattern` |
| 18,685 | `AlphaEM.LaplacianSpectrum.laplacian_spectrum_master` |
| 18,537 | `Simplex.GenerationStructure.matter_content_capstone` |
| 16,385 | `Nuclear.Shells.nuclear_magic_capstone` |
| 15,525 | `Hadron.ProtonElectronRatio.proton_electron_ratio_atomic` |

Each is a specific physics constant or pattern prediction
capstone:
  · Nuclear magic numbers
  · PMNS neutrino mixing
  · Laplacian spectrum
  · Matter content (3 generations)
  · m_p / m_e ratio

---

## §6.  Cross-domain identification (G109 cross-ref)

Physics is the OTHER half of G109's CDI bridges (math being
the math side anchored in Cohomology/HodgeConjecture).
Lib.Physics decls in G109's CDIs:

  · **CDI-1**: `Physics.Foundations.FiniteUniverse.inv_alpha_em_finite_3 / _10` (member)
  · **CDI-2**: `Physics.Mixing.Bridge.delta_cp_atomic`,
    `Physics.YangMills.Bridge.adjoint_SU_{d,NS}_atomic` (5-way)
  · **CDI-3**: `Physics.Couplings.ColorConfinement.inv_alpha_3_via_NS_sq`,
    `Physics.Simplex.Counts.adjoint_su5` + `inv_alpha_3_confined`
    (4-way K_25 bridge)
  · **CDI-4**: `Physics.Foundations.AtomicConstantsParametric.sq_of_add`
    (heaviest CDI by mass)
  · **CDI-5**: 8-way physics bracket-containment template
    (Cosmology, Nuclear, Atomic, Hadron, AlphaEM, YangMills)
  · **CDI-7**: `Physics.Cosmology.HubbleConstant.hubble_atomic`
    (Hubble ↔ diamond audit)
  · **CDI-8**: `Physics.Nuclear.Bridge.magic_atomic` (6-way fractal)

Lib.Physics anchors the **physics side** of 12 out of 25
math↔physics bridges from G109's 25 substantive cross-domain
identifications.

---

## §7.  Action items from G115

### PHYS-1 — AlphaEM ζ-sequence consolidation

`FractalLevelZeta{Bracket, CoeffSeq, Convergence, Modulus,
Spectrum}` — 5 files with ζ-related content for fractal
level corrections to α_em.  Likely share template structure
(Cauchy-convergent ζ-sequence pattern).

**Effort**: 1-2 sessions investigation + medium marathon if
templated.

### PHYS-2 — Physics bracket-containment template

G109 Bridge 8 + Bridge 20 = 8 decls share 321-1077 node
proof template.  Cross-physics-domain "observed constant X in
DRLT-bracket [low, high]" pattern.  Parametric template
`physics_bracket_containment` opportunity.

**Effort**: medium marathon.  Already partly raised in G109
§6 CDI-5.  Mass saving ~5K nodes + ~8 decl simplification.

### PHYS-3 — Atomic constants parametric family

`Foundations/AtomicConstantsParametric*.lean` (4 files: Plain,
Full, FullIff, N3).  Likely 4 variants of the same family.

**Effort**: short marathon investigation + parametric lift.

### PHYS-4 — Symmetry C3 chain documentation

C3 chain Phase 1-18 are documented in HANDOFF.md but not in
standalone form.  Could be promoted to a theory note linking
all 12 base phases + 6 extensions.

**Effort**: 1 session doc-writing.

### PHYS-5 — Capstones consolidation

`Physics/Capstones/` (6 decls) — top-level physics-track
capstones (PhysicsTrackComplete, etc.).  If these tie all
domain capstones, they're the executor's entry-point for
"give me the DRLT physics summary".

**Effort**: short documentation review.

---

## §8.  Research questions

### PHYS-RES1 — α_em precision derivation

AlphaEM's 903 decls produce a specific α_em prediction.
**Question**: what's the current precision?  How does it
compare to the observed value 1/137.0360 (ppb)?

**Effort**: 1 session reading AlphaEM Capstone + Brackets.

### PHYS-RES2 — Physics carrier types catalog

Physics uses its own carriers (atomic constants, mass ratios,
gauge groups) instead of importing math machinery directly.
**Question**: what are these carriers + how do they connect
back to atomicity?

**Effort**: 1 session.  Output: a `catalogs/physics-carriers.md`.

### PHYS-RES3 — Mixing PMNS / CKM simplicial pattern

`Mixing/NeutrinoMixing.PMNS_simplicial_pattern` (19K nodes) +
`Mixing/Bridge.delta_cp_atomic` (G109 CDI-2).  The PMNS matrix
+ δ_CP from DRLT atomicity.  **Question**: full PMNS+CKM
matrix derivation status.

**Effort**: 2-3 sessions.

### PHYS-RES4 — Higgs mechanism in DRLT (36 decls)

`Higgs/` has 36 decls.  **Question**: how is the Higgs
mechanism realised in DRLT framework terms?

**Effort**: 1-2 sessions.

### PHYS-RES5 — Cosmology constants chain

`Cosmology/` 28 decls + G109 CDI-7 (Hubble).  **Question**:
how many cosmology constants are derived from atomicity?
(Hubble H₀, Ω_Λ already seen; what else?)

**Effort**: 1 session.

---

## §9.  Significance for the meta-scan tree

### What G115 confirms

  · **Lib.Physics is the largest single subtree** (2,159 decls
    > G113 DyadicFSM 1,272 > G111 Cohomology 1,216 > G108
    Real213+Analysis 1,981 combined).
  · **AlphaEM dominates** (42 % of Physics) — α_em is the
    framework's most-elaborated physics claim.
  · **Maximally encapsulated**: 0 Cut/ZOmega touches, ~3 %
    Cohomology objects, 0.1 % Raw/Lens.view.  Physics builds
    on atomicity NUMERICS, not math infrastructure DIRECTLY.
  · **Atomicity threading**: NS/NT/d touch 40 % of decls —
    Raw-derived constants are systematically present across
    Physics, confirming G102's "physics constants threaded
    structurally" finding at finer resolution.

### What G115 newly surfaces

  · **AlphaEM as the corpus's biggest single physics
    investment** (903 decls in one subtree).
  · **PHYS-1 through PHYS-5 abstraction + research candidates**.
  · **Carrier separation**: Physics has its own carriers
    distinct from math infrastructure — supports Pattern #17
    (multiple Lens choices).

### What's still unexplored

  · `PatternCatalog/` (943 decls) — next G116 target.
  · Doctrinal capstones: Bishop (G117), theory standalone docs
    (TH-1/TH-2/TH-4).

---

## §10.  Updated executor priority (G108-G115)

1. **L1 LeibnizAlgLift marathon** (G106 — biggest single mass)
2. **G113 FSM-1 pellFSMmod parametric** (457 sites — broadest)
3. **G111 COH-1+COH-2+COH-3 batch** (~90K nodes)
4. **G115 PHYS-2 bracket-containment template** (~5K nodes, broad)
5. **G114 CD-1+CD-2+CD-3 small template batch** (~2K nodes)
6. **G112 HC-1 capstone investigation**
7. **G110 FLUX-1 forward/backward**
8. **G115 PHYS-1 ζ-sequence consolidation** (1-2 sessions)
9. **G115 PHYS-3 Atomic constants parametric**
10. **G108 REAL-1 + REAL-2**
11. **G113 FSM-3 pisano predictor**
12. **G114 CD-RES1 Codomain catalog**
13. **G108 CutSumOne C**
14. **G116 PatternCatalog deep dive** (943 decls)
15. **G117+ Bishop comparison (doctrinal)**

---

## §11.  Artifacts

  · This document: `research-notes/G115_lib_physics_deep_dive.md`
  · Source: G102 callgraph + G103 shape + G109 CDI cross-ref +
    Lean source inspection.

Next: G116 PatternCatalog (943 decls, Tier-1 pattern framework
meta).
