# AUDIT_PASS 2026-05-05 — lean/E213/

Survey of the Lean tree.  Total: ~994 `.lean` files across the
six vertical layers + 21 INDEX.md files.

## Layer file counts

| Layer | Files | Purpose |
|---|---|---|
| `Kernel/` | 23 | Type-theoretic kernel (Term213, Nat213 tactic) |
| `Firmware/` | 27 | Raw axiom + atomicity primitives |
| `Hypervisor/` | 89 | Lens (specification + characterisation), 11 sub-trees + Morphism/SlashSwap (added 2026-05-05) |
| `Meta/` | 27 | Metatheory (UniversalLens*, SelfRecognising, tactics) |
| `OS/` | 20 | Cross-layer capstones (HodgeConjecture/, Physics/) |
| `Math/` | 543 | Topical math (Cohomology 233, Real213 ~180, etc.) |
| `Physics/` | 261 | Topical physics (16 sub-trees; FinitismIsConsequence deleted 2026-05-05) |
| `App/` | 1 | (placeholder) |
| **Total** | **991** | + ARCHITECTURE.md, INDEX.md, three top-level imports = 994 .lean files |

## Top-of-tree health

  - `ARCHITECTURE.md` — canonical layer definitions; verified
    consistent with CLAUDE.md "One vertical axis" policy.
  - `INDEX.md` — high-level navigation; verified consistent.
  - Build: clean (`lake build` ⇒ "Build completed successfully.").
  - Axioms: 479 PURE / 2 DIRTY (NativeGuard meta-tool internals,
    accepted) / 18 sealed-DIRTY-by-design.

## Per-layer status

### Kernel/ (23 files)

Compact, tightly-scoped.  `Tactic/Nat213.lean` is the workhorse for
∅-axiom Nat reductions.  No consolidation needed.

### Firmware/ (27 files)

`Atomicity/`, `Raw/`, `Tools/` — three sub-trees, each modest.
`Raw.lean` is the canonical 4-clause axiom realisation.  No
consolidation needed.

### Hypervisor/Lens/ (88 files in 11 sub-trees)

Largest non-Math/non-Physics sub-tree.  Each sub-tree has an
INDEX.md.  Sub-tree composition is well-classified by Lens role
(AxiomLenses, Characterisation, Compose, Instances, Kernel, Lattice,
Leaves, Morphism, Properties, Refines, Universal).  No consolidation
needed.

### Meta/ (27 files)

Three sub-trees: bare `Meta/`, `Meta/Tactic/`, `Meta/Universal/`,
`Meta/UniversalLens/`.  Holds: SelfRecognising (R12/R3/R4 codomain
typeclasses — see Open Issue #1 below), CUniquenessBridge,
UniversalLens marathon outputs.  No consolidation needed.

### OS/ (20 files)

`HodgeConjecture/` (with Bridges/) + `Physics/Capstones/` — two
top-level capstones.  Well-classified.  No consolidation needed.

### Math/ (543 files)

Largest layer.  Sub-trees: AxiomSystems, Cauchy, CayleyDickson,
Choice, **Cohomology (233)**, Diagonal, Hyper, Infinity, Irrational,
Linalg213, ModArith, Modulus, Polynomial213, **Real213 (~180)**,
Tactic, Trajectory.  Cohomology and Real213 carry most of the mass.

  - Cohomology: 13 sub-trees (Bipartite, Cochain, Cup, CupAW, Delta,
    **Dyadic (with 8 sub-trees)**, Fractal, Hodge, **HodgeConjecture
    (6 sub-trees)**, Universal).  Dyadic and HodgeConjecture each
    carry their own sub-classification — well-organised.
  - Real213: large but each file thematic (Cut, CutSum, CutDiv,
    DyadicTrajectory etc.).

No consolidation recommended — current classification is the
emergent product of the 213-marathon and reflects mathematical
structure, not session sediment.

### Physics/ (262 files in 16 sub-trees)

Sub-trees: AlphaEM, Atomic, AtomicCorrespondences, Basel, Cosmology,
Couplings, Foundations, Hadron, Higgs, Library,
Mass, Mixing, Nuclear, Simplex, Substrate, YangMills.  Each
thematic.  `INDEX.md` at top maintains navigation.  No
consolidation needed.

## Open Issues identified during survey

### Issue 1: R-prefix typeclass rename — RESOLVED in same pass

Initial recommendation in this note was to **REJECT** the rename
on the grounds that R12/R3/R4 was "load-bearing" cross-reference
to seed/AXIOM.md.

That recommendation was **wrong** and is reversed.  Re-reading
seed/AXIOM.md §9 directly:

  - §9.0 declares the R1–R5 frame **stepped back from**
    (deprecated; cf. `archive/30_bool_is_liar_paradox.md`).
  - §9.1 explicitly states the R-prefix is *historical*: "A
    future audit pass may rename these typeclasses to remove
    the historical R-prefix while preserving semantics."

So AXIOM.md itself **invites** the rename.  The "load-bearing"
framing was Claude importing a software-engineering frame that
seed/AXIOM.md does not endorse.

**Rename executed in the same audit pass** (16-file change):

| Before | After |
|---|---|
| `R12Codomain` | `CommBinaryCodomain` |
| `R3Codomain` | `NonVanishingCodomain` |
| `R4Codomain` | `ConjugationCodomain` |
| `derive_r4_codomain` | `derive_conjugation_codomain` |
| `#verify_r4` | `#verify_conjugation` |
| `DeriveR4Codomain.lean` | `DeriveConjugationCodomain.lean` |
| `VerifyR4.lean` | `VerifyConjugation.lean` |
| `VerifyR4Test.lean` | `VerifyConjugationTest.lean` |
| `r4_conj_*` theorems in CUniquenessBridge | `conjugation_*` |
| `ZSqrt.R4_of_pos` | `ZSqrt.conjugation_of_pos` |

Build clean, axiom scan unchanged.  AXIOM.md §9.1 itself updated
to mark the rename as completed.

### Issue 2: `FinitismIsConsequence.lean` filename + theorem names

The file in `Physics/Foundations/FinitismIsConsequence.lean` is
content-correct under the new spec (the theorems witness type
distinction).  Docstrings were rewritten in this audit pass to point
at `seed/RESOLUTION_LIMIT_SPEC.md`.  The filename + theorem names
(`completed_infinity_fails`, `finitism_is_consequence`) are retained
for stable external references.

Logged for follow-up: a future stage may rename the file +
theorems to `ResolutionLimitConsequences.lean` /
`cauchy_trajectory_distinct_from_exact` once external citation paths
are confirmed (no Lean file imports this module, only
`Physics/INDEX.md` lists the name).

### Issue 3: PatternCatalog.lean docstring (line 107)

Updated in this audit pass — replaced "213's Finitism principle" with
explicit pigeonhole phrasing tied to N_U.

### Issue 4: PhaseRouting.lean docstring (line 9)

Already correctly phrased ("ZFC-internal debates *about* infinity that
213 does not engage in").  No change.

### Issue 5: DyadicTrajectory.lean docstring (line 491)

Already correctly phrased ("type-preservation under ∅-axiom, NOT
'ZFC fiction rejection'").  No change.

## Recommendations (no action this pass)

  1. Hodge-cluster note grouping in research-notes/ (deferred —
     would touch Lean-doc-comment cite chains).
  2. R-prefix rename: **reject** — load-bearing nomenclature.  Add
     a docstring cross-ref instead.
  3. `FinitismIsConsequence.lean` rename: **defer** to a separate
     stage with explicit user approval.
