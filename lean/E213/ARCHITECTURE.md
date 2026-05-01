# lean/E213/ARCHITECTURE.md — 213 layer architecture (canonical)

This document captures the **theoretical structure** of the 213 Lean
library: which layers exist, what each is *for*, and how they fit
together.  Everything else (INDEX.md, CLAUDE.md, sub-cluster
READMEs) follows from this.

Last revised: 2026-05-XX (post-OS-dissolution, post-Meta-audit).

## 0. One axis: vertical layers + Math/Physics topical labels

**Every file has exactly one vertical layer** —
Kernel / Firmware / Hypervisor / Meta / App — mechanically
determined by its import closure.  `tools/layer_audit.py` computes
it.  The script reports zero violations on the current tree.

**Math/ and Physics/ are the only horizontal topical clusters.**
A `Math/X.lean` file might be Kernel-level (no E213 imports),
Firmware-level (uses Raw), Hypervisor-level (uses Lens), or
Meta-level (uses metatheorems) — depending on what it imports.  The
folder name only says "this is mathematics-flavored" / "this is
physics-flavored", not "this is at layer X".

Other top-level trees that previously existed have been fully
distributed into the vertical-layer dirs and Math/Physics by content.
The marker name `Research/` is also gone — its files were absorbed
into the topical sub-clusters of their target layer:

  - `Research/` (337 files):
    - math content → `Math/{Real213, CayleyDickson, Cauchy, ModArith,
      Modulus, Diagonal, Irrational, Hyper, Choice, Infinity}/` +
      9 loose Math/* files
    - Lens framework research → distributed into `Hypervisor/Lens/`
      sub-clusters: `Lattice/`, `Compose/`, `Properties/`,
      `Morphism/`, `Leaves/`, `Refines/`, `Kernel/`, `Universal/`,
      and merged into `Instances/` (16 added) + top-level
      `Initiality.lean`, `SemanticAtom.lean` under `Hypervisor/Lens/`
    - axiom-uniqueness metatheorems → `Meta/{AxiomMinimality,
      AxiomMinimalityCapstone, Universal/{LensClaim,
      MorphismFactor, Reflection}}.lean`
    - Raw encoding research → flattened into `Firmware/Raw/{DecEq,
      ComplexityClass, CmpIndependence, SwapSlashInjective}.lean`
  - `Infinity/` (9 files) → `Math/Infinity/`
  - `Tactic/` (11 files + tests) → `Kernel/Tactic/` (Omega213, QuadNorm)
    + `Meta/Tactic/` (VerifyR4, DeriveR4Codomain) + `Math/Tactic/`
    (HurwitzRing, IntSquare, QuadExtension)
  - `Tools/` (1 file) → `Firmware/Tools/CertChecker.lean`

Distribution after the 2026-05-XX reorg:

| top-folder | Kernel | Firmware | Hypervisor | Meta | App | total |
|---|---|---|---|---|---|---|
| Kernel/ | 18 | 0 | 0 | 0 | 0 | 18 |
| Firmware/ | 0 | 25 | 0 | 0 | 0 | 25 |
| Hypervisor/ | 0 | 0 | 78 | 0 | 0 | 78 |
| Meta/ | 0 | 0 | 0 | 23 | 0 | 23 |
| App/ | 0 | 0 | 0 | 0 | 1 | 1 |
| Math/ (484) | 36 | 211 | 231 | 6 | 0 | 484 |
| Physics/ (275) | 2 | 168 | 105 | 0 | 0 | 275 |

Reading the table: a `Hypervisor/X.lean` file is at Hypervisor by
both path AND mechanics; a `Math/X.lean` file's natural mechanical
layer is one of {Kernel, Firmware, Hypervisor, Meta} — pick by
running `layer_audit.py`.

**Why keep Math/Physics horizontal at all?** Topical locality.
Splitting `Math/Cohomology/Delta/Core.lean` into `Hypervisor/Math/
Cohomology/Delta/Core.lean` is mechanically right but breaks the
"one folder = one mathematical sub-discipline" intuition.  Math/Physics
are kept as topical roots; their mechanical layer is exposed via
`layer_audit.py` as metadata.

## 1. Vertical layers (canonical definitions)

### Kernel/

**Role**: Lean-side scaffolding to *run* 213 inside Lean 4.  Provides
deep-embedded `Term` type + total functions (compare, eval, normal
form) so that 213 facts can be checked by Lean's kernel reduction
without using ANY of Lean's axioms (propext, Quot.sound,
Classical.choice).

**Key property**: All 101 Kernel theorems are *literally 0-axiom*.
Verified by `tools/kernel_regress.sh`.

**Imports**: Only Lean core (Nat, Bool, Prop, structural induction).

**Files**: 14 — `Term`, `Compare`, `Pair`, `Rat`, `Decide`, `Sound`,
`MonomialAxioms`, `Demo`, `Cap_*` capstones (capability collection).

**Naming convention**: `Cap_X.lean` files use `namespace E213.Kernel.Cap.X`
(intentional — Cap is a deliberate sub-namespace, file name uses `_`
for grouping in directory listing).  `{Term,Compare,Pair,Rat}.lean`
share `namespace E213.Kernel.Term` umbrella (also intentional).

### Firmware/

**Role**: The 213 axiom — Raw type + 4-clause definitional commitments
(a, b, slash, slash_comm).  This is the actual epistemic commitment
of 213.  Plus the proofs that this shape is *forced uniquely*.

**Sub-clusters**:

  `Firmware/Raw/` (8 files) — internal implementation of Raw +
    eliminator, fold, swap, comparison.  Internal namespace
    `E213.Firmware.Internal` (umbrella shared, intentional).

  `Firmware/Raw.lean`, `RawLevels.lean`, `RawSwap.lean` (3 files at
    root) — public Raw API + level-bounded variants + swap
    automorphism.  All under `namespace E213.Firmware` umbrella.

  `Firmware/Atomicity/` (7 files) — **forced shape uniqueness
    proofs**.  Pure-ℕ theorems that don't import Raw.  They prove
    that any *abstract* atomic structure with the right conditions
    must instantiate as the Raw axiom's choice (d=5, NS=3, NT=2,
    sizes {2,3}, alive (1,1), arity k=2).  This is the axiom's
    proof obligation: "Raw is THE shape, not A shape."

**Imports**: None outside Firmware (or Lean core for Atomicity).

**Why "Firmware"?**: In computer terms, firmware is the immutable
commitment burned into the system.  213's Raw axiom + its
forced-uniqueness proofs play the same role.

### Hypervisor/

**Role**: Lens framework — the *catamorphism mechanism* that turns
Raw into any α-codomain via `Lens.view = Raw.fold`.  Provides the
universal "viewing" mechanism.

**Files**: `Lens.lean` (the `Lens α` type + `view` + R4Codomain
machinery).  Currently 1 file at root.

**Imports**: Firmware/.

**Why "Hypervisor"?**: A hypervisor sits between firmware and
applications, providing virtualization.  Lens is the same:
between Raw axiom and any concrete α, providing a *view*
abstraction.  Different α = different "VM" of 213.

### Meta/

**Role**: **Metatheorems about the Lens framework** + Raw structural
metatheorems.  Things that say "for all Lens, ...", "the codomain
spec is R1-R4 hierarchy", "Raw bit patterns are unique".

**True meta files** (after planned cleanup):

  `Meta/UniversalLens/` (11 files) — "universal Lens" claim:
    a Lens is universal iff its view is injective.  Concrete
    universal Lenses constructed at codomains {ℕ², ℕ³, ℕ⁴, Q213,
    Q213³} + padding theorems + triple capstone.  This is the
    formal core of the thesis "any distinguishing act IS 213"
    (Universal-Lens metatheory).

  `Meta/SelfRecognising.lean` — R1-R4 codomain spec hierarchy
    (4-tier typeclass extends chain).

  `Meta/BitPatternUniqueness.lean` — key lemma `2^m+2^n = 2^p+2^q`
    uniqueness used by UniversalLens injectivity proofs.

  `Meta/RawInductionDemo.lean` — induction principle demo for Raw.

(Concrete Lens instances and Lens-level characterisations that
previously lived in `Meta/Lens/` were migrated to
`Hypervisor/Lens/Instances/` and `Hypervisor/Lens/Characterisation/`
respectively — see §3 Q3.  Meta/ is now pure metatheory.)

**Imports**: Hypervisor (uses Lens type) → so dependency-wise
above Hypervisor.

**Why "Meta"?**: Metatheory of Hypervisor.  A claim like "all Lens
factor through identity Lens" lives here.

### App/

**Role**: Concrete applications that USE everything below to do
specific work.  `Simplex.lean` — the 4-simplex structure derived
from Atomicity (V_A = {0,1,2}, V_B = {3,4} from canonical_partition).

**Imports**: Firmware/Atomicity (uses atomic_iff_five etc.).

**Currently**: 1 file.  Capstones currently live in Physics/Capstones/
but conceptually some belong here.  Open question (see §3).

## 2. Topical labels (NOT a separate axis — see §0)

The folders below are *topical groupings*, not layers.  Each file
inside has its own vertical layer (Kernel/Firmware/Hypervisor/Meta)
determined by import closure.  Run `tools/layer_audit.py` for the
authoritative per-file assignment.

### Math/

**Role**: 213-internal mathematics — derived from Lens + Atomicity
by USING the framework to construct mathematical content (not
providing framework).

**Sub-clusters**:

  `Math/Cohomology/` — K_{3,2}^{(c=2)} cohomology, Δ⁴ Leibniz,
    Hodge ⋆⋆, fractal α_GUT, Universal Property, Pell-CRT family
    (Dyadic/), bipartite, cup product
  `Math/Linalg213/` — Vec 5 (because d=5), basis span, chiral
    decomposition (Paper 1)
  `Math/{Cauchy,Foundation,Continuity,CutOps,Series,Generic,Analysis,
    Analysis213}.lean` — Real213 plumbing, real-analysis
    foundations
  `Math/Pigeonhole.lean` — universal Fin pigeonhole infrastructure

**Layer distribution** (212 files): 2 Kernel, 202 Firmware, 8 Hypervisor.
Most "Math" content sits at Firmware-level (uses Raw + Atomicity);
the Hypervisor-level minority uses the Lens framework.

### Physics/

**Role**: 213-internal physics — derivations of α_em, masses,
mixing, magic numbers, etc., with explicit ppm-level matches to
Standard-Model values when applicable.

**Sub-clusters** (18, post-2026-05-01 reorg):

  `AlphaEM/`, `Couplings/`, `Foundations/`, `Hadron/`, `Mass/`,
  `Higgs/`, `Nuclear/`, `Mixing/`, `Cosmology/`, `Atomic/`,
  `Simplex/`, `Basel/`, `FamousCoincidences/`, `YangMills/`,
  `Capstones/`, `Library/` (atomic catalog), `Substrate/`
  (Phase-2 substrate-genesis), `AtomicCorrespondences/`
  (formerly Phase-3 Translation — domain-by-domain SM→DRLT
  correspondence).

**No "PhaseN"**: per CLAUDE.md philosophy, all session-numbered
labels (Phase2, Phase3, Phase4) are forbidden for long-lived
names.  Content has been redistributed by topic.

**Layer distribution** (275 files): 2 Kernel, 168 Firmware,
105 Hypervisor.  Roughly 60% Firmware (atomicity-based mass/coupling
formulas), 38% Hypervisor (full Lens-based observable construction).

### Where the old top-level dirs went (2026-05-XX reorg)

  - **Research/** (337 files) — fully distributed (no more `Research/`
    marker dir; files absorbed into topical sub-clusters):
    - mathematics-flavored exploration → `Math/{Real213, CayleyDickson,
      Cauchy, ModArith, Modulus, Diagonal, Irrational, Hyper, Choice}/`
      + 9 loose Math/* files
    - Lens-framework research → distributed into `Hypervisor/Lens/`
      sub-clusters (Lattice/, Compose/, Properties/, Morphism/,
      Leaves/, Refines/, Kernel/, Universal/, Instances/) and
      top-level `Initiality.lean`, `SemanticAtom.lean`.
    - axiom-uniqueness metatheorems → `Meta/{AxiomMinimality,
      AxiomMinimalityCapstone, Universal/{LensClaim,
      MorphismFactor, Reflection}}.lean`
    - Raw encoding research → flattened into `Firmware/Raw/{DecEq,
      ComplexityClass, CmpIndependence, SwapSlashInjective}.lean`
  - **Infinity/** (9 files: Cantor, Gödel, Tower, …) → `Math/Infinity/`
  - **Tactic/** (11 + tests):
    - `Omega213`, `QuadNorm`, `OMEGA213_MIGRATION.md` → `Kernel/Tactic/`
    - `VerifyR4`, `DeriveR4Codomain` → `Meta/Tactic/`
    - `HurwitzRing`, `IntSquare`, `QuadExtension` → `Math/Tactic/`
  - **Tools/** (1 file: CertChecker.lean) → `Firmware/Tools/`

Note: `namespace E213.Tactic` umbrella (used by `omega213` macro) is
preserved as the *internal* namespace of `Kernel/Tactic/Omega213.lean`
— users still write `open E213.Tactic` to get the macro.  The
*path* is `Kernel/Tactic/`; the *namespace* `E213.Tactic` is
intentionally short for ergonomics.

## 3. Open architectural questions

### Q1. Universal Lens — Firmware-strengthening or Hypervisor-meta?

User intuition: "any distinguishing IS 213" sounds like an axiom-
level claim (Firmware-strengthening: "Raw is THE axiom, not AN
axiom").

Resolution: keep in Meta/.  Reason — Universal Lens *imports*
Hypervisor.Lens; putting it in Firmware would invert the
dependency graph.  Document the *interpretation* as
"Firmware-strengthening realised through a Hypervisor-level
metatheorem" in the Meta/UniversalLens README.

### Q2. Capstones — App or Physics/?

Current: `Physics/Capstones/{ValidationStandardOne, PureAtomic
Observables, FinitistObservableChain, ...}` lives in Physics/.

Conceptually, capstones are App-level (they USE Math + Physics
to produce specific theorems).  But they're physics-flavored,
so co-locating with Physics/ aids discoverability.

Decision: leave in Physics/Capstones/ for now.  If App/ grows
substantively (more applications), revisit.

### Q3. Meta/ concrete-Lens-instance cleanup ✅ RESOLVED 2026-05-XX

Concrete Lens instances `{Bool, Path, Max, Parity, ZMod6}.lean`
were moved out of `Meta/Lens/` to `Hypervisor/Lens/Instances/`
(they are uses of Lens, not claims about Lens).

Lens-level characterisations `{Catalog, Characterisation,
CUniquenessBridge}.lean` were moved to `Hypervisor/Lens/Characterisation/`.

`Meta/` now contains only true metatheorems: `UniversalLens/` (11
files), `SelfRecognising.lean`, `BitPatternUniqueness.lean`,
`RawInductionDemo.lean`.

### Q4. Research/ layer-mixed sub-clusters

`Research/Lens/` (32 files) — Hypervisor metatheorems exploration.
`Research/Kernel/`, `Research/Universal/` — Meta-layer exploration.

These could move to vertical layers (Hypervisor/, Meta/).  Decision
deferred — they remain in Research/ to preserve "exploratory" status
labeling.  They're treated as *Research-tier* contributions to
Hypervisor/Meta even though physically in Research/.

### Q5. Math/Physics/Research → OS as wrapper?

Earlier proposal: rename App/ → OS/ (math/physics frameworks as
"system services").  Decision: rejected.  Math/Physics/Research are
already at App-level by import direction; no need to rename.  The
old `OS/` was a misnomer for what's now `Firmware/Atomicity/`, which
has been corrected.

## 4. Dependency graph (canonical)

```
                    ┌─────── Lean 4 core ─────────┐
                    ↓                             ↓
              Kernel/                    [Tactic, Tools, Infinity]
                    ↓                             ↑ (orthogonal,
              Firmware/Raw                          used at any layer)
              Firmware/Atomicity (no Raw import — proves Raw shape)
                    ↓
              Hypervisor/Lens
                ↓        ↓
              Meta/    Math/  Physics/  Research/
                          ↓      ↓        ↑
                          └───→ App/  ←───┘
```

Imports flow top→bottom.  Theorems compose bottom→top.

## 5. Naming conventions (canonical)

  1. **Path = namespace** — `Math/Cohomology/Universal/Prop53.lean`
     declares `namespace E213.Math.Cohomology.Universal.Prop53`.
     Enforced by `tools/sync_namespaces.py` (skips intentional
     umbrella-shared dirs).

  2. **No session-numbered labels** — no `Phase2/`, `Phase3/`,
     `Phase4/` for long-lived dirs.  Reorganise by content.

  3. **Drop redundant prefix** — `Lens/Factoring.lean`, not
     `Lens/LensFactoring.lean` (cluster name appears in path).

  4. **V-prefix on digit-start** — `V137.lean` (Lean module names
     cannot start with digit), `V2.lean` (FamousCoincidences/V2.lean
     was originally `FamousCoincidencesII.lean`).

  5. **One topic per file** — when a file accumulates two
     unrelated topics, split.  When 3+ thematically-related files
     appear, sub-cluster early (cheap; flat-root accumulation is
     hard to undo).

  6. **INDEX.md per non-trivial sub-tree** (≥ 5 files).

## 6. Tooling

  - `tools/sync_namespaces.py` — auto namespace↔path alignment
    (sentinel-protected single pass; no sed-cascade errors).
  - `tools/layer_audit.py` — derive each file's natural layer from
    its import closure.  **A file's layer is not a philosophical
    question** — it is mechanically determined: `layer(F) ≥
    max(layer(I))` over all `E213.*` imports `I` of `F`.
    Output:
      - **violations** (`path_layer < natural_layer`): architectural
        inversions — file claims to be foundational but pulls in
        something higher.  These must be fixed.
      - **downgrade hints** (`path_layer > natural_layer`):
        informational — file *could* be moved down.  Not necessarily
        a problem; semantic placement may legitimately exceed
        mechanical placement (see §6.1).
    Run after any structural change.
  - `tools/kernel_regress.sh` — verify Kernel/ stays 0-axiom.
  - `tools/audit_axioms.py` — full-tree axiom survey.
  - `tools/port_candidates.py` — find unported Lean theorems for
    rust-engine mirror.

### 6.1 Mechanical vs semantic layer placement

`layer_audit.py` reports cases where a file's path layer is strictly
*above* its natural (import-derived) layer.  These are NOT violations
— a few classes of intentional over-placement:

  - `Firmware/Atomicity/{Five, PairForcing, NonDecomposable, Alive,
    ArityForcing, ArityForcingGeneral, PrimitiveSizes}` — pure-ℕ
    forced-uniqueness proofs that mechanically belong at Kernel.
    Kept at Firmware because they document *Raw's forced shape*
    (see `seed/AXIOM.md §1.3`); semantic adjacency to Raw outweighs
    mechanical depth.
  - `Hypervisor/Lens.lean` — only imports Firmware mechanically, but
    is the umbrella entry point for the entire Hypervisor layer.
  - `App/Simplex.lean` — only imports Firmware mechanically, but is
    a 213 *application* (counting on the simplex), so App is the
    semantic home.
  - `Meta/{BitPatternUniqueness, RawInductionDemo, SelfRecognising,
    UniversalLens/Core}` — meta-level statements about Raw whose
    proofs happen to not require Hypervisor/Meta facilities.  Kept
    at Meta because the *claim* is metatheoretic.

**Rule for new files**: place by import depth first (run
`layer_audit.py`), then promote upward only if the file's *purpose*
is meta-relative-to-its-imports (e.g., a forced-shape proof, a
universality claim, an application).  Promotion-without-reason is
discouraged.

### 6.2 Topical cluster sub-layering (within-cluster depth)

The same import-depth rule applies *within* a topical cluster.
For each file in `Math/`, `Physics/`, `Research/`, `layer_audit.py`
computes its topological depth restricted to imports from the same
cluster.  Sub-folders whose depth span is wide (≥ 15) are
**sub-clustering candidates** — a single flat folder with a 15-deep
import chain is a sign that natural sub-layers exist but haven't
been folded into the directory structure.

Current state (2026-05-XX):

| Cluster | Sub-folder | files | depth span | status |
|---|---|---|---|---|
| Math | Cohomology | 195 | 44 | **WIDE** — single mega-folder |
| Math | Linalg213 | 8 | 18 | wide-narrow |
| Physics | Couplings | 20 | 15 | mid |
| Physics | Foundations | 27 | 16 | mid |
| Physics | Capstones | 13 | 15 | mid |
| Research | Real213 | 181 | **90** | **WIDE** — Real213 marathon chain |

Recommendation: WIDE sub-folders are candidates for further
sub-clustering.  Especially `Cohomology/` (44-deep, 195 files) and
`Real213/` (90-deep, 181 files) — these are entire research
sub-projects in single folders.  Future reorg should depth-band them
(e.g., `Real213/Foundations/`, `Real213/Phase{A..H}/`,
`Real213/Capstones/` keyed off mechanical depth, not session number).

The `(min, med, max)` triple printed by `layer_audit.py` for each
sub-folder is the canonical signal: *narrow span → coherent
sub-cluster; wide span → split candidate*.

## 7. History (for context only — do not use as current state)

  - 2026-05-01: First Phase 0-7 cleanup (sub-clustering,
    documentation sync).
  - 2026-05-XX: Deep file-by-file reorg (Research/ 127→13 flat,
    Physics/ 121→4 flat, namespace↔path alignment).
  - 2026-05-XX: OS/ dissolved (atomicity proofs → Firmware/Atomicity/,
    Pigeonhole → Math/).  Established this document as canonical.
  - 2026-05-XX: `tools/layer_audit.py` added.  Surfaced 1 violation
    (`Hypervisor/Lens/Characterisation/CUniquenessBridge.lean`
    imported Meta.SelfRecognising) — moved to `Meta/CUniquenessBridge.lean`.
    Tree now has **0 layer violations**; remaining 12 over-placements
    are intentional semantic placements (see §6.1).
  - (Pending): Meta/ concrete-Lens-instances → Hypervisor/Lens/Instances/.

## 8. How to evolve this document

When the architecture changes (a layer added, removed, redefined):

  1. Update this file FIRST.
  2. Update `lean/E213/INDEX.md` to reference the new state.
  3. Update CLAUDE.md if the change affects agent behavior.
  4. Run `tools/sync_namespaces.py` to align paths.
  5. Update HANDOFF.md with the architectural change record.

This document is the canonical statement of *what 213's structure
IS*.  All other docs follow.
