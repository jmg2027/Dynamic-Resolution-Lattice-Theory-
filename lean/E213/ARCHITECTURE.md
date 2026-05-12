# lean/E213/ARCHITECTURE.md — 213 ring-model architecture (canonical)

This document captures the **theoretical structure** of the 213 Lean
library: which rings exist, what each is *for*, and how they fit
together.  Everything else (INDEX.md, CLAUDE.md, sub-cluster
READMEs) follows from this.

Last revised: 2026-05-06 (post-M14 architectural rename).
Pre-M14 history available via `git log -- lean/E213/ARCHITECTURE.md`.

## 0. Concentric ring model

213 is structured as **6 concentric rings** where imports flow
inward only.  A file at ring N may import only from rings ≤ N.

```
   App  ─→  Lib  ─→  Meta  ─→  Lens  ─→  Theory  ─→  Term
                                                      (0-axiom)
                  imports flow this direction
```

| Ring | Name | Role |
|---|---|---|
| 0 | `Term/`     | Type-theoretic mechanism, 0-axiom scaffolding |
| 1 | `Theory/`   | Raw axiom + forced-shape uniqueness proofs |
| 2 | `Lens/`     | Lens catamorphism algebra |
| 3 | `Meta/`     | Metatheorems about the framework |
| 4 | `Lib/`      | Mathematics + physics content libraries |
| 5 | `App/`      | User-facing applications |

The names are **direct**: each ring is named for what it actually
contains, not for an OS analogy.  Pre-M14 names were
Kernel/Firmware/Hypervisor/Meta/App; the metaphor leaked
("Hypervisor" is not virtualizing anything — it's the Lens
catamorphism layer).

## 1. Ring definitions

### Term/  (Ring 0 — type-theoretic mechanism)

**Role**: Lean-side scaffolding to run 213 inside Lean 4.  Deep-
embedded `Term` type + total functions (compare, eval, normal form)
so 213 facts check by Lean's kernel reduction without ANY of
Lean's external axioms (propext, Quot.sound, Classical.choice).

**Key property**: All 101 Term theorems are *literally 0-axiom*.
Verified by `tools/kernel_regress.sh`.

**Public API**: `Term/API.lean` re-exports the K1–K4 surface:
  * **K1 — Data**: `Term`, `Term.eval`, `Term.{nS, nT, d, c}`
  * **K2 — Computation**: `Term.{equiv, le_b, lt_b, pair, offDiag,
    equivQ, leQ}`, `Decide.{allBelow, existsBelow}`
  * **K3 — Soundness**: `Sound.{of_equiv, of_le_b, of_lt_b,
    of_equivQ, of_leQ}`
  * **K4 — Tactic** (separate import): `Term.Tactic.{Omega213,
    Nat213, Mod213, Pow213, Fin213, QuadNorm}`

### Theory/  (Ring 1 — the axiomatic commitment)

**Role**: The 213 axiom itself — `Raw` type + 4-clause definitional
commitments (a, b, slash, slash_comm).  This is the actual
epistemic commitment.  Plus the proofs that this shape is forced
uniquely.

**Sub-clusters**:
  * `Theory/Raw/`        — public Raw API (Core, Slash, Swap,
                            SwapSlash, Fold, Hom, Levels, Rec, Signed)
  * `Theory/Atomicity/`  — forced-uniqueness proofs (Five,
                            FiveHelpers, PairForcing,
                            NonDecomposable, ArityForcing,
                            ArityForcingGeneral, PrimitiveSizes,
                            Alive)
  * `Theory/Internal/`   — implementation detail (Raw/Cmp,
                            CmpIndependence, DecEq,
                            SwapSlashInjective).  Direct
                            import discouraged.

**Public API**: `Theory/API.lean` bundles:
  * **TH-A — Raw axiom data**: Raw + 4 clauses + structural primitives
  * **TH-B — Atomicity**: forced-uniqueness proofs

### Lens/  (Ring 2 — catamorphism algebra)

**Role**: Lens framework — the catamorphism mechanism turning Raw
into any α-codomain via `Lens.view = Raw.fold`.  Provides the
universal "viewing" mechanism.

**Sub-clusters**:
  * `Lens/Algebra/`         — algebraic kernel (CardinalityLB,
                               Congruence, Corresp, IdLensEq)
  * `Lens/AxiomLenses/`     — Lean-axiom Lens witnesses (Funext,
                               Propext, QuotSound) + Bridges
  * `Lens/Characterisation/` — characterisation typeclasses + catalog
  * `Lens/Compose/`         — composition operators
  * `Lens/Instances/`       — 24+ concrete Lens instances
  * `Lens/Lattice/`         — refines lattice (Join, Meet, Family*)
  * `Lens/Leaves/`          — depth-leaf hierarchy
  * `Lens/Morphism/`        — morphism shape catalogue
  * `Lens/Properties/`      — derived predicates
  * `Lens/Refines/`         — refines preorder (Chain, Preorder)
  * `Lens/Universal/`       — Universal flat / quot lens
  * `Lens/Internal/`        — internal proof infra
                               (Algebra/{FreeAudit, FourDistinct,
                                SwapInvariant, Space})

**Public API**: `Lens/API.lean` exposes HV1–HV6:
  * **HV1 — Type**: `Lens (α : Type)`, `Lens.view`,
    `Lens.{leaves, depth}`
  * **HV2 — Equivalence**: `Lens.{equiv, refines}` + closures
  * **HV3 — Initiality**: `Lens.view_unique`, `SemanticAtom`,
    `Universal.Flat`
  * **HV4 — Lattice**: `joinLens`, `prodLens`, `Lattice.*`
  * **HV5 — Composition**: `Compose.{Factoring, ImageMinimum, OnLens}`
  * **HV6 — Canonical Form**: `Universal.QuotLens.universalLens`,
    `Properties.CanonicalForm.universalLens_recovers`

Optional separate imports: HV7 (full Instances catalogue),
HV8 (Characterisation catalog).

### Meta/  (Ring 3 — metatheorems)

**Role**: Propositions *about* the Lens framework + Raw structural
metatheorems.  "for all Lens, ...", "the codomain spec is the
Comm/NonVanishing/Conjugation hierarchy", "Raw bit patterns are
unique".

**Sub-clusters**:
  * `Meta/UniversalLens/` — concrete witnesses (Nat2/3/4, Q213,
                            Padding, TripleCapstone)
  * `Meta/Tactic/`        — meta-level tactics
                            (DeriveConjugationCodomain,
                             VerifyConjugation, NativeGuard,
                             PureGuard)

**Top-level**: SelfRecognising (codomain typeclass hierarchy),
AxiomMinimality{,Capstone}, BitPatternUniqueness, LensInternality.

**Public API**: `Meta/API.lean` bundles ME-1 SelfRecognising +
ME-2 AxiomMinimality + ME-3 LensInternality + ME-4 UniversalLens.
Tactic is a separate import (cross-cutting).

### Lib/  (Ring 4 — content libraries)

**Role**: Mathematics + physics content built using the framework
rings.  Two bounded contexts:
  * `Lib/Math/`     — 213-native mathematics (~495 files)
  * `Lib/Physics/`  — 213-native physics (~128 files)

Each Lib sub-tree has its own `Bridge.lean` files for cross-
context citations (anti-corruption layer pattern).

### App/  (Ring 5 — applications)

**Role**: Concrete applications using everything below.
Currently 1 file (`Simplex.lean`).

## 2. Discipline conventions

### API.lean per ring

Every framework ring has an explicit `<Ring>/API.lean`:
  * `Term/API.lean`    (K1–K4)
  * `Theory/API.lean`  (TH-A + TH-B)
  * `Lens/API.lean`    (HV1–HV6)
  * `Meta/API.lean`    (ME-1 .. ME-4)

Downstream consumers (Lib, App, external papers, rust-engine)
should import the API.lean rather than reaching into specific
sub-files.  This makes internal refactor safe.

### Internal/ per ring

Implementation detail lives in `<Ring>/Internal/`.  Direct import
of `Internal/*` from outside the ring is a code-review smell.
Currently:
  * `Theory/Internal/Raw/`    — DecEq, Cmp, CmpIndependence,
                                 SwapSlashInjective
  * `Lens/Internal/Algebra/`  — FreeAudit, FourDistinct,
                                 SwapInvariant, Space

Files in `Internal/` namespace as `E213.<Ring>.Internal.<sub>`.

### Bridge.lean for cross-context

When a file in one bounded context cites results from another, the
citation should go through an explicit `Bridge.lean`:
  * `Lib/Math/Cohomology/AlphaEMBridge.lean`
  * `Lib/Physics/<Cluster>/Bridge.lean` (12 sub-clusters)

This is the anti-corruption layer pattern: cross-context
references are explicit, named, and grep-discoverable.

### Naming

  1. **Path = namespace** — `Lib/Math/Cohomology/Universal/Prop53.lean`
     declares `namespace E213.Lib.Math.Cohomology.Universal.Prop53`.
     Enforced by `tools/sync_namespaces.py`.  Intentional exceptions
     (path ≠ namespace, ~15 files, documented):
       - **Type-defining files** keep the bare type-namespace
         (e.g. `Lens/LensCore.lean` declares `namespace E213.Lens`,
         not `E213.Lens.LensCore`, because the file *is* the
         `Lens` type).
       - **Doubled-type-namespace pattern** (CayleyDickson) — when a
         structure of the same name as the file lives inside the
         file's namespace (e.g. `namespace E213.Lib.Math.CayleyDickson.ZI`
         + `structure ZI`), downstream extension files
         (`ZIDomain`, `ZIArith`, `ZIHom`) declare
         `namespace E213.Lib.Math.CayleyDickson.ZI.ZI` to attach
         dot-notation to ZI values.  This is R10 in
         `research-notes/CONSOLIDATION_PROTOCOL.md`.
       - **Internal-shared umbrella** (e.g. `Theory/Internal/Raw/`
         files share `namespace E213.Theory.Internal`).
       - **Descriptive sub-namespace** when the namespace label
         conveys the *content* better than the file name
         (e.g. `Lib/Physics/AlphaEM/Augmented.lean` declares
         `namespace E213.Lib.Physics.AlphaEM.BracketWithDysonTail`).

  2. **No session-numbered labels** — no `Phase2/`, `Phase3/` etc.
     for long-lived names.

  3. **Drop redundant prefix** — `Lens/Factoring.lean`, not
     `Lens/LensFactoring.lean` (cluster name appears in path).

  4. **One topic per file** — split when 2 unrelated topics
     accumulate.  Sub-cluster early when 3+ thematically-related
     files appear.

  5. **INDEX.md per non-trivial sub-tree** (≥ 5 files).

## 3. Tooling

  * `tools/sync_namespaces.py` — namespace ↔ path alignment
  * `tools/layer_audit.py`     — derives each file's natural ring;
                                 reports violations (path < natural)
                                 and downgrade hints (path > natural)
  * `tools/kernel_regress.sh`  — Term ring 0-axiom regression
  * `tools/scan_axioms.py`     — per-module axiom audit
  * `tools/scan_all_axioms.py` — repo-wide axiom audit

## 4. Companion artifact: rust-engine

`rust-engine/` mirrors this ring structure crate-by-crate:
  * `crates/term/`    ↔ `lean/E213/Term/`
  * `crates/theory/`  ↔ `lean/E213/Theory/`
  * `crates/lens/`    ↔ `lean/E213/Lens/`
  * `crates/app/`     ↔ `lean/E213/App/` + Lib content

Rust is a numerical / search-engine companion ("calculator for
when Lean takes too long"), not a re-implementation.  Every Rust
result must point to a Lean theorem (whitelist enforced via
`rust-engine/whitelist.toml` + `tools/verify-citations`).
