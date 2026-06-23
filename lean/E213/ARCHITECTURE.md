# lean/E213/ARCHITECTURE.md — 213 layer architecture (canonical)

This document defines the **layer structure** of the 213 Lean library —
which rings exist, what each is for, and how imports flow.  All other
documents (INDEX.md, CLAUDE.md, sub-cluster READMEs, etc.) follow this one.

## Philosophical foundations (canonical preamble)

The ring architecture below is a *code-organization convenience*,
not a philosophical hierarchy.  Per
`seed/AXIOM/05_no_exterior.md` §5.1, there is no exterior to
213; per §1.2 (revised), Lens application is itself a
residue-internal event, not a layer placed above Raw.

Hence:

- "X imports Y" is a Lean dependency relation, not an
  ontological "X depends on Y as substrate".
- The rings (Term → Theory → Lens → Lib + Meta) are
  *expressions of one residue* at different levels of derivation
  — Term encodes Raw mechanically; Theory states the axiom +
  observables; Lens records readings of that residue; Lib
  elaborates physics + math content.  Every ring is reading the
  same residue from a different vantage; none is a foundation
  supporting another.
- The substrate / superstructure framing ("Theory is more
  fundamental than Lens", "Term is the bare metal layer") is
  not consistent with §8.1.  In practice the rings express
  dependency order; nothing more.

Canonical statements:
  - "Lens is residue self-pointing" — `seed/AXIOM/04_uniqueness.md` §4.2 (revised 2026-05-20).
  - "Layers in code are not layers in reality" — present
    section.
  - "Lens application IS a residue-internal event, not an
    addition to Raw" — `seed/AXIOM/07_primacy.md` §7.
  - "All classical foundations are Lens compositions reading
    the same Raw residue" —
    `lean/E213/Lib/Math/Foundations/AxiomSystems/INDEX.md`.

When any sub-INDEX uses "substrate", "foundation", "bare-metal",
"sits between", or similar architectural metaphors, those are to
be read as code-organization vocabulary, not ontological claims.

## 0. Layer model

213 has a **4-ring + Meta** structure.  Meta is ring-independent (the Lean 4 bridge).

```
Meta  ← ring-independent — the bridge to Lean 4.  Usable by any ring.
        Use with care (axiom-cost / ring-independence trade-off).
─────────────────────────────────────────────────────────
Lib    ← uses only the Lens API           ↑
Lens   ← uses only the Theory API          │ import direction
Theory ← uses only the Term API            │ (inward only)
Term   ← Raw implementation (Tree, etc.)   │
─────────────────────────────────────────────────────────
```

**Import rule** — a file in each ring may use only:
  1. what is defined within its own ring
  2. the API of the ring **directly below** (exactly one step down)
  3. any file in Meta

Upward imports (e.g. Theory → Lib) or multi-step jumps (e.g. Lib → Theory
directly — bypassing the Lens API) are all violations.  Detected by the
layer audit.

| Ring | Role |
|---|---|
| `Term/`    | Implementation of Raw (Tree, etc.).  The API surface exposed to Theory. |
| `Theory/`  | Defines Raw's axiom + structure via the Term API.  The API surface exposed to Lens. |
| `Lens/`    | Defines the Lenses via the Theory API.  The API surface exposed to Lib. |
| `Lib/`     | Implements math/physics content via the Lens API. |
| `Meta/`    | The bridge to Lean 4.  Ring-independent — usable by any ring. |

> **Spec (original, Mingu Jeong, 2026-05-12):**
> 「해당 링에는 해당 링 아래에서 받아온 api 혹은 Meta (meta 는 링에서
> 벗어나서 존재할 수 있는 친구들.  Lean4 와의 브릿지라고 생각할 수
> 있음) 혹은 해당 링 안에서 정의된 것들만을 사용할 수 있다.  api 로
> 위쪽 링으로 올릴 수 있다.」
>
> *Translation:* "A given ring may use only the API received from the
> ring below it, or Meta (Meta being the things that can exist outside
> the rings — think of it as the bridge to Lean 4), or things defined
> within the ring itself.  Via the API, results can be lifted up to the
> ring above."

## 1. Ring definitions

### Term/  (Raw implementation)

**Role**: The machine representing 213's Raw inside Lean 4.  Deep-embedded
`Tree` + `Term` type + total functions (compare, eval, normal form).
**Closed under 0-axiom** within this ring — no external axioms (propext,
Quot.sound, Classical.choice, etc.).

**Key property**: Every Term theorem is *literally 0-axiom*.
Verified by `tools/kernel_regress.sh`.

**Public API**: `Term/API.lean` re-exports K1–K4:
  * **K1 — Data**: `Term`, `Term.eval`, `Term.{nS, nT, d, c}`
  * **K2 — Computation**: `Term.{equiv, le_b, lt_b, pair, offDiag,
    equivQ, leQ}`, `Decide.{allBelow, existsBelow}`
  * **K3 — Soundness**: `Sound.{of_equiv, of_le_b, of_lt_b,
    of_equivQ, of_leQ}`
  * **K4 — Tactic** (separate import): `Term.Tactic.{Omega213,
    Nat213, Mod213, Pow213, Fin213, QuadNorm}`

### Theory/  (Raw axiom + forced-shape proofs)

**Role**: The 213 axiom itself — `Raw` type + 4-clause definitional
commitments (a, b, slash, slash_comm).  Forced-shape uniqueness proofs
follow from these commitments.  **Uses only the Term API**.

**Sub-clusters**:
  * `Theory/Raw/`       — public Raw API (Core, Slash, Swap,
                           SwapSlash, Fold, Hom, Levels, Rec, Signed,
                           **Endomorphic**, Demo) + API.lean
                           (re-export shim).
  * `Theory/Atomicity/` — forced-uniqueness proofs (Five,
                           FiveHelpers, PairForcing,
                           NonDecomposable, ArityForcing,
                           PrimitiveSizes, Alive)
  * `Theory/CDDouble/`  — generic Order-4 mechanism (UniversalOrder4,
                           GenericLiftDemo)
  * `Theory/RawCmpIndependence.lean` — axiom-independence of cmp
                           choice (meta-theorem).

**Public API**: `Theory/API.lean` bundles:
  * **TH-A — Raw axiom data**: Raw + 4 clauses + structural primitives
  * **TH-B — Atomicity**: forced-uniqueness proofs

### Lens/  (Catamorphism algebra)

**Role**: The Lens framework — the catamorphism `Raw → α`
(`Lens.view = Raw.fold`).  The universal "viewing" machine.
**Uses only the Theory API**.

The Lens layer is **extended more frequently** than the other rings —
new lenses, new codomains, new property predicates, etc.  So its API
discipline is **2-tier**:

#### Tier 1 — Core API (stable, `Lens/API.lean`)

Every external consumer must import this.  **Only the essence** of Lens —
unchanged even when new lenses are added.

  * **HV1 — Type**: `Lens (α : Type)`, `Lens.view`, `Lens.mk`,
    projections
  * **HV2 — Basic algebra**: `Lens.equiv`, `Lens.refines` + closures,
    `Lens.compose` (functor-like)
  * **HV3 — Universal property**: `Universal.universalLens`,
    `Universal.Flat`, `Universal.factorization` — the theorem that
    *every distinguishability framework factors through a lens on Raw*

#### Tier 2 — extension sub-APIs (import as needed)

Areas where extension happens often get their own per-area import.

  * `Lens/Instances.lean`     — catalog of 25+ concrete lenses
  * `Lens/Lattice.lean`       — join / meet / Family lattice
  * `Lens/Compose.lean`       — composition operators
  * `Lens/Properties.lean`    — predicate catalog (IsLeaf, IsBoolValued, …)
  * `Lens/Codomain.lean`      — *(TBD)* codomain type catalog
                                (Bool213, Nat213, Int213, …)

External consumer pattern:
```lean
import E213.Lens.API                  -- core (required)
import E213.Lens.Instances            -- if the instance catalog is needed
import E213.Lens.Lattice              -- if lattice theorems are needed
-- …
```

#### Sub-clusters (current directories)

  * `Lens/Algebra/`          — Lens-kernel theory (Congruence,
                                Corresp, IdLensEq, internal:
                                FourDistinct, FreeAudit, Space,
                                SwapInvariant)
  * `Lens/AxiomLenses/`      — Lean-axiom Lens witnesses (Funext,
                                Propext, QuotSound) + Bridges
  * `Lens/Cardinality/`      — Raw + Lens-image cardinality
                                observables (Cantor, Tower,
                                BoolSpace, Countable, Pair, Godel,
                                Chain, LensCardinality, CardinalityLB)
  * `Lens/Characterisation/` — characterisation typeclasses + catalog
  * `Lens/Compose/`          — composition operators
  * `Lens/Instances/`        — 29 concrete Lens instances + Leaves/
                                sub-cluster (depth-leaf hierarchy)
  * `Lens/Lattice/`          — refines preorder + lattice (Chain,
                                Preorder, Join, Meet, Family*,
                                IndexedJoin)
  * `Lens/Properties/`       — derived predicates + Diagonal (sq
                                classification, ex-root) +
                                Characterisation/ + Morphism/ sub-
                                clusters
  * `Lens/Universal/`        — Universal flat / quot lens +
                                `Witnesses/` (Core, Nat2/3/4,
                                Q213/Q213_3, Padding, TripleCapstone)
  * `Lens/Internal/`         — internal proof infra

(9 sub-clusters: Axiom Lenses + Internal kept separate makes 9.)

### Lib/  (Mathematics + Physics content)

**Role**: Math/physics content implemented on top of 213.  **Uses only
the Lens API**.

Two bounded contexts:
  * `Lib/Math/`     — 213-native mathematics (11 thematic super-clusters)
  * `Lib/Physics/`  — 213-native physics (~18 sub-clusters)

**Lib/Math/ — thematic super-cluster hierarchy.**  Every sub-tree lives
under one of eleven thematic super-clusters; the path **is** the
namespace (`E213.Lib.Math.<Cluster>.<SubTree>.*`).  Each cluster groups
the sub-trees of one mathematical area:

  * `NumberSystems/` — `Real213` (the cut reals), `Padic`, `SignedCut`,
    `Complex`, `Hyper`, `Irrational`.  The number tower.
  * `Analysis/` — `ClassicCalc, Differentiation, Integration, DyadicSearch,
    FluxMVT, Series` + `Cauchy, Measure, Multivariable, Functional,
    Modulus, CascadeCalculus`.  Modulus-tracked (no ε-δ) analysis.
  * `Algebra/` — `CayleyDickson` (the CD tower), `Linalg213`, `Mobius213`
    (P-orbit), `Polynomial213`, `Group`, `GRA` (Graded Residue Arithmetic:
    7-axiom typeclass + 5 Readings + translation programme + monoidal
    product, 259 PURE).
  * `Cohomology/` — the K_{NS,NT}^{(c)} cohomology programme
    (`Cochain, Cup, CupAW, Delta, Fractal, Hodge, Bipartite, Surfaces,
    Universal, Examples, Bridge`) + `HodgeConjecture` (the HC programme).
  * `NumberTheory/` — `DyadicFSM` (FSM / Pell / Pisano / Trib / FLT),
    `ModArith` (Bezout / FLT / F_{p²}).
  * `Geometry/` — `Geometry, Topology, DiscreteCurvature` + the
    discrete-substrate geometry sub-trees
    (`AngleStructure, NumberGrid, GenerationRule, TriangularTower,
    LevelTopology, OperationTopology, BipartiteDecomp, CartesianVsDisjoint`).
  * `Foundations/` — `AxiomSystems, PatternCatalog, Choice, UniverseChain`
    + the cross-domain / paradigm / residue-form anchor files
    (`CrossDomainUnification, ParadigmDomain*, ResidueForm, ResolutionLimit`, …).
  * `Probability/` — `Probability`, `Information`.
  * `Combinatorics/` — `Combinatorics`, `Logic`.
  * `Tactic/` — `Tactic`, `Extras` (Math-side tactic / misc infra).
  * `ODE/` — ordinary differential equations (standalone).

Each Lib sub-tree carries a `Bridge.lean` for cross-context citation
(anti-corruption layer pattern).  `theory/math/` mirrors this hierarchy.

### Meta/  (Ring-independent — Lean 4 bridge)

**Role**: Things independent of the ring architecture.  The bridge to
Lean 4.  Importable by any ring — but use carefully (trade-offs exist:
axiom-cost, ring-independence, etc.).

**Current contents**:
  * `Meta/Nat/`           — ring-independent Nat lemmas (8 files)
  * `Meta/Tactic/`        — meta-level tactics
                             (DeriveConjugationCodomain,
                              VerifyConjugation, NativeGuard,
                              PureGuard)
  * `Meta/Int213/`        — ∅-axiom helpers over Lean Int
  * `Meta/Algebra213/`    — Ring213/StarRing213/CDDouble functor
                             typeclass tower
  * **Top-level**: SelfRecognising (codomain typeclass hierarchy),
                   AxiomMinimality{,Capstone}, BitPatternUniqueness,
                   LensInternality

**Public API**: `Meta/API.lean` bundles ME-1 SelfRecognising +
ME-2 AxiomMinimality + ME-3 LensInternality.  UniversalLens
witnesses live under `Lens/Universal/` with `Lens.API` (HV6) as
public surface.  Tactic is a separate import (cross-cutting).

## 2. Discipline conventions

### Import rule (★ most important)

A file in each ring may use only:
  1. another file in its own ring
  2. the `API.lean` of the ring **directly below** (API preferred over reach-in)
  3. any file in Meta

**Forbidden**:
  * Upward imports (Theory → Lib, Lens → Lib, etc.) — a direct spec violation
  * Multi-step jumps (Lib → Theory directly — must go through the Lens API)

### API.lean per ring

Every framework ring has an explicit `<Ring>/API.lean`:
  * `Term/API.lean`    (K1–K4)
  * `Theory/API.lean`  (TH-A + TH-B)
  * `Lens/API.lean`    (HV1–HV6)
  * `Meta/API.lean`    (ME-1 .. ME-4)

A downstream consumer (the layer above) should import `API.lean` — for
safety against internal refactors.  Reach-in (importing a specific
sub-file directly) is a code-review smell.

### Internal/ per ring

Implementation details go in `<Ring>/Internal/`.  Importing directly
from outside the ring is a smell.  Currently:
  * `Term/Internal/Tree*`     — Tree (inductive) + cmp, swap, fold,
                                 depth, leaves, fold_swap_hom,
                                 fold_signed_swap (all Tree-level,
                                 ∅-axiom).  Namespace
                                 `E213.Term.Internal` (path-aligned).
  * `Meta/Int213/`, `Meta/Algebra213/` — Int / Ring213 typeclass
                                 helpers (ring-independent, so they live in Meta)
  * `Lens/Internal/Algebra/`  — FreeAudit, FourDistinct,
                                 SwapInvariant, Space

These files use the `E213.<Ring>.Internal.<sub>` namespace.

### Bridge.lean for cross-context (within Lib)

When a file in one bounded context (Math, Physics) cites a result from
another context, it goes through an explicit `Bridge.lean`:
  * `Lib/Math/Cohomology/AlphaEMBridge.lean`
  * `Lib/Physics/<Cluster>/Bridge.lean` (12 sub-clusters)

Anti-corruption layer pattern — cross-context reference is explicit,
named, grep-discoverable.

### Naming

  1. **Path = namespace** — `Lib/Math/Cohomology/Universal/Prop53.lean`
     declares `namespace E213.Lib.Math.Cohomology.Universal.Prop53`.
     Enforced by `tools/sync_namespaces.py`.  Intentional exceptions
     (path ≠ namespace, documented):
       - **Type-defining files** keep the bare type-namespace
         (e.g. `Lens/LensCore.lean` declares `namespace E213.Lens`).
       - **Doubled-type-namespace pattern** (CayleyDickson) — when a
         structure of the same name as the file lives inside the
         file's namespace, downstream extension files declare a
         doubled namespace.  R10 in
         `lean/E213/docs/CONSOLIDATION_PROTOCOL.md`.
       - **Cross-ring extension of `Term/Internal/Tree`** — files
         in higher rings (Lens, Lib, Theory) that add Tree-level
         decls (e.g., `Lens/Cardinality/Godel.lean`'s `Tree.toNat`)
         must declare them inside `namespace E213.Term.Internal` so
         dot notation (`t.toNat`) resolves.  Namespace ≠ ring is OK
         in Lean — what matters is layer-import direction.  Same
         technique in `Meta/Tactic/{Nat213,Mod213,…}` sharing
         `E213.Tactic.*` for tactic discovery.
       - **Descriptive sub-namespace** when the namespace label
         conveys content better than the file name.

  2. **No session-numbered labels** — no `Phase2/`, `Phase3/` for
     long-lived names.

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

### Empirical verification of the ring split (G105)

The ring boundaries above are normatively-stated.  G105
(deliverable at `catalogs/recursor-inventory.md`)
verified them empirically by measuring per-namespace Expr-shape
densities:

  * Theory ring: ~100 Expr nodes / decl (deep proofs about Raw).
  * Lens ring:   ~10 Expr nodes / decl (Lens-projection plumbing).
  * Lib ring:    ~2-7 Expr nodes / decl (composite results on
                 derived APIs).

The three-layer λ-density split is **measurable**, not just stated.
Any future architectural change can be re-validated via the same
scanner (`tools/ast_shape_scan.py`).

## 4. Companion artifact: rust-engine

`rust-engine/` mirrors this ring structure crate-by-crate:
  * `crates/term/`    ↔ `lean/E213/Term/`
  * `crates/theory/`  ↔ `lean/E213/Theory/`
  * `crates/lens/`    ↔ `lean/E213/Lens/`
  * `crates/app/`     ↔ `lean/E213/Lib/`

Rust is a numerical / search-engine companion ("a calculator for when
Lean takes too long"), not a re-implementation.  Every Rust result must
point to a Lean theorem (`rust-engine/whitelist.toml` +
`tools/verify-citations`).
