# Hierarchical Placement — post-M11 final state

**Companion document to** `lean/E213/ARCHITECTURE.md` and
`research-notes/CONSOLIDATION_PROTOCOL.md` (R1–R11 rules).

This document captures the post-Stage-M11 state of the E213 tree:
**every directory has an umbrella file**, and **every umbrella links
the actual files in that directory** (modulo a small set of
pre-existing API-drift breakage documented at the end).

The directive that triggered this audit (Mingu, 2026-05-XX):

> 이런 식으로 E213디렉토리 밑의 모든 lean 파일들을 전부 수정 /
> Analysis가 제일 모범케이스인듯 아마도 / 그러고 나면 이제 본질적으로
> 계층적 설계에 대해서 완전하게 어느것이 어디로 들어가야하는지 모두
> 결정 가능할 것

Translation: apply the Analysis-style spec-as-code organization to
all lean files under E213/, after which the hierarchical design is
fully determined.  This document records the determination.

## 1. Spec-as-code coverage (final tally)

Every top-level layer + every Math/Physics sub-tree has an umbrella.

### 1.1 Top-level layer umbrellas (8/8)

| umbrella | files | imports | covers |
|---|---|---|---|
| `E213/Term.lean`     | 23  | 23  | bare-metal type theory + `Tactic/` macros |
| `E213/Theory.lean`   | 27  | 27  | Raw monad, Atomicity/, Tools/ |
| `E213/Lens.lean` | 89  | 79  | Lens algebra (10 deferred — pre-existing API drift) |
| `E213/Meta.lean`       | 27  | 27  | reflective primitives + meta tactics |
| `E213/App.lean`        | 1   | 1   | Simplex executable |
| `E213/OS.lean`         | 12  | 12  | HodgeConjecture/Bridges + Physics/Capstones |
| `E213/Math.lean`       | 469 | 38  | imports topical sub-umbrellas (not files directly) |
| `E213/Physics.lean`    | 127 | 14  | imports topical sub-umbrellas (not files directly) |

### 1.2 Math/ sub-tree umbrellas (17/17)

All Math sub-trees have full umbrella coverage; broken-file counts
are pre-existing API drift, documented inline in each umbrella.

| sub-tree         | files | imports | broken |
|---|---|---|---|
| Analysis         | 74  | 11  | 0 (chapter-style: 7 sub-dir umbrellas + 3 top-level files; DyadicSearch grew from 5→9 files for the G31 trajectory-as-witness IVT) |
| AxiomSystems     | 4   | 4   | 0 |
| Cauchy           | 14  | 14  | 0 |
| CayleyDickson    | 29  | 20  | 9 (heavy variants, LipschitzLens, R5Vacuity, ZSqrtProduct) |
| Choice           | 4   | 4   | 0 |
| Cohomology       | 217 | 208 | 9 (CupAW.LeibnizSmall, Dyadic API drift, etc.) |
| Diagonal         | 2   | 2   | 0 |
| Hyper            | 3   | 3   | 0 |
| Infinity         | 8   | 8   | 0 |
| Irrational       | 6   | 6   | 0 |
| Linalg213        | 8   | 8   | 0 |
| ModArith         | 9   | 9   | 0 |
| Modulus          | 4   | 4   | 0 |
| Polynomial213    | 2   | 1   | 0 (core file at sibling `Polynomial213.lean`) |
| Real213          | 45  | 45  | 0 |
| Tactic           | 5   | 5   | 0 |
| Trajectory       | 1   | 1   | 0 |

### 1.3 Physics/ sub-tree umbrellas (14/14)

All Physics sub-trees have full umbrella coverage; 0 broken.

| sub-tree    | files | imports |
|---|---|---|
| AlphaEM     | 6   | 6   |
| Atomic      | 20  | 20  |
| Basel       | 2   | 2   |
| Cosmology   | 6   | 6   |
| Couplings   | 11  | 11  |
| Foundations | 17  | 17  |
| Hadron      | 8   | 8   |
| Higgs       | 4   | 4   |
| Mass        | 3   | 3   |
| Mixing      | 5   | 5   |
| Nuclear     | 6   | 6   |
| Simplex     | 7   | 7   |
| Substrate   | 13  | 13  |
| YangMills   | 5   | 5   |

## 2. Vertical-layer placement (mechanical)

Per `ARCHITECTURE.md` §0, every file's natural layer is mechanically
determined by its import closure.  Run `tools/layer_audit.py` to
recompute.  Post-M11 distribution:

| top-folder    |  Term |  Theory |  Lens | Meta | App | total |
|---|---|---|---|---|---|---|
| Term/         | 24     | 0        | 0          | 0    | 0   | 24    |
| Theory/       | 0      | 27       | 0          | 0    | 0   | 27    |
| Lens/         | 0      | 0        | 105        | 0    | 0   | 105   |
| Meta/         | 0      | 0        | 0          | 30   | 0   | 30    |
| App/          | 0      | 0        | 0          | 0    | 1   | 1     |
| Lib/Math/     | 49     | 235      | 180        | 9    | 0   | 525   |
| Physics/(127) | 0      | 116      | 11         | 0    | 0   | 127   |
| Prelude.lean  | 1      | 0        | 0          | 0    | 0   | 1     |

**Reading**: `Term/X.lean` files are at  Term by both path AND
mechanical computation.  `Math/X.lean` files' mechanical layer is
distributed across {Term, Theory, Lens, Meta} — the path
encodes the *topical* axis only.

## 3. Layer-claim violations: 0

No file imports a layer above its claimed level.
`tools/layer_audit.py` reports `## Violations: 0`.

## 4. Layer downgrade hints (28 informational)

These files could mechanically move to a lower layer; they're not
violations, just below-claimed-cost.  Listed for future audit.

  - **App → Theory**: `App/Simplex.lean` (1)
  - **Theory → Term**: 7 files in `Theory/Atomicity/`
  - **Lens → Theory**: `Lens/LensCore.lean` (1)
  - **Lens → Term**: 8 files in `Lens/AxiomLenses/Core/`
  - **Meta → Lens**: 5 files (`SelfRecognising`, `Universal/`, etc.)
  - **Meta → Term**: 6 files (`AxiomMinimality`, `Tactic/Derive*`, etc.)

These are *path locality* decisions: e.g. `Theory/Atomicity/Alive`
is mechanically Term-level but lives under Theory/ because it
groups topically with the rest of `Atomicity/`.  Moving them down
is optional and can be deferred.

## 5. Spec-as-code rule compliance (R1–R11)

| rule | description | post-M11 status |
|---|---|---|
| R1  | File name = chapter title; no session-residue suffixes  | clean |
| R2  | Every dir has umbrella `<DirName>.lean`                 | **complete** |
| R3  | Sub-namespace preservation when merging                 | clean |
| R4  | Drop pure-bundle capstones; keep unique content         | 232 sealed deleted |
| R5  | Verify all sub-tree umbrellas individually              | enforced in M11 |
| R6  | Cycle prevention                                        | clean |
| R7  | Sub-cluster at 3+ files; sub-directory at ~30+          | applied |
| R8  | Verify-and-clean after every merge stage                | enforced |
| R9  | Iterative umbrella with broken-file exclusion           | applied |
| R10 | Nested-type-namespace caveat (doubled `X.X.*`)          | documented + applied |
| R11 | Tactic-emitted hardcoded paths                          | M7 + M11b + M11i fixed |

## 6. Deferred / known-broken inventory (28 files)

All deferred files are pre-existing API drift, NOT regressions caused
by the M11 sweep.  They're documented inline in each umbrella.

### 6.1  Lens (10 deferred)

Common patterns:
  - `open E213.Meta` (now `E213.Meta.SelfRecognising`)
  - `E213.Lib.Math.DiagonalClassification` (namespace deleted)
  - cascading API drift in lens-refines combinators

Files: `CompoundBool`, `NegSq`, `ParityXor{Incomparable,Join}`,
`RawAChar`, `Morphism/{BoolSqClassification,SlashCharNotFold}`,
`Properties/{ABRefines,Leaf,ParityCollapseFalse}`.

### 6.2 CayleyDickson (9 deferred)

  - `CDTower`, `*Heavy` variants — `hurwitz_ring` tactic plumbing
    fails to synthesize through deeper API
  - `LipschitzLens` — `open E213.Meta` + `Raw.{a,b,slash}` rename
  - `R5Vacuity` — same `E213.Meta` issue
  - `ZSqrtProduct` — `SwapMatching` + `D₁/D₂` variable-binding drift

### 6.3 Cohomology (9 deferred)

  - `CupAW.{LeibnizScaling, LeibnizSmall}` — `Universal.Prop31.pattern_eq`
    became `pattern_eq_at` (index-pointwise vs function-level)
  - `Dyadic.{ArithFSM.{Hierarchy,V1to2}, AlgebraicDegree, NumberTheory213}`
    — `ArithFSM.V1.Ar*.padTo2` API rename
  - `Dyadic.Archive.{EdgeSignature,SubwordComplexity}` — free-variable
    elaboration drift
  - `Dyadic.Pell.ProperBridge` — function-application type mismatch

### 6.4 Meta + OS (0 deferred — fully clean post-M11h)

  - Meta: `VerifyConjugationTest.lean` repaired in M11b.
  - OS: `HodgeTate.lean` unblocked by `Bipartite/Filled.lean` fix in M11h.

## 7. Future hierarchical work

### 7.1 Layer downgrades (optional)

The 28 downgrade hints (§4) are candidates for path migration if
topical locality cost is acceptable.  Recommended only after
landing the deferred-28 (§6) cleanup so the migration doesn't
collide with API-drift fixes.

### 7.2 Polynomial213 layout

`Polynomial213.lean` (core impl) + `Polynomial213/{Sound, Ineq}.lean`
(extensions) is asymmetric vs the Analysis-style pattern.
Two valid resolutions:

  - Keep as-is (current): `Polynomial213.lean` IS the core, and the
    sibling subdirectory adds extensions.  Simple, working, but
    `Polynomial213.lean` is not a pure umbrella.
  - Refactor: rename `Polynomial213.lean` → `Polynomial213/Core.lean`,
    create new `Polynomial213.lean` as umbrella that imports
    `Core + Sound + Ineq`.  More uniform but adds one file.

Deferred — both are acceptable.

### 7.3  Lens namespace audit

The 10 deferred  Lens files share the `open E213.Meta` issue
(namespace relocated in M-series).  A targeted Lens-cluster
sweep — analogous to M11h's Cohomology fix — is the natural
follow-up.

## 8. Verification command set

```bash
cd lean
lake build E213.Term E213.Theory E213.Lens E213.Meta \
            E213.App E213.OS E213.Lib.Math E213.Lib.Physics
# Each should report ✔ Built E213.<Layer>.

python3 ../tools/layer_audit.py | head -10
# Expects: ## Violations: 0
```

If both pass, the spec-as-code is complete and the placement
hierarchy is determined.
