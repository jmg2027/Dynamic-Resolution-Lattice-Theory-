# lean/E213/ARCHITECTURE.md — 213 layer architecture (canonical)

이 문서는 213 Lean library 의 **layer 구조**를 정의한다 — 어느 ring 이
있고, 각자 무엇을 위한 것이며, 어떻게 import 가 흐르는지.  다른 모든
문서 (INDEX.md, CLAUDE.md, sub-cluster README 등) 는 이 문서를 따른다.

Last revised: 2026-05-12 — layer spec confirmation (Mingu Jeong).
Pre-2026-05-12 history (6-ring concentric model) available via
`git log -- lean/E213/ARCHITECTURE.md`.

## 0. Layer model

213 은 **4 ring + Meta** 구조.  Meta 는 ring-independent (Lean 4 bridge).

```
Meta  ← ring-independent — Lean 4 와의 bridge.  어느 ring 도 사용 가능.
        사용시 유의 (axiom-cost / ring-independence trade-off).
─────────────────────────────────────────────────────────
Lib    ← Lens API 만 사용                ↑
Lens   ← Theory API 만 사용              │ import 방향
Theory ← Term API 만 사용                │ (inward only)
Term   ← Raw 구현체 (Tree 등)            │
─────────────────────────────────────────────────────────
```

**Import 규칙** — 각 ring 내 file 은 다음만 사용 가능:
  1. 자기 ring 안에서 정의된 것
  2. **바로 아래** ring 의 API (정확히 한 단계 아래)
  3. Meta 의 임의 file

위 방향 import (예: Theory → Lib) 또는 다단계 점프 (예: Lib → Theory
직접 — Lens API 우회) 는 모두 위반.  Layer audit 으로 검출.

| Ring | Role |
|---|---|
| `Term/`    | Raw 의 구현체 (Tree 등).  Theory 에 공개할 API 구현부. |
| `Theory/`  | Term API 통해 Raw 의 axiom + 구조 정의.  Lens 에 공개할 API 구현부. |
| `Lens/`    | Theory API 통해 Lens 들 정의.  Lib 에 공개할 API 구현부. |
| `Lib/`     | Lens API 통해 수학/물리 콘텐츠 구현. |
| `Meta/`    | Lean 4 와의 bridge.  Ring 무관 — 어느 ring 도 사용 가능. |

> **Spec 원문** (Mingu Jeong, 2026-05-12):
> 「해당 링에는 해당 링 아래에서 받아온 api 혹은 Meta (meta 는 링에서
> 벗어나서 존재할 수 있는 친구들.  Lean4 와의 브릿지라고 생각할 수
> 있음) 혹은 해당 링 안에서 정의된 것들만을 사용할 수 있다.  api 로
> 위쪽 링으로 올릴 수 있다.」

`App/` — legacy 위치, 현재 1 file (`Simplex.lean`).  Spec 상 명시되지
않음 — Lib 의 일부로 흡수 또는 별도 ring 둘 중 결정 보류 (2026-05-12).

## 1. Ring 정의

### Term/  (Raw 구현체)

**Role**: Lean 4 안에서 213 의 Raw 를 표현하는 기계.  Deep-embedded
`Tree` + `Term` type + 전체함수 (compare, eval, normal form).  이
ring 안에서 **0-axiom 으로 닫힘** — propext, Quot.sound,
Classical.choice 등 외부 axiom 비사용.

**Key property**: 모든 Term 정리가 *literally 0-axiom*.
`tools/kernel_regress.sh` 로 검증.

**Public API**: `Term/API.lean` re-exports K1–K4:
  * **K1 — Data**: `Term`, `Term.eval`, `Term.{nS, nT, d, c}`
  * **K2 — Computation**: `Term.{equiv, le_b, lt_b, pair, offDiag,
    equivQ, leQ}`, `Decide.{allBelow, existsBelow}`
  * **K3 — Soundness**: `Sound.{of_equiv, of_le_b, of_lt_b,
    of_equivQ, of_leQ}`
  * **K4 — Tactic** (separate import): `Term.Tactic.{Omega213,
    Nat213, Mod213, Pow213, Fin213, QuadNorm}`

### Theory/  (Raw axiom + forced-shape proofs)

**Role**: 213 axiom 자체 — `Raw` type + 4-clause definitional
commitments (a, b, slash, slash_comm).  이 commitment 의 결과로
forced shape uniqueness 증명.  **Term API 만 사용**.

**Sub-clusters**:
  * `Theory/Raw/`       — public Raw API (Core, Slash, Swap,
                           SwapSlash, Fold, Hom, Levels, Rec, Signed)
  * `Theory/Atomicity/` — forced-uniqueness proofs (Five,
                           FiveHelpers, PairForcing,
                           NonDecomposable, ArityForcing,
                           ArityForcingGeneral, PrimitiveSizes, Alive)
  * `Theory/Internal/`  — implementation detail (DecEq, Cmp,
                           CmpIndependence, SwapSlashInjective).
                           Direct import 외부에서 권장 안 됨.

**Public API**: `Theory/API.lean` bundles:
  * **TH-A — Raw axiom data**: Raw + 4 clauses + structural primitives
  * **TH-B — Atomicity**: forced-uniqueness proofs

### Lens/  (Catamorphism algebra)

**Role**: Lens framework — Raw → α 의 catamorphism
(`Lens.view = Raw.fold`).  Universal "viewing" 기계.
**Theory API 만 사용**.

**Sub-clusters**:
  * `Lens/Algebra/`          — algebraic kernel (CardinalityLB,
                                Congruence, Corresp, IdLensEq)
  * `Lens/AxiomLenses/`      — Lean-axiom Lens witnesses (Funext,
                                Propext, QuotSound) + Bridges
  * `Lens/Characterisation/` — characterisation typeclasses + catalog
  * `Lens/Compose/`          — composition operators
  * `Lens/Instances/`        — 24+ concrete Lens instances
  * `Lens/Lattice/`          — refines lattice (Join, Meet, Family*)
  * `Lens/Leaves/`           — depth-leaf hierarchy
  * `Lens/Morphism/`         — morphism shape catalogue
  * `Lens/Properties/`       — derived predicates
  * `Lens/Refines/`          — refines preorder (Chain, Preorder)
  * `Lens/Universal/`        — Universal flat / quot lens
  * `Lens/Internal/`         — internal proof infra (Algebra/{
                                FreeAudit, FourDistinct,
                                SwapInvariant, Space})

**Public API**: `Lens/API.lean` exposes HV1–HV6:
  * HV1 — Type, HV2 — Equivalence, HV3 — Initiality,
    HV4 — Lattice, HV5 — Composition, HV6 — Canonical Form

Optional separate imports: HV7 (Instances), HV8 (Characterisation).

### Lib/  (Mathematics + Physics content)

**Role**: 213 위에서 구현된 수학/물리 콘텐츠.  **Lens API 만 사용**.

Two bounded contexts:
  * `Lib/Math/`     — 213-native mathematics (~495 files)
  * `Lib/Physics/`  — 213-native physics (~128 files)

각 Lib sub-tree 는 cross-context citation 용 `Bridge.lean` 보유
(anti-corruption layer pattern).

### Meta/  (Ring 무관 — Lean 4 bridge)

**Role**: 링 아키텍처에 구애받지 않는 것들.  Lean 4 와의 bridge.
어느 ring 도 import 가능 — 그러나 사용시 신중 (axiom-cost,
ring-independence 등 trade-off 존재).

**현재 내용**:
  * `Meta/UniversalLens/` — universal lens witnesses (Nat2/3/4,
                             Q213, Padding, TripleCapstone)
  * `Meta/Tactic/`        — meta-level tactics
                             (DeriveConjugationCodomain,
                              VerifyConjugation, NativeGuard,
                              PureGuard)
  * **Top-level**: SelfRecognising (codomain typeclass hierarchy),
                   AxiomMinimality{,Capstone}, BitPatternUniqueness,
                   LensInternality

**Public API**: `Meta/API.lean` bundles ME-1 SelfRecognising +
ME-2 AxiomMinimality + ME-3 LensInternality + ME-4 UniversalLens.
Tactic 은 separate import (cross-cutting).

> **Pre-2026-05-12 정정**: 이전 ARCHITECTURE 에서 Meta 가 Ring 3
> (Lens 와 Lib 사이 concentric ring) 으로 분류되어 있었음.  현재
> spec: Meta 는 ring 무관 — Lib 도, Lens 도, Theory 도 사용 가능.

## 2. Discipline conventions

### Import 규칙 (★ 가장 중요)

각 ring 내 file 은 다음만 사용 가능:
  1. 자기 ring 내 다른 file
  2. **바로 아래** ring 의 `API.lean` (reach-in 보다 API 권장)
  3. Meta 의 임의 file

**금지**:
  * 위 방향 import (Theory → Lib, Lens → Lib 등) — spec 직접 위반
  * 다단계 점프 (Lib → Theory 직접 — Lens API 통해야)

### API.lean per ring

모든 framework ring 은 explicit `<Ring>/API.lean` 보유:
  * `Term/API.lean`    (K1–K4)
  * `Theory/API.lean`  (TH-A + TH-B)
  * `Lens/API.lean`    (HV1–HV6)
  * `Meta/API.lean`    (ME-1 .. ME-4)

Downstream consumer (위 layer) 는 API.lean import 권장 — 내부
refactor 안전성 확보.  reach-in (specific sub-file 직접 import) 는
code-review smell.

### Internal/ per ring

Implementation detail 은 `<Ring>/Internal/` 안에.  Ring 외부에서
직접 import 는 smell.  현재:
  * `Theory/Internal/Raw/`    — DecEq, Cmp, CmpIndependence,
                                 SwapSlashInjective
  * `Lens/Internal/Algebra/`  — FreeAudit, FourDistinct,
                                 SwapInvariant, Space

File 들은 `E213.<Ring>.Internal.<sub>` namespace 사용.

### Bridge.lean for cross-context (Lib 내부)

한 bounded context (Math, Physics) 의 file 이 다른 context 의
결과를 인용할 때는 explicit `Bridge.lean` 통해:
  * `Lib/Math/Cohomology/AlphaEMBridge.lean`
  * `Lib/Physics/<Cluster>/Bridge.lean` (12 sub-clusters)

Anti-corruption layer pattern — cross-context reference 가 explicit,
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
         `research-notes/CONSOLIDATION_PROTOCOL.md`.
       - **Internal-shared umbrella** (e.g. `Theory/Internal/Raw/`
         files share `namespace E213.Theory.Internal`).
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

## 4. Companion artifact: rust-engine

`rust-engine/` mirrors this ring structure crate-by-crate:
  * `crates/term/`    ↔ `lean/E213/Term/`
  * `crates/theory/`  ↔ `lean/E213/Theory/`
  * `crates/lens/`    ↔ `lean/E213/Lens/`
  * `crates/app/`     ↔ `lean/E213/App/` + Lib content

Rust 는 numerical / search-engine companion ("calculator for when
Lean takes too long"), re-implementation 이 아님.  모든 Rust 결과는
Lean 정리를 가리켜야 (`rust-engine/whitelist.toml` +
`tools/verify-citations`).
