# lean/E213/ARCHITECTURE.md — 213 layer architecture (canonical)

이 문서는 213 Lean library 의 **layer 구조**를 정의한다 — 어느 ring 이
있고, 각자 무엇을 위한 것이며, 어떻게 import 가 흐르는지.  다른 모든
문서 (INDEX.md, CLAUDE.md, sub-cluster README 등) 는 이 문서를 따른다.

Last revised: 2026-05-12 — layer spec confirmation (Mingu Jeong).
Pre-2026-05-12 history (6-ring concentric model) available via
`git log -- lean/E213/ARCHITECTURE.md`.

## Philosophical foundations (canonical preamble)

The ring architecture below is a *code-organization convenience*,
not a philosophical hierarchy.  Per
`seed/AXIOM/07_self_reference.md` §8.1, there is no exterior to
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
  - "Lens is residue self-pointing" — `seed/AXIOM/00_nature.md`
    §1.2 (revised 2026-05-20).
  - "Layers in code are not layers in reality" — present
    section.
  - "Lens application IS a residue-internal event, not an
    addition to Raw" — `seed/AXIOM/05_primacy.md` §6.
  - "All classical foundations are Lens compositions reading
    the same Raw residue" —
    `lean/E213/Lib/Math/AxiomSystems/INDEX.md`.

When any sub-INDEX uses "substrate", "foundation", "bare-metal",
"sits between", or similar architectural metaphors, those are to
be read as code-organization vocabulary, not ontological claims.

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

`App/` — 2026-05-13 Session H 에 정리 완료: 유일 멤버 `App/Simplex.lean`
(block-pair classification on Fin 5, S_3 × S_2 invariance) 은 math
combinatorics 라 `Lib/Math/Combinatorics/Simplex5.lean` 로 이동, App/
디렉토리 + `App.lean` aggregator 삭제.

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
                           SwapSlash, Fold, Hom, Levels, Rec, Signed,
                           **Endomorphic**, Demo) + API.lean
                           (re-export shim).  Endomorphic absorbed
                           the former `Theory/Closed/` content
                           2026-05-14 (FoldRaw rename 2026-05-15).
  * `Theory/Atomicity/` — forced-uniqueness proofs (Five,
                           FiveHelpers, PairForcing,
                           NonDecomposable, ArityForcing,
                           PrimitiveSizes, Alive)
  * `Theory/CDDouble/`  — generic Order-4 mechanism (UniversalOrder4,
                           GenericLiftDemo)
  * `Theory/RawCmpIndependence.lean` — axiom-independence of cmp
                           choice (meta-theorem).
  Theory.Internal/ directory 제거 (2026-05-12 cleanup) — Int213
  및 Algebra213 family 는 Meta 로 promotion.

**Public API**: `Theory/API.lean` bundles:
  * **TH-A — Raw axiom data**: Raw + 4 clauses + structural primitives
  * **TH-B — Atomicity**: forced-uniqueness proofs

### Lens/  (Catamorphism algebra)

**Role**: Lens framework — Raw → α 의 catamorphism
(`Lens.view = Raw.fold`).  Universal "viewing" 기계.
**Theory API 만 사용**.

Lens layer 는 다른 ring 들 보다 **확장이 빈번** — 새 lens 추가,
새 codomain, 새 property predicate 등.  따라서 API discipline 도
**2-tier**:

#### Tier 1 — Core API (안정, `Lens/API.lean`)

외부 consumer 가 반드시 import.  Lens 의 **본질만** — 새 lens
추가시에도 안 바뀜.

  * **HV1 — Type**: `Lens (α : Type)`, `Lens.view`, `Lens.mk`,
    projections
  * **HV2 — Basic algebra**: `Lens.equiv`, `Lens.refines` + closures,
    `Lens.compose` (functor-like)
  * **HV3 — Universal property**: `Universal.universalLens`,
    `Universal.Flat`, `Universal.factorization` — *모든
    distinguishability framework 가 Raw 위 lens 로 factor* 의 정리

#### Tier 2 — 확장 sub-API (필요시 import)

확장 자주 일어나는 영역은 영역별 별도 import.

  * `Lens/Instances.lean`     — 25+ concrete lens 카탈로그
  * `Lens/Lattice.lean`       — join / meet / Family lattice
  * `Lens/Compose.lean`       — composition operators
  * `Lens/Properties.lean`    — predicate catalog (IsLeaf, IsBoolValued, …)
  * `Lens/Codomain.lean`      — *(TBD)* codomain type catalog
                                (Bool213, Nat213, Int213, …)

외부 consumer 패턴:
```lean
import E213.Lens.API                  -- 핵심 (필수)
import E213.Lens.Instances            -- instance catalog 필요시
import E213.Lens.Lattice              -- lattice 정리 필요시
-- …
```

#### Sub-clusters (현재 디렉토리)

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
                                — 2026-05-13 통합 (구 Lib/Math/Infinity
                                + Lens/Algebra/{LensCardinality,
                                CardinalityLB})
  * `Lens/Characterisation/` — characterisation typeclasses + catalog
  * `Lens/Compose/`          — composition operators
  * `Lens/Instances/`        — 29 concrete Lens instances + Leaves/
                                sub-cluster (depth-leaf hierarchy,
                                Leaves 폴드 2026-05-13)
  * `Lens/Lattice/`          — refines preorder + lattice (Chain,
                                Preorder, Join, Meet, Family*,
                                IndexedJoin) — Refines 폴드 2026-05-13
  * `Lens/Properties/`       — derived predicates + Diagonal (sq
                                classification, ex-root) +
                                Characterisation/ + Morphism/ sub-
                                clusters — 2026-05-13 3 sub-clusters
                                폴드
  * `Lens/Universal/`        — Universal flat / quot lens +
                                `Witnesses/` (Core, Nat2/3/4,
                                Q213/Q213_3, Padding, TripleCapstone)
                                — 2026-05-13 Meta/UniversalLens 흡수
  * `Lens/Internal/`         — internal proof infra

(9 sub-clusters 후 — Cardinality (+1), Leaves 폴드 (−1), Refines 폴드
(−1), Characterisation/Morphism 폴드 (−2), Diagonal 폴드 (root file,
sub-cluster count 무관): 14→9, `research-notes/LENS_AUDIT.md` §4 의
13→7 권장 거의 달성 (Axiom Lenses + Internal 별도 유지로 9).)

### Lib/  (Mathematics + Physics content)

**Role**: 213 위에서 구현된 수학/물리 콘텐츠.  **Lens API 만 사용**.

Two bounded contexts:
  * `Lib/Math/`     — 213-native mathematics (~38 sub-clusters)
  * `Lib/Physics/`  — 213-native physics (~13 sub-clusters)

**Lib/Math/ — major sub-organized clusters** (2026-05-13 sub-org
pass 후):
  * `CayleyDickson/{Tower,Integer,Levels,Lipschitz,Misc}` (5 sub-dirs, 57 files)
  * `Real213/{Core,Sum,Mul,Lattice,Bisection,ExpLog,Cauchy}` (7 sub-dirs, 57 files)
  * `SignedCut/{Core,CD,Hurwitz,Level,Bridge,Octonion}` (6 sub-dirs, 35 files)
  * `Probability/{Foundation,Distribution,Inequality,Limit,Bridge}` (5 sub-dirs, 25 files)
  * `Cohomology/{Examples,Bridge,Cochain,Cup,CupAW,Delta,Fractal,
                  Hodge,Bipartite,Surfaces,Universal}` (11 sub-dirs)
  * `DyadicFSM/{Product,Signature,Forward,Tier,ArithFSM,Pell,Fib,
                Pisano,Trib,Legendre,BitFSM,Archive}` (12 sub-dirs)
  * `HodgeConjecture/{Foundation,Structure,Pairing,Refinement,
                       Bridge,MotivicBridge,Toolkit}` (7 sub-dirs)
  * `Analysis/{ClassicCalc,Differentiation,DyadicSearch,FluxMVT,
                Integration,ODE,Series}` (7 sub-dirs)

각 Lib sub-tree 는 cross-context citation 용 `Bridge.lean` 보유
(anti-corruption layer pattern).

### Meta/  (Ring 무관 — Lean 4 bridge)

**Role**: 링 아키텍처에 구애받지 않는 것들.  Lean 4 와의 bridge.
어느 ring 도 import 가능 — 그러나 사용시 신중 (axiom-cost,
ring-independence 등 trade-off 존재).

**현재 내용**:
  * `Meta/Nat/`           — ring-independent Nat 보조정리
                             (구 Lib/Math/NatHelpers, 8 파일,
                              promoted 2026-05-13)
  * `Meta/Tactic/`        — meta-level tactics
                             (DeriveConjugationCodomain,
                              VerifyConjugation, NativeGuard,
                              PureGuard)
  * `Meta/Int213/`        — Lean Int 위 ∅-axiom helpers
                             (promoted from Theory.Internal 2026-05-12)
  * `Meta/Algebra213/`    — Ring213/StarRing213/CDDouble functor
                             typeclass tower
                             (promoted from Theory.Internal 2026-05-12)
  * **Top-level**: SelfRecognising (codomain typeclass hierarchy),
                   AxiomMinimality{,Capstone}, BitPatternUniqueness,
                   LensInternality

  UniversalLens witnesses (11 파일) 는 2026-05-13 `Lens/Universal/
  Witnesses/` 로 이동 — Lens-content 가 Meta 에 misshoused 된 상태
  였음을 LENS_AUDIT §4 가 지적.

**Public API**: `Meta/API.lean` bundles ME-1 SelfRecognising +
ME-2 AxiomMinimality + ME-3 LensInternality. UniversalLens
witnesses 는 `Lens/Universal/` 로 이동 후 `Lens.API` (HV6) 가
public surface.  Tactic 은 separate import (cross-cutting).

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
  * `Term/Internal/Tree*`     — Tree (inductive) + cmp, swap, fold,
                                 depth, leaves, fold_swap_hom,
                                 fold_signed_swap (all Tree-level,
                                 ∅-axiom).  Moved fully from Theory
                                 2026-05-15.  Namespace
                                 `E213.Term.Internal` (path-aligned).
  * `Meta/Int213/`, `Meta/Algebra213/` — Int / Ring213 typeclass
                                 helpers (promoted from Theory.Internal
                                 2026-05-12; ring-independent so Meta 거주)
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

## 4. Companion artifact: rust-engine

`rust-engine/` mirrors this ring structure crate-by-crate:
  * `crates/term/`    ↔ `lean/E213/Term/`
  * `crates/theory/`  ↔ `lean/E213/Theory/`
  * `crates/lens/`    ↔ `lean/E213/Lens/`
  * `crates/app/`     ↔ `lean/E213/Lib/` (App/ tier 2026-05-13 정리 후)

Rust 는 numerical / search-engine companion ("calculator for when
Lean takes too long"), re-implementation 이 아님.  모든 Rust 결과는
Lean 정리를 가리켜야 (`rust-engine/whitelist.toml` +
`tools/verify-citations`).
