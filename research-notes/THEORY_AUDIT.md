# Theory/ Layer Audit — Ring 1 (canonical reading)

**Date**: 2026-05-14
**Scope**: Full audit of `lean/E213/Theory/` (49 files, 8 sub-clusters).
**Purpose**: Verify that Theory's role is "Raw axiom + forced-shape
uniqueness proofs" per ARCHITECTURE.md; identify any layer leakage,
dead code, or architectural drift.

## Method

Each file: imports / namespace / role / role-fit / observations.

---

## 0. Top-level (3 files)

### `Theory/API.lean`
- **Imports**: `Theory.Raw`, `Theory.Atomicity`
- **Role**: Public surface bundling TH-A (Raw axiom data) + TH-B (Atomicity forced uniqueness).
- **Fit**: ✓ canonical entry point.
- **Sealed-mark**: `Theory.Raw.Internal.*` + `Theory.Tools.CertChecker` (direct import discouraged).

### `Theory/Raw.lean`
- **Imports**: 9 files — Raw.{Core, Slash, Fold, Swap, Levels, Signed, Hom, Rec} + Internal.Raw.Cmp.
- **Role**: TH-A re-export aggregator for Raw type + 4 clauses + observables.
- **Fit**: ✓ matches ARCHITECTURE.md "public Raw API".
- **Note**: pulls in `Internal.Raw.Cmp` (one piece of Internal needed for public Raw — Cmp is the Tree comparator that `Raw.slash` validates against).
- **Not re-exported**: `Raw.SwapSlash` (only used by `Lens.Instances.Swap`).
- **Note**: `Raw/Mobius.lean` and `Raw/Demo.lean` NOT included in aggregator (will inspect).

### `Theory/Atomicity.lean`
- **Imports**: 8 Atomicity sub-files only. **No Raw import** — deliberate.
- **Role**: TH-B re-export — forced shape uniqueness proofs (atomic ↔ d=5, pair=2, closure=3, alive=(1,1), arity=2).
- **Fit**: ✓ but note: abstract structural-forcing over generic ℕ-systems, then specialized to Raw downstream. NOT proofs *about* Raw directly. Architecturally clean separation.

## 1. Raw/ — public Raw API (13 files)

### `Raw/Core.lean` (61 LOC)
- **Imports**: none (foundational)
- **Defines**: `Internal.Tree` (a/b/slash), `Tree.cmp`, `Tree.canonical`, `Raw := {t // t.canonical}`, `Raw.a`, `Raw.b`, `DecidableEq Raw`
- **Role**: ✓ Foundation. Tree namespace is `E213.Theory.Internal`, Raw is `E213.Theory` — clean separation.

### `Raw/Slash.lean` (57 LOC)
- **Imports**: Raw.Core, Internal.Raw.Cmp
- **Defines**: `Raw.slash` (smart ctor, canonicalising), `Raw.slash_comm`, `Tree.depth`, `Raw.depth`
- **Role**: ✓ The 4th axiom clause + depth observable.

### `Raw/Fold.lean` (67 LOC)
- **Imports**: Raw.Slash
- **Defines**: `Tree.fold`, `Raw.fold`, `Raw.fold_a/b/slash`
- **Role**: ✓ Catamorphism (unique morphism into any α-codomain).
- **WARNING (in file)**: asymmetric `combine` → silent axiom leak. `fold_slash` requires `hsym`.

### `Raw/Swap.lean` (159 LOC)
- **Imports**: Internal.Raw.Cmp
- **Defines**: `Tree.swap`, `Raw.swap`, `Raw.swap_swap`, `Raw.swap_injective` + Tree helpers
- **Role**: ✓ Swap automorphism + involutivity (paper Theorem 3.2).

### `Raw/Levels.lean` (~80 LOC)
- **Imports**: Raw.Swap, Raw.Fold
- **Defines**: `Tree.swap_depth`, `Tree.leaves`, `Tree.swap_leaves`, fold-bridges
- **Note**: Uses `Nat213.max_comm` from Term/Tactic.

### `Raw/Hom.lean` (64 LOC)
- **Imports**: Raw.Swap, Raw.Fold
- **Defines**: `Raw.fold_swap_hom` — generic conj-distributing fold-swap.
- **Role**: ✓ Algebraic homomorphism abstraction (used for ℤ[i] etc.).

### `Raw/Signed.lean` (~50 LOC)
- **Imports**: Raw.Swap, Raw.Fold, Raw.Hom, **`Internal.Int213`** (same ring, OK)
- **Defines**: `Raw.fold_signed_swap` — swap as Int negation.

### `Raw/Rec.lean` (87 LOC)
- **Imports**: Raw.Swap, Raw.Slash
- **Defines**: `@[elab_as_elim] Raw.rec` (noncomputable custom induction).
- **WARNING (in file)**: slash branch motive must be swap-invariant.

### `Raw/SwapSlash.lean` (82 LOC)
- **Imports**: Raw.Swap, Raw.Slash
- **Defines**: `Raw.swap_slash` (Raw.swap is automorphism).
- **Not in aggregator**; single downstream user (`Lens.Instances.Swap`).

### `Raw/Demo.lean` (~30 LOC)
- **Imports**: Raw (aggregator)
- **Role**: ⚠️ Demo of generated levels L0/L1/L2. All by `rfl/decide`. OK to live here.

### ⚠️ `Raw/Mobius.lean` — **RING 위반**
- **Imports**: `Lib.Math.Tactic.Ring213` ← **Ring 4 → Ring 1**
- **Defines**: Pell-Fib recurrences for Möbius matrix [[2,1],[1,1]]
- **Verdict**: 이건 *content* (수치/물리). `Lib/Math/Modular/`로 이주해야.
- **Not in aggregator** (`Theory/Raw.lean`이 excluded — 위반을 격리하긴 한 셈).

### Raw/ 요약
- 8 core: Core/Slash/Fold/Swap/Levels/Hom/Signed/Rec — 모두 aggregator + Ring-clean ✓
- 1 compat: SwapSlash — aggregator 밖, 단일 소비자
- 1 demo: Demo — OK
- 1 **misplaced: Mobius** (Ring 4 import) — Lib으로 이주 권고

## 2. Atomicity/ — forced-uniqueness proofs (8 files)

### `Atomicity/Five.lean`
- **Imports**: Term.Tactic.{Nat213, Mod213}, Atomicity.FiveHelpers
- **Role**: ✓ Defines `Decomp`, `IsAlive` (both atom multiplicities odd), `Atomic`. Proves `atomic_iff_five` — given atoms {2,3}, unique alive decomp ⟺ n=5.
- **Note**: ∅-axiom, no omega/simp/rcases.

### `Atomicity/FiveHelpers.lean`
- **Imports**: Term.Tactic.Nat213
- **Role**: ✓ Pure ℕ helpers (Bézout shifts, add-K-ne-self).

### `Atomicity/PairForcing.lean`
- **Imports**: Atomicity.Five, Term.Tactic.{Nat213, Mod213}
- **Role**: ✓ Strengthens Five → uniqueness of atom pair (2,3). Custom `half : Nat → Nat` (peels off 2 at a time) to bypass propext-leaking `Nat.div`.

### `Atomicity/NonDecomposable.lean`
- **Imports**: Term.Tactic.Nat213
- **Role**: ✓ Paper Prop 6.5 — `n ∈ {2, 3}` ⟺ `n` non-decomposable as `a + b` with `a, b ≥ 2`.

### `Atomicity/ArityForcing.lean`
- **Imports**: Term.Tactic.Nat213
- **Role**: ✓ `Raw3` (arity-3 analog). Shows arity 3 is vacuous over `Fin 2` base. Hand-proof; no Lib import.

### ⚠️ `Atomicity/ArityForcingGeneral.lean` — **RING 위반**
- **Imports**: **`Lib.Math.Pigeonhole`** ← Ring 4 → Ring 1
- **Role**: General `RawNk N k` for any N, k with N < k. Uses `Pigeonhole.no_inj_lt`.
- **Verdict**: Pigeonhole is a generic math lemma — should be reachable from Theory. Either:
  - Move `Pigeonhole` to a shared lower layer (Term/ or Theory/Internal), OR
  - Move `ArityForcingGeneral` to Lib/.
- **Note**: docstring claims `Classical.choice` is replaced by structural `getBase` — good, but Pigeonhole import remains.

### `Atomicity/PrimitiveSizes.lean`
- **Imports**: Atomicity.NonDecomposable
- **Role**: ✓ Final spec — `pairSize = 2`, `closureSize = 3` named.

### `Atomicity/Alive.lean`
- **Imports**: (none — purely arithmetic ℕ)
- **Role**: ✓ Defines `residue a = a % 2`. Docstring is **architecturally honest**: Alive is a *separate* structural principle (exterior-algebra/fermion statistics), NOT derived from Raw alone.

### Atomicity/ 요약
- 7 files Ring-clean ✓ (use only Term/Tactic from below)
- 1 violation: **ArityForcingGeneral** (Lib.Math.Pigeonhole)
- 의도된 분리 ✓: 이 cluster는 Raw를 import 안 함 — abstract ℕ-system forcing

## 3. Internal/ — implementation detail (7 files total)

### `Internal/Raw/Cmp.lean`
- **Imports**: Raw.Core
- **Defines**: Tree.cmp_eq_iff, cmp_swap, cmp_gt_to_lt_swap, cmp_lt_to_gt_swap, cmp_self_eq, Bool.and_eq_true_to_pair, etc.
- **Role**: ✓ Internal lexicographic + Bool helpers consumed by Raw/Slash, Raw/Swap, Raw/Rec, Raw/Levels.
- Note: Raw.lean aggregator pulls this — necessary scaffolding.

### `Internal/Raw/CmpIndependence.lean`
- **Imports**: Theory.Raw (the aggregator)
- **Role**: ✓ Meta-theorem — the `Tree.cmp` choice is an *encoding* artifact, not part of the axiom. Any `CmpProps`-respecting comparison gives bijective `RawBy cmp`.
- **Docstring**: explicitly authorises Internal access for this file (axiom-independence verification of the encoding scaffold).

### `Internal/Int213.lean`
- **Imports**: Term.Tactic.Nat213
- **Role**: ✓ 0-axiom Int helpers (add_comm, neg_add, etc.). Replacements for Lean-core simp-heavy `Int.*`. Used by Raw/Signed + Cayley-Dickson tower.

### `Internal/Int213Instance.lean`
- **Imports**: Internal.{Int213, Algebra213}
- **Role**: ✓ Registers `Int` as `Ring213` / `CommRing213` instance. Enables generic ring lemmas at Int.

### `Internal/Algebra213.lean`
- **Imports**: Internal.Int213
- **Role**: ✓ **The abstract typeclass hierarchy** (Ring213, CommRing213, StarRing213, IntegerNormed213). Generic theorems (normSq_mul via Hurwitz decomp) at abstract level.
- **Design**: docstring lists ∅-axiom constraints (no simp tags, no Decidable on abstract types, Eq-typed fields).
- **Importance**: this is the *replacement for `hurwitz_ring` tactic timeouts* in CD layers.

### `Internal/Algebra213CDDouble.lean`
- **Imports**: Internal.{Int213, Algebra213}
- **Role**: ✓ CD doubling functor at typeclass level: `CommStarRing213 → StarRing213`. Mathematical meta-theorem.
- Sequence: `CDDouble Int = ZI`, `CDDouble ZI = Lipschitz`, `CDDouble Lipschitz = Cayley` (loses associativity).

### `Internal/Algebra213CDDoubleStar.lean`
- **Imports**: Internal.Algebra213CDDouble
- **Role**: ✓ Completes the generic StarRing213 instance for `CDDouble α`. Filler lemmas (mul_add, mul_assoc, conj_*).

### Internal/ 요약
- 7 files, **모두 Ring-clean** ✓
- `Raw/Cmp` + `Raw/CmpIndependence`: Tree comparison + encoding-independence meta-theorem
- `Int213` + `Int213Instance`: 0-axiom Int + Ring213 instance registration
- `Algebra213` + `CDDouble` + `CDDoubleStar`: **abstract algebra typeclass hierarchy** (Ring213 → CommRing213 → StarRing213 → IntegerNormed213 + CD doubling functor)
- **Observation**: Algebra213* files are *structurally* abstract algebra — they could arguably live in `Lib/Math/Algebra/` if not for the dependency from `Raw/Signed` on `Int213` (and `Int213` on Nat helpers).  Currently OK in Internal because Int213 is the bedrock for Raw's signed-fold.

## 4. Closed/ — closed-universe artefacts (6 files)

**Cluster thesis (from `FoldRaw.lean` docstring)**: 213 = closed universe.
Raw가 곧 universe. 외부 type (Bool, Nat, Prop, Lens) 의존하지 않고 모든
연산이 `Raw → Raw` 안에서 닫힘. 이게 "압축 thesis의 logical 끝점".

### `Closed/FoldRaw.lean`
- **Imports**: Raw.{Fold, Swap, Slash, SwapSlash, Rec}
- **Defines**: `slashOrSelf` (total function avoiding `x ≠ y` requirement), `foldRaw : Raw → Raw → (Raw → Raw → Raw) → Raw → Raw`
- **Role**: ✓ Endomorphic catamorphism (codomain = Raw). Foundation for the "closed universe" prototypes below.
- **Note**: docstring explicitly contrasts with generic `Raw.fold {α : Type}` which pulls external type axioms.

### `Closed/Bool213.lean`
- **Imports**: Closed.FoldRaw
- **Defines**: `Bool213.{T, F}` = (Raw.a, Raw.b) Method A. Operations `not`, `and`, `or`, `xor` as Raw → Raw.
- **Role**: ✓ Bool encoded in Raw, no external `Bool`.

### `Closed/Bool213System.lean`
- **Imports**: Closed.Bool213, Raw.Rec
- **Defines**: `Bool213System` (Z, C : Raw, hZC) — *any* distinct Raw pair → valid Bool213. Isomorphism `iso A B`.
- **Role**: ✓ Meta pattern: infinitely many Bool213 systems, all isomorphic.

### `Closed/Nat213.lean`
- **Imports**: Closed.FoldRaw
- **Defines**: `zero := Raw.a`, `succ n := slashOrSelf n Raw.b`. Method A Nat as Raw chain.
- **Role**: ✓ Nat encoded in Raw.

### `Closed/NumberingSystem.lean`
- **Imports**: Closed.Nat213
- **Defines**: `NumberingSystem` = (Z, C : Raw, hZC). Any distinct Raw pair → valid numbering. `iso_numeral` for isomorphism.
- **Role**: ✓ Meta pattern: infinitely many Nat encodings via foldRaw.

### ⚠️ `Closed/Nat213Bridge.lean` — **RING 위반**
- **Imports**: Closed.Nat213, **`Theory.Nat213.Core`**, **`Lib.Math.NatHelpers.PureNat`**
- **Role**: Bridge Layer 1 closed-Raw Nat213 ↔ Layer 2 inductive Nat213 isomorphism.
- **Verdict**:
  - `Lib.Math.NatHelpers.PureNat` import = Ring 4 → Ring 1 violation.
  - But: this is fundamentally a bridge file; perhaps PureNat helpers should migrate to Term/Tactic or Theory/Internal.

### `Closed/RawCut.lean`
- **Imports**: Closed.{Bool213, Nat213}
- **Role**: ✓ "Lean-free cut" prototype — `RawCut := Raw → Raw → Raw`. Demo of pushing the "closed universe" all the way to cut/Cauchy.
- **Significance** (per docstring): "G84 압축 thesis 의 logical 끝점".

### Closed/ 요약
- 6 files; **all are *demonstrations* of the "closed universe" thesis** — encoding Bool/Nat/Cut as Raw alone.
- 5 Ring-clean ✓
- 1 violation: **Nat213Bridge** (Lib.Math.NatHelpers.PureNat)
- **Architectural observation**: Closed/ is interesting — it's *content* (showing 213 can self-host Bool/Nat/Cut) but currently lives in Theory. Arguably this belongs in Lib/ (since it's exploratory content, not foundational scaffolding). But the design choice is intentional per the docstring vision.

## 5. Nat213/ — Nat 213 arithmetic system (6 files)

### `Nat213/Core.lean`
- **Imports**: Term.Tactic.Nat213
- **Defines**: `inductive Nat213 | one | succ` — 213-native ℕ₊ (no zero). add, mul closed; no sub.
- **Role**: ✓ Theory-layer inductive ℕ₊ (Layer 2 representation).
- **Note**: distinct from `Theory.Closed.Nat213` (Layer 1, Raw chain). Bridge in `Closed/Nat213Bridge`.

### `Nat213/Lenses.lean`
- **Imports**: Nat213.Core, Theory.Raw
- **Role**: ✓ Characterizes Raw → Nat213 lenses (multiple, infinite family, swap-invariant iff `ba = bb`).
- **Note**: This actually belongs to *Lens* domain — but currently in Theory because it characterises a specific Raw catamorphism shape. Borderline.

### ⚠️ `Nat213/AtomicityCorrespondence.lean` — **RING 위반**
- **Imports**: Nat213.Core, Theory.Raw, **`Lib.Physics.Simplex.Counts`**, **`Lib.Math.UniverseChain.PairAxes`**
- **Role**: User-inspired note connecting `Raw=3 ctors + Nat213=2 ctors = 5 = d`. Atomicity 2/3/5 ↔ fractal signature.
- **Verdict**: This is **interpretive content**, not Theory infrastructure. Imports Lib physics.
- **Recommendation**: 이주 to Lib/Math (or research-notes since it's an interpretive observation).

### ⚠️ `Nat213/OneAsGlue.lean` — depends on Mobius (already flagged)
- **Imports**: **`Theory.Raw.Mobius`** (transitively Ring 4), Nat213.AtomicityCorrespondence
- **Role**: Interpretive theorem about "1 as glue" in Möbius P. NS/NT/d encoded in matrix entries.
- **Verdict**: Same as AtomicityCorrespondence — content, not infra. Belongs in Lib or research-notes.

### ⚠️ `Nat213/RotationGeometry.lean` — **RING 위반**
- **Imports**: Nat213.{AtomicityCorrespondence, OneAsGlue}, **`Theory.Raw.Mobius`**, **`Lib.Math.Topology.EulerChi`**
- **Role**: K_{3,2}^{(2)} bipartite + Möbius P + Pell-Fib spiral connection.
- **Verdict**: Geometric/topology content. Lib/Math/Topology에 속함.

### ⚠️ `Nat213/AlgebraicGeometry.lean` — **RING 위반**
- **Imports**: Nat213.RotationGeometry, **`Lib.Math.Topology.EulerChi`**, **`Lib.Math.CayleyDickson.Hurwitz213`**
- **Role**: SL(2, F_5) ≅ 2I (binary icosahedral), Betti b_0=1, b_1=8, χ=-7, Type D Hurwitz.
- **Verdict**: Pure content/cohomology. Lib.

### Nat213/ 요약
- **2 files Ring-clean** (Core, Lenses)
- **4 files violate Ring** (AtomicityCorrespondence, OneAsGlue, RotationGeometry, AlgebraicGeometry) — all import Lib.
- **All 4 violators are interpretive/content**, not Theory infrastructure.
- **Architectural drift detected**: this sub-cluster has accumulated *commentary/connection notes* that were placed here because they discuss `Nat213` but actually use Lib content. They should live in Lib (or research-notes).

## 6. Tower/ — Nat-pair / Nat-triple → Int / Z₂ (3 files)

### `Tower/NatPairToInt.lean`
- **Imports**: Internal.Int213, Term.Tactic.Nat213
- **Role**: ✓ ℕ → ℤ via orthogonal-axis pair `(a, b) → a - b`. G62 research note materialisation.

### `Tower/NatPairToQPos.lean`
- **Imports**: Nat213.Core
- **Role**: ✓ ℚ_+ via multiplicative quotient.

### `Tower/NatTripleToZ2.lean`
- **Imports**: Internal.Int213, Term.Tactic.Nat213, Tower.NatPairToInt
- **Role**: ✓ ℤ² (Gaussian-style).

### Tower/ 요약
- **3 files, all Ring-clean** ✓
- "G62 orthogonal-axis 2-side extensions" — 철학적으로 atomicity {2,3}에서 자연스러운 확장
- Theory에 머무를 자격 있음 (motivation이 atomicity).

## 7. CDDouble/ — Cayley-Dickson double in Theory (3 files)

### `CDDouble/UniversalOrder4.lean`
- **Imports**: Internal.Algebra213CDDouble
- **Role**: ✓ Generic `(0, u)² = (-1, 0)` over abstract StarRing213.

### `CDDouble/GenericLiftDemo.lean`
- **Imports**: Internal.Algebra213CDDoubleStar, CDDouble.UniversalOrder4
- **Role**: ✓ CD-doubling lift demo.

### ⚠️ `CDDouble/UniversalInduction.lean` — **RING 위반**
- **Imports**: 5× `Lib.Math.CayleyDickson.*` (Lipschitz, Cayley, L4T/L5T/L6T Order4Monopoly)
- **Role**: Induction over concrete CD layer instances.
- **Verdict**: Instances live in Lib → 이 파일도 Lib에 속함.

### CDDouble/ 요약
- 2 Ring-clean, 1 violation
- **UniversalInduction**은 Lib content 의존이라 이주 권고.

## 8. Tools/ — Theory tools (1 file)

### ⚠️ `Tools/CertChecker.lean` — **RING 위반**
- **Imports**: `Lib.Physics.AlphaEM.Brackets`, `Lib.Physics.Basel.Bound`
- **Role**: Rust `Certificate` schema의 Lean-side verifier. Cite/Apply/Bound 검증.
- **Verdict**: Physics 증서 검증 도구 — Lib/Physics/ 또는 App/ 또는 새 Verification/에 속함.
- **Note**: API.lean이 이미 "Sealed (NOT API) utility"로 분류.

---

## Summary of findings

### Theory의 실제 역할 (사용자 질문에 대한 답)

> "원래 의도는 Term의 AST를 두고 Theory에서 그걸 가져다 Raw를 구성하는거?"

**답: 아니다.** Term의 AST와 Theory의 Raw는 **두 개의 독립적인 deep-embedded 타입**:

- `Term`: 4-생성자 (zero/succ/add/mul) — Nat counting AST
- `Raw`: 3-생성자 (a/b/slash with canonicality) — 213 axiom data

이 둘은 **서로 import하지 않는다.** Theory는 Term의 *AST*를 가져다 쓰지 않고, Term의 *Tactic 라이브러리*만 (PURE Nat lemmas) import한다.

→ Term은 ARCHITECTURE.md 표현대로 "Lean-side scaffolding to run 213 inside Lean 4" — Nat 산술의 0-axiom 검증 substrate.
→ Theory는 "the 213 axiom itself" — Raw type + 4 clauses + 강제된 형상 유일성 증명.

**두 디딤돌, 평행.** Term은 Theory를 *구성*하지 않고 *지원*한다 (tactic 라이브러리로).

### Theory의 4가지 구조적 역할

1. **TH-A (Raw API)** — `Raw/` 13 files
2. **TH-B (Atomicity)** — `Atomicity/` 8 files (Raw import 안 함, 의도된 분리)
3. **Internal scaffolding** — `Internal/` 7 files
4. **Closed universe demos** — `Closed/` 6 files

### 발견된 Ring 위반 (10건) — Lib에서 import

ARCHITECTURE.md "imports flow inward only" 위반:

| File | Imports Lib |
|---|---|
| `Raw/Mobius.lean` | `Lib.Math.Tactic.Ring213` |
| `Atomicity/ArityForcingGeneral.lean` | `Lib.Math.Pigeonhole` |
| `Closed/Nat213Bridge.lean` | `Lib.Math.NatHelpers.PureNat` |
| `Nat213/AtomicityCorrespondence.lean` | `Lib.Physics.Simplex.Counts`, `Lib.Math.UniverseChain.PairAxes` |
| `Nat213/OneAsGlue.lean` | (transitively via `Raw/Mobius`) |
| `Nat213/RotationGeometry.lean` | `Lib.Math.Topology.EulerChi` |
| `Nat213/AlgebraicGeometry.lean` | `Lib.Math.Topology.EulerChi`, `Lib.Math.CayleyDickson.Hurwitz213` |
| `CDDouble/UniversalInduction.lean` | 5× `Lib.Math.CayleyDickson.*` |
| `Tools/CertChecker.lean` | `Lib.Physics.AlphaEM.Brackets`, `Lib.Physics.Basel.Bound` |

### 이주 권고

| 현재 | 권장 위치 | 이유 |
|---|---|---|
| `Raw/Mobius.lean` | `Lib/Math/Modular/` | 수치/물리 content |
| `Atomicity/ArityForcingGeneral.lean` | 유지 (Pigeonhole를 Term/Tactic으로) | 일반화 정리 |
| `Closed/Nat213Bridge.lean` | 유지 (PureNat을 Term/Tactic으로) | bridge |
| `Nat213/AtomicityCorrespondence.lean` | `Lib/Math/Atomicity/` 또는 `research-notes/` | 해석적 메모 |
| `Nat213/OneAsGlue.lean` | `Lib/Math/Modular/` | 해석적 메모 |
| `Nat213/RotationGeometry.lean` | `Lib/Math/Topology/` | 토폴로지 content |
| `Nat213/AlgebraicGeometry.lean` | `Lib/Math/Cohomology/` | 코호몰로지 content |
| `CDDouble/UniversalInduction.lean` | `Lib/Math/CayleyDickson/` | concrete CD induction |
| `Tools/CertChecker.lean` | `Lib/Physics/Tools/` or `App/` | 인증서 검증 도구 |

### 깨끗한 Theory 코어 (canonical, 35~37 files / 49)

- `Theory/API.lean` (entry)
- `Theory/Raw.lean` aggregator + 8 core (Core, Slash, Fold, Swap, Levels, Hom, Signed, Rec) + Cmp
- `Theory/Atomicity.lean` aggregator + 7 of 8 sub
- `Theory/Internal/*` (7 files; all Ring-clean)
- `Theory/Closed/*` (5 of 6; demos)
- `Theory/Tower/*` (3 files)
- `Theory/CDDouble/UniversalOrder4`, `GenericLiftDemo` (2 of 3)

나머지 ~12 files은 해석적 콘텐츠 / Ring 위반 / 이주 후보.

### "Term → Theory 의도"에 대한 최종 답

원래 의도는 아마 이렇게 그렸을 가능성:

```
Lean kernel
  ↓
Term (Nat counting AST + tactic suite for 0-axiom verification)
  ↓
Theory (Raw axiom data + forced-shape proofs)
  ↓
Lens (catamorphism α-codomain framework)
  ↓
Meta (metatheorems)
  ↓
Lib (math + physics content)
  ↓
App (interface)
```

**실제로는**: Term의 AST(Term)는 Theory에서 사용되지 않음. Theory의 Raw는 Term의 AST와 무관하게 Lean kernel + Term의 Tactic 라이브러리로 직접 정의됨. 즉:

```
Lean kernel + Term.Tactic.* (PURE Nat helpers)
  ↓                       ↘
Term.Term (AST)        Theory.Raw (a/b/slash)
  ↓                       ↓
Term.{Compare,Sound,...}  Theory.{Raw API, Atomicity}
                            ↓
                          Lens, Meta, Lib, App
```

**Term.Term (AST)는 사실상 dead end** (downstream에 안 쓰임). Term의 진짜 가치는 *Tactic 라이브러리* (Nat213, Mod213 등 PURE helpers). 이게 사용자가 Term을 "불투명하다"고 느낀 진짜 이유 — Term이라는 이름이 두 개의 다른 역할 (AST + Tactic)을 묶고 있음.

→ 향후 가능한 architectural rename: `Term/` = AST 전용으로 슬림하고, `Tactic/` (현재 Term/Tactic/) 을 top-level로 승격. ARCHITECTURE.md §3 "Path = namespace, ideally" 만족 (namespace는 이미 `E213.Tactic.*`).

