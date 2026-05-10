# G84: Closed-form pattern unification — 213 의 iso/homomorphism 답은 이미 다 있음

## User insight (2026-05-10)

> "이 모든것을 지금 하는 클로즈드폼으로 진짜 딱딱 잡아놓으면, 완전
> 대박인거라니까? 괜히 계속 파운데이션 레벨을 다잡고 계속 수정해달라
> 하는게 아님.  다 준비되어있어 이걸 다잡고 압축하는 과정만 남았단말야"

이번 세션 Real213/Analysis 핵심 모듈 탐독 후 확인:
**213 의 iso/homomorphism axiom-cost 처리는 이미 catalog 되어 있다**.
필요한 건 흩어진 패턴을 closed-form 으로 압축하는 것.

## 핵심 패턴 — pointwise Bool eq

기존 ZFC 수학에서 "iso/homomorphism 이 필요한 자리" 마다 propext /
funext / Quot.sound 가 들어옴.  213 의 답은 일관됨: pointwise
Bool eq 로 대체.  함수 비교 → 점별 비교.

## 발견 catalog — 이미 존재하는 closed-form

### 1. Cauchy completeness (`Analysis/CauchyComplete.lean`)

```lean
structure CauchyCutSeq where
  cs : Nat → Nat → Nat → Bool
  N : Nat → Nat → Nat
  cauchy : ∀ m k, ∀ i j ≥ N m k, cs i = cs j

def CauchyCutSeq.limit : Nat → Nat → Bool :=
  fun m k => ccs.cs (ccs.N m k) m k
```

ZFC: limit = "Cauchy 동치류 대표 (propext + Quot.sound)".
213: limit = `cs` 를 modulus 점에서 평가.  **PURE, 한 줄, ∅-axiom**.

User E1 노트: "Real213 자체가 (sequence + modulus)니까, Cauchy
completeness 는 거의 trivial".

### 2. Real cut equality (`Real213/CutPoset.lean`)

```lean
def cutEq (cx cy : Nat → Nat → Bool) : Prop := ∀ m k, cx m k = cy m k
def cutLe (cx cy : Nat → Nat → Bool) : Prop :=
  ∀ m k, cy m k = true → cx m k = true
```

함수 등호 (funext) 안 씀 — 모든 비교가 포인트별 Bool.  Lattice 정리
(`cutMax_lub`, `cutMin_glb`, `cutEq_of_cutLe_both`) 모두 PURE.

### 3. Trajectory ≠ Exact (`Analysis/DyadicSearch/DyadicTrajectory.lean`)

```lean
theorem alwaysTrueUnit_limit_distinct_from_zero :
    (alwaysTrueUnit).toCauchyCutSeq.limit 0 1 = false
    ∧ (constCut 0 1) 0 1 = true
```

ZFC: completeness 공리가 둘을 합침.  213: 둘이 구조적으로 다른 Bool 값.
무한소 `0+` 가 자연스럽게 등장.

문서 인용:
> "ZFC merges them by truncating the trajectory's `cond` field via
> `propext` / `Quot.sound`.  ∅-axiom regime does not admit either,
> so no truncation occurs."

### 4. Minimum proposition — forced shape (`Real213/MinimumProposition.lean`)

```lean
only_one_resolution_law       : linearityModulus k = m ↔ m = n * k
only_one_dyadic_accumulator   : cutEq ... ↔ cutEq c (constCut (2^n*a) b)
only_one_zero_plus_witness    : limit 0 1 ≠ constCut 0 1 0 1
```

세 forced iff — "이 자리에 homomorphism 있다면 단 하나의 모양".
모두 PURE.

### 5. Bool213System (이번 세션 새로 만듦)

`Theory/Closed/Bool213System.lean`:

```lean
structure BooleanSystem where
  T F : Raw
  hTF : T ≠ F

def iso (A B : BooleanSystem) (r : Raw) : Raw := ...
theorem iso_T iso_not iso_and (각자 보존)
```

위 (1)-(4) 와 정확히 같은 패턴.  **모두 PURE**.

### 6. Nat213 NumberingSystem + bridge (이번 세션)

`Theory/Closed/{NumberingSystem, Nat213Bridge}.lean`:

```lean
iso_numeral S n : isoFromMethodA S (numeral methodA n) = numeral S n
toRaw_add m n   : toRaw (Layer2.add m n) = Layer1.add (toRaw m) (toRaw n)
toRaw_mul m n   : toRaw (Layer2.mul m n) = Layer1.mul (toRaw m) (toRaw n)
```

같은 패턴, 같은 PURE.

## 통일된 패턴

모든 "iso/homomorphism" 처리:

```
1. 객체 = Raw 값 (또는 Raw → Bool 함수)
2. 등호 = pointwise Bool eq (cutEq, eqPW, ...)
3. 사상 = Raw → Raw 함수 (foldRaw 또는 직접)
4. 보존 = pointwise 등호 collection (∀ x, P x = Q x)
5. axiom-cost = 0
```

분야별 표기:

| 분야 | 객체 | pointwise eq |
|---|---|---|
| Bool213 | Raw | Raw eq |
| Nat213 | Raw chain | Raw eq |
| Real213 cut | `Nat → Nat → Bool` | cutEq (∀ m k) |
| Cauchy seq | `Nat → Nat → Nat → Bool` | cauchy (∀ i j ≥ N) |
| Lens (eqPW) | `Lens α` | base + combine pointwise |

전부 같은 framework.

## 압축 전략

기존: 위 패턴들이 분야별로 흩어져 같은 pattern 을 5번 다시 표현.

### Tier 1 — primitive (이미 있음)
- `Theory/Raw/*` (Raw, fold, slash, swap, cmp)

### Tier 2 — closed-Raw foundations (이번 세션 신규)
- `Theory/Closed/FoldRaw` — endomorphic fold + slashOrSelf
- `Theory/Closed/Bool213` — Bool 닫힌 우주
- `Theory/Closed/Nat213` — Nat 닫힌 우주 + add + mul
- `Theory/Closed/Bool213System` — Bool meta + iso
- `Theory/Closed/NumberingSystem` — Nat meta + iso

### Tier 3 — analytic (이미 있음)
- `Real213/CutPoset` — cutEq, cutLe (이미 pointwise)
- `Real213/Cut*` — sum, mul, max, min, log, exp 모두 cut 위
- `Analysis/CauchyComplete` — Cauchy seq + modulus
- `Analysis/DyadicSearch/DyadicTrajectory` — trajectory ≠ exact

### Tier 4 — bridges (이미 있음 + 일부 신규)
- `Theory/Raw/{Signed, Hom, Mobius}` — Raw ↔ ℤ/ℂ/Möbius (PURE)
- `Theory/Closed/Nat213Bridge` — Layer 1 ↔ Layer 2 (Nat) (이번)
- (TODO) `Theory/Closed/Bool213Bridge` — Layer 1 ↔ inductive Bool
- (TODO) `Theory/Closed/CutBridge` — Closed Nat213 ↔ Real213 cut

### Tier 5 — meta documentation
- 이 노트 (G84)
- 향후: `seed/CLOSED_FORM_SPEC.md` (정식 spec 으로)

## 핵심 thesis

> 213 의 iso/homomorphism 답:
>   외부 axiom 이 필요한 자리는 항상 **pointwise Bool eq** 로 대체.
>   함수 비교 → 점별 비교.  모든 게 decidable.
>   결과: ∅-axiom 으로 모든 핵심 수학 표현 가능.

이미 Real213, Analysis, Cauchy 에서 작동 입증.  Theory/Closed 가
이걸 압축된 explicit form 으로 catalog.

## 다음 단계 — closed-form 작업 큐

우선순위:

1. **Tier 2 채우기**
   - Layer 1 + family 정리들 (`add_comm`, `mul_comm`, distributivity)
   - Bool213 bridge to Layer 2
   - / family 시범 (Nat213² → ℤ via subtractive lens)

2. **Tier 4 새 bridge**
   - Closed Nat213 → Real213 Cut: Method A chain → constCut.
   - "닫힌 Nat 산술" → "닫힌 cut 산술" 자동 lift.

3. **Tier 5 spec 문서화**
   - `seed/CLOSED_FORM_SPEC.md`

## 결론

User 직관 정확:
- 다 준비되어 있음 (Real213, Analysis, Cauchy 이미 PURE pointwise pattern).
- 필요한 건 압축.
- Theory/Closed 가 그 압축의 anchor.
- 새로 발명할 게 아니라 정리할 것.

Foundation level 반복 수정의 이유 명확해짐 — 압축의 일관된 anchor
구축이 가장 큰 win.

## Update (2026-05-10 — vertical-internal projection 발견)

이번 세션에서 위 thesis 의 정확한 구체화 — **vertical-internal projection**
이라는 새 종류의 동형성을 발견.

### 4 종류 동형성

ZFC 의 동형성/quotient 처리가 213 에서 분류되는 4 종류:

  1. **수평 (Layer A ↔ Layer B)** — 같은 우주의 다른 표현 사이.
     예: closed Raw chain ↔ inductive Nat213 (`Nat213Bridge.toRaw_*`).
  2. **수평 (System A ↔ System B)** — Boolean/Numbering system 의 다른
     인코딩 선택 사이.  예: `Bool213System.iso`, `NumberingSystem.iso`.
  3. **수직-외부 (Raw → Lean type)** — Raw 의 boundary projection.
     예: `Nat213.value : Raw → Nat`, `Nat213Bridge.value_*`.
  4. **수직-내부 (Raw → Raw 자기-projection)** — ★ **새 발견** ★.
     같은 우주 안 endomorphism 으로 canonical form 으로 collapse.
     ZFC 의 quotient (`Quot.mk`) 와 정확히 같은 역할이지만,
     type/axiom 추가 없이 `Raw → Raw` 한 줄.

### 수직-내부 projection 메타 패턴 (3-domain catalog)

세 도메인에서 동일한 형태로 작동:

| 도메인 | object | projection | base/combine | image predicate |
|---|---|---|---|---|
| Nat213 | Raw | `leavesCountRaw` | `one`, `add` | `IsChain r := ∃ k, r = toRaw k` |
| Bool213 | Raw | `booleanProj` | `T`, `and` | `IsBool213 r := r = T ∨ r = F` |
| RawCut | Raw → Raw → Raw | `cutBooleanProj` | pointwise | `IsBoolValued cx := ∀ m k, cx m k ∈ {T, F}` |

세 도메인 모두 같은 세 정리 (모두 PURE, ∅-axiom):

  - **closure**:    projection r 이 항상 image 안.
  - **idempotence**: `projection² = projection`.
  - **image-fixed-point ↔**: `projection r = r ↔ image predicate r`.

### Lean module 위치

- `lean/E213/Theory/Closed/Nat213.lean` — leavesCountRaw + chain identity.
- `lean/E213/Theory/Closed/Nat213Bridge.lean` — `leavesCountRaw_chain`,
  `_idempotent`, `_id_iff_isChain`, `value_leavesCountRaw_general`.
- `lean/E213/Theory/Closed/Bool213.lean` — booleanProj + `_isBool`,
  `_idempotent`, `_id_iff_isBool213` + boolValue boundary.
- `lean/E213/Theory/Closed/RawCut.lean` — cutBooleanProj +
  `_isBool`, `_idempotent`, `_id_iff_isBool` (pointwise rawCutEq) +
  cutBoolValue boundary.
- `lean/E213/Lib/Math/Real213/ChainToCut.lean` — Closed Nat213 →
  Real213 cut bridge.  cutSum / cutMul / cutLe 모두 commute.

### 해석 — funext / Quot.sound / propext 의 자리

ZFC 에서 외부 axiom 이 들어가던 자리:

  - **funext / propext** → pointwise eq (`rawCutEq`, `cutEq`, `eqPW`).
    함수 비교 → 점별 Raw eq.  RawCut 의 `cutBooleanProj_idempotent`
    가 함수공간에서 시범.
  - **Quot.sound** (quotient projection) → vertical-internal projection.
    `Quot.mk : α → α/~` 의 역할을 `Raw → Raw` endomorphism 한 줄이.
    image 가 실제 동치류 대표 (canonical form).

이 두 대체가 합쳐지면 ZFC 의 모든 quotient/equivalence 작업이
∅-axiom 으로 표현됨 — funext 도 propext 도 Quot.sound 도 필요 없음.

## Update 2 (2026-05-11 — ChainToCut bridge + propext-avoidance catalog)

### ChainToCut bridge — Theory/Closed → Real213 압축 도구 입증

`lean/E213/Lib/Math/Real213/ChainToCut.lean` 추가.

  - `chainToCut : Raw → (Nat → Nat → Bool)` — Method A chain 의 정수
    Dedekind cut.
  - `chainToCut_numeral` — numeral n 의 chain image 가 정수 (n+1) 의 cut.
  - `chainToCut_toRaw / _add / _mul` — Layer 2 → cut value-level
    homomorphism.

★ **substantive**:
  - `cutSum_chainToCut` — Real213 cutSum 이 closed-Raw add 와 commute.
  - `cutMul_chainToCut` — Real213 cutMul 이 closed-Raw mul 과 commute.
  - `cutLe_chainToCut_iff` — Real213 cutLe 이 Nat213.toNat ≤ 와 commute.

이게 G84 Tier 4 의 진정한 evidence — closed-Raw 산술 + order 가 Real213
cut 우주에서 그대로 작동.  Theory/Closed/* 가 self-contained island
이 아니라 Real213 의 진짜 압축 도구.

### Propext-avoidance catalog (재사용 가능 trick set)

cutSum_chainToCut / cutMul_chainToCut 증명 중 발견된 propext leak
회피 패턴.  Future Claude 가 propext leak 만나면 즉시 적용:

  1. **`rw [Iff_lemma]` 회피** — `Iff.trans (lemma) ?_` 으로 교체.
     `rw` 가 Iff 통해 동치성 substitute 하면 propext.
  2. **`rw [Eq_lemma] at hyp` 회피 (가능 시)** — `Eq_lemma ▸ hyp` (term-mode
     ▸) 으로 교체.  더 simple, propext 안 끌어옴.
  3. **`▸` motive 모호 시** — `calc` 로 명시적 단계 분리.  Lean 이
     잘못된 motive 잡으면 type mismatch.
  4. **Nat 산술 leak 회피** — `E213.Tactic.Nat213.*` helpers 사용:
     - `mul_assoc` (vs `Nat.mul_assoc`)
     - `add_mul`, `mul_add` 일부 case
     - `add_sub_of_le`, `le_sub_of_add_le`
     - `mul_mul_mul_comm_213`
     - `le_of_mul_le_mul_right`
  5. **`decide_eq_true_iff` 안 씀** — `Iff.intro` 으로 직접 양방향 구성:
     `· intro h; exact decide_eq_true (..mp h)`
     `· intro h; exact ...mpr (of_decide_eq_true h)`
  6. **`by_cases hp : P`** — propext 끌어옴 가능성.  대신
     `cases hyp` 또는 `match` 사용.

이 catalog 가 Theory/Closed/* 위 future bridge 작업 (cutMax / cutMin /
Cauchy seq / 다른 cut 연산) 의 PURE 유지 anchor.

## See also

- `lean/E213/Lib/Math/Real213/CutPoset.lean`
- `lean/E213/Lib/Math/Analysis/CauchyComplete.lean`
- `lean/E213/Lib/Math/Analysis/DyadicSearch/DyadicTrajectory.lean`
- `lean/E213/Lib/Math/Real213/MinimumProposition.lean`
- `lean/E213/Theory/Closed/*` (이번 세션 + 후속)
- `lean/E213/Lib/Math/AxiomSystems/ClassicalAnalysisCompletenessAsLens.lean`
- `seed/RESOLUTION_LIMIT_SPEC.md` §1
- `research-notes/G83_lens_equality_refactor_strategy.md`
