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

## See also

- `lean/E213/Lib/Math/Real213/CutPoset.lean`
- `lean/E213/Lib/Math/Analysis/CauchyComplete.lean`
- `lean/E213/Lib/Math/Analysis/DyadicSearch/DyadicTrajectory.lean`
- `lean/E213/Lib/Math/Real213/MinimumProposition.lean`
- `lean/E213/Theory/Closed/*` (이번 세션)
- `lean/E213/Lib/Math/AxiomSystems/ClassicalAnalysisCompletenessAsLens.lean`
- `seed/RESOLUTION_LIMIT_SPEC.md` §1
- `research-notes/G83_lens_equality_refactor_strategy.md`
