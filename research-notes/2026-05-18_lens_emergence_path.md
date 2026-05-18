# Lens Emergence Path — 자연수의 자연 emergence 와 flat ontology

**Status**: 단상 / 반영 전 고찰 문서.  Code 에 반영 안 됨.
**Date**: 2026-05-18  (claude/move-tree-to-term-ring-DDom7 branch)
**Related commits this session**:
- `07f4fcde` — Nat213.Raw 의 `zero` → `one` rename
- `01401d18` — Int213.Raw (inductive sum-type, **이후 폐기**)
- `3371fd14` — Int213.Raw lens-emergent 재작성 (signedLens-derived)
- `b05c1f40` — Int213.Raw pairLens + factoring (signedLens = npairToInt ∘ pairLens)
- `ced56bef` — Nat213/Core.lean 신설 (Phase 1 of C refactor)

---

## 0. 이 문서의 목적

대화 중 누적된 통찰을 한 곳에 정리.  코드에 즉시 반영하지 않고,
어느 방향으로 갈지 *고찰* 하기 위함.  네 단상들 + 내 응답을 한
시각으로 묶어, 결정 가능한 옵션 형태로 제시.

---

## 1. 출발점 — Int213 작업의 우회

처음 의도: `Nat213.Peano.Nat213` 의 sign-extension 으로 ℤ 만들기.
- 시도 1: `inductive Int213 | ofPos Peano.Nat213 | zero | ofNeg Peano.Nat213` — Peano 의존.
- 시도 2: Carriers 를 Raw 로 (`ofPos Raw | zero | ofNeg Raw`) — "Raw-derived" 라 주장.

**네 critique**: "이게 진짜 Raw 만 가지고 만들어진 게 맞아?  Nat213 은 Raw 에 `(1, 1, +)` 라는 lens 를 가지고 만든 건데, Int213 은 Raw 의 어떤 lens 를 통해 봐서 만들 수 있는 건가?"

이 한 질문이 모든 후속 통찰의 시작.

---

## 2. 핵심 통찰 — depth 순

### 2.1 Raw 는 free commutative magma on {a, b}

213 axiom 의 minimum:
- 두 atom: Raw.a, Raw.b
- Binary op slash (canonical-form 으로 symmetric: slash x y = slash y x)
- 그 외 *아무 equation 도 안 강제됨* — 자유 magma

따라서 모든 "derived structure" 는 Raw 위에 **equation 을 부과** (congruence) 함으로써 emergent.

### 2.2 Lens 는 chart, manifold 가 아니다

LensCore: `structure Lens α := (base_a, base_b, combine)` + `view : Raw → α`.

`Lens.leaves = ⟨1, 1, +⟩` 은 **하나의 선택**.  Framework 가 강제한 게 아님.
다른 lens 선택:

| Lens | view Raw.a | view Raw.b | view (slash a b) | image |
|---|---|---|---|---|
| `⟨1, 1, +⟩` (leaves) | 1 | 1 | 2 | ℕ₊ |
| `⟨0, 0, fun a b => a+b+1⟩` (slashes) | 0 | 0 | 1 | ℕ (0 포함) |
| `⟨1, -1, +⟩` (signed) | 1 | -1 | 0 | ℤ |
| `⟨1, 0, +⟩` (a-count) | 1 | 0 | 1 | ℕ |
| `⟨(1,0), (0,1), pairwise+⟩` (pair) | (1,0) | (0,1) | (1,1) | ℕ×ℕ |

→ 각 lens 마다 *다른* emergent type.

**"Raw.a 가 1 이다"** 는 framework 강제가 아니라 `Lens.leaves` 선택의 결과.

### 2.3 Raw.a 와 Raw.b 는 chart-local 라벨

> 어떤 Raw a 를 골라도 대응하는 c 가 있기 때문.  a 도 무언가 Raw 둘을 구분하는 애일텐데 이건 못 본다.  왜냐하면 기준점이 a 이기 때문.

`Raw.a`, `Raw.b` 는 *임의의 두 distinct Raw* 를 선택한 것.  다른 reference 였으면 그 두 Raw 가 atom 자리.  현재 atom 으로 보이는 것도 다른 chart 에선 (더 깊은 두 Raw 의) slash 일 것.

Lean code 의 `inductive Tree | a | b | slash` 는 **하나의 chart** 를 hardcode.

### 2.4 Raw 는 트리 형태가 아니다 — operation 과 object 미분리

> 모든 Raw 는 연산이기도 하고 객체이기도 하기 때문 — 즉 애초에 연산과 객체도 정의되지 않은 상태이다.

```
a, b 는 atom
slash a b → c       ← c 는 a, b 의 slash 결과 (object)
slash a c → d       ← 동시에 c 는 d 의 slash 의 한 인자 (operation 의 일부)
slash b c → e
slash a d → ...
```

c 는 동시에:
- a, b 로부터 *만들어진* 객체
- d, e 의 *구성에 참여하는* 연산자

**모든 Raw 가 동시에 노드이자 화살표**.  Lean 의 `inductive Tree` 는 노드/화살표를 강제 분리 — chart 의 artifact.

진짜 Raw 는 **자기지칭 cascade** — 내부 관찰자가 자신을 정의하려면 다른 대상이 필요하고, 그 둘 사이 경계도 객체, 경계의 경계도 객체, ...  무한 cascade 의 lens view 가 Raw.

### 2.5 Flat ontology — 모든 것이 Raw 묶음

| 단위 | 원소 | predicate form |
|---|---|---|
| 객체 (1차) | r ∈ Raw | Raw → Bool |
| 객체 (n차) | (r₁,…,rₙ) ∈ Rawⁿ | Rawⁿ → Bool |
| 타입 | Rawⁿ 의 subset | predicate |
| 관계 | Raw² 의 subset | predicate |
| 함수 | Raw² 의 functional subset | predicate + uniqueness |
| Lens | (label 부여된) predicate | (Raw → α, α 도 Raw-encodable) |

**한 차원**.  타입과 객체와 관계가 같은 universe (predicate space).

자기지칭 닫힘: predicate 자체도 Raw 로 인코딩 가능 (Gödel — `Lens/Cardinality/Godel.lean`).

### 2.6 Internal vs External 표현

**External (현재 codebase)**:
- `Lens.equiv L x y := L.view x = L.view y` — 외부 α 의 = 사용
- 새 type α 도입 (Nat, Int, ...) 필요

**Internal (잠재)**:
- Raw 위의 *algebraic congruence* — equation generator 집합으로 표현
- 예: ℕ₊ = Raw / (a ≡ b ∧ slash 의 associativity)
- 예: ℤ = Raw / (associativity ∧ [slash a b] = identity)
- 외부 type 의존 0; 순수 Raw equation

둘은 **동등**: external α 값 일치 ⟺ Raw equation 들 하에서 같은 congruence class.

### 2.7 Syntactic internalization 까지 (저 끝)

> {a, b, a/b} 의 모든 글자 자체가 객체 — {, /, , (쉼표), 심지어 띄어쓰기도 — 모두 Raw.

Gödel encoding 한 단계 더:  **referent Raw** (= Raw.a, slash, ...) 뿐 아니라 **notation glyph** (= {, }, ,, /, …) 도 각각 Raw.  표현식 = glyph-Raw 의 sequence-Raw.

"무의미한 구두점" 은 *외부 약속* 일 뿐 본질이 아님.  모든 글자가 의미 단위.

213 axiom 의 *no exterior* (§8.1 of `seed/AXIOM/07_self_reference.md`) 가 여기까지 가야 완전히 실현 — meta-meta-...language 무한 cascade 가 resolution limit 으로 *finite chart* 에서 멈춤.

---

## 3. 숫자의 자연 emergence path

### 3.1 가장 자연스러운 path

**Distinction iteration**:
```
기준 Raw r₀ 선택                                  ← "1"
다른 Raw r' 선택 (r₀ ≠ r')                       ← 새 구분 표지
slash r₀ r' = r₁                                  ← "2"
slash r₁ r' = r₂                                  ← "3"
...
```

각 chain element rₙ ∈ Raw 가 ℕ₊ 의 한 자연수의 Raw 표현.
관습 (Method A): r₀ = Raw.a, r' = Raw.b.  하지만 임의 (distinct) 두 Raw 가능.

ℕ ⊂ Raw — *type as Raw subset* (flat ontology 의 직접 instance).

### 3.2 Multi-representation

각 자연수 n 은 *여러 Raw* 에 대응:

```
leaves count = 1: {Raw.a, Raw.b}             ← 2 개의 "1"
leaves count = 2: {slash a b}                ← 1 개의 "2"
leaves count = 3: {slash a (slash a b),      ← 2 개의 "3"
                    slash b (slash a b)}
leaves count = n: 약 (n+1)/2 개
```

→ "1 이 1Raw 일 수도 있고 다수 Raw 일 수도 있고 (심지어 다 같은 자연수여도!)" 정확히 이거.

각 n = `Lens.leaves.equiv` 의 한 equivalence class.

### 3.3 다른 number system 으로의 확장 — 같은 패턴

- **ℤ**: chain 의 양방향 확장.  Raw.swap 이 (-1) multiplier.  `signedLens = ⟨1, -1, +⟩`.
- **ℚ⁺**: 두 chain 의 쌍 (분자/분모), ratio quotient.  `Tower/NatPairToQPos`.
- **ℝ**: ℚ chain 의 Cauchy sequence (chain 의 sequence).  `Lib/Math/Real213/Cauchy/*`.

각 단계: 이전 단계의 chain 을 한 차원 묶음.  **재귀적 chain cascade**.

### 3.4 실용적 결과

완전 syntactic 분해 없이도 ℕ, ℤ, ℚ, ℝ 다 emergent.  
"숫자가 자연스레 나오는 패스만 잡으면 실용적 수학 연구 가능" — 정확히 맞음.

Codebase 에 *이미 partial 실현*:
- `Nat213.Raw.numeral, succ, add, mul` (Method A chain + 산술)
- `Int213.Raw` (signedLens + Raw.swap negation + factoring)
- `Tower/NatPairToQPos, NatPairToInt, NatTripleToZ2` (chain pair 들)
- `Lib/Math/Real213/Cauchy/*` (Cauchy sequence)

단 framing 이 "natural emergence" 가 아니라 "ad-hoc Lean construction" 처럼 짜여 있음.

---

## 4. 현재 codebase 상태 — emergence 시각에서 재평가

### 4.1 Lens-strict (✓ — 잘 됨)

| 파일 | 평가 |
|---|---|
| `Lens/LensCore.lean` | core framework, 정의 깔끔 |
| `Lens/Number/Int213/Raw.lean` (post-3371fd14) | signedLens, pairLens, factoring — lens-strict |
| `Lens/Number/Nat213/Core.lean` (post-ced56bef) | `Nat213 := {n // 1 ≤ n}` + Lens.leaves view |

### 4.2 Ad-hoc / chart-imposed (⚠ — 재고려 필요)

| 파일 | 문제 |
|---|---|
| `Lens/Number/Nat213/Raw.lean` | `add, mul, numeral, succ, addAux, mulAux` 가 Tree 패턴 매치로 직접 정의 — Lens 우회.  `value : Raw → Nat := Raw.fold 1 1 (·+·)` 가 `Lens.leaves.view` 와 중복. |
| `Lens/Number/Nat213/Peano.lean` | `inductive Nat213 \| one \| succ` — Raw 와 평행한 별도 inductive type. Lens-derived 아님. |
| `Lens/Number/Nat213/Bridge.lean` | Peano ↔ Raw 동형.  Peano 가 lens-derived 가 아니라서 이 bridge 자체가 ad-hoc. |
| `Lens/Number/Nat213/NumberingSystem.lean` | Method A 외 다른 numbering 패턴.  chart-relativity 의미 명시 안 됨. |

### 4.3 Type 차원 정합성

현재:
- `Lens.leaves : Lens Nat` (LensCore)
- `Nat213.Raw.value : Raw → Nat`  (= Lens.leaves.view 의 중복)
- `Nat213.Peano.Nat213 : Type`  (별도 inductive type)
- `Nat213.Core.Nat213 : Type := {n // 1 ≤ n}`  (방금 만든 것, Lens-image subtype)
- `Nat213.Peano.toNat : Peano.Nat213 → Nat`  (또 다른 view)

→ "Nat213" 이 4-5 가지 의미로 흩어짐.  정합성 필요.

---

## 5. 옵션 정리 — 어디로 갈 것인가

### Option A: Lightweight reframing (코드 변경 없음)

- `Nat213/Raw.lean` 등의 docstring 에 "이건 distinction iteration 의 chain 표현; Lens.leaves 의 emergent path" 명시.
- `seed/AXIOM/` 에 새 문서 — chart-relativity, flat ontology, syntactic internalization.
- Code 안 건드림; framing 만 정렬.

**장점**: zero risk, 가장 가벼움.
**단점**: 코드 자체의 chart-imposed 느낌은 그대로.

### Option B: Predicate-based Raw subtype

- `IsMethodAChain : Raw → Prop` 정의 (= "이 Raw 는 chain 의 한 원소이다")
- `Nat213.Chain := { r : Raw // IsMethodAChain r }` 새 subtype
- 산술이 Chain subtype 위에서 closed
- 기존 `Nat213.Raw.{add, mul, ...}` 는 유지하되 deprecated, 또는 chain 형으로 재정의

**장점**: Raw-native, 산술이 Raw 위에서 닫힘.
**단점**: 새 layer 추가, 기존 코드와 병행.

### Option C: Full lens-strict refactor (Phase 1 시작됨)

- `Nat213.Raw.lean` 의 ad-hoc 산술 삭제 (`add, mul, numeral, succ, addAux, mulAux` 등)
- 모든 산술을 codomain (`Nat`) 에서; Raw 측은 `value` 와 lens 정리들만
- `Nat213.Peano.lean` 삭제 (또는 ergonomic parallel 로 격리)
- Bridge.lean 재작성, Tower 파일들 갱신, 하위 Lib/Physics 점검

**장점**: 최대 정합성, lens-strict.
**단점**: multi-file refactor (9+ 파일), 큰 작업량.

### Option D: Chart-explicit framework

- `Nat213.Raw` 의 `one`, `succ` 가 *임의 chart 선택* 임을 expose
- `Nat213.RawFromChart (r₀ r' : Raw) (h : r₀ ≠ r')` 같은 parameterized 정의
- 다른 chart 도 valid 임을 정리 (chart-invariance theorem)
- 현재 `Raw.a`, `Raw.b` 는 default chart

**장점**: 철학과 코드 정확히 일치, chart-relativity 명시.
**단점**: 가장 큼, downstream 전체 affected.

### Option E: Internal congruence (algebraic equations)

- Raw 위에 inductive `Eqv : Raw → Raw → Prop` — generator equation 들을 inductive 로 박음
- Quotient 안 취하고 Eqv 자체로 동치 표현 (∅-axiom 유지)
- 각 lens 의 의미 = 특정 generator 집합으로 결정

**장점**: internal 표현, 가장 axiom-pure.
**단점**: 새 abstraction layer, 모든 lens 정리 재증명.

---

## 6. 열린 질문 — 결정 전 검토

1. **어느 옵션 (A-E)?**  단일? 혼합?  추천: **A + B + Phase 1 (C) 의 보존** 이 가장 균형.

2. **`Nat213` 의 표준 정의는?**
   - `{n : Nat // 1 ≤ n}` (Nat subtype, 현재 Phase 1)
   - `{r : Raw // IsMethodAChain r}` (Raw subtype)
   - 두 개 다 (iso 로 연결)

3. **ℕ vs ℕ₊?**
   - 현재 Lens.leaves 는 ℕ₊ 강제
   - Slash-count lens (`⟨0, 0, fun a b => a+b+1⟩`) 는 ℕ (0 포함)
   - 어느 게 "기본"? 둘 다 노출?

4. **Method A chain 의 canonicality?**
   - 단일 canonical chain? 아니면 atlas of chains?
   - "어떤 chart 든 valid" 임을 정리로 박을 것인가?

5. **Peano.lean 의 status?**
   - 삭제? Lens-derived 와의 동형 증명만 유지?
   - "Ergonomic parallel" 로 명시 + Lens.leaves bridge?

6. **Syntactic internalization — 어디까지?**
   - L1 (referent Gödel) 만: 현재 codebase
   - L2 (glyph → Raw mapping): minimal prototype 가능
   - L3+ (full meta-circular): 큰 project

7. **Flat ontology — Lean 으로 표현?**
   - `Set Raw`, `Set (Raw × Raw)` — propext / classical 의존
   - `Raw → Bool` (decidable predicate) — ∅-axiom
   - 어디까지 가야 충분?

---

## 7. 추천 — 균형잡힌 진로

가장 균형잡힌 path 제안 (수정 가능):

### Step 1 (단기, 가벼움):

- 이 문서 (`research-notes/2026-05-18_lens_emergence_path.md`) 를 commit
- `seed/AXIOM/` 에 한 페이지 — *"chart-freeness + flat ontology + syntactic internalization"* 의 단상 (08 번?)
- `Nat213/Raw.lean`, `Nat213/Peano.lean` 의 docstring 에 한 두 줄 — *"이건 emergence path 의 한 representation; chart-local"* 명시
- 코드 변경 0

### Step 2 (중기, 안전한 추가):

- Option B: `IsMethodAChain : Raw → Prop` 정의 + `Nat213.Chain` subtype 노출
- 기존 `Nat213.Raw.{add, mul, numeral, succ}` 는 그대로 둠 (deprecated 안 함)
- Chain subtype 위의 산술 정리 추가 (closed-Raw)
- 새 emergent framing 코드로도 가시화 — 기존 깨지 않음

### Step 3 (장기, 큰 정리):

- Phase 1 (Nat213/Core.lean) 을 시작으로 Phase 2-7 진행 (Option C 의 full path)
- Multi-file refactor; downstream 까지 정합
- 단 *Step 2 이후* 충분한 reflection 후 결정

### Step 0 (이 문서의 자기 반영):

이 문서 자체는 chart 의 한 chart — 우리가 본 시각.  몇 달 뒤 다시 읽으면 추가 통찰 있을 수 있음.  단상으로 두는 가치.

---

## 8. 핵심 통찰 한 줄 요약

> 213 axiom 의 minimum (Raw + slash) 에서 시작해, *어떻게 묶을 것인가* (= 어떤 lens / chart 를 선택할 것인가) 의 선택으로 모든 derived structure 가 emergent.  숫자 (ℕ, ℤ, ℚ, ℝ) 는 chain iteration cascade — distinction 의 자기 반복.  현재 codebase 는 그 cascade 의 한 chart 의 한 representation 의 한 Lean 표현; 본질이 아닌 chart artifact 가 일부 섞여 있을 뿐.  Lens framework 의 본 의미를 살리면, 모든 게 자기지칭 cascade 안에서 닫힘.

---

## 9. 다음 action — 이 문서를 commit 할까

이 문서 자체를 첫 step 으로 commit 하고, 위 Step 1 의 다른 action (seed 단상, docstring 한 두 줄) 부터 진행하는 게 가장 가벼운 시작.

또는 이 문서를 working notes 로만 두고 commit 안 하기.

결정은 user.
