# AUDIT_Lean.md — Lean framework × AXIOM.md 대조

**감사 대상**: `framework/E213/Firmware/`
**기준 문서**: `AXIOM.md` (2026-04-24)
**감사일**: 2026-04-24
**전체 판정**: **충실 (Faithful)**.  구조적 수정 불필요.
소소한 sanding 3건 권고.

---

## §1. 공리 4조 대조

### 공리 1: "뭔가가 있다.  최소 둘.  a, b.  원시적 구분."

Lean 구현 (`Firmware/Raw/Core.lean`):
- `Raw.a : Raw := ⟨.a, rfl⟩` (line 60)
- `Raw.b : Raw := ⟨.b, rfl⟩` (line 61)
- `DecidableEq Raw` 인스턴스 제공 → "같지 않음" 판정 가능.

**판정**: ✓ 일치.

### 공리 2: "두 뭔가의 페어링은 또 하나의 뭔가."

Lean 구현 (`Firmware/Raw/Slash.lean`):
- `Raw.slash (x y : Raw) (h : x ≠ y) : Raw` (line 20)
- 결과는 다시 Raw — 닫힘.

**판정**: ✓ 일치.

### 공리 3: "페어링은 대칭."

Lean 구현 (`Firmware/Raw/Slash.lean`):
- `Raw.slash_comm : Raw.slash x y h = Raw.slash y x (Ne.symm h)`
  (line 31)

**판정**: ✓ 일치.

### 공리 4: "자기 자신과의 페어링은 없음."

Lean 구현:
- `Raw.slash` 의 시그니처에 `h : x ≠ y` 가 필수 인자.
  → x = y 일 때 호출 자체 불가능.
- `x ≠ y` 는 Lean 타입 시스템이 정적으로 강제.

**판정**: ✓ 일치.

---

## §2. "공리에 없는 것" 점검

### 크기 / 카디널리티 / 유한성 / 무한성

Firmware 자체에는 크기 개념 없음.  `leaves`, `depth` 정의가
있으나 이들은 `Raw.fold` 를 통한 **관측 결과**이지 공리가
아님.  `Infinity/` 모듈도 별도 폴더 (Firmware 밖).

**판정**: ✓ 준수.

### 순서 / 위계 / 서열

**주의 지점 (A)**.  Internal namespace에 `Tree.cmp` 가 있다
(`Firmware/Raw/Core.lean:23–36`).  이는 canonical form 선택을
위한 **encoding 장치**이지 Raw의 성질이 아니다.  PAPER.md
§1.2 에서 이미 *"the ordering is the encoding's selection
function, not a property of the axiom"* 로 명시됨.

그러나 AXIOM.md 에는 이 점이 명시되어 있지 않다.
→ **권고 1**: AXIOM.md §7.1 에 "Lean encoding은 primitive
quotient 부재로 인해 canonical form을 쓰며, 이 때 사용되는
ordering은 공리가 아닌 encoding artifact" 를 명시.

**판정**: △ 일치하지만 AXIOM.md 갱신 필요.

### 집합 / 원소 / 멤버십

Lean 4 core 의 `inductive Tree` 는 ZFC 집합이 아님 (type
theory).  `RawLevels.lean` 의 `List Raw` 는 Lens-level
enumeration 이며 Firmware 외부 수준이라도 수용.

**판정**: ✓ 준수.

### 관측자 / 공간 / 인식 / 구조 / 기하

Firmware 자체에 없음.  Hypervisor 의 `Lens` 가 별도 모듈.

**판정**: ✓ 준수.

### 존재 양식

Lean `inductive` 는 정의상 Platonic / stepwise 어느 해석과도
양립.  `Infinity/` 의 `notes/17_existence_mode_lens.md` 참조.

**판정**: ✓ 준수.

### 연산의 결합·분배·항등원·역원

`Raw.slash` 는 대칭성 (공리 3) 과 반사 불허 (공리 4) 만
보장.  결합·분배 등 **없음**.  있다면 Lens-level (e.g.
Research/LipschitzLens).

**판정**: ✓ 준수.

---

## §3. 공리 **외**의 Firmware 내용

AXIOM.md 가 금지하지 않지만, 공리 외의 utility 가 Firmware 에
있는 것들 — 검토 필요.

### Raw.fold (catamorphism)

위치: `Firmware/Raw/Fold.lean`.  이는 inductive type의
표준 eliminator의 wrapper 이며 특정 Lens가 아닌 **모든 Lens
를 만드는 도구**.  Consumer utility 로 분류.

**판정**: ✓ 수용.  Firmware 위치 OK.

### Raw.swap (automorphism)

위치: `Firmware/Raw/Swap.lean`.  Swap은 공리 1 ("a, b 는 같지
않음 외의 어떤 관계도 없음") 로부터 직접 **도출**되는 사실
 — a ↔ b 교환이 자동으로 automorphism 이 됨.  즉 첫 번째
derivation.

**주의 지점 (B)**.  "공리 1의 자동 도출" 임이 AXIOM.md에서
명시되지 않음.  Paper 1 §2 (Symmetry of Raw) 에 있지만
AXIOM.md 에 크로스 레퍼런스 필요.
→ **권고 2**: AXIOM.md §5 또는 §7.2 에 "Raw.swap 은 공리 1
로부터의 첫 derivation" 명시.

**판정**: △ 수용하지만 AXIOM.md 보강 필요.

### Raw.depth, Raw.leaves

위치: `Firmware/Raw/Slash.lean:52`, `Firmware/Raw/Levels.lean`.

**주의 지점 (C)**.  `depth`, `leaves` 는 특정 Lens (Lens.depth,
Lens.leaves) 의 observable 이다.  이들이 Firmware 에 `Raw.depth`,
`Raw.leaves` 로 노출된 건 **Lens-layer bleed**.

AXIOM.md §3.3 은 "크기 / 카디널리티" 를 공리에서 제외.
`Raw.leaves r` 는 **그 Raw 의 특정 Lens 관측 결과** 이므로
공리 차원에 두어선 안 됨.  현재 위치는 엄밀 말해 잘못.

다만 실용적으로:
- Internal `Tree.depth`, `Tree.leaves` 는 canonicality 관련
  불변량 증명에 쓰임 — Internal 보존 필요.
- Public `Raw.depth`, `Raw.leaves` 는 Hypervisor 로 **이전**
  되어야.

→ **권고 3**: `Raw.depth`, `Raw.leaves` 의 public 선언을
Hypervisor 층으로 이동.  Internal 선언은 canonicality 증명에
필요하므로 유지.

**판정**: ✗ Lens-layer bleed.  이전 필요.

### Raw.fold_eq_depth / fold_eq_leaves / fold_signed_swap / fold_swap_hom

위치: `Firmware/Raw/Signed.lean`, `Firmware/Raw/Hom.lean`.

이들은 "Raw.fold 로 특정 Lens 를 재구성했을 때의 bridge
정리"들.  **Lens-level 정리**이며 Hypervisor 또는 Meta 에
속함.

→ 권고 3 과 함께 이전.

**판정**: ✗ Lens-layer bleed.  이전 필요.

---

## §4. 전체 판정

**Lean framework 는 AXIOM.md 공리의 충실한 구현이다.**
구조적 재작성은 필요하지 않음.  첫 2주간의 작업 (78 모듈,
457 정리, 0 sorry, 0 axiom) 은 axiom 갱신 없이 유지 가능.

### 권고 3건 (우선순위 순)

1. **AXIOM.md §7.1 보강** — Lean encoding 에서의 canonical
   form / Tree.cmp 는 encoding artifact 이지 공리가 아님을
   명시.  (5분 작업.)

2. **AXIOM.md §5 또는 §7 보강** — Raw.swap 은 공리 1 의
   첫 derivation 임을 명시.  (5분 작업.)

3. **Lens-layer bleed 이전** — `Raw.depth`, `Raw.leaves`,
   `Raw.fold_eq_*`, `Raw.fold_signed_swap`, `Raw.fold_swap_hom`
   의 public 선언을 Hypervisor 또는 Meta 로 이동.  Internal
   `Tree.*` 는 유지.  (1 세션 작업.  `import` 연쇄 수정
   필요.)

권고 1, 2 는 AXIOM.md 문서 갱신.  권고 3 은 Lean refactor
이며 `lake build` 재실행 필요.

### 무엇을 **하지 않아야** 하는지

- **공리 자체의 형태를 바꾸지 말 것.**  현재 `Raw.a`, `Raw.b`,
  `Raw.slash (h : x ≠ y)`, `Raw.slash_comm` 은 AXIOM.md §3.2
  의 1:1 번역이다.  이 형태를 ch22 의 3원소·2연산 형태로
  "업그레이드" 해서는 안 된다 (ch22 는 별개 fudge 문제).

- **78 모듈 457 정리를 버리지 말 것.**  권고 3 의 이동 작업
  이후 대부분은 그대로 유지.  증명 내용 자체는 변경 불필요.

### 다음 단계 (Step 3 이후)

- Step 3: PAPER.md §1 을 AXIOM.md 로 대체.  §2-§4 (R1-R5 + ℂ)
  를 별도 논문으로 분리.
- Step 4: `book/AUDIT.md` — ch01-ch21 감사.

---

## 변경 이력

- 2026-04-24: 최초 감사.  Session
  `claude/lean-infinity-explanation-QqnSp`.

## Author

- Audit by: Claude (Anthropic), under Mingu Jeong's direction.

---

## §5. 심층 감사: Corner cases / 안전장치 (2차, 2026-04-24)

1차 감사는 공리 대조에 집중했다.  2차는 **"encoding artifact
가 Lens 출력으로 새어 나갈 수 있는가?"** 를 본다.

Raw 는 quotient 로서 `Tree.cmp` 선택에 무관한 추상 대상이지만,
Lean 구현은 canonical form 을 쓰므로 user code 가 실수로
cmp 에 의존하면 그 Lens 는 **encoding artifact** 를 물고
들어가게 된다.

### §5.1 이미 있는 안전장치 (pass)

| 장치 | 위치 | 효과 |
|------|------|------|
| `h : x ≠ y` 강제 인자 | `Raw.slash` 시그니처 | 반사 금지 정적 강제 |
| `Raw.slash_comm` 정리 | Slash.lean | 대칭성 공식 증명 |
| `fold_slash` 의 `hsym` 전제 | Fold.lean | 대칭 combine 에서만 axiom 부합 결과 |
| `fold_swap_hom` 의 4 전제 | Hom.lean | 대칭+distributive 에서만 conj 하향식 부합 |
| `Internal` namespace 분리 | Core.lean | `open E213.Firmware` 로는 Tree 노출 안 됨 |
| Mathlib-free + 0 sorry | 프로젝트 규약 | 외부 공리 수입 차단 |
| `@[elab_as_elim] Raw.rec` | Rec.lean | `induction` tactic 이 Raw 층 eliminator 강제 |

이들은 실제로 작동한다.  Canonical form 의 **존재** 가 Lens
출력을 오염시키는 시나리오는 이 장치들로 대체로 차단됨.

### §5.2 미비한 안전장치 (issues)

#### (A) **`Raw.fold` 에 combine 대칭성 요구 없음** — HIGH

`Raw.fold ba bb combine r` 는 `combine` 이 **비대칭이어도**
타입이 맞는다.  그런 `combine` 으로 `Raw.fold` 를 쓰면
결과는 Tree 의 canonical ordering (= cmp 선택) 에 의존한다.
이는 공리에 없는 것 (encoding artifact) 이 Lens 출력에
새어 들어가는 **silent leak**.

`fold_slash` 가 대칭성을 전제로 요구하지만, 이건 정리일 뿐
`Raw.fold` 자체 호출은 막지 못한다.  user 가 비대칭 combine
으로 Lens 를 만들면 아무 경고 없이 작동하고, 그 결과는
공리에 비해 overcommitted.

**권고 A**: `Raw.fold` 의 doc-string 에 경고 추가.  또는
장기적으로 `Lens.valid` 술어 도입 (combine 대칭을 type-level
로 강제).

#### (B) **`Raw.rec` 의 `slash x y h` 순서** — HIGH

`Raw.rec` 의 slash 분기는 user 에게 `(x, y)` 순서쌍을 건넨다.
이 순서는 canonical form 에서 유래 — 즉 `cmp x y = .lt`.

User 가 `slash` 분기에서 **x 와 y 를 비대칭 처리** 하면
(예: `f x + 2 * g y`), 그 결과는 cmp 선택에 의존한다.
다시 silent leak.

**권고 B**: `Raw.rec` doc-string 에 "slash 분기는 x, y 를
대칭적으로 다루어야 한다; 그렇지 않으면 결과가 encoding
artifact 에 의존" 경고.  또는 `Raw.rec_sym` 같은 대체 버전
을 만들어 motive 가 swap-불변임을 요구.

#### (C) **`Subtype.val` 접근** — LOW

`r.val` 을 쓰면 underlying Tree 가 보인다.  실무적으로는
모든 Raw 가 canonical 이므로 `.val` 은 "유일 대표" 이고
leak 이 크지 않다.  단, `.val` 을 Lens semantics 에 쓰면
(예: `r.val.depth` 대신 `Lens.depth.view r`) 가능.

**권고 C**: `NOTATION.md` 에 "`.val` 접근은 encoding 층
내부 전용; Lens semantics 에 쓰지 말 것" 추가.

#### (D) **`open E213.Firmware.Internal` 의 관례 의존성** — MEDIUM

Lean 4 core 에는 strict visibility control 이 없다 (module
system 이 아님).  User 가 임의 모듈에서 `open E213.Firmware.
Internal` 하면 Tree 에 직접 접근 가능.

**권고 D**: `CLAUDE.md` DO-NOT 에 "`E213.Firmware.Internal`
의 `open` 은 Firmware 내부 모듈 외에 금지" 명시.  또는
CI 에 grep 규칙 추가.

#### (E) **`ValidLens` 술어 / 구조 부재** — MEDIUM (future)

현재 `Lens` 는 `⟨base_a, base_b, combine⟩` 만 요구.  combine
대칭성 / base 대칭성 / R1-R5 만족도 등이 Lens 정의 시점에
검증되지 않는다.

**권고 E**: `Hypervisor/Lens.lean` 에 `ValidLens` 술어 도입.
최소한 combine 대칭을 field 로.  모든 Lens 선언이 validity
증명을 동반하게.  (별도 세션 1회 분량.)

### §5.3 Corner cases가 **아닌** 것들 (이미 방어됨)

- **비 canonical Tree 를 Raw 로 위장**: subtype 이 `canonical
  = true` 증명 요구.  `decide` 없이는 통과 불가.  OK.
- **`Tree.slash x x` 같은 반사형**: canonical false 이므로 Raw
  에 못 들어감.  OK.
- **서로 다른 canonical proof 가 같은 Raw 로 인식**: Lean 의
  Subtype.ext 가 proof-irrelevance 로 처리.  OK.
- **무한 깊이 Raw**: inductive type 은 well-founded — 모든
  구체 Raw 는 유한 깊이.  axiom 과 부합.  OK.
- **`Tree.a ≠ Tree.b` 가 공리에서 도출 안 됨**: Lean inductive
  type 의 no-confusion 원리로 자동.  axiom 1 (원시적 구분) 의
  자연스러운 기계 표현.  OK.

### §5.4 조치 우선순위

| # | 권고 | 난이도 | 영향 |
|---|------|--------|------|
| A | Raw.fold doc 에 대칭 요구 경고 | 5분 | HIGH |
| B | Raw.rec doc 에 대칭 요구 경고 | 5분 | HIGH |
| D | CLAUDE.md 에 Internal open 금지 추가 | 5분 | MEDIUM |
| C | NOTATION.md 에 `.val` 금지 추가 | 5분 | LOW |
| 3 (§3) | Lens-layer bleed 이전 | 1 세션 | MEDIUM |
| E | ValidLens 술어 도입 | 1 세션 | MEDIUM (future) |

A, B, C, D 는 doc 추가로 당장 적용 가능.  3, E 는 코드 수정
필요로 별도 세션.

---

## §6. 전체 재판정 (심층 감사 반영)

**여전히 Faithful, 단 silent leak 경로 2건 존재**.

1차 감사의 결론 (공리 4조 충실, "없는 것" 목록 준수) 은 유지.
2차 감사는 이에 더해 **Lens 출력이 encoding artifact 에
silent 하게 의존할 수 있는 API 표면** 2건을 발견 (Raw.fold,
Raw.rec).  doc-level 경고로 mitigate 가능.  장기로는 ValidLens
술어로 type-level 강제 권장.

78 모듈 457 정리의 구조적 정합성은 영향 없음.  기존 Lens
들 (Lens.depth, Lens.leaves, signedLens 등) 은 모두 **대칭
combine 사용** 으로 이미 leak 없음 — 검증 완료 (Fold.lean 의
`fold_slash` 증명이 그들의 대칭성을 사용함).

**취약점은 미래 사용자가 비대칭 Lens 를 만들 때만 발현.**
doc 경고로 충분히 방지 가능.
