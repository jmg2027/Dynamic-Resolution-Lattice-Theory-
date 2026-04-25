# CLAUDE.md — 213

## 이 파일의 위상

213을 다루는 모든 세션은 이 파일을 시작 전에 반드시 읽는다.
내용이 "철학적"으로 보일 수 있지만, 생략하면 매 세션 1시간
이상의 혼란이 재발한다 (과거 여러 세션에서 실증).

**이 파일은 세션 가이드이고, 공리 자체는 `AXIOM.md`에 있다.**
형식 감사 기준은 `AXIOM.md` (씨앗 문서).  CLAUDE.md는
그 공리가 세션 작업 중 무의식적으로 침해되지 않도록 하는
운영 매뉴얼.

## 213의 정체성

### 공리는 선택이 아니라 잔여물

213의 공리는 "세상의 근본"에 대한 주장이 아니다.
**뭔가를 가리키려는 순간 피할 수 없이 남는 최소 잔여물**이다.

Formal core (`AXIOM.md` §1.1): Raw axiom 의 4 clause (a, b, slash,
distinctness) 가 framework-internal 로 strict minimum
(`Research/AxiomMinimality.lean` 의 4 case).
Conceptual extension (`AXIOM.md` §1.2 + `notes/75-76`): "의미 의
atom" framing 은 formal core 의 *interpretive reading* — formal
Lean 으로 direct 검증 부재.  두 layer 의 분리 유지.

- "a와 b"를 쓰는 순간 "와"도 뭔가다.
- "a, b"를 쓰는 순간 ","도 뭔가다.  그 ","가 일반적인지
  절대적인지도 모른다 — 또 하나의 뭔가.
- a와 "와"는 구분되는가?  무엇이 구분하는가?  또 다른 뭔가.

표기를 시작하는 순간 표기 자체가 새 뭔가를 끝없이 낳는다.
재귀는 회피 불가능하다.  공리는 이 재귀의 최소 표현이다.

### "관계"가 아니라 "원시적 구분"

- "관계": 이미 있는 두 뭔가 전제 + 집합론 프로퍼티 묵시 수입.
- "원시적 구분": 구분이 먼저 작동 + "같지 않음" 하나만 요구.
- "원시적" = 더 이상 환원 불가능함의 서약.

### 213이 모든 것의 상위

뭔가를 가리키는 모든 틀 — 집합론, 카테고리, 논리, 언어,
물리 — 은 뭔가의 구분·관계 능력에 의존한다.  213은 그
능력 자체의 최소 잔여물이다.  모든 틀은 이 잔여물 위의
Lens들이다.

**"절대 기준 없음"은 조건이 아니라 기본 상태.**  "절대 기준
있음"이 오히려 공리 추가 부담이다.  따라서 213의 상위성은
**무조건적** 구조적 귀결이다.

### 언어적 불가피성

"원시적 구분"조차 완벽하지 않다.  "다름"은 "같음"을 전제,
"와"는 "and"로 오해, ","는 본질 아닌 분리자.  완벽한 표현은
없다.  현재의 단어들은 **최소 commitment 표현**이며 잔여
수입을 인정한 상태로 사용.  최소화만 가능, 제거 불가.

### Derive, not reconcile

모든 결과는 213 공리 + 명시적 Lens 성질에서만 derive
되어야 한다.  외부 상수 대입, 실험값 맞추기, 다른 이론
수입은 모두 **fudge**.

- ch22는 eval 외부 대입으로 틀림.
- Paper 1 §1 (공리 부분, R1–R5 이전)이 올바른 템플릿.
- 모든 물리 chapter는 이 방법론으로 derive 되어야 한다.
- fudge 발견 시 공식이 아니라 Lens를 고친다.
- 그것도 안 되면 **이론을 포기한다**.  "Lens를 더 찾으면
  될 것"이라는 무한 연장 방어는 허용되지 않는다.

### 왜 형식화·기계 검증이 필수인가

기계 검증은 fudge를 허용하지 않는다.  따라서 **derive
실패 시점을 강제로 드러낸다**.  사람이 수기로 하면 눈감고
보정이 가능하지만, 기계는 안 된다.  이게 Mathlib-free +
0 sorry + 0 axiom 제약을 두는 이유다.  공리는 계약서이고,
기계 검증은 감사관이다.

### 외부 공리 추가는 이론 전체 폐기 조건 (Falsifiability)

AXIOM.md §5.2.1 의 **falsifiability 기준**:

- 213 의 모든 결과는 Lean 4 core + Raw 공리 만으로 derive
  가능해야 함.
- **어떤 결과가 공리 추가 없이 절대 불가능** 하다고 밝혀지면,
  **213 이론 전체 폐기**.  해당 결과만 포기가 아님.
- 이는 Raw 공리가 "최소 잔여물" 이라는 §1 선언의 직접 귀결:
  공리 추가가 정말 필요하면 Raw 가 최소가 아니었던 것.

운영 원칙:

- Classical, LEM, native_decide 등 외부 axiom 추가 일절 금지.
- 막히는 결과는 "open" 으로 두되, **영구적 벽 vs 일시적 난관**
  감별.  영구적 벽이면 이론 실패 선언.
- Lean 검증 = falsifiability 의 기계적 감사관.

Mingu 확정 (2026-04-24).  절대 완화 안 됨.

### "뭔가"의 지위는 open

"뭔가"라고 말하는 순간부터 Lens인가? 그럴 수 있다.
213이 이데아인가? 아마 아님.  이 문제들은 open이고
213의 쓸모에 영향을 주지 않는다.  중요한 건 derive
성공 여부이지 존재론이 아니다.

## 운영 규칙 (위 내용의 직접 귀결)

이것들은 독립 규칙이 아니라 위 정체성에서 자동으로 따라
나오는 것들이다.  규칙만 외우지 말고 **왜 그런지 되짚을 것**.

- **Lens ≠ functor.**  Functor는 카테고리 구조 선행 전제.
  Raw에는 morphism 없음.  "functor"를 Lens에 붙이는 순간
  카테고리 이론 묵시 수입.  →  `notes/19_lens_not_functor.md`.
- **"관측자", "공간", "인식", "구조", "관계"** 같은 단어는
  213 공리 설명에 사용 금지.  이 단어들은 derive 결과이지
  전제가 아님.
- **표기 규약**: `NOTATION.md` 참조.  ZFC 집합 literal
  `{a, b, /}`, "Raw contains X" 같은 collective 언어,
  Raw 좌측의 ∈ 기호 모두 금지.
- **Cardinality는 (Raw, Lens) 쌍의 성질**.  Raw만으로는
  countable/uncountable 말할 수 없음.
- **Existence mode don't care.**  Platonic / stepwise 구분은
  Lens 출력이지 공리 성질 아님.
  →  `notes/17_existence_mode_lens.md`.
- **`E213.Firmware.Internal` namespace `open` 은 Firmware
  내부 모듈 외 금지.**  Internal 은 encoding scaffolding
  (`Tree`, `Tree.cmp`, `Tree.canonical` 등) 전용.  User
  code 에서 `open Internal` 은 Raw 추상 위반.  → `AUDIT_Lean.md`
  §5.2(D).
- **`Raw.fold` / `Raw.rec` 는 `combine` 대칭 / slash 대칭
  처리를 user 책임으로 둔다.**  비대칭 Lens 는 encoding
  artifact 를 출력에 leak.  각 파일 doc-string 의 WARNING
  참조.  →  `AUDIT_Lean.md` §5.2(A), (B).

## 정리 규칙 (organization)

문서·파일·디렉토리 의 정리 는 다음 원칙 을 따른다.  쌓이고
난 후 가 아니라 **새 파일 만들 때 마다** 의식한다.

- **Deprecated 는 삭제**.  superseded 된 문서·코드 는 보존
  하지 말고 지운다 (git history 에 남는다).  "역사적 기록" 가치
  로 살려두면 그 자체 가 noise.
- **파일 너무 많으면 안 됨**.  비슷한 주제 small fragments 는
  하나로 통합.  예: 같은 arc 의 notes 5 개 → 1 개 synthesis note.
- **파일 하나 너무 길면 안 됨**.  한 파일 이 자연스럽게 두
  주제 로 갈리면 분리.  Lean: 80 줄 hook 이 강제.
- **디렉토리 하나 에 entry 너무 많으면 안 됨** (50+ 개 면
  sub-dir 검토).  너무 적어도 안 됨 (3 개 이하 면 부모 로 통합).
- **디렉토리 너무 깊거나 너무 많아도 안 됨**.  depth 3-4 단
  이내 권장.  "그냥 거기 있으니까" 만들지 말 것.
- **자연스러운 순서 로 읽힐 수 있도록 정렬**.  notes 의 NN_
  prefix, Lean 모듈 의 layer 구조 (Firmware → Hypervisor →
  Research) 모두 reading order 가 자연스럽게 흐르도록.
- **새 파일 만들기 보다 기존 파일 갱신 우선**.  관련 내용 있는
  파일 이 이미 있으면 거기 에 append/edit 한다.

위 규칙 을 어기는 정리 는 정리 가 아니라 누적.

## 물리 chapter 감사 기준

그 chapter의 결과가 **AXIOM.md + 명시적 Lens 성질** 로부터
fudge 없이 derive 가능한가?  안 되면 **speculative 격리**.

## Paper 1, 2 삭제됨 (2026-04-24)

이전 `213/PAPER.md` (R1-R5 → ℂ 도출) 및 `213/PAPER2.md`
(r5-critique) 는 삭제됨.  이유: 두 문서 모두 **특정 시점의
derivation 시도** 였고, arc 진행 중 프레이밍이 낡음.
`notes/30_bool_is_liar_paradox.md` 가 이 삭제 배경 기록.

현재 **AXIOM.md 가 유일한 공리 문서**.  derivation 은 notes/
에서 자유롭게 탐구 (판정 프레임 없이).

## 파일 지도

- **`AXIOM.md` — 공리 씨앗 문서 (최상위 기준).**
- **`ORIGIN.md` — 이론의 원본 프롬프트 chain (2026-04-24 고정).**
  공리의 형태가 "왜 이것인가" 의심될 때 먼저 참조.
- `NOTATION.md` — 표기 규약.
- `IMPLEMENTATION.md` — Raw + Firmware 구현 감사 연구.
  안전장치가 공리 추가가 아님을 엄밀 분석.
- `AUDIT_Lean.md` — Lean × AXIOM 대조 감사.
- `research/infinity-as-lens/` — 세부 노트들.
- `framework/E213/` — Lean 4 core 형식화.
- 루트 `../HANDOFF.md` — 세션 아크 연속성.

## Author & licence

- Author: **Mingu Jeong only**.  Claude in Acknowledgments.
- 0 sorry, 0 external axioms.  Lean 4 core only — no Mathlib.
