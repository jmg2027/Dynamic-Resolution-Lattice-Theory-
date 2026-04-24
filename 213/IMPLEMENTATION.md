# IMPLEMENTATION.md — Raw + Firmware 구현 감사 연구

## Abstract

이 문서는 `framework/E213/Firmware/` 에 구현된 Raw 프레임워크가
`AXIOM.md` 공리의 **충실한 emulator** 임을 구조적으로 입증한다.
구체적으로:

1. Lean 4 core 의 구현 장치 (inductive type, subtype, canonical
   form, smart constructor, custom eliminator) 각각이 공리 추가
   인지 encoding artifact 인지 derivation 인지 분류.

2. 안전장치 (type gate, 정리 전제, doc 경고, namespace 규약)
   각각이 **수학적 commitment 를 추가하는지** 분석.

   **결론: 추가 commitment 는 없다.**  안전장치는 다음 중
   하나에 속한다:
   - (i) 공리 clause 의 type-level 재표현,
   - (ii) 정리의 조건부 전제 (정리 자체가 조건부),
   - (iii) meta-syntactic hygiene (인간의 오용 방지).

3. Encoding artifact 가 Lens 출력에 leak 될 수 있는 API 표면
   (Raw.fold, Raw.rec) 분석과 현재 mitigation 상태.

관련 문서: `AXIOM.md`, `AUDIT_Lean.md`.

---

## §1. 문제 진술

`AXIOM.md` 공리는 4개 clause 로 이루어진다 (§3.2).  Lean 4 core
에는 primitive quotient 가 없으므로, 이 공리를 기계에 태우는
과정에서 여러 구현 장치가 도입된다:

- `inductive Tree | a | b | slash (x y : Tree)` — 순서 있는
  자유 magma.
- `Tree.cmp : Tree → Tree → Ordering` — 전순서, canonical form
  선택자.
- `Tree.canonical : Tree → Bool` — 정규형 predicate.
- `Raw : Type := { t : Tree // t.canonical = true }` — subtype.
- `Raw.slash (x y : Raw) (h : x ≠ y) : Raw` — smart constructor
  (자동 canonicalize).

각 장치에 대해 다음을 판정해야 한다:

(α) **공리의 type-level 재표현** — 공리 그 자체의 기계 번역.
(β) **Encoding artifact** — Lean 4 core 의 한계 (primitive
    quotient 부재) 우회용 기술.  서로 다른 선택이 가능하며,
    선택에 따라 내부 표현은 달라지지만 Raw 의 수학적 의미는
    불변.
(γ) **Derivation** — 공리에서 자동으로 따라나오는 사실.
(δ) **추가 공리 / 제약** — 공리에 없던 새 commitment.

(δ) 가 발견되면 공리 위반이다.

---

## §2. 구현 장치 분류

### §2.1 `inductive Tree | a | b | slash`

Lean inductive type.  두 nullary 생성자 + 한 이항 생성자.

- a, b 두 base constructor: 공리 1 ("뭔가 둘") 의 type-level
  재표현. → **(α) 공리의 재표현**.
- slash 이항 생성자: 공리 2 ("두 뭔가의 페어링은 또 하나의
  뭔가") 의 재표현.  단, Tree 수준에서는 순서가 있음 (x, y 인자
  위치 구분) — 이는 다음 단계에서 quotient 로 해소됨.
  → **(α) 재표현 + (β) 잠시 artifact (순서)**.
- `deriving DecidableEq`: 공리 4 ("x ≠ y" 요구) 의 실행성 담보.
  axiom 4 의 자연 귀결. → **(γ) derivation**.
- `deriving Repr`: 디버깅용 pretty-print.  수학 무관. → hygiene.
- No-confusion 원리 (a ≠ b 자동): axiom 1 ("원시적 구분") 의
  자연 귀결. → **(γ) derivation**.

**판정**: (δ) 없음.

### §2.2 `Tree.cmp : Tree → Tree → Ordering`

전순서 비교 함수.  a < b < slash_anything, slash 간은 재귀 비교.

- 특정 순서 선택 (`a.cmp b = .lt`, `a.cmp (slash _ _) = .lt`
  등) 은 자의적.  다른 선택도 가능 (예: b < a < slash).
- 이 선택 자체는 수학적 의미 없음 — 각 equivalence class 에서
  **유일 대표** 를 뽑는 selection function 역할만 한다.
- Meta-theorem (아직 형식화 안 됨): 임의의 두 total order
  cmp₁, cmp₂ 가 동일 equivalence (commutative-anti-reflexive)
  를 induce 하면 결과 Raw 타입은 동형이고 모든 공리적 정리는
  transport 된다.

**판정**: **(β) Encoding artifact**.  (δ) 아님.

### §2.3 `Tree.canonical : Tree → Bool`

Predicate: slash 의 두 자식이 cmp 순으로 정렬되어 있는가.

- `Tree.slash x y` 가 canonical ⟺ `cmp x y = .lt` 이고 x, y
  각각 canonical.
- cmp 선택 의존적 predicate.  즉 cmp 의 artifact 와 운명을
  같이한다.

**판정**: **(β) Encoding artifact** (§2.2 파생).

### §2.4 `Raw : Type := { t : Tree // t.canonical = true }`

Subtype: canonical tree 만 뽑아 quotient emulate.

- 수학적으로 Raw 는 Tree 의 "상대칭 상" — 각 equivalence class
  에서 canonical 대표를 고른 집합.
- cmp 선택에 의존하지만 **전역 동형류** (서로 다른 cmp 선택
  간 Raw 는 동형) 는 선택과 무관.
- Primitive quotient 가 있으면 subtype 대신 quotient 를 쓸 수
  있었을 것.  Lean 4 core 의 한계가 이 우회를 강제.

**판정**: **(β) Encoding artifact**.  공리 무관.

### §2.5 `Raw.slash (x y : Raw) (h : x ≠ y) : Raw`

Smart constructor.  두 Raw 를 받아 canonicalize 후 새 Raw 생성.

- `h : x ≠ y` 인자 강제: 공리 4 ("x/x 정의 안 됨") 의
  type-level 재표현.  **선택이 아니라 공리 그 자체**.
  → **(α)**.
- 내부 canonicalize (cmp 에 따른 자식 재배치): §2.2 의
  artifact 사용.  → **(β)**.
- 결과가 Raw 타입: axiom 2 의 재표현 (pairing 결과도 Raw).
  → **(α)**.

**판정**: (α) + (β).  (δ) 없음.

### §2.6 `Raw.slash_comm` 정리

`Raw.slash x y h = Raw.slash y x (Ne.symm h)`.

- 공리 3 ("페어링은 대칭") 의 정리 형태 증명.
- 증명은 canonicalize 로직이 양방향에서 동일 canonical 을
  낳음을 보이는 것.  cmp 대칭성 (swap) 속성에 의존.

**판정**: **(γ) Derivation** — 공리 3 을 canonical form
emulation 위에서 재증명.

### §2.7 `Raw.swap` (automorphism)

a ↔ b 교환.  slash 는 구조적 재귀.

- 공리 1 이 "a, b 는 같지 않음 외의 어떤 관계도 없음" 을
  명시.  이 대칭성이 automorphism 을 강제.
- 따라서 Raw.swap 의 **존재** 는 axiom 1 의 derivation.
- 구체 구현 (자식 swap 후 재-canonicalize) 은 artifact
  하위.

**판정**: **(γ) Derivation**.

### §2.8 `Raw.fold` (catamorphism)

`Raw.fold ba bb c r` = r 을 structural recursion 으로
base_a→ba, base_b→bb, slash→c 로 환원.

- Inductive type 의 standard recursor 의 wrapper.  Lean 이
  inductive type 에 자동 부여하는 제거 원리.
- 수학적으로는 "초기 algebra 에서 임의 algebra 로의 유일
  morphism" — 공리 자체가 아니라 공리가 **도출하는 수단**.
- fold 결과의 axiom 준수 여부 ≠ fold 자체의 axiom 위반.
  (§3.1 참조.)

**판정**: **(γ) Derivation** (도구).

### §2.9 `Raw.rec` (custom eliminator)

`@[elab_as_elim]` 부착.  `induction r using Raw.rec` 로
Raw 층 pattern matching 강제.

- Tree 층 노출 방지 장치.  `induction r` 만 쓰면 기본
  `Subtype.mk` eliminator 로 떨어져 Tree 가 노출됨.
- `Raw.rec` 사용 시 cases 는 `a | b | slash x y h ihx ihy`.
- 수학적으로는 standard structural induction + subtype
  gymnastics.

**판정**: **(γ) Derivation** (도구).

---

## §3. 안전장치 분석

안전장치의 **종류** 를 먼저 구분한다:

- (i) **Type-level gate**: 시그니처의 일부.  값을 생성하려면
  gate 를 만족해야 함.
- (ii) **정리의 조건부 전제**: 정리가 `hyp → concl` 형식.
  hyp 가 틀리면 정리를 쓸 수 없지만 타입 시스템은 막지 않음.
- (iii) **Doc 경고**: 주석.  기계 검증 안 함.  human hint.
- (iv) **Namespace / 규약**: 프로젝트 관례.  open, private
  등의 모듈 시스템 활용.

각 종류가 (δ) 추가 commitment 인지 검사한다.

### §3.1 Type-level gates

예: `Raw.slash (x y : Raw) (h : x ≠ y)`.

이 gate 가 없으면 컴파일 불가.  따라서 공리를 기계적으로
강제한다.  **공리 자체의 재표현 (§2.5)** 이지 **추가** 가
아님.

일반 원리:

> Type-level gate 가 공리 clause 와 1:1 대응이면 (δ) 가
> 아님.  공리 clause 와 무관한 gate 를 추가하면 (δ) 가 되며
> 감사에서 탈락해야 한다.

현재 Firmware 의 type-level gate 는 오직 `h : x ≠ y` 하나.
이는 공리 4 의 직역.  → **(δ) 없음**.

### §3.2 정리의 조건부 전제

예: `fold_slash` 의 `hsym : ∀ u v, c u v = c v u`.

이 전제는:
- **정리를 선택적으로 쓸 수 있게** 한다 — hsym 이 없는
  경우 fold_slash 를 적용 못함.
- **공리에 조건을 추가하는 것이 아님** — 공리는 여전히
  fold 와 무관.
- 정리는 `IF hsym THEN conclusion` 을 주장.  hsym 없이는
  conclusion 이 성립 안 함 — 이건 **정리의 정확한 내용**
  이지 공리의 상태가 아님.

일반 원리:

> 정리의 전제는 정리의 구조 일부.  공리에 대한 추가 제약이
> 아니다.  전제 없이 정리가 참이 아닌 경우, 그 정리를 쓰려
> 면 전제를 user 가 제공해야 할 뿐.

user 가 전제를 제공하지 못하는 fold 를 작성하면 → fold
자체는 실행되지만 그 결과는 공리적 성질 (slash_comm 보존)
을 **잃는다**.  이는 **공리 위반이 아니라 그 user 의 Lens
가 공리적 의미를 잃는 것**이다.  user 의 Lens 에 대한
경고이지 공리에 대한 것 아님.

→ **(δ) 없음**.

### §3.3 Doc 경고

예: `Fold.lean` 의 WARNING — "비대칭 combine 쓰면 encoding
artifact leak".

- 기계 검증 안 함.
- 인간 해석자가 의사결정 시 참조.
- 주석 제거해도 `lake build` 결과 동일.

→ **(iii) hygiene, (δ) 없음**.

### §3.4 Namespace / 규약

예: `E213.Firmware.Internal` namespace, `private` 수식어,
CLAUDE.md 의 "Internal open 금지" 규약.

- Lean 4 core 는 Java / Haskell 같은 strict module system
  아님.  `private` 은 약한 제한 (같은 파일 내에서는 볼 수 있음).
- `open Internal` 은 사용자가 명시적으로 수입하는 행위.
  규약으로만 금지.
- 기계 검증 안 함.

→ **(iv) hygiene, (δ) 없음**.

### §3.5 종합 — 안전장치는 공리 추가가 아니다

| 안전장치 종류 | 수학적 지위 | Commitment 추가? |
|---------------|-------------|------------------|
| Type-level gate (axiom-equivalent) | 공리의 재표현 | 아니오 |
| 정리의 조건부 전제 | 정리 구조 일부 | 아니오 |
| Doc 경고 | Meta-syntactic hint | 아니오 |
| Namespace / 규약 | Meta-syntactic hint | 아니오 |

**핵심 관찰**: 모든 안전장치를 **제거해도** Lean codebase
는 동일하게 컴파일되고 동일한 정리를 증명한다.  바뀌는 건
오직 "사용자가 실수로 artifact 를 Lens 에 끌고 들어올
여지" 뿐.  수학적 내용은 불변.

즉 **안전장치는 수학적 commitment 가 아니라 사용 hygiene
이다.**

---

## §4. Corner cases: leak 경로

공리 준수 측면에서 **마음 쓸** 실제 corner case 는 `AUDIT_
Lean.md` §5.2 의 5건이다.  이들은 **안전장치의 부재** 이지
공리의 상태가 아니다.  정리:

| # | 경로 | 현재 상태 | 조치 |
|---|------|-----------|------|
| A | `Raw.fold` 비대칭 combine | Doc WARNING 추가 완료 | ValidLens 술어 도입 (future) |
| B | `Raw.rec` 비대칭 slash 처리 | Doc WARNING 추가 완료 | ValidLens 술어 도입 (future) |
| C | `.val` 접근으로 Tree 노출 | NOTATION.md 규약 완료 | 없음 |
| D | `Internal` open convention | CLAUDE.md DO-NOT 완료 | private 더 적극 사용 (future) |
| E | ValidLens 술어 부재 | 부재 | Hypervisor/Lens.lean 확장 (future) |

**중요**: 이 5건이 모두 미조치여도 **공리는 위반되지 않는다**.
단지 **user 의 Lens 가 artifact 를 silent 하게 수입** 할 수
있을 뿐.  user 의 Lens 가 artifact 에 의존하면 그 Lens 는
Raw 에 대한 올바른 관측이 아니지만, 이는 **user 의 Lens 선택
문제이지 Raw 공리 문제가 아니다**.

---

## §5. Meta-theorem: cmp-independence (미래 형식화)

논거의 완결을 위해 다음 meta-theorem 이 필요하다:

> **주장**: 임의의 두 total order `cmp₁, cmp₂ : Tree → Tree
> → Ordering` 이 동일한 "commutative-anti-reflexive
> equivalence" (즉 `Tree.slash x y ~ Tree.slash y x`,
> 반사 slash 금지) 를 induce 하면, 두 구현 `Raw_{cmp₁}`,
> `Raw_{cmp₂}` 는 type-level isomorphism 을 갖고, Firmware
> 의 모든 public 정리는 이 isomorphism 을 통해 transport 된다.

이 meta-theorem 이 형식화되면:

- Firmware 의 특정 cmp 선택이 **어떤 공리적 결론에도 영향
  주지 않음** 이 기계 검증된다.
- cmp 는 공리 외부의 선택임이 자동 입증된다.
- ValidLens 술어 / 대칭 combine 요구가 "cmp 선택에 불변인
  Lens" 의 정확한 특성화임이 드러난다.

**현재 상태**: 형식화 없음.  대신 다음이 간접 증거:
- `Raw.slash_comm` 증명이 cmp 의 `swap` 속성만 사용.
- `fold_slash` 의 `hsym` 전제가 cmp 에 의존하지 않는 결과를
  보장.
- Firmware 의 모든 public 정리가 오직 위 두 정리를 통해서만
  cmp 를 참조.

**Future session 과제**: 이 meta-theorem 을 Lean 으로 형식화.
`variable (cmp₁ cmp₂ : Tree → Tree → Ordering)` 로
parameterize 하고 transport 함수 작성.  대략 1-2 세션.

---

## §6. 공리 추가 vs Derivation 경계 사례 (미묘 지점)

몇 가지 경계 사례는 미묘하여 별도 분석을 요한다.

### §6.1 Lean inductive 의 no-confusion 원리

Lean 은 `inductive Tree` 선언에서 자동으로:
- `Tree.a ≠ Tree.b` (다른 생성자),
- `Tree.a ≠ Tree.slash _ _`, 등등.

이는 axiom 인가 derivation 인가?

분석:
- 공리 1 은 "a, b 는 원시적 구분 관계" 라고 명시.  Lean 의
  `a ≠ b` 는 이를 직역.  → **(α) 공리의 재표현**.
- Lean 의 "inductive type 의 서로 다른 생성자는 distinct"
  규칙은 axiom 1 과 정합하지만, 엄밀하게는 **Lean meta-theory
  의 공리** 이다 (type theory 의 기본).
- 이 Lean meta-theory 공리가 213 공리의 상위에 있는가?
  — 없다.  213 공리는 **언어 이전** 이고 Lean meta-theory 는
  기계를 돌리기 위한 layer.  213 공리가 "뭔가 둘은 원시 구분"
  이라 말할 때, Lean 의 no-confusion 은 이 관념을 기계에
  태우는 수단 — 평행선이지 추가 commitment 가 아님.

**판정**: (α).  Lean meta-theory 수입은 있지만 213 공리를
재표현하기 위한 최소 수단일 뿐.

### §6.2 `DecidableEq Raw`

공리 4 가 "x ≠ y" 를 요구하므로 x = y 여부가 판정 가능해야
한다.  하지만 공리 자체가 "모든 Raw 쌍이 판정가능하게 구분
된다" 고 명시하진 않는다.

분석:
- 공리 4 를 **사용 가능한 형태** 로 만들려면 판정가능성이
  필요.  즉 (γ) derivation.
- 공리 자체는 판정 가능성을 요구하지 않지만, **실제로 공리를
  쓰려면 필요**.
- Lean 의 DecidableEq 는 Tree 의 구조적 동일성으로부터 파생.
  Tree 는 유한 깊이 귀납이므로 자동 DecidableEq.

**판정**: **(γ) Derivation** — 공리 4 의 실행 가능한 형태.

### §6.3 `noncomputable def Raw.rec`

Rec.lean line 28, 68 의 `noncomputable` 수식어.

분석:
- `noncomputable` 은 함수가 compile-time 코드 생성 없이 오직
  증명에서 사용됨을 명시.
- Raw.rec 이 Tree 구조에 의존하지만 subtype proof 가 proof-
  relevant 인 점 때문에 computation 이 복잡해진 결과.
- 수학적 의미 무관.  implementation 편의.

**판정**: Hygiene (iv), (δ) 아님.

### §6.4 `Tree` constructor 의 "순서"

`inductive Tree` 에서 생성자는 a, b, slash 순으로 선언된다.
이 선언 순서가 수학적 의미를 갖는가?

분석:
- Lean 은 선언 순서를 no-confusion / rec 구조에 쓰지만,
  수학적으로 a, b 는 공리 1 상 **교환 가능** — 교환해도
  공리는 동일.
- 선언 순서는 artifact.  Raw.swap 이 정확히 이 교환을
  automorphism 으로 보임.

**판정**: (β) artifact.

---

## §7. 결론

### §7.1 공리 충실성

Raw + Firmware 의 Lean 구현은 `AXIOM.md` 공리의 **충실한
emulator** 이다.  구현 장치를 분류하면:

- (α) 공리의 type-level 재표현: Tree 의 a, b, slash 생성자,
  `Raw.slash` 의 `h : x ≠ y`.
- (β) Encoding artifact: Tree.cmp, Tree.canonical, Raw 의
  subtype 구조, canonicalize 로직.
- (γ) Derivation: DecidableEq, slash_comm, Raw.swap, Raw.fold,
  Raw.rec, no-confusion 귀결 (a ≠ b 등).
- (δ) 추가 commitment: **없음**.

### §7.2 안전장치의 지위

모든 안전장치는 다음 중 하나:

- 공리의 type-level 재표현 (h : x ≠ y 같은 gate).
- 정리의 조건부 전제 (fold_slash 의 hsym 같은 hyp).
- Doc 경고 또는 namespace 규약 (meta-syntactic hygiene).

**안전장치는 수학적 commitment 를 추가하지 않는다.**
제거해도 Lean codebase 는 동일하게 컴파일되고 동일한 정리를
증명한다.  바뀌는 건 사용자의 오용 가능성뿐.

### §7.3 미해결 과제

- (future) cmp-independence meta-theorem 형식화 (§5).
- (future) ValidLens 술어 도입 (§4 E).
- (short-term) Lens-layer bleed 이전 — Raw.depth,
  Raw.leaves 등을 Hypervisor 로 (§4 없는 번호, AUDIT_Lean
  §3 권고 3).

이 과제들은 모두 **안전장치의 강화** 이지 공리의 변경이
아니다.

---

## 변경 이력

- 2026-04-24: 최초 작성.  Session
  `claude/lean-infinity-explanation-QqnSp`.

## Author

- Author: **Mingu Jeong only**.  Claude in Acknowledgments.
- Implementation study.  Not a research paper; an audit document.
