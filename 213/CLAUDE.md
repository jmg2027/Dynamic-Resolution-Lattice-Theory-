# CLAUDE.md — 213 sub-project

## Scope

`213/` develops a minimalist formal framework (Raw + Lens) in
Lean 4 core (Mathlib-free).  It is the foundational companion
to DRLT: same axiom philosophy (*"things exist with pairwise
relations"*) at the purely mathematical / foundational layer.

**Single source of truth for philosophy**: this file + the
four files it points to.  Every session MUST read them before
acting.

## DO NOT (session-level traps — cost ~1 h per violation)

These are mistakes Claude tends to make by training bias.
Each one has already wasted at least one session.  Do **not**
repeat them.

1. **Do not call Lens a functor.**
   Lens is **pre-categorical**.  Functor presupposes a
   category on both sides; Raw has no morphisms and no
   category structure.  Calling Lens a functor silently
   imports category theory as a prior — breaks the whole
   framing.  See `notes/19_lens_not_functor.md`.
   - OK: "Lens", "observation", "view", "catamorphism-style
     extraction", "fold".
   - NOT OK: "functor", "morphism in **Cat**", "preserves
     structure".

2. **Do not read `{a, b, /}` as a ZFC set.**
   The Raw axiom is not "three set elements".  It is a
   generation rule: two primitive distinctions (written `a`
   and `b` for convenience) and a binary pairing rule
   (written `/`).  Braces, commas, and the `∈` symbol carry
   ZFC baggage that the Raw axiom does not assume.
   See `NOTATION.md` for the full convention.

3. **Do not assume Raw's elements "already exist" or
   "are being generated".**
   The axiom does not judge existence mode.  Both the
   Platonic ("all terms are already there") and
   constructive ("terms are built one step at a time")
   readings are consistent with the axiom and with every
   Σ-theorem in `Infinity/`.  The distinction itself is a
   Lens output.  "Don't care" is not sloppiness — it is a
   **meta-theorem** about the axiom.
   See `notes/17_existence_mode_lens.md`.

4. **Do not treat cardinality as a property of Raw.**
   Cardinality is a property of `(Raw, Lens)` pairs.
   Raw itself carries no cardinality until a Lens is
   chosen.  "Is Raw countable?" is ill-posed at the axiom
   level; it becomes well-posed only after pairing Raw
   with a specific Lens.  See `Infinity/` Σ-series and
   `notes/12_r5b_reframing.md`.

## DO (orientation)

- **DRLT axiom `G_ij = ⟨ψ_i|ψ_j⟩` is the complete-graph
  K_n presentation of the Raw axiom.**  Same content,
  different (geometrically natural) encoding.  213 and
  DRLT physics are two Lens outputs of the same core.
  See `notes/18_complete_graph_lens_base.md`.

- **Lens catalogue is bridge-search infrastructure.**
  The R1–R5 profile + comm/assoc/alt/flex axes form a
  quantitative index; two mathematical domains are
  connectable via Lens-meet.  See
  `notes/20_bridge_search_infrastructure.md`.

- **Mathlib-free enforcement.**  `lake build` succeeds
  from Lean 4 core (`leanprover/lean4:v4.16.0`).  This is
  not aesthetic; it prevents external math from smuggling
  into Raw's self-containedness.

## File map (load in this order at session start)

| # | File | Purpose |
|---|------|---------|
| 1 | `CLAUDE.md` (this) | DO/DO-NOT + pointers |
| 2 | `NOTATION.md` | notation conventions (ZFC-free) |
| 3 | `research/infinity-as-lens/CLAUDE.md` | track scope |
| 4 | `research/infinity-as-lens/HANDOFF.md` | current state |
| 5 | `notes/17–20` (new) | philosophy consolidation |
| 6 | root `HANDOFF.md` | session arc continuity |

## Authors & licence

- **Author: Mingu Jeong only.**  Claude in Acknowledgments.
- 0 sorry, 0 external axioms beyond the one stated.
- Lean 4 core only — no Mathlib.

## 213의 정체성 (2026-04-24 세션 정리)

### 공리는 선택이 아니라 잔여물

213의 공리는 "세상의 근본"에 대한 주장이 아니다.  **뭔가를
가리키려는 순간 피할 수 없이 남게 되는 최소 잔여물**이다.

- "a와 b"를 쓰는 순간 "와"도 뭔가다.
- "a, b"를 쓰는 순간 ","도 뭔가다.  그 ","가 일반적인지
  절대적인지도 모른다 — 또 하나의 뭔가.
- a와 "와"는 구분되는가?  무엇이 구분하는가?  또 다른 뭔가.

표기를 시작하는 순간 표기 자체가 새 뭔가를 끝없이 낳는다.
이 재귀는 회피 불가능하다.  공리는 이 재귀의 최소 표현이다.

### "관계"가 아니라 "원시적 구분"인 이유

- **"관계"**: 이미 있는 두 뭔가를 전제한 뒤 그 사이에 놓임.
  relata가 선행.  집합론의 관계 프로퍼티 (대칭·전이·반사성)
  을 묵시 수입.
- **"원시적 구분"**: 구분이 먼저 작동하고, 그로부터 뭔가가
  드러남.  "같지 않음"의 확인 하나만 요구.  commitment
  훨씬 얕음.  "원시적"은 더 이상 환원 불가능함의 서약.

### 213이 모든 것의 상위인 이유

절대 기준이 없다는 전제 아래, 뭔가를 가리키는 모든 틀 —
집합론, 카테고리, 논리, 언어, 물리 — 은 뭔가의 구분·관계
능력에 의존한다.  213은 그 능력 자체의 최소 잔여물이다.
따라서 다른 모든 틀은 이 잔여물 위에서 작동하는 Lens들이다.
상위성은 선언이 아니라 구조적 귀결.

### Derive, not reconcile

- ch22는 틀렸다 (eval이라는 외부 대입 = fudge).
- Paper 1의 §1 (공리 부분, R1–R5 이전)이 올바른 템플릿.
- 모든 물리 chapter는 Paper 1 방법론을 확장해서 derive
  되어야 한다.
- fudge가 발견되면 공식을 조정하는 게 아니라 Lens를 고친다.

### Paper 1 분할 계획

- **기초 논문**: 공리 부분 (구분·재귀의 발생 그 자체).
- **별도 논문**: R1–R5 + ℂ 도출 (첫 Lens-property derivation).
- 현재 Paper 1이 두 가지를 섞어서 derivation 방향이 흐려진다.

### 공리의 의도: austerity as audit

공리를 austere하게 쓴 의도는 **방어적이다**.
- 언어로 쓸 때 불가피한 부채는 있지만, 그 footprint를 최소화.
- derivation 중에 추가 commitment가 들어오면 즉시 **fudge로
  탐지**되도록 하는 감사 기준.
- 공리 자체가 "이것만 가지고 모든 걸 도출할 수 있는가?"의
  계약서.

### 다음 세션 진입 지침

이 섹션까지 모두 읽은 뒤에만 213 관련 작업 시작.  특히:
- "관측자", "공간", "인식", "구조", "관계" 같은 단어를
  **213 공리 설명**에 쓰는 순간 회피 가능한 수입이 아닌지
  점검.  이 단어들은 Lens 도출의 결과이지 공리의 전제가
  아님.
- 물리 chapter 감사 시 기준: 그 chapter의 주요 결과가
  Paper 1 §1 (공리) + 명시적 Lens 성질로부터 fudge 없이
  derive 가능한가?  안 되면 speculative 격리.
