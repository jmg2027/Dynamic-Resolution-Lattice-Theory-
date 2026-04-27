# F3 — Transcendental 의 Recurrence Lens 분 류

## User question (2026-04-26)

> "213 의 자연수 픽업 프로토콜 위 에 서 π 나 e 같은 초월수 들 은
> 단순히 끝없는 궤적을 넘어 어 떤 특수한 패턴 생성 규칙 (혹은
> 렌즈의 구조) 을 가진 stream 으로 정의?"

D2 의 FSM/ICT classification 의 cut-form specific 화.

## 핵심 framing

각 real 은 RealCut (Nat → Nat → Bool) 의 valid function.  *Generating
Lens* (recurrence) 가 이 cut function 을 unfolding 하는 rule.

**Recurrence Lens** structure:

```
state : Type
init : state
transition : state → state
output : state → Nat → Nat → Bool
```

각 step: state n+1 = transition (state n).  Cut at (m, k) by partial
output 의 limit.

## 분류

### Tier 1 — Algebraic (FSM)

State = finite (Fin n).  Transition = modular.  Convergence = exact
finite step (rational) 또 는 cyclic.

- 유리수 : 1-state Lens (constant).
- √p (algebraic irrationals) : Pell-type state, finite-period 의 mod-N
  Lens.

### Tier 2a — Transcendental with canonical Lens

**e**: state = (i, factorial_i, partial_sum_i).
- transition: i → i+1, factorial *= i+1, sum += 1/factorial.
- Recurrence: a_{i+1} = a_i / (i+1).
- Convergence: tail ≤ 2/(N+1)! — super-exponential.
- *Canonical* Lens 보유 — natural unique choice.

### Tier 2b — Transcendental with multiple Lenses

**π**: 여 러 representations:
- Leibniz: a_i = (-1)^i / (2i+1), tail ~ 1/N — slow.
- Wallis: product (2i)²/((2i-1)(2i+1)) — moderate.
- Madhava-Leibniz: combined — faster.
- BBP (digit extraction) — fast.

모두 valid Lens, all yield same cut-equivalence class.  *Canonical
선택 부재* — π 의 "preferred" Lens 구조 없 음.

## 의의

213 안 모든 reals 가 *some Lens-recurrence 의 unfolding*:

- Algebraic: finite state (Tier 1).
- Transcendental with canonical: factorial / specific recurrence.
- Transcendental with multiple: equivalence class of Lenses.

ZFC ℝ 의 *power-set* arbitrary subset 과 의 차이: 213 안 모든 reals
가 *generative recurrence* 보유.  "임 의" subset 부재 — 모든 cut
function 이 some Lens 의 output.

## Cross-references

- `notes/D2_complexity_class_hierarchy.md` (FSM/ICT classification).
- `notes/F2_real_as_lens_output.md` (Real = Lens output reframe).
- `framework/E213/Research/Real213CutExp.lean` (e 의 recurrence
  Lens — factorial series).
- `framework/E213/Research/Real213RecurrenceLens.lean` (formal
  structure).
