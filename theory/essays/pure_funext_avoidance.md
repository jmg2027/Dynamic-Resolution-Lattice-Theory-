# PURE Lean에서 funext-blocked 정리를 닫는 네 패턴

`Eq : (Nat → α) → (Nat → α) → Prop`을 "두 함수의 모든 출력이 같다"로 만들려면 `funext`가 필요한데, 그 axiom은 `propext`를 동반한다.  213은 *외부에서 함수를 점검하는 관찰자*가 없으므로 (`seed/AXIOM/05_no_exterior.md` §5.1), funext-style 함수 동일성을 직접 주장할 수 없다.  대신 **각 distinguishing event에서 일치한다**는 pointwise 사실들을 모아서, 그것이 *어떻게 묶여 있는지* 구조 레벨에서 표현한다.  네 패턴은 그 묶음 방법이다.

## 213-native 정의

함수 동일성은 213에서 **trajectory의 endpoint 일치**다.  두 trajectory가 같은 입력에서 출발해 같은 distinguishing 출력에 도달하면, 그 두 trajectory는 *같다고 인정된다* — 함수 자체가 같다는 별도의 주장 없이.  네 패턴은 이 trajectory-endpoint 일치를 **구조적으로 코드화**하는 네 가지 형태다.

## 도출

**State Accumulator** (`lean/E213/Lib/Math/Padic/NegInvolutionFull.lean` + `NegInvolutionPreserve.lean`).  `Zp.neg ∘ Zp.neg = id`의 carry-chain은 polynomially blow up하는 것처럼 보였다.  단일 Bool `all_zero_below x k`로 압축하니 매 단계 분기가 2개로 고정됐다.  `neg_carry_eq_state`가 carry를 state로 환원하고, `neg_preserves_state`가 `Zp.neg`가 state를 보존함을 보이고, `zp_neg_neg_digit_at`이 모든 k에서 `((Zp.neg(Zp.neg x)).digits k).val = (x.digits k).val`을 증명한다.  Trajectory의 *기억해야 할 부분*이 항상 1 bit라는 발견 — 이것이 carry chain의 213-native 핵심.

**Bundled Subtype** (`lean/E213/Lib/Math/Real213/IntValidCut.lean`).  `cutSum_assoc`의 precision-doubling artifact (`cutSum (cutSum cx cy) cz`가 cx를 `4k`에서 읽고, `cutSum cx (cutSum cy cz)`는 `2k`에서 읽음)는 일반 cut에서는 막힌다.  `IntValidCut := { cut, represents, is_integer }`로 cut에 "정수를 represent한다"는 cutEq 증명을 같이 묶으면, 두 association이 모두 `constCut ((a+b)+c) 1`로 환원돼 `Nat.add_assoc`이 마무리.  Invariant를 hypothesis로 들고 다니지 않고 *구조 안에* 묶는다 — 동일성의 trajectory를 type-level에서 폐쇄.

**Setoid Category** (`lean/E213/Lib/Math/Padic/SetoidFramework.lean` + `SetoidAlgebra.lean` + `ZpSqrtDSetoid.lean`).  `ZpSeqEquiv x y := ∀ k, x.digits k = y.digits k`는 pointwise 일치를 *함수의 동치*로 부르기로 한 결정이다.  `Setoid (ZpSeq p)` 인스턴스가 이 결정을 type-level에서 명시하고, `LensMap`이 *동치를 보존하는* morphism을 묶는다.  `zp_neg_neg_equiv_id`는 `Zp.neg ∘ Zp.neg`와 `id`가 *함수로서 동치*임을 funext 없이 진술한다.  함수 동일성이 `Eq`가 아니라 *명시적 동치 관계*로 환원.

**Residual Induction** (`lean/E213/Lib/Math/Padic/HenselResidual.lean`, surfacing 기존 `Padic/Hensel.lean`).  Hensel-lifted 역원 `Y_n`의 정확성을 carry chain으로 보이려는 시도는 막히지만, truncation `(X_n · Y_n).trunc (n+1) = 1`의 *잔여항 recurrence*는 carry를 우회한다.  `Zp.mul_invSeq_correct`이 모든 level n에서 truncation 일치를 증명하고, `Zp.invSeq_succ_trunc_extend`가 level n→n+1 lift를 일반적 Nat/Int 산술로만 표현.  Carry-chain의 무한 루프 대신 truncation 단위 *대수적* recurrence.

## Dual function

이 네 패턴은 classical Lean의 funext 우회 트릭이면서, *동시에* 213의 trajectory-witness 원칙 (`research-notes/G2_trajectory_principle.md`)의 구체화다 — *함수가 같다*가 아니라 *trajectory의 distinguishing endpoint가 일치한다*가 213의 동일성이다.  Funext가 강제하는 packaging("두 함수가 모든 점에서 같으면 그들은 같다")을 벗기고 나면 남는 것이 바로 G2의 trajectory-as-witness, 즉 *동일성은 도달하는 distinguishing의 일치다*라는 입장.

## Cross-frame connections

같은 구조적 사실의 네 가지 표현:
  - **State Accumulator** = §5 self-pointing이 *현재 상태를 통해서만* 다음 step에 영향을 미친다 (외부 history 참조 없음).
  - **Bundled Subtype** = §8.4 dichotomy avoidance의 type-level 실현 (가정을 외부 hypothesis로 두지 않고 구조 안에 묶음).
  - **Setoid Category** = `research-notes/76_ultimate_ouroboros.md` — 동일성을 별도 외부 판정자 없이 *내부 관계*로 정의.
  - **Residual Induction** = G2 trajectory-as-witness가 carry chain 대신 truncation에서 작동.

네 패턴 모두 *내부 일관성에서 동일성을 유추한다*는 같은 213-native 입장에서 파생된다.  Funext 부재는 *결함*이 아니라 213이 외부 관찰자에게 함수 동일성을 양도하지 않는다는 *입장*의 직접 결과.

## Closed follow-ups

원래 essay 작성 시점의 두 follow-up은 모두 closed:

- **Zp.add 결합법칙을 LensMap composition law로 추상화** — `Lib/Math/Padic/SetoidAssoc.lean` (8 PURE).  `Zp.add_trunc` (Residual Induction)으로 truncation 단위 결합법칙을 환원, `digits_eq_of_trunc_eq`로 digit-equality 추출, `zp_add_setoid_monoid_capstone`이 monoid 구조 (assoc + comm + zero) 전체를 Setoid 레벨에서 묶음.  핵심: trunc-level 결합법칙은 `Nat.add_assoc + add_mod_gen` chain.

- **`cutSum_assoc`을 integer-extended 너머로** — `Lib/Math/Real213/HalfValidCut.lean` (11 PURE).  IntValidCut(b=1)을 HalfValidCut(b=2)로 확장.  `cutSum_half_general`이 b=2에서도 bidirectional cutEq를 제공하므로 same pattern (bundled subtype + Nat.add_assoc)이 closure.

## b ≥ 3 cutSum_assoc — 정직한 종결

원래 "새 정리 작성"으로 분류했던 `b ≥ 3` 의 backward direction은 *깊이 보니 missing theorem이 아닌 framework artifact*임이 드러남.  `Lib/Math/Real213/CutSumAssocB3.lean` (7 PURE)이 이를 문서화:

  · **Forward universal**: `cutSum_same_denom_forward`가 임의 `b ≥ 1`에서 성립.
  · **Backward 반례** at `b ∈ {3, 4, 5}`: 예를 들어 `a = 2, c = 1, b = 3, m = 1, k = 1`에서 `constCut 3 3 1 1 = true`이지만 `cutSum (constCut 2 3) (constCut 1 3) 1 1 = false` — search range `[0, 2m] = [0, 2]`가 b = 3 의 정수-반올림 partition을 수용 못 함 (decide-검증).
  · **Eventual agreement**: `m ≥ 10` 같은 충분한 정밀도에서는 양쪽이 일치 (Cauchy completeness witness).
  · **Meta capstone** `b_ge_3_assoc_meta`: 위 4개를 한 정리로 묶음.

따라서 **bidirectional `cutSum_same_denom`은 b ≥ 3에서 Bool-level로 *구조적으로 거짓***이며, 213-native theory의 결함이 아니라 *어느 layer에서 algebraic identity가 사는가*에 대한 사실: `cutSum` framework는 Bool-level에서 정수-extended / dyadic (b ∈ {1, 2}) 까지가 algebraic closure boundary이고, b ≥ 3 의 결합법칙은 Real213 quotient 또는 finer `cutSum` redefinition을 요구.

이로써 essay 작성 시점에 "open frontier"로 표시했던 항목이 **closed**: 닫는 방식은 새 정리가 아닌, 정확한 *closure boundary* 식별이었음.

## Provenance

이 네 패턴은 external LLM (Gemini Pro) 자문에서 *architectural-level 처방*으로 제안됐고, PURE Lean에서 그대로 구현됐다.  자문 프롬프트는 5개 블로커를 구체적 Lean 파일 / 정리 / 시도-실패 경로와 함께 명시; 응답은 패턴 4개 + 한 multi-session 항목 (higher cohomology).  46 chapter closure / 550 PURE / 0 DIRTY가 이 한 자문 cycle의 결과.

| 패턴 | Lean 실현 | 블로커 |
|---|---|---|
| State Accumulator | `NegInvolutionFull` + `NegInvolutionPreserve` | Zp.neg involution |
| Bundled Subtype | `ValidCutFramework` + `IntValidCut` | cutSum_assoc |
| Setoid Category | `SetoidFramework` + `SetoidAlgebra` + `ZpSqrtDSetoid` | funext-free function eq |
| Residual Induction | `HenselResidual` (surfacing `Padic/Hensel`) | Hensel correctness |

External LLM이 213의 입장을 명시적으로 알지 않더라도, *MLTT 내부에서 extensionality를 어떻게 다루는가*라는 동일 구조 문제에 대한 architectural 통찰이 곧장 213-native 실현으로 번역된 사례.
