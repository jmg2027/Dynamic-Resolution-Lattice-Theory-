# PURE Lean에서 funext-blocked 정리를 닫는 다섯 패턴

`Eq : (Nat → α) → (Nat → α) → Prop`을 "두 함수의 모든 출력이 같다"로 만들려면 `funext`가 필요한데, 그 axiom은 `propext`를 동반한다.  213은 *외부에서 함수를 점검하는 관찰자*가 없으므로 (`seed/AXIOM/05_no_exterior.md` §5.1), funext-style 함수 동일성을 직접 주장할 수 없다.  대신 **각 distinguishing event에서 일치한다**는 pointwise 사실들을 모아서, 그것이 *어떻게 묶여 있는지* 구조 레벨에서 표현한다.  다섯 패턴은 그 묶음 방법이다.

## 213-native 정의

함수 동일성은 213에서 **trajectory의 endpoint 일치**다.  두 trajectory가 같은 입력에서 출발해 같은 distinguishing 출력에 도달하면, 그 두 trajectory는 *같다고 인정된다* — 함수 자체가 같다는 별도의 주장 없이.  네 패턴은 이 trajectory-endpoint 일치를 **구조적으로 코드화**하는 네 가지 형태다.

## 도출

**State Accumulator** (`lean/E213/Lib/Math/Padic/NegInvolutionFull.lean` + `NegInvolutionPreserve.lean`).  `Zp.neg ∘ Zp.neg = id`의 carry-chain은 polynomially blow up하는 것처럼 보였다.  단일 Bool `all_zero_below x k`로 압축하니 매 단계 분기가 2개로 고정됐다.  `neg_carry_eq_state`가 carry를 state로 환원하고, `neg_preserves_state`가 `Zp.neg`가 state를 보존함을 보이고, `zp_neg_neg_digit_at`이 모든 k에서 `((Zp.neg(Zp.neg x)).digits k).val = (x.digits k).val`을 증명한다.  Trajectory의 *기억해야 할 부분*이 항상 1 bit라는 발견 — 이것이 carry chain의 213-native 핵심.

**Bundled Subtype** (`lean/E213/Lib/Math/Real213/IntValidCut.lean`).  `cutSum_assoc`의 precision-doubling artifact (`cutSum (cutSum cx cy) cz`가 cx를 `4k`에서 읽고, `cutSum cx (cutSum cy cz)`는 `2k`에서 읽음)는 일반 cut에서는 막힌다.  `IntValidCut := { cut, represents, is_integer }`로 cut에 "정수를 represent한다"는 cutEq 증명을 같이 묶으면, 두 association이 모두 `constCut ((a+b)+c) 1`로 환원돼 `Nat.add_assoc`이 마무리.  Invariant를 hypothesis로 들고 다니지 않고 *구조 안에* 묶는다 — 동일성의 trajectory를 type-level에서 폐쇄.

**Setoid Category** (`lean/E213/Lib/Math/Padic/SetoidFramework.lean` + `SetoidAlgebra.lean` + `ZpSqrtDSetoid.lean`).  `ZpSeqEquiv x y := ∀ k, x.digits k = y.digits k`는 pointwise 일치를 *함수의 동치*로 부르기로 한 결정이다.  `Setoid (ZpSeq p)` 인스턴스가 이 결정을 type-level에서 명시하고, `LensMap`이 *동치를 보존하는* morphism을 묶는다.  `zp_neg_neg_equiv_id`는 `Zp.neg ∘ Zp.neg`와 `id`가 *함수로서 동치*임을 funext 없이 진술한다.  함수 동일성이 `Eq`가 아니라 *명시적 동치 관계*로 환원.

**Residual Induction** (`lean/E213/Lib/Math/Padic/HenselResidual.lean`, surfacing 기존 `Padic/Hensel.lean`).  Hensel-lifted 역원 `Y_n`의 정확성을 carry chain으로 보이려는 시도는 막히지만, truncation `(X_n · Y_n).trunc (n+1) = 1`의 *잔여항 recurrence*는 carry를 우회한다.  `Zp.mul_invSeq_correct`이 모든 level n에서 truncation 일치를 증명하고, `Zp.invSeq_succ_trunc_extend`가 level n→n+1 lift를 일반적 Nat/Int 산술로만 표현.  Carry-chain의 무한 루프 대신 truncation 단위 *대수적* recurrence.

**Inductive cong constructor** (`lean/E213/Lib/Math/Cohomology/Bipartite/V33EnrichedParametricDualSpan.lean` + `V33EnrichedParametricDualSpanHard.lean`).  HARD direction `joint ψ-kernel ⊆ InPrimary`는 임의 face cochain `v`에 대해 후보 `candidate v = ⊕ᵢ bᵢ·gᵢ` (8개 primary cup generator의 b-coefficient XOR-add)를 구성하지만, candidate는 `v`와 *pointwise 같지만 함수 literal로는 다르다*.  `funext` 없이는 `InPrimary v`에 도달할 수 없는 듯 보인다.  해결: `InPrimaryCupSpanPlusBoundary` inductive type에 새 constructor를 추가
```
| cong (v w : EnrichedFaceVal c) (h : ∀ s t m, v s t m = w s t m) :
    InPrimaryCupSpanPlusBoundary c w → InPrimaryCupSpanPlusBoundary c v
```
— pointwise 동치를 *inductive 구조 자체*에 묶어 InPrimary witness가 pointwise-eq 동치류 전체에 전파되게 함.  Setoid Category가 *외부* 동치 관계로 함수 동일성을 환원하는 데 비해, cong constructor는 *inductive type 안에* 동치를 embedding한다 — pointwise 사실이 *그 자리에서* InPrimary 자격을 부여.  기존 induction 사용처 (`primary_cup_span_soundness_conditional`) 한 곳에 새 case 추가 (`psi_layer_pw_congr`로 dispatch).  이 패턴이 `joint_psi_kernel_subset_primary_c1`을 funext 없이 닫고, 그 다음 `promote_face` 기반 ∀c lift도 `cong`을 통해 layer 간 pointwise eq 전파를 처리.

## Dual function

이 네 패턴은 classical Lean의 funext 우회 트릭이면서, *동시에* 213의 trajectory-witness 원칙 (`research-notes/G2_trajectory_principle.md`)의 구체화다 — *함수가 같다*가 아니라 *trajectory의 distinguishing endpoint가 일치한다*가 213의 동일성이다.  Funext가 강제하는 packaging("두 함수가 모든 점에서 같으면 그들은 같다")을 벗기고 나면 남는 것이 바로 G2의 trajectory-as-witness, 즉 *동일성은 도달하는 distinguishing의 일치다*라는 입장.

## Cross-frame connections

같은 구조적 사실의 다섯 가지 표현:
  - **State Accumulator** = §5 self-pointing이 *현재 상태를 통해서만* 다음 step에 영향을 미친다 (외부 history 참조 없음).
  - **Bundled Subtype** = §8.4 dichotomy avoidance의 type-level 실현 (가정을 외부 hypothesis로 두지 않고 구조 안에 묶음).
  - **Setoid Category** = `research-notes/76_ultimate_ouroboros.md` — 동일성을 별도 외부 판정자 없이 *내부 관계*로 정의.
  - **Residual Induction** = G2 trajectory-as-witness가 carry chain 대신 truncation에서 작동.
  - **Inductive cong constructor** = inductive 구조 *안에* 동치류를 embedding — Setoid가 외부 관계를 type-level로 끌어들이는 데 비해, cong은 동치 자체를 inductive type의 한 case로 만든다 (predicate가 동치류에서 정의된다는 것을 *형태*가 명시).

다섯 패턴 모두 *내부 일관성에서 동일성을 유추한다*는 같은 213-native 입장에서 파생된다.  Funext 부재는 *결함*이 아니라 213이 외부 관찰자에게 함수 동일성을 양도하지 않는다는 *입장*의 직접 결과.

## Closed follow-ups

원래 essay 작성 시점의 두 follow-up은 모두 closed:

- **Zp.add 결합법칙을 LensMap composition law로 추상화** — `Lib/Math/Padic/SetoidAssoc.lean` (8 PURE).  `Zp.add_trunc` (Residual Induction)으로 truncation 단위 결합법칙을 환원, `digits_eq_of_trunc_eq`로 digit-equality 추출, `zp_add_setoid_monoid_capstone`이 monoid 구조 (assoc + comm + zero) 전체를 Setoid 레벨에서 묶음.  핵심: trunc-level 결합법칙은 `Nat.add_assoc + add_mod_gen` chain.

- **`cutSum_assoc`을 integer-extended 너머로** — `Lib/Math/Real213/HalfValidCut.lean` (11 PURE).  IntValidCut(b=1)을 HalfValidCut(b=2)로 확장.  `cutSum_half_general`이 b=2에서도 bidirectional cutEq를 제공하므로 same pattern (bundled subtype + Nat.add_assoc)이 closure.

## b ≥ 3 cutSum_assoc — 진단의 진행

원래 "새 정리 작성"으로 분류했던 `b ≥ 3` 의 backward direction은 *cutSum 구현의 hardcode artifact*.  `Lib/Math/Real213/CutSumAssocB3.lean` (7 PURE)이 현상을 문서화:

  · **Forward universal**: `cutSum_same_denom_forward`가 임의 `b ≥ 1`에서 성립.
  · **Backward 반례** at `b ∈ {3, 4, 5}`: 예를 들어 `a = 2, c = 1, b = 3, m = 1, k = 1`에서 `constCut 3 3 1 1 = true`이지만 `cutSum (constCut 2 3) (constCut 1 3) 1 1 = false` (decide-검증).
  · **Eventual agreement**: `m ≥ 10` 같은 충분한 정밀도에서는 양쪽이 일치.
  · **Meta capstone** `b_ge_3_assoc_meta`: 위 4개를 한 정리로 묶음.

상세 분석은 `essays/bool_assoc_failure_meaning.md`.  핵심: `cutSum`의 factor-2 hardcode가 (NS, NT) = (3, 2) atom 중 NT만 반영하고 NS를 빠뜨림.  framework "바깥"의 문제가 아니라 *cutSum 구현이 213의 (3, 2) commitment를 under-realize* 한 것 — `Physics/Foundations/AtomicConstantsParametricFullIff.lean` `c2b_full_iff` + `Theory/Atomicity/Five.lean` `atomic_iff_five`가 (3, 2) → 모든 real 판정 chain을 이미 증명.

**Closure 진척**: `Lib/Math/Real213/Sum/CutSumN.lean` (6 PURE)이 parametric `cutSumN N` (factor-N search granularity) 정의 + 임의 N > 0에서 `cutSumN_same_denom` bidirectional 증명.  `Lib/Math/Real213/ThirdValidCut.lean` (15 PURE)이 b = 3 결합법칙을 IntValidCut/HalfValidCut 패턴으로 닫음 — `cutSumN_assoc_thirdValidCut` (full assoc), `cutSumN_comm_thirdValidCut`, `thirdvalidcut_full_assoc_capstone`.  CutSumAssocB3의 반례 (a=2, c=1, m=1, k=1)가 `cutSumN 3`에서는 true임을 `cutSumN_3_2_1_at_1_1`이 decide-검증.

미완: `is_native` wrapper (`b ∈ ⟨2, 3⟩` multiplicative monoid 게이트) — b ∈ {1, 2, 3} 각각의 closure는 닫혔으나 일반 multiplicative composite (b = 6, 9, 12, ...)의 통합 wrapper는 follow-up.

## Provenance

이 네 패턴은 external LLM (Gemini Pro) 자문에서 *architectural-level 처방*으로 제안됐고, PURE Lean에서 그대로 구현됐다.  자문 프롬프트는 5개 블로커를 구체적 Lean 파일 / 정리 / 시도-실패 경로와 함께 명시; 응답은 패턴 4개 + 한 multi-session 항목 (higher cohomology).  46 chapter closure / 550 PURE / 0 DIRTY가 이 한 자문 cycle의 결과.

| 패턴 | Lean 실현 | 블로커 |
|---|---|---|
| State Accumulator | `NegInvolutionFull` + `NegInvolutionPreserve` | Zp.neg involution |
| Bundled Subtype | `ValidCutFramework` + `IntValidCut` | cutSum_assoc |
| Setoid Category | `SetoidFramework` + `SetoidAlgebra` + `ZpSqrtDSetoid` | funext-free function eq |
| Residual Induction | `HenselResidual` (surfacing `Padic/Hensel`) | Hensel correctness |
| Inductive cong constructor | `V33EnrichedParametricDualSpan` (cong case) + `V33EnrichedParametricDualSpanHard` | HARD direction `joint ψ-kernel ⊆ InPrimary` candidate-to-target bridge |

External LLM이 213의 입장을 명시적으로 알지 않더라도, *MLTT 내부에서 extensionality를 어떻게 다루는가*라는 동일 구조 문제에 대한 architectural 통찰이 곧장 213-native 실현으로 번역된 사례.

## Lens-arrow 측의 자매 chapter — Pattern P1 ↔ Inductive cong constructor

`theory/lens/dirty_recovery_patterns.md` 는 DIRTY (propext / Quot.sound)를 PURE Lens-arrow statement로 환원하는 4개 패턴 (P1-P4)을 제시한다.  본 essay의 다섯 패턴과 **layer가 다르지만 구조가 같다**:

  · **P1 (Lens-Eq → LensIso via eqPW)** ↔ 본 essay의 **Inductive cong constructor**.  P1은 `L = M : Lens α` 라는 funext-요구 주장을 `LensIso L M` (= `∀ x y, L.equiv x y ↔ M.equiv x y`)로 환원하고, bridge `lensIso_of_eqPW`가 pointwise eq proof + symmetric-combine 가정만으로 닫는다.  Inductive cong constructor는 같은 *pointwise-equality-as-bridge* 원리를 임의 inductive predicate (predicate가 function-typed argument를 가질 때)으로 일반화한다 — `InPrimaryCupSpanPlusBoundary`가 그 예시.
  · P2 (mutual morphism → LensIso): Setoid Category의 자매 — *동치를 외부 관계로 명시*하는 대신 *mutual morphism pair*가 자연스러운 곳에서 적용.
  · P3 (Quot → LensImage): Bundled Subtype의 Lens-level 변종 — Σ-type representation이 `Quot.sound`를 회피.
  · P4 (slash-cong 주장 → kernel 상속): structural DIRTY 영역 (universalLens 역방향)을 명시적으로 분리 — recovery 가능 vs sealed-by-design.

두 방향 (Padic / Real213 vs Lens-algebra)이 같은 *pointwise-distinguishing-as-equivalence* 원리에서 파생된다.  Lens-arrow가 unified_equivalence.md의 single concept (동치 / 동치류 / 동형 / 준동형의 213-native 통합 object)이듯, **cong constructor도 같은 single concept이 inductive predicate level에서 manifest되는 형태** — 외부 axiom 없이 *내부 구조*가 동치류 closure를 표현.
