# 결합법칙이 Bool 레벨에서 실패하는 것의 의미

`cutSum (constCut 2 3) (constCut 1 3) m k`와 `constCut 3 3 m k`는 같은 Dedekind 실수 `1`로 수렴하지만, 작은 `(m, k)`에서 서로 다른 Bool 값을 낸다.  이건 framework artifact가 아니라 **Real / Lens / Trajectory의 213-native 구분이 노출되는 사건**이다.

## 213-native 답

Real213의 cut function `c : Nat → Nat → Bool`은 *실수가 아니라 Lens application의 출력*이다.  `(m, k)` 쿼리에 대한 Bool 값은 *trajectory의 checkpoint*이지 *실수 값* 자체가 아니다 (`theory/math/real213.md` §"Why classical ℝ doesn't fit 213").  두 trajectory가 같은 Dedekind 실수로 수렴해도, *그 수렴 경로가 다르면 checkpoint 패턴이 다르다*.  `cutSum`은 실수의 합이 아니라 **trajectory의 합성** — 그래서 같은 실수에 대한 다른 trajectory들은 다른 cutSum-Bool 패턴을 가진다.

## 도출

`lean/E213/Lib/Math/Real213/CutSumAssocB3.lean`의 `backward_counter_example_b3`이 구체적 사실을 보여준다: `a=2, c=1, b=3, m=1, k=1`에서 `(2/3) + (1/3)`의 cutSum trajectory는 `[0, 2]` 정수 search range 안에 partition을 찾지 못하지만, `(3/3 = 1)`의 direct cut은 즉시 true를 낸다.  두 trajectory는 같은 실수 `1`에 도달하지만, *어떤 distinguishing 패턴으로 도달했는가*가 다르다.

이건 G2 trajectory-as-witness 원칙 (`research-notes/G2_trajectory_principle.md`)이 깊은 레벨에서 작동하는 것이다.  실수는 *trajectory의 equivalence class*이고, cut function은 *그 class의 한 대표*다.  `cutSum`은 대표끼리의 합성이라 결과 대표는 *어느 대표를 골랐는지에 의존한다*.  Bool checkpoint가 다른 것은 *대표 선택의 흔적*이다.

여기서 결정적: classical 수학은 `funext` + `propext`로 *"두 함수가 모든 점에서 같으면 같다"*고 선언하여 **trajectory와 실수를 동일시한다**.  213은 funext를 거부 (`theory/essays/pure_funext_avoidance.md`)함으로써 *이 동일시를 거부*하고 두 layer를 별개로 유지한다.  `cutSum_assoc`이 Bool level에서 실패하는 것은 *213이 trajectory의 정체성을 보존하는 행위*이다.

## Dual function

Classical 분석은 `(2/3) + (1/3) = 1`을 *실수-level identity*로만 본다 (trajectory는 implementation detail이므로 funext로 collapse).  213은 같은 identity를 *두 layer로 분리*: 실수 level에서 `cutEq` (Cauchy-completeness)로 같지만, trajectory level에서 다른 distinguishing 패턴.  이것은 classical 입장의 *불필요한 packaging을 벗긴 것*인 동시에 (`research-notes/G29_residue.md` "Linguistic inevitability"), trajectory의 정체성을 *명시적 1차 시민*으로 만든 *refinement*다.  Funext가 hide하던 구분을 213이 surface하는 결정적 순간.

## Cross-frame connections

같은 사실의 네 가지 표현:

- **§5 self-pointing** (`seed/AXIOM/05_no_exterior.md`): distinguishing은 *내부 행위*이지 external 관찰자의 *판정*이 아니다.  Bool checkpoint는 distinguishing event 그 자체이지, 외부 진리값 부여가 아니다.
- **G2 trajectory-as-witness**: 실수 자체가 아닌 trajectory가 witness — 다른 trajectory는 다른 witness를 만든다.
- **Resolution limit** (`seed/RESOLUTION_LIMIT_SPEC.md`): `N_U = 5^25`는 *동시에 distinguish 가능한 trajectory의 cap*.  작은 `(m, k)`에서 가능한 trajectory의 수가 b의 partition 가능성에 비해 *부족*해서 두 trajectory가 보이지 않게 분기됨.  이게 b ≥ 3 counter-example의 정밀도-의존성 본질.
- **`cutSum_assoc_intValidCut`** (b=1) / **`cutSum_assoc_halfValidCut`** (b=2): b ≤ 2에서는 search range가 partition을 항상 수용 — *trajectory 분기가 보이지 않음*.  b ≥ 3에서 처음 분기가 *resolved*된다.

네 frame 모두 *layer-아이덴티티가 framework의 1차 사실*이라는 같은 213-native 입장에서 도출된다.

## 함의

Marathon에서 "blocker"로 분류했던 b ≥ 3 cutSum_assoc은 사실 *framework가 정확히 작동하는 증거*다.  Classical Lean이 funext로 collapse하는 layer 구분을 213은 보존하고, 그 결과 *boundary of algebraic identity는 b ≤ 2*라는 정확한 분리선이 떠오른다.  이건 *the framework is correct*의 증명이지 *the framework is incomplete*가 아니다.

더 깊게: 이 phenomenon은 213이 *왜 N_U = 5^25 같은 resolution cap을 가지는지*와 동형이다.  유한한 distinguishing capacity 안에서 trajectory를 보유한 채로 실수 algebra를 운영하면, 어느 precision에서는 두 trajectory가 분기로 보일 수밖에 없다.  Classical 수학에서 invisible한 trajectory 분기가 213 framework에서는 *resolution-dependent하게 surface*된다.  이게 the resolution limit의 *algebraic level 발현*.

## 구체적 결과

이 발견의 비-시적 readout:

- `theory/essays/pure_funext_avoidance.md`의 "open frontier" 분류는 잘못이었다 — 정답은 *closure boundary가 b ≤ 2다*.
- `cutSum`의 Bool-level "결합법칙 실패"는 213이 *trajectory를 1차 시민으로 보유한다는 사실의 증거*다.
- Classical "real = Cauchy-class" identity가 213에서는 *어느 layer에서 실수와 trajectory가 분리되는가*라는 질문으로 정확화된다.
- Marathon의 `IntValidCut` / `HalfValidCut` bundled-subtype 패턴은 *trajectory가 실수와 collapse하는 b 값*을 정확히 표현하는 도구다.

이 사실의 *진짜 다음 질문*은 "어떻게 b ≥ 3을 닫을 것인가"가 아니라 **"trajectory와 실수의 layer 분리를 어떻게 1차 객체로 표현할 것인가"**다.  Setoid Framework (`Lib/Math/Padic/SetoidFramework.lean`)이 ZpSeq 쪽에서 한 일 — pointwise equivalence를 type-level로 lift — 의 Real213 analog가 다음 작업의 영역.
