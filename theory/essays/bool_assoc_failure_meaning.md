# 왜 b ≥ 3에서 cutSum 결합법칙이 Bool 레벨로 실패하는가

`cutSum`의 내부 search granularity가 factor-2 (dyadic)로 hardcode 되어 있고, b ≥ 3에서 ceiling super-additivity gap이 search slack을 초과한다.

## 산술 진단

`cutSum (constCut a b) (constCut c b) m k = true` 의 조건을 풀면:

```
∃ m1 ∈ [0, 2m]:  a · 2k ≤ b · m1  ∧  c · 2k ≤ b · (2m − m1)
⇔  ⌈2ka/b⌉ ≤ m1 ≤ 2m − ⌈2kc/b⌉
⇔  ⌈2ka/b⌉ + ⌈2kc/b⌉ ≤ 2m
```

`constCut (a+c) b m k = true` 의 조건:

```
(a+c) · k ≤ b · m  ⇔  ⌈2k(a+c)/b⌉ ≤ 2m
```

두 조건의 차이는 **ceiling super-additivity gap**:

```
⌈X/b⌉ + ⌈Y/b⌉  ≥  ⌈(X+Y)/b⌉
```

각 ceiling은 최대 `(b-1)/b`만큼 올림이 발생; 합쳐서 최대 `2(b-1)/b`만큼 over-shoot.  이 over-shoot가 0인 경우만 두 조건이 일치.

## Dyadic boundary

`2k/b`가 항상 정수일 때만 ceiling gap이 0이다:

| b | `2k/b` 정수성 | gap |
|---|---|---|
| 1 | 항상 (`2k/1 = 2k`) | 0 |
| 2 | 항상 (`2k/2 = k`) | 0 |
| 4 | k가 짝수일 때만 | 발생 |
| 3, 5, 6, 7, ... | k가 b의 배수일 때만 | 발생 |

b ∈ {1, 2}는 cutSum의 factor-2 doubling에 정확히 fit; b ≥ 3은 분모와 doubling factor의 불일치.

## Framework 의도

`theory/math/real213.md` §"Why classical ℝ doesn't fit 213"에 명시: Real213은 **dyadic rational에서의 Dedekind cut**이다.  Native cut form은 `dyadicCut M E := M/2^E` (모든 분모가 2의 거듭제곱).  `constCut a b`는 임의 b를 받는 **convenience 함수**일 뿐, framework의 native object가 아니다.

`cutSum`의 ε/2 trick (`Lib/Math/Real213/Sum/CutSum.lean` 정의의 `2*k` factor)은 dyadic structure에 정확히 fit하도록 설계됐다.  b = 2^n 형태의 cut에서는 이 doubling이 모든 division을 흡수하므로 ceiling gap이 0.  b ≥ 3 (non-dyadic) cut에서는 doubling이 division과 어긋나서 gap이 발생.

## 그래서 b ≥ 3 결합법칙 실패의 의미

이전 essay (`bool_assoc_failure_meaning.md`)에서 시적으로 표현했던 "trajectory vs real distinguishing"은 over-poetic.  실제 사실은:

  · `constCut a b`는 b ≥ 3에서 framework의 native object가 아니다.
  · `cutSum`은 dyadic structure에 hardcode 되어 있다.
  · 두 non-native object를 native operation에 넣으면 search granularity mismatch가 발생한다.
  · 그래서 결합법칙은 dyadic class (b ∈ {1, 2})까지만 Bool level에서 닫힌다.

이건 layer-distinction phenomenon이 아니라 **framework가 자기 design intent (dyadic only)를 정직하게 enforce하는 결과**.

## 해결 후보

세 가지 방향이 가능하다.

**A. Non-dyadic constCut을 framework에서 추방**.  모든 cut을 `dyadicCut M E` 형태로만 받는다.  b ≥ 3은 framework 바깥; `constCut 2 3` 같은 표현은 illegal (또는 dyadic 근사 wrapper로만 허용).  가장 design-purity 우선.

**B. `cutSum`의 search granularity를 동적화**.  cut이 자기 native 분모를 carry하게 하고, `cutSum`이 그에 맞춰 search range를 `b·m`으로 확장.  Framework 자체의 generalization, 큰 redesign.

**C. Non-dyadic cut을 dyadic 근사로 환원**.  `constCut a b ≈ dyadicCut (round (a · 2^E / b)) E` for large enough E.  근사 framework에서 작동시키고, 원래 cut과의 cutEq를 별도로 유지.  Incremental.

가장 213-native는 (A).  Framework가 dyadic structure에 commit했으므로 비-dyadic은 *외부 import*이고, 외부 import의 algebraic 결함은 *framework의 결함이 아니다*.  단순히 그 표현이 framework 안에 자연스럽게 살지 않는다는 정직한 신호.

## 함의

Marathon의 `IntValidCut` (b=1) + `HalfValidCut` (b=2)는 framework 내부 dyadic class에서 algebraic 결합법칙이 닫히는 *정확한 boundary*를 마킹한다.  b ≥ 3에서 결합법칙이 닫히지 않는 것은 *그 boundary가 정확하다는 증거*, framework의 결함이 아니라 framework가 자기 commit (dyadic only)을 honor한다는 사실.

진짜 후속 작업은 (essay가 hint한 "Setoid Framework Real213 analog"가 아니라) **dyadic-only enforcement**: `constCut a b`가 b가 2의 거듭제곱이 아닐 때 *컴파일 타임에 거부하거나*, *dyadic 근사로 wrap하는* type-level 게이트.  그러면 b ≥ 3 결합법칙 질문 자체가 framework 안에서 발생하지 않는다.
