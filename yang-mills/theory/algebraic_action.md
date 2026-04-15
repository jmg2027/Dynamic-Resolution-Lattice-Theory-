# Algebraic Action: arccos 제거와 정수론적 질량 갭

## 핵심 관찰

Regge action $S = \sum_h \sqrt{\det(G_h)} \cdot \delta_h$에서 초월적인 부분은
오직 $\delta_h = 2\pi - \sum \arccos(\ldots)$의 arccos뿐이다.

그런데:
1. $\cos\theta$는 **대수적**: Gram 역행렬의 비율
   $$\cos\theta = -\frac{G^{-1}_{lm}}{\sqrt{G^{-1}_{ll} \cdot G^{-1}_{mm}}}$$

2. $\pi^2 = 6\zeta(2) = 6\sum_{n=1}^{\infty} \frac{1}{n^2}$: **정수의 합**

3. Chebyshev 다항식 $T_n(\cos\theta) = \cos(n\theta)$: **정수 계수 다항식**

## 대수적 Action

$$S[G] = \sum_h \sqrt{\det(G_h)} \cdot \sum_{n=1}^{N_{\text{eff}}} \frac{1 - T_n(\cos\theta_h)}{n^2}$$

- 입력: $\cos\theta_h$ (대수적, Gram det 비율)
- $n$: 정수 (hop count)
- $T_n$: 정수 계수 다항식 (Chebyshev)
- $1/n^2$: 전파자 ($s=2$)
- $\pi$는 $\zeta(2) = \sum 1/n^2$의 결과로만 나타남

## Clausen 함수 연결

$$\sum_{n=1}^{\infty} \frac{T_n(x)}{n^2} = \text{Re}\left[\text{Li}_2(e^{i\theta})\right] \quad (x = \cos\theta)$$

여기서 $\text{Li}_2$는 dilogarithm. 따라서:

$$\sum_{n=1}^{\infty} \frac{1 - T_n(x)}{n^2} = \zeta(2) - \text{Re}[\text{Li}_2(e^{i\theta})] = \frac{\theta^2}{4} - \frac{\theta(\pi-\theta)}{2} + \ldots$$

$x = \cos\theta$일 때 이 급수는 $\theta$ (deficit angle)과 관련된다.

## 질량 갭의 정수론적 표현

$$\Delta = \sqrt{\det(G_{\text{AAA}})} \cdot \delta_{\text{AAA}} = \sqrt{\det} \cdot \pi$$

여기서 $\pi = \sqrt{6\zeta(2)} = \sqrt{6 \sum_{n=1}^{\infty} \frac{1}{n^2}}$.

따라서:
$$\boxed{\Delta = \sqrt{\det(G_{\text{AAA}})} \cdot \sqrt{6 \sum_{n=1}^{\infty} \frac{1}{n^2}}}$$

- $\sqrt{\det}$: 대수적 (Gram 행렬)
- $1/n^2$: 정수
- $\pi$: 창발적 (급수의 결과)
- arccos: **어디에도 없음**

## 확립된 이면각 공식 (대수적)

| Hinge | $\cos\theta$ | 대수적 |
|-------|-------------|--------|
| AABt | $\varepsilon/\sqrt{1-2\varepsilon^2}$ | ✓ |
| ABet | $-\varepsilon^2/(1-2\varepsilon^2)$ | ✓ |

| Hinge | $\det$ |
|-------|--------|
| AABe | $1 - 2\varepsilon^2$ |
| ABet | $1 - \varepsilon^2$ |

## Lean 형식화 방향

1. Chebyshev $T_n$을 `Polynomial ℤ`로 정의
2. $T_n(\cos\theta) = \cos(n\theta)$ 증명 (Mathlib에 있을 가능성)
3. 대수적 action $\sum (1-T_n(x))/n^2$ 정의
4. $N_{\text{eff}} \to \infty$에서 $\zeta(2) = \pi^2/6$ 연결
5. 질량 갭 = $\sqrt{\det} \cdot \sqrt{6\zeta(2)}$ 형식화

## 의의

**"정수론/대수학으로 복소해석학을 만든다"**의 구체적 실현:
- arccos (초월) → Chebyshev 급수 (대수)
- π (초월) → ζ(2)의 급수 (정수)
- 연속 각도 → 이산 hop count의 합

이론의 모든 물리량이 정수와 대수적 함수로 환원된다.
