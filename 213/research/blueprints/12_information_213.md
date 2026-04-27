# Information Theory 213 — Blueprint

**우선순위**: ★★ (binary tree 가 정보이론의 *바로 그것*)

---

## 1. 왜 이 분야인가

ZFC information theory:
- Shannon entropy H(X) = -Σ p log p
- Mutual information I(X;Y)
- Channel capacity, error-correcting codes
- Kolmogorov complexity

213 의 자연 등장:
- **Dyadic tree = binary information tree**
- **각 bisection = 1 bit**
- **bisectN n = n bits of information**
- log₂ 자연 등장 (atomic depth)

## 2. 213-native 등장

### 2.1 1 bit = 1 bisection

dyadic tree 의 깊이 n = n bits.  Information content 자연
정의:
- log₂(2^n) = n
- atomic prime 2 = bit base

### 2.2 Shannon entropy = path distribution

분포 p on dyadic tree → entropy = expected path length.
H(X) = -Σ p_i log₂ p_i.

213-native: probability 213 (blueprint 01) + log₂ via bisection
depth.

### 2.3 Mutual information = cohomological

I(X;Y) = H(X) + H(Y) - H(X,Y).
FluxCut 의 add 연산이 자연.

### 2.4 Channel = trajectory

Communication channel = mapping of input cut → output cut +
noise.  bisectN with random oracle = noisy channel.

### 2.5 Source coding (Huffman)

Optimal binary code = optimal bisection tree.  213-native
optimization.

### 2.6 Kolmogorov complexity

213 의 *axiomatic minimality* (Raw axiom 4 clause = 최소
잔여물) 이 *the smallest description*.  Kolmogorov complexity
의 213 native form.

## 3. 빌딩 블록

| 도구 | 활용 |
|---|---|
| `bisectN` | bit sequence |
| `DyadicBracket.expE` | bit count |
| Probability 213 | distribution |
| `partialSum` | entropy 계산 |
| `IsAntiderivative.integral` | 연속 entropy |
| `cutPow 2 n` | 2^n |

## 4. Phase 계획

### Phase IA — Bit + entropy 기초 (3-5 commits)

1. `bitDepth db := db.expE` (= 1 bit per bisection)
2. `informationContent p` for dyadic prob
3. Shannon entropy of finite distribution
4. H(uniform on 2^n) = n propEq

### Phase IB — Mutual info + KL divergence

1. Joint distribution
2. Mutual information formula
3. KL divergence + Jensen's inequality

### Phase IC — Channel + capacity

1. Channel model (input → output cut)
2. Channel capacity = max mutual info
3. Binary symmetric channel
4. Shannon coding theorem skeleton

### Phase ID — Coding theory

1. Huffman optimal code
2. Hamming distance + error correction
3. Linear code = subgroup of Fin 2^n

### Phase IE — Kolmogorov complexity

1. Description length = AST size
2. 213 axiom 4 clause = minimum
3. Universality of 213

### Phase IF — Capstone

학부 정보이론 1년차 + Kolmogorov 첫 단계.

## 5. 다른 트랙 연결

- **Probability 213**: 분포 = 정보 분포
- **Quantum gravity**: holographic principle (Bekenstein bound)
- **Yang-Mills**: gauge information
- **Cosmology**: ER=EPR, holographic
- **사용자 vision (3)**: 양자 decoherence 제거 = information loss 제거

## 6. 미해결 / Open

- **Quantum information** — qubit, von Neumann entropy
- **Channel coding lower bound** — converse theorem
- **AIT (algorithmic info)** — universal Turing machine 213?

## 7. 핵심 인사이트 (★)

★ **bit = bisection** — 213 의 dyadic tree 가 정보이론의 본바탕.

★ **Shannon entropy = expected bit depth** — bisectN 직접 활용.

★ **213 자체가 minimum description** — Raw 공리 4 clause =
Kolmogorov 0-axiom-minimal description.

★ **사용자 vision (3) "양자 decoherence 제거"** = 정보 손실
없는 dyadic 채널.  213 = 결정론적 비트 + dyadic = 자연 양자
대안.

## 8. 첫 마라톤 명령

```
"Phase IA 시작.  bitDepth + Shannon entropy on uniform 2^n"
```

