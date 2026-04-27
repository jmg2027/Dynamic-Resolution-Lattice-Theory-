# Information Theory 213 — Blueprint

**Priority**: ★★ (binary tree *is* information theory)

---

## 1. Why This Field

ZFC information theory:
- Shannon entropy H(X) = -Σ p log p
- Mutual information I(X;Y)
- Channel capacity, error-correcting codes
- Kolmogorov complexity

Natural emergence in 213:
- **Dyadic tree = binary information tree**
- **each bisection = 1 bit**
- **bisectN n = n bits of information**
- log₂ naturally appears (atomic depth)

## 2. 213-native Emergence

### 2.1 1 bit = 1 bisection

Depth n of dyadic tree = n bits.  Information content naturally
defined:
- log₂(2^n) = n
- atomic prime 2 = bit base

### 2.2 Shannon entropy = path distribution

Distribution p on dyadic tree → entropy = expected path length.
H(X) = -Σ p_i log₂ p_i.

213-native: probability 213 (blueprint 01) + log₂ via bisection
depth.

### 2.3 Mutual information = cohomological

I(X;Y) = H(X) + H(Y) - H(X,Y).
FluxCut's add operation is natural.

### 2.4 Channel = trajectory

Communication channel = mapping of input cut → output cut +
noise.  bisectN with random oracle = noisy channel.

### 2.5 Source coding (Huffman)

Optimal binary code = optimal bisection tree.  213-native
optimization.

### 2.6 Kolmogorov complexity

213's *axiomatic minimality* (Raw axiom 4 clause = minimum
residual) is *the smallest description*.  Kolmogorov complexity
in 213-native form.

## 3. Building Blocks

| Tool | Use |
|---|---|
| `bisectN` | bit sequence |
| `DyadicBracket.expE` | bit count |
| Probability 213 | distribution |
| `partialSum` | entropy computation |
| `IsAntiderivative.integral` | continuous entropy |
| `cutPow 2 n` | 2^n |

## 4. Phase Plan

### Phase IA — Bit + entropy foundations (3-5 commits)

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

First year undergraduate information theory + introductory Kolmogorov.

## 5. Connections to Other Tracks

- **Probability 213**: distribution = information distribution
- **Quantum gravity**: holographic principle (Bekenstein bound)
- **Yang-Mills**: gauge information
- **Cosmology**: ER=EPR, holographic
- **User vision (3)**: removing quantum decoherence = removing information loss

## 6. Open Problems

- **Quantum information** — qubit, von Neumann entropy
- **Channel coding lower bound** — converse theorem
- **AIT (algorithmic info)** — universal Turing machine 213?

## 7. Key Insights (★)

★ **bit = bisection** — 213's dyadic tree is the foundation of information theory.

★ **Shannon entropy = expected bit depth** — bisectN directly applicable.

★ **213 itself is the minimum description** — Raw axiom 4 clause =
Kolmogorov 0-axiom-minimal description.

★ **User vision (3) "remove quantum decoherence"** = information-loss-free
dyadic channel.  213 = deterministic bit + dyadic = natural quantum
alternative.

## 8. First Marathon Command

```
"Start Phase IA.  bitDepth + Shannon entropy on uniform 2^n"
```

