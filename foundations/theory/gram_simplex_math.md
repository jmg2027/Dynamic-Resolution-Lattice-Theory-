# Gram Simplex Geometry — Mathematical Core

**Date:** 2026-04-18
**Scope:** DRLT 의 수학적 기반 — Gram matrix, simplex geometry,
          fractal structure 의 formal 정리.
**Focus:** 물리 응용 (atoms, masses) 이 아니라 **순수 수학적 구조**.

---

## §0. Notation & Setup

- $\mathbb{K} = \mathbb{C}$ (by ch01 Frobenius 유도).
- $d = 5$ (by ch02 atomic decomposition).
- Simplex: $N$ unit vectors $\{\psi_1, \ldots, \psi_N\}$ with
  $\|\psi_i\| = 1$ in $\mathbb{C}^d$.
- **Gram matrix:** $G_{ij} := \langle \psi_i | \psi_j \rangle \in \mathbb{C}$.
- **Properties of $G$:**
  - Hermitian: $G_{ji} = \overline{G_{ij}}$.
  - Diagonal: $G_{ii} = 1$.
  - Positive semi-definite: $\mathbf{c}^\dagger G \mathbf{c} \ge 0$.
  - Rank: $\mathrm{rank}(G) \le d = 5$ (fundamental constraint).

---

## §1. Hinge geometry

**Hinge** = 3-vertex subset $h = \{i, j, k\} \subseteq [N]$.
Total hinges: $\binom{N}{3}$.

**Hinge Gram matrix:**
$$
G_h = \begin{pmatrix}
1 & G_{ij} & G_{ik} \\
\overline{G_{ij}} & 1 & G_{jk} \\
\overline{G_{ik}} & \overline{G_{jk}} & 1
\end{pmatrix}
$$

**Hinge determinant formula** (ch06 eq:detGh):
$$
\det(G_h) = 1 - |G_{ij}|^2 - |G_{jk}|^2 - |G_{ki}|^2
         + 2 |G_{ij}| |G_{jk}| |G_{ki}| \cos \Phi_h
$$
where $\Phi_h = \arg(G_{ij} \cdot G_{jk} \cdot G_{ki})$ 는 holonomy phase.

**Hinge area:** $A_h = \sqrt{\det(G_h)}$ (nonneg due to PSD).

**Key identity (Binet-Cauchy, Lean verified):**
For $N \ge d+1$ vertices in $\mathbb{C}^d$,
$$
\det(G_h) = \sum_{I \subset [d], |I|=3} |\det \Phi_I|^2
$$
where $\Phi$ is the $d \times 3$ matrix of the 3 hinge vertices'
coordinates.  SSS + SST + STT channel decomposition:
$$
1 + 12 + 12 = 25 = d^2 \quad (d=5, (n_S, n_T) = (3,2)).
$$

---

## §2. Regge action

**Definition:**
$$
S = \sum_{h} A_h \cdot \delta_h
$$
where $\delta_h = 2\pi - \sum_{\sigma \supset h} \theta_\sigma$ 는 deficit angle.

**Dynamical Planck constant** (ch07):
$$
\hbar_h = \frac{A_h}{4 \ln 2}.
$$
Scale per hinge: $\hbar_h$ 는 각 hinge 의 local "양자 크기".

**Variational principle:** $\delta S / \delta \psi_i = 0$
는 자기 일관된 $\psi$ 배치 결정.  (ch05, ch10, ATM_056 등 참조)

---

## §3. Rank-5 constraint 의 구조적 함의

### §3.1 Gram matrix rank

$N$ unit vectors in $\mathbb{C}^d$ → $G$ 는 $N \times N$ Hermitian PSD
with $\mathrm{rank}(G) \le d$.

For $N \le d$: generically rank $N$ (full rank, 독립).
For $N > d$: rank는 최대 $d$, 즉 **$N - d$ linear dependencies**.

### §3.2 Linear dependencies

When $N > d$, 최소 $N - d$ 개의 $\psi_i$ 가 다른 $\psi$ 의 선형 결합.
이는 DRLT 에서 **"overlap"** 으로 해석:
$\psi_i$ 가 다른 vector 들의 선형 결합이면, 그 $i$ 는 "독립 vertex"
아니라 **derived** (effective).

### §3.3 Fractal 관점 (§16)

Fractal universe 에서:
- 전체 $N$ vertex (예: $N \sim 10^{75}$)
- 모두 $\mathbb{C}^5$ 에 살음 → rank $\le 5$
- **$N - 5$ 개의 강제 dependency** → self-similar 패턴 (§16.5)

Dependencies 의 구체 패턴은 **fractal 의 recursive 구조** 를 따름 (가설).

---

## §4. Fractal simplex — mathematical definition

### §4.1 Recursive structure

**Base simplex** $\Sigma_0$: $d$ unit vectors $\{e_1, \ldots, e_d\}$
forming orthonormal basis of $\mathbb{C}^d$.

Gram matrix of $\Sigma_0$: $G_0 = I_d$ (identity).

**Recursion $T$:** Each vertex $e_k$ of $\Sigma_0$ "becomes" a
sub-simplex $\Sigma_1^{(k)}$ with $d$ sub-vertices in $\mathbb{C}^d$.

Sub-vertex ansatz (symmetric):
$$
s_i^{(k)} = \alpha \cdot e_k + \beta \cdot \xi_i^{(k)}, \quad i = 1, \ldots, d,
$$
where $\xi_i^{(k)}$ are unit vectors orthogonal to $e_k$, and
$\alpha^2 + \beta^2 = 1$ (normalization).

### §4.2 Scale ratio 조건

Sub-vertex 간 overlap:
$$
\langle s_i^{(k)} | s_j^{(k)} \rangle = \alpha^2 + \beta^2 \gamma,
$$
where $\gamma = \langle \xi_i | \xi_j \rangle$ (for $i \ne j$).

**Symmetric sub-simplex** ($\xi_i$ 가 $(d-1)$-dim 의 equidistant unit
vectors, i.e., $d$-dim 정 simplex 의 vertex 방향): $\gamma = -1/(d-1)$.

For $d = 5$: $\gamma = -1/4$.

**Sub-Gram matrix of $\Sigma_1^{(k)}$:**
$$
G_1^{(k)}_{ij} = \begin{cases} 1 & i = j \\ c & i \ne j \end{cases}
$$
with $c = \alpha^2 + \beta^2 \gamma = \alpha^2 - \beta^2/(d-1)$.

### §4.3 Self-similarity 조건

**Fixed-point recursion:** $T(G_0) = G_1$ 이 self-similar 이려면
$G_1$ 의 "형태" 가 $G_0$ 와 같아야 (rescaling 만 차이).

$G_0 = I$ vs $G_1 = (1-c)I + c J$ (where $J$ is all-ones).

이 두 matrix 는 **형태가 다름** (rank structure 다름):
- $G_0$: full rank $d$, eigenvalues all 1
- $G_1$: eigenvalues $(1 + (d-1)c, 1-c, \ldots, 1-c)$

즉 **$G_1$ 는 $G_0$ 의 rescaling 이 아님** (generically).  Scale-ratio
기반 fractal 은 non-trivial.

### §4.4 대안: Gram-preserving fractal

**새 정의:** $T$ 가 $G$ 의 **상수 배 + identity shift** 를 유지
:  $T$ 가 $G \mapsto \lambda G + (1-\lambda) I$ 형태.

만약 $T(G_0) = G_1 = \lambda I + (1-\lambda) I' = I$ (?) — 자명.

Fractal 은 이런 단순 recursion 이 아닐 수도.

### §4.5 Fulton-MacPherson 구조 (실제 fractal)

FND_011 에 따르면 $FM_N(Gr(3,5))$ 의 Euler characteristic:
$$\chi(FM_N) = 5^N \cdot (N+1)!$$
for $N = 1, \ldots, 5$.

이게 **진짜 fractal 구조**: Fulton-MacPherson **compactification**
는 point 들이 겹칠 때 **bubble** 이 생성 (각 bubble 이 sub-simplex).

**Recursive:** 각 bubble 내부에서 또 겹침 가능 → 또 bubble → 재귀.

FM compactification 은 well-defined 기하학적 대상이고, 이게 DRLT
fractal 의 정확한 수학.  Scale ratio 는 bubble 의 "크기" 에 해당하고,
topology 는 FM 의 blow-up 구조에서 결정.

---

## §5. Binet-Cauchy 재도출 (matrix algebra)

**Claim:** For $\Phi \in \mathbb{C}^{d \times 3}$ (3 column vectors
in $\mathbb{C}^d$),
$$
\det(\Phi^\dagger \Phi) = \sum_{I \subset [d], |I|=3} |\det \Phi_I|^2
$$
where $\Phi_I$ is the $3 \times 3$ sub-matrix of $\Phi$ 의 rows $I$.

**For $d = 5$:** $\binom{5}{3} = 10$ minors.  Channel decomposition
에 의해 $I$ 들을 SSS (0 temporal), SST (1 temporal), STT (2 temporal)
로 분류:
- SSS: $\binom{3}{3}\binom{2}{0} = 1$
- SST: $\binom{3}{2}\binom{2}{1} = 6$
- STT: $\binom{3}{1}\binom{2}{2} = 3$

**$c$-weighting** (c = n_T = 2):
- SSS weight 1 → total 1
- SST weight $c^1 = 2$, 6개 → total 12
- STT weight $c^2 = 4$, 3개 → total 12
$$ 1 + 12 + 12 = 25 = d^2. $$

이 수식 은 Lean `BinetCauchy.lean` 에서 형식 증명됨.

---

## §6. $\alpha_{\rm GUT}$ 의 수학적 유도 (재구성)

From §5:  $d^2 = 25$ channel, 각 channel 이 solid-angle propagator
$D(n) = 1/n^{n_S - 1} = 1/n^2$ 로 전파.

$$ \frac{1}{\alpha_{\rm GUT}} = d^2 \cdot \sum_{n=1}^\infty \frac{1}{n^2}
= d^2 \cdot \zeta(2) = \frac{25 \pi^2}{6}. $$

$\alpha_{\rm GUT} = 6/(25\pi^2) \approx 0.02433$.

**FND_040/041 감사:** 세 경로 (Binet-Cauchy + Basel, GUE sine kernel,
Euler coprime density) 가 모두 이 공식.  Path 1 ≡ Path 3 via Euler
identity $\zeta(2) = \sum 1/n^2 = \prod_p (1-1/p^2)^{-1}$.  Path 2
는 heuristic consistency check.

**수학적으로 엄밀한 유도:** Path 1 (조합 + Basel) 이 가장 깔끔.
Lean 에서 $\alpha_{\rm GUT}$ 공식 자체는 formal 유도 가능.

---

## §7. Swap involution 과 FND_012, FND_038

**FND_012 (이미 Lean 형식):** Repeated atom pair 에 대한 swap σ
가 σ-invariance ↔ vector-like 대응을 formalize.

**FND_038 swap tower (Lean):**
$T: {\rm AliveDim} \to \mathbb{N}$ with $T(d) = 2\lceil a/2 \rceil + 3 \lceil b/2 \rceil$,
iterating any alive $d = 2a + 3b$ (with $a, b \ge 1$) down to 5.

**Fractal 해석 (§16):** 각 level 의 $T$ 적용이 한 step.  모든 alive
시작점이 유한 step 내 $d = 5$ 로 수렴.  이게 fractal 이 "base (3,2)"
로 terminate 하는 수학적 이유.

**Level 상한:** $T$ 적용이 $O(\log d)$ step 이라서, fractal depth
는 $O(\log N)$ for total vertex count $N$.

---

## §8. 열린 수학 질문

### §8.1 Scale ratio $\lambda$ 의 유도

Fractal sub-simplex 의 "크기 비" $\lambda$ 는 다음 중 어느 것:
- (a) $\lambda = 1/\sqrt{d} = 1/\sqrt{5}$ from orthogonalization ($\alpha = 1/\sqrt{5}$ case in §4)?
- (b) $\lambda$ from FM blow-up convention?
- (c) $\lambda$ from $\hbar$ ratio (ch07)?

현재 각 후보의 결과가 다름.  일관된 DRLT 유도 필요.

### §8.2 $d = 5$ 의 유일성 via fractal

ch02 에서 atom = {2, 3} → $d = 5$.  Fractal 관점:
- $d = 5$ 가 fractal recursion 의 **fixed point** (FND_038 확증됨)
- 다른 $d$ 는 terminate 안 되거나 다른 fixed point 도달

Fractal 관점의 $d = 5$ 유일성 proof 는 FND_038 이 제공.

### §8.3 Hinge pattern 의 algebraic 분류

Simplex 의 10 hinge 는 AAA/AAB/ABB/BBB 로 분류 (ch06).  각 pattern
의 Gram 구조는:
- AAA: 3 spatial vertices → det 일반적으로 > 0
- AAB: 2 spatial + 1 temporal → det = 1 - 2ε² for standard setup
- ABB: 1 spatial + 2 temporal → det = 1 - ε² (one coupling)
- BBB: 3 temporal → det = 0 (n_T = 2 < 3)

BBB 의 degeneracy 는 $n_T = 2$ 의 rank 제약 (ℂ² 에 3 vector 불가능).
이건 **정리**: $n_T = 2$ 에서 BBB hinge 는 자동 soft.

### §8.4 Global pseudo-rank 5 의 수학적 구조

$N$ vertex 의 Gram matrix 의 rank 5 구조 를 이해:
- 5개 주 eigenvector (principal components)
- $N - 5$ 개의 dependent combinations
- Dependencies 의 self-similar pattern (fractal)

구체적 수학: **Principal subspace projection**.
$G = \Psi^\dagger \Psi$ where $\Psi \in \mathbb{C}^{5 \times N}$.
$\Psi$ 는 각 vertex 의 coordinate matrix.
Dependencies = $\ker(\Psi)$ 의 structure.

---

## §9. Lean 형식화 가능성

**이미 formalized:**
- `Core.lean`: atoms = {2, 3}
- `BinetCauchy.lean`: 1 + 12 + 12 = 25
- `ChiralChannels.lean`: $\mathbb{C}^5 = \mathbb{C}^3 \oplus \mathbb{C}^2$ 유일
- `SwapAnnihilation.lean`: σ-invariance ↔ vector-like
- `SwapTower.lean`: $T$ 의 $d=5$ 고정점

**Formalizable (다음 후보):**
- (a) Gram matrix PSD + rank 정리 (기본 linear algebra)
- (b) Hinge det formula (3×3 matrix algebra)
- (c) Fractal simplex recursion (abstract structure)
- (d) $\alpha_{\rm GUT}$ = $1/(d^2 \zeta(2))$ formula (숫자)

---

## §10. 다음 단계

**이 문서의 목적:** DRLT 의 Gram simplex 수학을 **순수 수학 언어**
로 재조직.  물리 응용 (atoms, masses) 은 별도.

**Immediate TODO:**
1. §4 fractal 정의를 완성 (FM compactification 접목)
2. §8.1 scale ratio $\lambda$ 의 후보들 수치 비교
3. §9 (a)(b) Lean 형식화 (기본 matrix algebra)

**Longer-term:**
- Fractal simplex 의 Hausdorff dimension 의 정확한 값
- $d = 5$ 의 fractal 관점 유일성 증명 (FND_038 formalization 확장)
- $\alpha_{\rm GUT}$ formula 의 Lean 증명

---

**작성 시작 (2026-04-18):** 사용자 요청 "atom 말고 Gram simplex 기하학
수학으로".

---

## §11. 213 Foundation 과의 연결 (2026-04-18 발견)

**사용자 알림:** `claude/continue-handoff-213-fC38X` 브랜치 에 213 framework
의 광범위한 연구 (574 commits).  이게 Gram simplex 의 **더 깊은 기반**.

### §11.1 213 의 핵심 primitive

**사용자 최종 formulation (`CLEAN_PRIMITIVE.md`):**
> "두 객체 사이에 관계가 있음."
>
> - 두 객체 = 두 개의 distinct positions (구조적).
> - 같은 객체를 두 position 에 넣을 수 없음.
> - 따라서 1/1 은 existence 질문 자체가 없음.

**Lean 구현 (`Clean213.lean`, 0 sorry):**
```lean
inductive Raw where
  | object   : Fin 3 → Raw
  | relation : Raw → Raw → Raw

inductive Reachable : Raw → Prop where
  | base : (i : Fin 3) → Reachable (.object i)
  | step : Reachable x → Reachable y → x ≠ y →
           Reachable (.relation x y)
```

**핵심:** `relation x x` 는 syntax 상 가능하나 Reachable 아님.
즉 "same input" 은 정보 없음 → primitive 아님.

### §11.2 DRLT Gram 과의 동형 구조

**DRLT 쪽:**
- $G_{ij} = \langle \psi_i | \psi_j \rangle$
- $G_{ii} = 1$ (trivial diagonal, 정보 없음)
- 정보 는 $G_{ij}$ for $i \ne j$ 에만

**213 쪽:**
- `relation x y` between distinct objects
- `relation x x` not Reachable (정보 없음)
- 정보 는 distinct pair 에만

**정확한 대응:**
| DRLT | 213 |
|------|-----|
| Vertex $\psi_i$ | `object i` (if base) or Reachable Raw |
| $G_{ij}$ (i≠j) | `relation x y` (x ≠ y) |
| $G_{ii}$ = 1 | `relation x x` — not Reachable |
| Gram structure | Reachable 의 결합 구조 |
| $\mathbb{C}^d$ valued | Just structural, no numeric value in 213 |

**차이:** DRLT 는 $\mathbb{C}$ valued (숫자), 213 은 structural only.

### §11.3 Lens framework: Gram 의 "view"

**213 Lens (`BOOK_213.md §6`):**
```lean
structure Lens (α : Type) where
  atomValue : Fin 3 → α
  combine   : α → α → α
```
각 `Lens` 는 Raw 구조를 α-valued "view" 로 보여줌.

**DRLT 로 번역:**
- Raw 구조 → DRLT Gram matrix
- Different lenses → different projections of G
- Examples:
  - **Spatial lens:** $G$ 의 AA block (nn_S = 3)
  - **Temporal lens:** $G$ 의 BB block (n_T = 2)
  - **Full lens:** 전체 $\mathbb{C}^d$ structure
  - **Rank lens:** eigenvalue spectrum
  - **Hinge lens:** $\det(G_h)$ per 3-vertex subset

각 "view" 는 **DRLT 공리 의 lens-based 재해석**.

### §11.4 Provability Classifier (213 Stage 3)

**213 framework (`RESEARCH_VISION.md`):**
명제 φ, lens L 에 대해:
- **ProvableIn L φ:** ∀ Reachable x, φ x
- **RefutableIn L φ:** ∃ Reachable x, ¬ φ x
- **IndependentIn L φ:** ∃ x y, L.equiv x y ∧ φ x ∧ ¬ φ y
- **Respecting L φ:** ∀ x y, L.equiv x y → (φ x ↔ φ y)

**DRLT 적용:**
- φ = "$\det(G_h) > 0$" (hinge 가 non-degenerate 인가)
- Spatial lens 에서 ProvableIn? RefutableIn?
- Full lens 에서 다른 결과?

**Gödel-style 통찰:** 어떤 DRLT 주장은 특정 lens 에서 **independent**
— 즉 lens 가 너무 coarse 해서 결정 못 함.  이게 BBB hinge 의 det=0
degeneracy 와 연결?  (n_T=2 에서 ℂ²-rank 제약으로 BBB 가 degenerate)

### §11.5 Hierarchy of DRLT foundations

이제 DRLT 의 구조 layer 가 명확:

```
Level 0: 213 (distinct-pair primitive)          [foundational]
         ↓
Level 1: DRLT relation axiom                    [specialize to ℂ values]
         "N points with pairwise relations G_ij ∈ ℂ"
         ↓
Level 2: Gram algebra                           [linear structure]
         Hermitian, PSD, rank ≤ 5
         ↓
Level 3: Simplex geometry                       [topological structure]
         Hinges, det, Regge action
         ↓
Level 4: Physical applications                  [interpretation]
         Atoms, masses, cosmology
```

각 layer 는 아래 layer 의 **specialization** (additional structure).

### §11.6 이 insight 의 의미

1. **DRLT 는 213 의 specific instance**:
   - 213 의 "two distinct objects" → DRLT 의 "two distinct vertices"
   - 213 의 "relation object" → DRLT 의 $G_{ij}$ value
   - 213 의 Reachable → DRLT 의 valid Gram structures

2. **Gram simplex 수학 은 213 위에서 concrete linear algebra**:
   - 213: pure structural
   - Gram simplex: add $\mathbb{C}$ valuation + rank-5 constraint

3. **Lens framework 이 DRLT 의 다양한 "projection" 분석**:
   - 각 sub-project (atoms, nuclear, ...) 가 specific lens 의 view
   - Independent claims = lens 가 너무 coarse

4. **Future Lean 형식화 기반:**
   - 213 가 이미 Lean 에 있음 (Clean213.lean 0 sorry)
   - DRLT 는 213 위에 linear algebra 추가로 formalize 가능
   - 단계적 formalization path 가능

### §11.7 다음 작업

1. **213 을 메인 branch 에 병합** (또는 reference)
2. **DRLT 공리 를 213 lens 로 formal 표현**
3. **Gram simplex 의 Lens 분류** (spatial/temporal/rank/hinge views)
4. **ProvabilityClassifier 를 DRLT 주장에 적용** — 어떤 것이 독립?

**즉각 benefit:**
- DRLT 수학 코어 가 213 의 concrete specialization 임이 명확
- 전체 프로젝트의 mathematical architecture 가 clean 해짐
- 중복 foundational 작업 피함 (213 은 이미 있음)

---

**사용자 제안 (2026-04-18):** "213 연구 가 꽤 됐는데 도움 될까 싶어서 알려줌"
→ **대답: 매우 도움됨.**  Gram simplex math 의 foundational backbone 이
이미 formalized 되어 있음을 확인.  이 문서의 §0-§10 은 Level 2-3 (Gram
algebra + simplex geometry) 다룸.  Level 0 (213) 와 Level 1 (DRLT axiom)
는 이미 별도 foundation.
