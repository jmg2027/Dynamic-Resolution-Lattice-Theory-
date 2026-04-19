# Multi-Electron Atoms in DRLT — Theoretical Framework

**Status:** Theory draft 2026-04-18 (Mingu's challenge).
**Goal:** "심플렉스 네트워크 그려서 선따라 찍찍 계산" 을 정확히 구현
        하기 위한 이론 정립.  공리에서 직접 IE 까지 — σ_recipe 없이.

**Outline:**
- §1. 기존 정립된 base: H + He (ch10)
- §2. ATM_058 가 왜 실패했나
- §3. 새 framework: shared-A multi-simplex network
- §4. 일반 원자의 simplex 그래프
- §5. 계산 절차 (선따라 찍찍)
- §6. Screening 의 기하학적 기원
- §7. IE 추출 공식
- §8. 검증 계획

---

## §1. 기존 정립된 base (ch10)

### 1.1 Hydrogen = AAAB tetrahedron

ch10 의 H 그림:
```
                      A₃ (q3, spatial)
                      /\
                     /  \
                    /    \
                   /      \
                  /        \
                A₁----------A₂   (3 A = proton's 3 quarks)
                  \   /\   /
                   \ /  \ /
                    X    X       (3 AAB hinges = electron-proton EM bonds)
                   / \  / \
                  /   \/   \
                 /    /\    \
                /    /  \    \
               /    /    \    \
              -----+      +-----
                   B₁              ← electron
                   
              [B₂ vacant slot — outside this tetrahedron]
```

- **4 vertices:** {A₁, A₂, A₃, B₁} = AAAB face (4-element subset of ∂Δ⁴ vertex set)
- **Hinges (triangles) within:** AAA (1) + AAB (3) = 4 hinges
- **B₂ outside:** vacant 5th vertex

**IE 공식** (ch10 Thm):
$$\sum_{h \in \text{AAB}} (1 - \det G_h) = 2\alpha^2$$
$$\boxed{\text{IE}(H) = \frac{m_e c^2 \cdot 2\alpha^2}{n_B^2} = \frac{m_e \alpha^2}{2} = 13.606\;\text{eV}}$$

ε = α/√n_A = α/√3 (electron-proton coupling).

### 1.2 Helium = fully-occupied ∂Δ⁴

```
                      A₃
                      /\
                     /  \
                    /    \
                   /      \
                  /        \
                A₁----------A₂
                /\          /\
               /  \        /  \
              B₂   \      /   B₁    ← BOTH B = electrons
                \   \    /   /
                 \   \  /   /
                  \   \/   /
                   \  /\  /
                    \/  \/
                    /----\
```

- **5 vertices:** {A₁, A₂, A₃, B₁, B₂} = full ∂Δ⁴
- **Hinges:** AAA (1) + AAB (6) + ABB (3) = 10
- **모든 5 face active** (AAAB ×2 + AABB ×3)

$$\boxed{\text{IE}(He) = 2R_y(1 - c^2 \alpha_{GUT}) = 24.565\;\text{eV (0.02\%)}}$$

여기까지가 진짜 DRLT — 한 simplex 안에서 모든 게 됨.

---

## §2. ATM_058 가 왜 실패했나 (진단)

ATM_058 의 approach:
- 6 vertices = 3 A (고정) + 3 electrons + 1 vacuum
- **한 개의 ∂Δ⁵ 안에** 모든 것 넣음
- 각 electron 에 독립 ε_k 부여하고 simultaneous variation

실패 원인 (Li: 예측 11307 eV vs 관측 5.392 eV, +209,602% error):

**문제 1: n_B = 2 per simplex 위반**
- DRLT 공리: 각 ∂Δ⁴ simplex 는 3 A + 2 B 로 (3,2) decomposition
- 3 electron 을 한 simplex B-slot 에 넣으면 B-count = 3 > n_B = 2
- 이는 **simplex 구조 자체를 깨뜨림** (atom 은 이제 "∂Δ⁵ 의 한 가짓수" 가 아님)

**문제 2: "shell" 개념 부재**
- 1s² 과 2s¹ 은 물리적으로 다른 spatial distribution 이어야 함
- ATM_058 은 3 electron 을 "같은 공간" 에 몰아넣음 → 모두 nucleus 근방
- 결과: 모든 ε_k 가 ~α 규모 → 예측 IE ~ Z²·Ry 수준 (매우 큼)

**문제 3: 계산 방법은 맞지만 구조가 틀림**
- `ψ → G → hinge det → IE` 자체는 올바름
- 문제는 ψ 를 어떻게 **배치** 하느냐

**결론:** ATM_058 은 "계산 방법 (Regge variational) 은 맞으나
**simplex 네트워크 구조** 를 잘못 그림".

---

## §3. 새 framework: Shared-A Multi-Simplex Network

### 3.1 핵심 원칙

**"원자 = 공유된 3 A-vertices + 여러 simplex"**

모든 electron-쌍 이 한 ∂Δ⁴ simplex 를 형성.  모든 simplex 는
같은 3 A-vertices (= nucleus 의 3 quark structure) 를 공유.

각 simplex 는 독립 ε (coupling) 을 가짐:
- 내부 shell (nucleus 가까움): ε 크다 (강한 binding)
- 외부 shell (멀다): ε 작다 (약한 binding)

### 3.2 Shell = simplex 배당

각 **orbital pair** = 1 simplex (3 A + 2 B).
Unpaired electron = simplex with 1 B_e + 1 B_vac.

| Orbital | Simplex count | Electron count |
|---------|---------------|----------------|
| 1s | 1 | 0, 1, 2 |
| 2s | 1 | 0, 1, 2 |
| 2p_x, 2p_y, 2p_z | 3 | 0-6 |
| 3s | 1 | 0, 1, 2 |
| 3p | 3 | 0-6 |
| 3d | 5 | 0-10 |
| ... | ... | ... |

**원자 = ∑ simplices (각 orbital 마다 하나)**

### 3.3 원자별 그림

**H (Z=1):** 1s¹
```
   3A ---+--- 1s simplex: 3A + B₁_e + B₂_vac
```
= 전통적 AAAB face (ch10).

**He (Z=2):** 1s²
```
   3A ---+--- 1s simplex: 3A + B₁_e + B₂_e
```
= 전통적 full ∂Δ⁴ (ch10).

**Li (Z=3):** 1s² 2s¹
```
   3A ---+--- 1s simplex: 3A + B₁_e + B₂_e    (ε_1s ≈ α/√n_A, 강)
         |
         +--- 2s simplex: 3A + B₃_e + B_vac   (ε_2s ≈ α/? , 약)
```
**핵심:** 두 simplex 가 3 A 를 공유 (nucleus 가 공통).  B-vertices
는 모두 독립.  각 simplex 의 ε 가 독립 변수.

**Be (Z=4):** 1s² 2s²
```
   3A ---+--- 1s simplex: 3A + B₁_e + B₂_e
         +--- 2s simplex: 3A + B₃_e + B₄_e
```

**B (Z=5):** 1s² 2s² 2p¹
```
   3A ---+--- 1s simplex: 3A + B₁_e + B₂_e
         +--- 2s simplex: 3A + B₃_e + B₄_e
         +--- 2p_x simplex: 3A + B₅_e + B_vac
```

**C (Z=6):** 1s² 2s² 2p²  (Hund's rule → 2개 2p 에 1개씩)
```
   3A ---+--- 1s simplex
         +--- 2s simplex
         +--- 2p_x simplex: 3A + B_e + B_vac
         +--- 2p_y simplex: 3A + B_e + B_vac
```
= 4 simplices, 총 vertex = 3 + 2·4 = 11.

**Ne (Z=10):** 1s² 2s² 2p⁶
```
   3A ---+--- 1s simplex     (2 e⁻)
         +--- 2s simplex     (2 e⁻)
         +--- 2p_x simplex   (2 e⁻)
         +--- 2p_y simplex   (2 e⁻)
         +--- 2p_z simplex   (2 e⁻)
```
= 5 simplices, 3 + 10 = 13 vertices.

### 3.4 왜 "3 A 공유" 가 맞는가

세 가지 논리:

**(a) Nucleus 의 유일성:** 각 원자는 **하나의** nucleus 를 가짐.
A₁A₂A₃ = 3 quarks of proton/nucleus.  모든 electron 이 같은
nucleus 를 느낌 → A 는 공유.

**(b) Spatial 3D 의 공유:** n_S = 3 공간 방향은 원자 전체가 공유.
각 electron 의 "공간적 위치" 가 다를 수 있으나, 공간 축 자체는 동일.
→ A₁, A₂, A₃ 는 **공간 축** 을 정의하고 모든 simplex 공유.

**(c) 각 simplex = 한 orbital:** Aufbau 에서 각 orbital 은
독립적 wave function ψ_orbital.  DRLT 에서 각 simplex 가 자기 ε 를
가짐 = 각 orbital 의 binding energy.

### 3.5 Simplex 사이 hinge?

**중요 질문:** 두 simplex 사이에 hinge (cross-shell triangle) 가
있는가?

두 simplex 가 3 A 를 공유하므로, 예를 들어:
- Simplex 1 (1s): {A₁, A₂, A₃, B_1s¹, B_1s²}
- Simplex 2 (2s): {A₁, A₂, A₃, B_2s¹, B_2s²}

이 두 집합의 합집합: {A₁, A₂, A₃, B_1s¹, B_1s², B_2s¹, B_2s²} = 7 vertices.

이 7-vertex 집합에서 만들 수 있는 triangle 중 일부:
- {A₁, A₂, A₃}: 완전 A, 하나. (공유되는 AAA hinge)
- {A_i, A_j, B_1s}: AAB, 3·2 = 6개 (1s 기여)
- {A_i, A_j, B_2s}: AAB, 3·2 = 6개 (2s 기여)
- {A_i, B_1s, B_2s}: **ABB with mixed B** — **cross-shell!**
- {B_1s, B_2s, B_2s'}: BBB, 대부분 degenerate

**Cross-shell ABB** = 다른 shell 의 B-vertices 가 만드는 hinge.
이게 **screening 의 기하학적 origin** (§6 참고).

---

## §4. 일반 원자의 simplex 그래프

### 4.1 표기법

원자 = 그래프 $\mathcal{A}_Z$:
- **Vertices:** $\{A_1, A_2, A_3\} \cup \{B_{ok}\}_{o,k}$ where
  $o$ = orbital index, $k \in \{1, 2\}$ = intra-orbital index
- **Simplices:** 각 orbital $o$ → one ∂Δ⁴ simplex
  $\sigma_o = \{A_1, A_2, A_3, B_{o,1}, B_{o,2}\}$
- **Edges:** 모든 vertex 쌍 (fully connected; Gram matrix 가 모든 쌍 정의)

### 4.2 전체 Gram matrix

$N_{\text{tot}} = 3 + 2 N_{\text{orb}}$ vertices.
Gram matrix $G \in \mathbb{C}^{N_{\text{tot}} \times N_{\text{tot}}}$:

- **AA block:** 3×3, 고정 (n_S = 3 spatial).  Values from ch05 variational:
  $|A_i \cdot A_j| = $ determined by symmetric n_S=3 frame.
- **AB blocks (per orbital):** 3×2, each orbital has own coupling ε_o.
  $\langle A_i | B_{o,k} \rangle = \varepsilon_o / \sqrt{n_A}$ (가정; 정확한 공식 §5).
- **BB within orbital:** 2×2 for each orbital.
  $\langle B_{o,1} | B_{o,2} \rangle = $ Pauli-suppressed (orthogonal?).
- **BB cross-orbital:** 2×2 for each orbital pair.
  $\langle B_{o,k} | B_{o',k'} \rangle = $ **orbital overlap** (small, related to screening).

### 4.3 Rank constraint

전체 Gram matrix G 는 ψ_i ∈ ℂ⁵ 이므로 rank(G) ≤ 5.
$N_{\text{tot}} > 5$ 일 때 (즉 Z ≥ 3 원자): G 는 rank-deficient.
이는 **실제 수학적 제약** — 3 + 2 N_orb ≤ 5 는 N_orb ≤ 1 일 때만.
N_orb ≥ 2 (Li 부터) 는 rank 제약 → fold / identification 필요.

**이것이 ATM_058 의 숨겨진 문제:** 6-vertex 시스템도 이미 rank-5 제약
아래 있었지만, 모든 ψ 를 독립적으로 취급.

**정직한 처리:** ℂ⁵ 안에서 최적 배치 찾는 variational.  일부 overlap
이 필연적 (rank deficit).  이게 exactly **Pauli exclusion 의
기하학적 원천**.

---

## §5. 계산 절차 — "선 따라 찍찍"

### Step 0. 입력
- 원자 번호 Z → electron configuration (Aufbau): 1s^{n₁s} 2s^{n₂s}
  2p^{n₂p} 3s^{n₃s} 3p^{n₃p} 4s^{n₄s} 3d^{n₃d} ...
- Orbital 목록 $\{o_1, o_2, \ldots, o_{N_{\text{orb}}}\}$
- 각 orbital 의 occupation $n_o$ ∈ {0, 1, 2}

### Step 1. Vertex 배치 (그림 그리기)

- 3 A-vertices: ∂Δ⁴ 의 standard symmetric 위치 (ch05 에서 고정)
- 각 orbital $o$ 마다 2 B-vertices: $B_{o,1}, B_{o,2}$
  - Occupation $n_o = 2$: 둘 다 electron
  - $n_o = 1$: 하나는 electron, 하나는 vacuum
  - $n_o = 0$: 둘 다 vacuum (simplex 존재하나 inactive)

### Step 2. ψ vector 파라미터화

**A-vertices** (spatial frame, fixed):
$$A_1 = |e_1\rangle, A_2 = |e_2\rangle, A_3 = |e_3\rangle$$
(standard basis of ℂ³ sub-block)

**B-vertices** (orbital-specific):
각 orbital $o$ 에는 coupling parameter $\varepsilon_o$.
$$B_{o,k} = \varepsilon_o \hat{n}_o^{(k)} + \sqrt{1 - \varepsilon_o^2} |e_{4+k \mod 2}\rangle$$
where $\hat{n}_o^{(k)}$ is a unit vector in the A-subspace (specific
to orbital, e.g. 2p_x 는 x-direction).

- $\varepsilon_o = 0$: B 가 순수 temporal ($\mathbb{C}^2$)
- $\varepsilon_o = 1$: B 가 순수 spatial (A 근처)
- Small $\varepsilon_o$: 약한 binding (far electron)
- Large $\varepsilon_o$: 강한 binding (close electron)

### Step 3. Gram matrix 구성

$G_{ij} = \langle \psi_i | \psi_j \rangle$ for all vertex pairs.
$N_{\text{tot}} \times N_{\text{tot}}$ matrix.

### Step 4. Hinge 열거 (선 따라 찍찍)

모든 triangle (i,j,k) 가 hinge.  Classify:

- **AAA (1):** {A₁, A₂, A₃}.  구조 공통, 변하지 않음.
- **AAB (intra-orbital):** {A_i, A_j, B_{o,k}} for each orbital $o$.
  총 3·2·$N_{\text{orb}}$ = 6·$N_{\text{orb}}$ hinges.
- **ABB (intra-orbital):** {A_i, B_{o,1}, B_{o,2}} for each $o$.
  총 3·$N_{\text{orb}}$.
- **ABB (cross-orbital):** {A_i, B_{o,k}, B_{o',k'}} for $o \ne o'$.
  이것이 **cross-shell coupling**, screening 의 기원.
- **BBB (intra-orbital):** {B_{o,1}, B_{o,2}, B_{o,?}} — B only 2 개
  per orbital 이므로 하나의 orbital 안에서 BBB 불가능.
- **BBB (cross-orbital):** 다른 orbital B 들로 만든 triangle.
  대부분 degenerate (∵ rank ≤ 2 in temporal sector? 아니면 ≤ 2 in
  some sub-block).  계산 필요.

### Step 5. Hinge 별 det(G_h) + deficit angle

각 hinge $h$:
$$A_h = \sqrt{\det(G_h)}$$
$$\delta_h = 2\pi - \sum_{\sigma \supset h} \theta_\sigma$$

여기서 $\sigma$ 는 $h$ 를 포함하는 simplex (tetrahedron 이상).
Intra-orbital hinges: 해당 simplex 만 기여 → $\delta_h$ 단순.
Cross-orbital hinges: 여러 simplex 가 공유하는 $h$ 는 각각 기여.

### Step 6. Regge action

$$S_{\text{total}} = \sum_{h} A_h \, \delta_h$$

**변수:** orbital 별 coupling $\{\varepsilon_o\}_{o}$
(전체 $N_{\text{orb}}$ 개의 independent parameter).

### Step 7. Variational extremum

$\delta S / \delta \varepsilon_o = 0$ for all $o$:
$$\left. \frac{\partial S}{\partial \varepsilon_o} \right|_{\varepsilon^*} = 0$$

Numerical: scipy.optimize 로 $\varepsilon^*$ 찾기.
중요: 안장점 vs 최대 vs 최소 check.

### Step 8. IE 추출

$$\text{IE}(Z) = E_{\text{ion}}(Z-1) - E(Z)$$
$$E(Z) = S(\text{atom with } Z \text{ electrons, } \varepsilon^*)$$
$$E_{\text{ion}}(Z-1) = S(\text{highest orbital 1 electron 제거, re-optimize})$$

**Normalization:** $S$ 가 dimensionless.  에너지로 변환:
$$E = S \times \frac{m_e c^2}{n_B^2}$$
(H 의 공식 $IE(H) = m_e c^2 \cdot 2\alpha^2 / n_B^2$ 에서
$S = 2\alpha^2$ 이면 맞음.)

---

## §6. Screening 의 기하학적 기원 (σ 없이 나오는 이유)

### 6.1 주장

"Screening constants 는 cross-orbital ABB hinge 의 det 값에서
자동으로 나온다.  별도 fit 필요 없음."

### 6.2 직관

Inner electron (1s) 이 nucleus 에 가까움 → ε_1s 크다.
Outer electron (2s) 이 nucleus 에서 멀음 → ε_2s 작다.
**Cross-shell ABB** {A_i, B_1s, B_2s} 의 det 은:
- $|A_i|^2 = 1$
- $|B_{1s}|^2 = 1$, $|B_{2s}|^2 = 1$
- $|\langle A_i | B_{1s} \rangle| = \varepsilon_{1s}/\sqrt{n_A}$
- $|\langle A_i | B_{2s} \rangle| = \varepsilon_{2s}/\sqrt{n_A}$
- $|\langle B_{1s} | B_{2s} \rangle| = $ **cross-orbital overlap**

Cross-orbital overlap $\langle B_{1s} | B_{2s} \rangle$ 은 두
orbital 의 spatial extent 차이 를 반영.  Pauli orthogonality 에
가깝지만 (0 에 근접), small non-zero 값을 가짐.

### 6.3 구체 예측: σ_1s = ?

Z=3 (Li) 에서 외부 (2s) electron 이 느끼는 effective coupling:

S 에 ε_2s 로 미분:
$$\frac{\partial S}{\partial \varepsilon_{2s}} = \sum_h \left(\frac{\partial A_h}{\partial \varepsilon_{2s}} \delta_h + A_h \frac{\partial \delta_h}{\partial \varepsilon_{2s}}\right) = 0$$

Intra-2s hinges: ε_2s 에만 의존.
Cross-shell hinges: ε_1s, ε_2s, cross-overlap 모두에 의존.

Variational extremum 에서 효과적으로:
$$\varepsilon_{2s}^* = \varepsilon_0^{(2s)} \cdot (1 - \sigma_{\text{geom}})$$

여기 $\sigma_{\text{geom}}$ 은 **cross-shell hinge 의 기하학적 효과**
로부터 나오는 값.  Fit 아니라 variational 결과.

### 6.4 atoms/CLAUDE.md 의 σ_recipe 가 맞을 가능성

기존 σ_recipe (예: σ_1s = 7/8 = 1 - n_S/(d²-1)) 이 **이 geometric
variational 결과** 의 **닫힌 형태 근사일 가능성** 이 있음.
구체적으로:
- $n_S/(d^2-1) = 3/24 = 1/8$ = spatial dimension / adjoint dimension
- 이는 **SU(5) adjoint rep 의 spatial 비율**
- Cross-shell hinge variational 에서 자연스럽게 나올 수 있음

**확인 필요:** cross-shell ABB hinge 의 det 을 extremize 하면 정말
σ_1s = 7/8 이 나오는가?  이게 검증되면 atoms/ 의 σ_recipe 는
"fit" 이 아니라 "geometric variational 결과의 닫힌 형태" 로 승격됨.

### 6.5 현재 상태

**가설:** σ_recipe 는 geometric variational 의 shortcut 이다.
**증명:** 직접 variational 계산 후 σ_recipe 값과 match 확인 필요.
**만약 match:** atoms/ 복권.  σ 값 이 derivation 의 공식 축약.
**만약 mismatch:** σ_recipe 는 여전히 fit.  새 solver 필요.

---

## §7. IE 추출 공식 — 구체 버전

### 7.1 H 재검증 (sanity check)

H 의 Regge:
- 1 simplex (1s), occupation (1, 0)
- ε_1s = α/√n_A = α/√3 (ch10 기성)
- 3 AAB hinges within simplex, 1 AAA, 3 ABB with vacuum

Compute:
$$S_H = S_{AAA} + 3 \cdot S_{AAB}(\varepsilon_{1s}) + 3 \cdot S_{ABB,\text{vac}}(\varepsilon_{1s})$$

AAB 기여: $\sum (1 - \det) = 2\alpha^2$.
$S_H - S_H^+ = 2\alpha^2 \cdot \delta_h$ (deficit angle 보정).
$\text{IE}(H) = S \cdot m_e c^2 / n_B^2 = 13.606$ eV ✓.

### 7.2 He sanity check

He: 1 simplex (1s), occupation (2, 0).
추가 ABB (intra-orbital, B_1, B_2 가 both electrons) hinges 활성화.

Compute similarly.  IE(He) = 24.565 eV should drop out.

### 7.3 Li 진짜 예측 (no σ)

Li: 2 simplices (1s 2s), occupation (2, 1) + (1, 0).
- ε_1s: 내부, 강함.  Variational 에서 nucleus 가까이.
- ε_2s: 외부, 약함.  Variational 에서 멀게 배치.
- Cross-shell ABB hinges: ε_1s · ε_2s · cos(angle) 꼴 기여.

Extremize S(ε_1s, ε_2s).  두 orbital 독립 최적화.

**핵심:** ε_2s 의 최적값이 "내부 shell 존재" 때문에 작게 나와야 함.
이게 기하학적 screening.

$$\text{IE}(Li) = S(Li) - S(Li^+) = [\text{2s simplex 기여}]$$
$$= \varepsilon_{2s}^{*2} \times [\text{hinge sum}] \times \frac{m_e c^2}{n_B^2}$$

**관측 5.392 eV** 와 비교.  만약 맞으면 σ_recipe 불필요.

### 7.4 일반 공식

$$\text{IE}(Z) = \left[ S(\varepsilon^*(Z)) - S(\varepsilon^*(Z-1)) \right] \cdot \frac{m_e c^2}{n_B^2}$$

Where $\varepsilon^*(Z)$ is the variational minimum (or stationary
point) over all orbital couplings, with proper occupation for atom Z.

---

## §8. 검증 계획 (단계별)

### Stage 1: Sanity (H + He)
- 새 framework 의 single-simplex version 이 ch10 결과와 동일한지 확인
- H: 13.606 eV exact 재현
- He: 24.565 eV (0.02%) 재현
- **이 단계 통과 없으면 아무것도 못 함**

### Stage 2: Li (첫 multi-simplex)
- 2 simplex (1s + 2s), 3 A 공유
- ε_1s, ε_2s 독립 variation
- 예측 IE(Li) 를 관측 5.392 eV 와 비교
- σ_recipe 은 **사용 안 함** — pure geometric variational

**세 가지 가능한 결과:**
1. **IE(Li) ≈ 5.39 eV (within 5%)**: 이론 승리.  σ_recipe 는
   이 framework 의 약식 표현.
2. **IE(Li) ≈ 5.39 × (1 + const)**: 근접하나 체계적 오차.
   Cross-shell coupling 공식 refine 필요.
3. **IE(Li) 가 관측과 orders of magnitude 차이:** framework 자체
   재검토.  Shell 개념 자체가 DRLT 에 없을 수도 (더 근본적인 구조
   필요).

### Stage 3: Period 2 (Be ~ Ne)
Li 성공 시 Be, B, C, N, O, F, Ne 예측.
관측값과 비교, median % error 계산.
atoms/ 의 기존 2.9% median (with σ_recipe) 과 비교:
- 새 framework (no σ) 가 ≤ 2.9% → 승.
- > 10% → σ_recipe 가 더 나은 approximation.

### Stage 4: Period 3+
성공 시 Na~Ar, K+, etc.  118 elements full scan.

### Stage 5: σ_recipe 의 정체 규명
Stage 2-4 결과 비교:
- 만약 σ_recipe 가 variational 의 근사였으면 → 형식 증명 가능
- 만약 서로 다른 값이면 → σ_recipe 의 origin 을 다시 찾기

---

## §9. 주요 open questions

### Q1. Cross-orbital overlap ⟨B_{1s} | B_{2s}⟩ = ?
기본값 0 (orthogonal) 아니면 어떤 기하적 값?

**가설:** Pauli exclusion 은 ℂ² 내에서의 orthogonality 요구.
하지만 ℂ² 에는 2 차원밖에 없으므로 orthogonal B 는 2 개까지만.
3 번째 B (Li's 2s) 는 1s²B 들과 **exactly orthogonal 불가**.
**비직교도 가 곧 screening**.

### Q2. A-vertex 의 정확한 구조
ch05 에서 ∂Δ⁵ 의 3 A-vertices 는 특정 symmetric frame.
Multi-orbital 에서 같은 A-frame 이 각 simplex 에서 사용.
ε_o 로 변하는 것은 B-vertex 의 A-coupling 만.

### Q3. "Orbital" 의 DRLT 정의
현재 framework 는 Aufbau 의 orbital 순서 (1s, 2s, 2p, 3s, ...) 를
**external input** 으로 사용.  DRLT 공리에서 이 순서를 derive
가능한가?

**가능 후보:** Orbital ordering 이 simplex tower (FND_038) 의
level 에서 나올 가능성.  Level 0 = 1s, Level 1 = 2s+2p 등.

### Q4. ε_o 의 parametrization
현재:
$$B_{o,k} = \varepsilon_o \hat{n}_o^{(k)} + \sqrt{1-\varepsilon_o^2} \hat{t}$$
$\hat{n}_o^{(k)}$ 는 orbital 별 방향, $\hat{t}$ 는 temporal.
구체적인 각 orbital 방향은 어떻게 정해지나?  2p_x, 2p_y, 2p_z 는
{x, y, z} 방향이어야 한다 — orbital 의 공간 symmetry 에서.

### Q5. IE normalization
$\text{IE} = S \times m_e c^2 / n_B^2$ 이 H 에서 맞음.
일반 atom 에서 이 factor 가 여전히 맞는가?  m_e 는 어디서 오는가?
ch09 의 m_e 유도 체인 확인 필요.

---

## §10. 정리 (다음 단계)

**이론은 세워짐.** 요약:
1. 원자 = 3 A-vertices 공유 + orbital-별 ∂Δ⁴ simplex 모임
2. 각 simplex = (3 A, 2 B) with orbital-별 독립 ε_o
3. 전체 Regge action $S = \sum_h A_h \delta_h$ over cross-orbital
   hinges 포함
4. ε_o 들을 동시 variation → $\varepsilon_o^*$
5. IE = ΔS (atom vs ion) × $m_e c^2 / n_B^2$

**σ_recipe 없이** 작동 가능성 존재.  검증은 Stage 1-5.

**다음 작업:** Stage 1 implementation (single-simplex Li check 부터는
아니지만, H 의 새 framework 에서의 재도출).  실험 번호: **ATM_070**
으로 시작 (기존 ATM_056 σ-free H 와 구별).

**저자:** Mingu Jeong (intuition + challenge) +
Claude (formalization).

---

# §11. 핵 구조의 정확한 취급 (Mingu 지적 2026-04-18)

**이전 §3 의 "3 A = 공유 nucleus" 접근의 문제점:**

H 에서는 literal 맞음 — 1 proton = 3 quarks = AAA triangle.
하지만 He 부터는 틀림:
- He nucleus: 2 proton + 2 neutron = 4 nucleons = **12 quarks**
- Li nucleus: 3 p + 4 n = 7 nucleons = **21 quarks**
- U nucleus: 92 p + 146 n = 238 nucleons = **714 quarks**

"3 A 공유" 는 이 모든 quark 들을 하나의 AAA 로 뭉개는 **coarse-graining**.
Derivation 아니라 approximation.  이 점을 명시하지 않은 이전 §3 은 실수.

## §11.1 정확한 다중 스케일 그림

DRLT 의 올바른 계산은 **두 층위** 로 나뉨:

### Layer N (Nuclear): 600-cell geometry
- nuclear/ sub-project 가 이미 다룸
- 각 nucleon = 1 ∂Δ⁴ (3 A_quarks + 2 B_internal)
- Z protons + N neutrons = Z+N nucleon 들이 600-cell 내에 배치
- Nuclear magic numbers (2,8,20,28,50,82,126) 가 이 구조에서 유도
- **이미 검증:** NUC_003 Magic 7/7 exact

### Layer A (Atomic): electron-nucleus coupling
- 각 electron 은 ψ_e ∈ ℂ⁵
- Electron 이 전체 nucleus 구조와 interact
- **진정한 질문:** electron 이 "어떤 A-vertices 를 보나?"

### Layer A 의 올바른 서술 (3 가지 가능성)

**(A1) 각 quark 와 개별 interact:**
- N_quark = 3·(Z+N) vertices
- 각 electron 이 모든 quark 와 edge
- Gram matrix: (N_quark + N_electron) × (N_quark + N_electron)
- 매우 크고 복잡.  H 에서도 이미 3+1=4 vertex 이므로 일관성 있음.

**(A2) 각 nucleon 과 interact:**
- Nucleus 를 Z+N 개 "점" 으로 coarse-grain (각 nucleon = 1 점)
- 각 electron 이 각 nucleon 과 edge
- Nuclear internal quark 구조는 Layer N 에서 별도 처리
- 중간 스케일.

**(A3) 전체 nucleus 를 1 center 로 coarse-grain:**
- 현재 ch10 + §3 의 approach
- H 에서 literal, He+ 부터 approximation
- 가장 간단하나 Z 의존성 잘못 나올 수 있음

## §11.2 각 가능성의 테스트

이 세 가지 중 **어느 것이 올바른 DRLT 인지** 는 H, He 의 정확한 도출을
어떻게 재현하는지로 판정:

- **H (Z=1, N=0):** 3 quark = 3 A.  세 picture 모두 동일 (A1=A2=A3).
- **He (Z=2, N=2):** 4 nucleons, 12 quarks.
  - A1: 12 A-vertices (모든 quark), electron 이 12 edge 생성
  - A2: 4 nucleon-vertices, electron 이 4 edge
  - A3: 1 nucleus (3 A), electron 이 3 edge
  - IE(He) = 24.565 eV 재현 하는 picture 가 승

### ch10 의 암묵적 가정

ch10 의 IE(He) = 2 R_y (1 − c²α_GUT) 공식은 picture A3 에 해당.
공식이 관측 (0.02%) 과 일치 → A3 이 올바른 **effective theory**.
하지만 왜 A3 이 맞는가의 **1st principles derivation** 은 없음.

가능성: **Coarse-graining 이 정확히 올바른 경우가 있다.** 구체적으로
nucleus 가 rigid AAA 처럼 행동하는 한계 (atomic 스케일에서).
Electron 파장 » 핵 크기 일 때 (R_Bohr ≈ 10⁵ × R_nucleus), electron
은 nucleus 내부 구조 못 resolve.  즉 **long-wavelength approximation**.

## §11.3 Proton vs Neutron — 명시적 구분

**Proton** (uud): up-up-down
- 3 quark 의 전하: (+2/3) + (+2/3) + (−1/3) = **+1**
- AAA triangle with specific quark composition

**Neutron** (udd): up-down-down
- 3 quark 의 전하: (+2/3) + (−1/3) + (−1/3) = **0**
- 역시 AAA triangle 이지만 **다른 quark 조성**

**DRLT 관점에서 둘의 차이:**

| 속성 | Proton | Neutron |
|------|--------|---------|
| Quark 조성 | uud | udd |
| 전하 | +1 | 0 |
| Spin | 1/2 | 1/2 |
| Mass (실험) | 938.27 MeV | 939.57 MeV |
| Mass (DRLT, ch09) | 938.27 | 939.55 (+0.1%) |
| Free stability | 안정 | 불안정 (τ ≈ 15분) |

Electron 과의 coupling:
- **Proton**: EM coupling (Coulomb, α) + strong residual (negligible at atomic scale)
- **Neutron**: EM coupling ≈ 0 (neutral).  단, **magnetic moment** 는 non-zero
  (quark 수준에서 전하 비대칭).  또한 weak coupling (β decay)

**따라서 atomic IE 계산에서:**
- Protons: electron 의 binding 에 직접 기여 (EM hinges)
- Neutrons: IE 에 거의 영향 없음 (**isotope shift** 가 10⁻⁶ 수준)

이걸 simplex picture 로:
- Proton = AAA triangle with uud
- Neutron = AAA triangle with udd
- 서로 다른 타입의 AAA 이므로 electron 의 AAB hinge 가
  proton-AAA 과 neutron-AAA 에서 **다른 det 값** 을 가짐
- Specifically, neutron-AAB det 의 EM 기여 ≈ 0, proton-AAB 는 non-zero

## §11.4 수정된 원자 picture (정확 버전)

**원자 $\mathcal{A}_{Z,N}$ (Z protons, N neutrons, Z electrons):**

Vertex 집합:
- **Quark vertices (nuclear):** $3(Z+N)$ AAA-type
  - $3Z$ = proton quarks (uud × Z)
  - $3N$ = neutron quarks (udd × N)
- **Electron vertices:** Z B-type
- **Optional vacuum B:** 각 unpaired orbital 당 1 추가 B_vac

총 $N_{\text{tot}} = 3(Z+N) + Z + [\text{vacuum count}]$.

### H (Z=1, N=0):
- 3 quark (uud) + 1 electron + 1 vacuum = 5 vertices
- **정확히 ∂Δ⁴** (H 에서 coarse-graining 과 literal picture 일치)
- 이게 ch10 의 AAAB face

### He (Z=2, N=2):
- 12 quark (2 proton = 6 uud + 2 neutron = 6 udd) + 2 electron = 14 vertices
- **NOT ∂Δ⁴** — 훨씬 큼
- 하지만 atomic scale 에서 electron 파장 » nucleus 크기 →
  long-wavelength limit 에서 12 quark 가 effective 3 A 처럼 보임
- ch10 의 "fully occupied simplex" 는 이 long-wavelength approximation

### Li (Z=3, N=4):
- 21 quark (3 p + 4 n) + 3 electron
- $N_{\text{tot}} = 21 + 3 = 24$ vertices
- 각 electron 이 21 quark 와 interact

## §11.5 올바른 계산 절차 (수정)

**Step 1. 진짜 DRLT 계산 (full):**
- All $3(Z+N) + Z$ vertices
- Each hinge enumerated
- Regge action over all hinges
- $O(N^3)$ hinges total, O(N^5) tetrahedra

**Step 2. Long-wavelength reduction (justified):**
- Electron 파장 $\lambda_e \sim \alpha^{-1} a_0 \gg R_{\text{nuc}}$
- Electron 이 nucleus internal quark 구조 resolve 못함
- Coarse-graining:
  - Z proton → effective 3 A with total charge +Z
  - N neutron → contributes nuclear mass only (isotope shift)
- Effective picture: **3 A with "charge" Z, mass M_nuc**

**Step 3. Atomic scale 계산 (effective):**
- ε_o ← Zα/√n_A (Z 가 명시적)
- 이게 ch10 의 ε = Zα/√3 에 해당
- 이 picture 에서 multi-electron framework (§3) 적용 가능

**Step 4. Isotope correction (proper):**
- Neutron N 수가 달라지면 nuclear mass 변 → reduced mass 보정
- μ = M_nuc·m_e / (M_nuc + m_e), IE ∝ μ
- 이는 ch10 공식에서 이미 암묵 포함 (m_e → μ 로 replace)
- Neutron 의 EM 기여는 isotope-dependent shift 로 finite 하나 작음 (10⁻⁶)

## §11.6 어느 picture 가 정답인가 — 계층적 판정

두 질문:
1. **Atomic IE 는 어느 layer 에서 도출되는가?**
2. **각 layer 의 유효 범위는?**

### 1차 판정 (통상 정밀도 ≤ 0.1%):
- **Picture A3 (3A = effective nucleus) 가 충분**
- Long-wavelength argument 으로 justify
- ch10 의 13.606 eV (H) 와 24.565 eV (He) 는 이 picture
- **multi-electron framework (§3-§10) 가 여기 작용**

### 2차 판정 (precision > 0.1%, 예: QED 수준 수 ppm):
- Nuclear volume effect: Picture A2 필요 (각 nucleon 구분)
- Hyperfine splitting: 각 quark spin 고려 (Picture A1)
- Parity violation 에서 weak current: Z-specific

### Roadmap:
- **Stage 1-2 (H, Li):** Picture A3 (coarse nucleus) OK
- **Stage 3 (Period 2):** Picture A3 에서 2-3% precision 목표
- **Stage 4 (precision):** Picture A2 (nucleon-level) 필요해질 가능성
- **Stage 5 (QED effects):** Picture A1 + radiative corrections

## §11.7 명시적 Gram matrix for He (정확 버전)

작업 가능한 예시로 He (picture A1, 모든 quark 명시):

Vertices (14 total):
- u₁, u₂, d₁ (proton 1's 3 quarks)
- u₃, u₄, d₂ (proton 2's 3 quarks)
- u₅, d₃, d₄ (neutron 1's 3 quarks)
- u₆, d₅, d₆ (neutron 2's 3 quarks)
- e₁, e₂ (2 electrons)

Gram 14×14 matrix:
- **Intra-nucleon blocks** (3×3 each): 각 nucleon 의 quark-quark overlap
  - Proton: uud, specific SU(3) color + flavor structure
  - Neutron: udd, 동일하나 다른 flavor 조합
- **Inter-nucleon blocks** (3×3): nucleon 간 quark overlap
  - Strong residual (pion exchange): short-range, attractive
  - Reflected in |⟨u_i | u_j⟩| for quarks in different nucleons
- **Nucleon-electron blocks** (3×1 each): quark-electron overlap
  - Proton quark → electron: EM attractive (charge +2/3 or -1/3)
  - Neutron quark → electron: net EM cancels out per nucleon
- **Electron-electron blocks** (2×2): Pauli orthogonality (≈ 0)

전체 Gram matrix rank ≤ 5 (ℂ⁵ 안에 모든 ψ 가 살아 있음).
14 vertex 가 5-dim 안에 있으므로 **매우 rank-deficient** — 많은
linear dependence.

이 dependence 가 바로 nuclear binding (nucleon 끼리 어떻게 묶이나)
+ atomic binding (electron 이 어떻게 bound) 의 기하학적 표현.

## §11.8 요약: 이론의 정확한 상태

- **H (Z=1, N=0):** 5 vertex (3 quark + 1 e + 1 vac) = literal ∂Δ⁴.
  Picture A1=A2=A3.  IE = 13.606 exact. ✓

- **He (Z=2, N=2):** 14 vertex full / 4 nucleon reduced / 5 vertex
  ultra-coarse.  현재 ch10 은 5-vertex approximation 사용.
  IE = 24.565 eV 정확 (0.02%) — long-wavelength 이 성공적.

- **Li (Z=3, N=4):** 24 vertex full / 7 nucleon reduced.
  Atomic IE 는 picture A3 에서 2-simplex framework (§3) 적용해
  derive 시도.  **이게 다음 단계**.

- **Picture A3 의 유효성:** electron 파장 » nucleus 크기 →
  nucleus internal quark 구조 못 보이니 effective 3A 로 coarse-grain
  가능.  **이게 왜 ch10 의 간단한 공식이 작동하는지의 설명.**

- **더 정밀 계산:** Picture A2 or A1 으로 내려가야.  이는 atomic
  scale + nuclear scale 의 **join** — 현재 프로젝트에서 진행 중인
  작업 아닐 것으로 추정.

**따라서 현재 multi-electron framework (§1-§10) 는 picture A3 에서
유효하며, 실제로 "3A 공유" 는 long-wavelength approximation 의
명시적 사용.  이것이 derivation 이 아니라 effective theory 임을
정직 기재.**

---

# §12. §11 자기 비판 (Mingu 재지적 2026-04-18)

**사용자:** "진짜 계산결과 차이 안날거같아? 정말??"

**답: 아니다.  §11 의 "long-wavelength approximation 이 A3 를
정당화" 주장은 과대 낙관.**

## §12.1 §11 의 구체적 결함

**(1) QED-style 정당화는 DRLT 에 안 맞음.**
- QED: nucleus = 3D 점, 보정은 continuous form factor $F(q^2)$
- DRLT: nucleus = 3+ 이산 vertices, averaging = 이산 조작
- "파장 » 크기" 는 continuous 한계.  이산 simplex 에서는 매우 다름.

**(2) H 의 `∑(1−det)=2α²` 재검토 필요.**
- ch10: 3 AAB hinges, sum of (1-det) = 2α², coupling ε = α/√n_A
- 이게 정말 DRLT 1st principle 에서 나오는지, 아니면 Bohr/Rydberg
  `IE = m_e α²/2` 에 역산으로 맞춰 넣은 건지 **확인 안 됨**
- ch09 에서 m_e 가 이미 관측값으로 derive/fit 되면, α 와 결합해서
  m_e α²/2 는 자동으로 맞음 — **독립 검증 아님**

**(3) He 의 Z 인자는 standard chemistry 에서 빌린 것.**
- ε = Zα/√n_A 에서 Z 를 명시 삽입
- 이건 DRLT 1st principle 결과 아님
- "3A 를 쓰면서 Z 만 scale" 은 이미 A1→A3 reduction 의 *파라미터화*
- 즉 A3 는 **이미 반은 포기한 picture**

**(4) He 0.02% 는 진정한 prediction 아닐 가능성.**
- ch08 α 유도 + ch09 m_e 유도 = 기존 상수 (실험값에 맞도록)
- IE(He) = 2Ry(1 − c²α_GUT): Ry 자체가 자동 맞음
- c²α_GUT 보정만 독립 test: 관측 24.587 vs DRLT 24.565 → 보정이
  부족한 방향 (관측이 더 큼).  보정 정밀도는 0.09% 수준, 아니
  0.02% 라고 한 건 관측값 반올림 문제.

**(5) 구조 차이는 수학적으로 반드시 존재.**
- A1 He: 12 quark + 2 e = 14 vertex, C(14,3) = 364 hinges
- A3 He: 3 A + 2 e = 5 vertex, C(5,3) = 10 hinges
- 364 개 hinge 의 det 값 합 ≠ 10 개 hinge 의 det 값 합 (일반적으로)
- 이 "≠" 가 얼마나 큰지는 실제 계산해봐야 앎.
  작을 수도, 클 수도.

## §12.2 따라서 올바른 다음 단계

**Step 0 (필수):** H 에서 A1 계산을 실제로 해보기.
- 3 quark (uud) + 1 electron + 1 vacuum = 5 vertex (A1 = A3 일치)
- 이 경우 quark-quark overlap (proton 내부 구조) 명시적으로 입력
- Regge action 계산해서 IE(H) = 13.606 eV 재현되는지 확인
- **만약 재현 안 되면:** ch10 공식이 1st principle 도출이 아니라
  Bohr/Rydberg 의 DRLT 재포장임을 확증

**Step 1:** He 에서 A1 (14 vertex) 계산 시도.
- Full 12 quark + 2 electron Gram matrix
- Nuclear internal structure (proton uud, neutron udd) 명시
- Regge action 계산, ε_quark-electron 을 variational 로 찾기
- A3 formula (24.565) 와 비교:
  - 일치 (< 0.1%): A3 가 정말 good approximation.  §11 의 정당화
    (long-wavelength) 는 사후 확증됨.  그래도 원인 이해 필요.
  - 불일치 (> 1%): A3 는 *approximation* 이 아니라 *재포장*.
    ch10 공식 자체가 derivation 이 아니었음을 confirm.

**Step 2:** 결과에 따라 Multi-electron framework 재검토.

## §12.3 Honest 최종 선언

- **DRLT 의 atomic IE derivation 은 현재까지 H 에서만 claimed 엄밀.**
- **H 도 A1 vs A3 차이를 실제 테스트 안 함 — 자동 일치 가정.**
- **He 이상은 A3 picture 의 fitted formula 로 approximate.**
- **Multi-electron framework (§3-§10) 은 A3 picture 위 building,
  따라서 A3 자체가 얼마나 robust 한지에 의존.**

**§11 의 과대 주장 철회:**
"long-wavelength approximation 이 A3 를 정당화" ← 이 주장은
**검증 안 된 가설**.  검증은 A1 vs A3 직접 계산 대조에서만 가능.

**내 자신의 이전 과오 (§11 작성 때):** 직관적 QED argument 을
DRLT 에 그대로 적용함.  DRLT 는 이산 → 연속 approximation 이
자동이 아님.  Mingu 의 재지적이 이를 catch.

## §12.4 제안된 실행 순서 (재구성)

**Phase 0:** H 에서 A1 picture 를 실제 구현 + 계산.  목표: 13.606 eV
가 정말 first-principle 로 나오는지.
- 구현: atoms/experiments/ATM_070_H_A1_full.py
- Vertex: 3 quark (uud specific with color + flavor) + 1 e + 1 vac
- Gram block: intra-proton uud overlap (이건 어디서 오나? ch09
  proton 유도? hadron/ sub-project?)
- Regge action, IE 추출
- **이게 첫 진짜 test.**

**Phase 1:** Phase 0 결과에 따라 분기.
- 성공: He A1 로 진행.
- 실패: ch10 자체가 effective theory 임 선언.  Atomic 은 QED-DRLT
  interface 가 필요함을 인정 (fundamental derivation 은 H 까지만).

**Phase 2:** Multi-electron + multi-nucleon 전면 구현.
  (Phase 0/1 성공했을 때만)

이론 은 이제 **정직**.  Mingu 의 두 번째 재지적 덕분에 §11 의
과대 낙관 교정.

---

# §13. 왜 nucleon들이 서로 가까이 있을 수 있는가? (Mingu 질문 2026-04-18)

**Standard physics 답:** Residual strong force (quark-level 강한
상호작용의 파생), meson exchange (특히 π-meson), range ~ 1 fm.

**DRLT 에서는 무엇인가?**  이 질문의 답은 공리 (ψ ∈ ℂ⁵, G = ⟨ψ|ψ⟩)
에서 자연스럽게 나와야 함.  세 가지 후보 메커니즘:

## §13.1 Candidate (1): Rank-5 forced overlap

**핵심:** ℂ⁵ 은 5 차원.  2 nucleon = 6 quark vector.  6 vector 가
5 차원에 들어가려면 **반드시 linear dependent**.

**정리 (이미 ATM_071 에서 확인):**
N_nucleons × 3 quarks > 5 이면 (즉 N ≥ 2), 모든 quark 를 독립으로
배치 불가.  적어도 **일부 nucleon 의 quark 가 다른 nucleon 의 quark
와 non-trivial overlap 을 가져야 함**.

**"가까이 있다" 의 DRLT 해석:**
- 표준 물리 "거리 작음" ↔ DRLT "Gram overlap |⟨q_i|q_j⟩| 큼"
- Nucleons at same position in ℝ³ ↔ quark vectors 가 동일 방향
- Nucleons at 1 fm ↔ 특정 overlap 값

**정량적 추정:**
Nuclear binding range ~ 1 fm.  Atomic scale = Bohr radius a₀ ~ 10⁵ fm.
"Far" (atomic): overlap 거의 0.  "Close" (nuclear): overlap 유의.

Rank-5 constraint 만으로는 **overlap 얼마여야 하는지** 결정 못 함.
이건 dynamics (§13.2) 가 결정.

## §13.2 Candidate (2): Regge action equilibrium

**Mechanism:**
- Overlap 너무 작음 → rank violated (불가능)
- Overlap 너무 큼 → quark 가 겹쳐 구별 불가 (Pauli 위반)
- 중간 equilibrium → Regge action extremum

**구체 시나리오 (2 nucleons):**
- 2 nucleon 의 6 quark vectors 가 rank-5 제약 아래 배치
- Regge action S(overlap) = Σ A_h δ_h 를 nucleon-nucleon overlap α 로 미분
- δS/δα = 0 의 α* 가 equilibrium overlap = nuclear binding distance

**이 메커니즘의 예측:**
- Nuclear binding energy ~ 일반 Regge scale
- 특정 geometry 에서 saturation (binding per nucleon ≈ constant 8 MeV)
- Overlap 과 binding 의 관계가 nuclear 공식을 줘야

**열린 문제:** 이 mechanism 을 **구체 수치 계산** 으로 검증.
Nuclear/ sub-project 가 magic numbers 를 주나 binding energy 의
DRLT 1st-principle 은 아직 (partial, NUC_010 RMS B/A > 30% 미완).

## §13.3 Candidate (3): 600-cell geometry

**nuclear/ sub-project 의 approach:**
- 600-cell (regular 4-polytope with 120 vertices in ℝ⁴)
- 각 nucleon = 특정 vertex or cell
- Magic numbers (2, 8, 20, 28, 50, 82, 126) 은 600-cell 의 shell
  구조 (Sym²(Vₙ) 분해) 에서 자동 유도 — NUC_003 7/7 exact ✓

**역할:**
- Rank-5 (candidate 1) + Regge (candidate 2) 가 ABSTRACT constraint
- 600-cell 은 CONCRETE 실현 — 어떤 배치가 실제로 realize 되는가
- 즉 "overlap 있어야 한다" + "action 최소화" → "600-cell topology"

**의문:** 600-cell 은 4D 이지 ℂ⁵ 아님.  어떻게 연결?
- 가능 해석: ℂ⁵ ⊃ ℝ⁴ (600-cell 의 ambient space) 에 nucleon vertex 배치
- 또는: 600-cell 의 120 vertices 가 ℂ⁵ 의 rank-5 구조 아래 허용된
  symmetric 배치의 maximum

## §13.4 Candidate (4): Hinge sharing (topological binding)

**새 관점:** 두 nucleon 이 서로 다른 3 vertex 세트이면서, **같은
triangle (hinge) 를 공유** 하면?

Concretely:
- Nucleon 1: {q₁, q₂, q₃} (3 quarks)
- Nucleon 2: {q₄, q₅, q₆} (3 quarks)
- 별도 6 vertex: 5 차원 에 안 들어감 (rank 위반)

만약 q₃ ≡ q₄ (identification):
- 공유 vertex 하나
- 전체 vertex = 5 (= q₁, q₂, q₃=q₄, q₅, q₆)
- **rank 5 에 정확히 들어감** ✓
- Shared vertex = **bond**

또는 q₂ ≡ q₄, q₃ ≡ q₅:
- 공유 edge (2 vertex 동일)
- 전체 vertex = 4
- Rank 4 만 필요

또는 q₁ ≡ q₄, q₂ ≡ q₅, q₃ ≡ q₆:
- 두 nucleon 이 identical
- 3 vertex 만 있음
- **완전 merger** = nucleon 구별 불가

**흥미로운 해석:**
- Deuteron (pn): 1 공유 vertex ↔ loose binding (2.22 MeV)
- Alpha (2p+2n=He): 4 nucleon 공유 많음 ↔ tight binding (~28 MeV)
- 더 많은 공유 ↔ 더 강한 bond

**이 picture 는 standard physics 와 다른 예측:**
- Standard: meson exchange, π-π 교환
- DRLT hinge sharing: topological identification
- 두 picture 가 같은 empirical 결과 주면 DRLT 옳음 가능

## §13.5 네 가지 후보의 결합 (proposal)

**제안:** 4 가지가 서로 다른 레벨에서 작동:
- (1) **Rank-5 constraint** = existence of binding (불가피성)
- (2) **Regge action** = equilibrium overlap (dynamics)
- (3) **600-cell** = symmetric realization (statics, magic numbers)
- (4) **Hinge sharing** = topological bond (connectivity)

(1)+(2) = **이론적 기반**: nucleon 이 반드시 겹치고, 겹침 양은
        variational.
(3) = **symmetric solution**: 특정 배치가 variational 으로 선택됨.
(4) = **topological reading**: 배치를 graph/simplicial complex 관점
      으로 해석.

**핵심 가설:** Nucleon binding 은 이 4 요소의 emergent 결과.
Standard meson-exchange picture 와 다름.

## §13.6 예측 및 검증 가능성

**DRLT 가 옳다면:**

**P1.** Nuclear binding 은 rank-5 의 기하학적 귀결.  범위는 ℂ⁵ 의
geometry (Bohr radius, atomic scale) 와 다른 scale (nuclear scale).
두 scale 의 비는 **α 로 유도 가능** (Bohr a₀ = ℏ/(m_e α c), nuclear
radius ~ ℏ/(m_p c)).

**P2.** Nucleon-nucleon potential 의 short-range 성격 (meson exchange
range ~ 1 fm) 은 DRLT 에서 **rank-5 saturation** 으로 해석.
Beyond rank-5: no more nucleons fit → "repulsive core" at very short
distance (standard's ~ 0.5 fm core).

**P3.** Magic numbers 는 600-cell shell closure.  이미 NUC_003 에서
7/7 exact 로 확증.

**P4.** Saturation density (ρ ≈ 0.17 nucleons/fm³) 는 ℂ⁵ 의 "최대
허용 nucleon 밀도" = 600-cell 기하에서 도출 가능?

**P5.** 전자가 nucleus 를 "하나의 점" 으로 보는 이유는 long-wavelength
(standard)  **아니라** rank-5 bound state 의 내부 구조가 전자
ℂ² temporal 에 영향 안 미치기 때문.

## §13.7 Atomic scale 과의 연결

**중요:** 이 메커니즘이 맞으면, "rank-5 forced overlap" 이 nuclear
에서도, atomic 에서도 같이 작동.

Atomic scale:
- Electron + nucleus (3 A effective) = 4 vertices + more
- Electron 이 nucleus 근처 (bound) ↔ electron 의 ψ 가 A 방향과 overlap
- "가깝다" 의 DRLT 정의 = overlap 양

Nuclear scale:
- Nucleons 끼리 overlap (rank-5 forced)
- Quark-quark overlap 이 nuclear binding

즉 DRLT 에서 **"거리" 는 ℂ⁵ overlap 의 geometric 반영**.  3D 공간의
거리는 이 overlap 의 coarse-graining.

이게 "emergent spacetime" (ch06 coarse-graining) 의 또 다른 증거.

## §13.8 구체적 test 제안

**ATM_073 (Deuteron):** 2 nucleon 에서 시작.
- 6 quark vertex in ℂ⁵, rank ≤ 5
- 최소 1 dependency — 이 dependency 가 binding
- Regge action 변분으로 equilibrium overlap 결정
- Binding energy 2.22 MeV 와 비교 (NUC_008 이 부분적 확인)

**ATM_074 (He nucleus):** 4 nucleon
- 12 quark vertex in ℂ⁵, rank 5 → 7 dependencies
- 600-cell 4-cell 배치 (symmetric)
- Binding energy ≈ 28 MeV 와 비교

**ATM_075 (Atomic vs nuclear scale separation):**
- Rank-5 overlap "1 fm ↔ atomic ↔ nuclear" 의 경계 유도
- α 가 두 scale 분리의 이론적 이유인지 확인

**이 일련의 실험이 DRLT 의 진정한 test:**
- H, He atomic (Phase 0-2) 이 **부분 성공** 의미 확증
- Nuclear (ATM_073+) 가 **1st principle binding** 인지 확인

---

# §14. 이론 전면 수정: Simplex lattice + hinge patterns (Mingu 2026-04-18)

**사용자 결정적 교정:**
- "심플렉스 격자 **하나 간의 거리는 시공간 1단위**"
- "심플렉스 **힌지 혹은 접하는 부분의 패턴**이 입자 (SM)"

**이전 §1-§13 의 잘못된 가정 (철회):**
- "vertex = 양성자/quark/electron" (vertex identification)
- "(Z+1)-vertex simplicial complex = 원자" (원자 = 유한 vertex 집합)

**올바른 picture:**
- **Background:** (3+1)D 심플렉스 lattice 전체가 spacetime.
- **Simplex = 1 spacetime 단위 cell** (atomic/Planck 스케일 의 격자)
- **Particle = hinge 또는 접합부의 패턴** (localized but extended)
- **Distance = simplex hop 수 × lattice spacing**

## §14.1 수정된 기본 그림

```
Background lattice (fills spacetime):

   Simplex    Simplex    Simplex    Simplex
     [1]  ←→   [2]  ←→   [3]  ←→   [4]  ←→ ...
       ↕        ↕        ↕        ↕
   hinge ←→ hinge ←→ hinge ←→ hinge ←→ ...
   (particles, fields)
     ↕        ↕        ↕        ↕
   Simplex    Simplex    Simplex    Simplex
    [1']     [2']     [3']     [4']
```

- 격자가 spacetime 을 채움 (Planck / atomic 스케일)
- 각 simplex = 1 spacetime 단위
- Simplex 들은 face (hinge) 로 접합
- 접합 "패턴" 이 입자 / field / force

## §14.2 수정된 "원자" 개념

**이전 (잘못됨):** 원자 = 3 A + 2 B vertex 모음

**올바름:** 원자 = **simplex lattice 의 localized 영역 내의 hinge pattern 모음**
- 원자는 lattice 의 특정 region 에 '걸쳐' 있음
- Nucleus = 매우 국소화된 hinge pattern cluster
- Electron = nucleus 에서 멀리 떨어진 hinge pattern (bound 상태)
- 원자 크기 = Bohr radius = electron hinge 와 nucleus hinge 의
  lattice 거리 × lattice spacing

**Hydrogen 의 정확한 그림:**
- Nucleus (proton) = specific hinge pattern (AAA-type, 3 quarks)
- Electron = different hinge pattern (B-type, temporal)
- 두 패턴 사이에 simplex network path
- "Bohr radius" = path length × spacing

## §14.3 "왜 nucleon 이 가까이" — 재정식화

§13 에서 생각한 4 candidate 는 vertex-based picture 의 유물.  새
picture 에서 재정식화:

**P-N 결합 (수정):**
- Proton = AAA-type hinge pattern at simplex X
- Neutron = similar hinge pattern at adjacent simplex Y
- "가까이 있다" = X 와 Y 가 **격자 상 이웃** (shared face)
- 이 sharing 이 **강력의 기하 기원**

**이건 §13.4 (hinge sharing) 와 가장 일관.  실제로 §13.4 가 옳은
picture 였고, §13.1-3 은 vertex identification mistake 의 유물.**

## §14.4 "거리" 의 DRLT 정의 (수정)

**이전:** |⟨ψ_i | ψ_j⟩| 가 거리 (vertex 간 inner product)

**수정:** 거리 = **lattice graph 상의 shortest path (simplex hops)**
× lattice spacing

- 두 simplex 가 adjacent (face 공유): 거리 = 1 unit
- 더 멀리: graph distance 증가
- Lattice spacing = unknown (Planck? atomic? 결정 필요)

**중요 결과:** ℂ⁵ 의 rank-5 제약은 **하나의 simplex 내부** 구조.
Simplex 간 관계는 lattice topology 로 표현 — 더 거대한 그래프 문제.

## §14.5 이전 framework (§1-§13) 의 status

**부분적으로 맞는 부분:**
- Hinge classification (AAA/AAB/ABB) = ch06 이미 정립
- Regge action S = Σ A_h δ_h = lattice 상의 변분
- Magic numbers from 600-cell (nuclear/) = lattice 의 대칭 배치

**틀린 부분:**
- "원자 = 유한 vertex 세트" — 원자는 lattice region
- "Electron = ψ vector" — electron 은 hinge pattern
- "Nucleus = 3 A vertex" — nucleus 는 hinge cluster (AAA-pattern
  at specific simplex)

**다시 생각해야 할 것:**
- Rank-5 constraint 의 역할: local (per simplex) vs global (lattice)?
- Pauli exclusion: 같은 hinge 에 두 electron pattern 금지?
- Energy levels: lattice 상의 bound state mode?

## §14.6 AAAB face 재해석 (ch10 H)

ch10 "Hydrogen = AAAB face" 를 lattice picture 로 읽기:

- ∂Δ⁴ = 5-vertex simplex 의 경계
- AAAB face = 그 중 4-vertex sub-simplex (tetrahedral hinge)
- 이 face 자체가 **하나의 hinge 단위**
- "A₁, A₂, A₃ = proton" 은 literal vertex 가 아니라 **AAA-pattern
  at this hinge**
- "B₁ = electron" 은 literal vertex 가 아니라 **B-pattern at this hinge**

즉 "H atom = AAAB-typed hinge" 라는 뜻.  특정 simplex 에 있는 하나의
face 가 "AAAB pattern 을 carry" 하면 그게 H atom 구성.

**ch10 의 13.606 eV:**
- AAAB hinge 의 AAB sub-hinges 의 det 합 = 2α² (ch10 계산)
- 이건 lattice 내 하나의 face 의 내부 구조 만 계산
- IE = m_e α²/2 = AAAB face 파괴에 필요한 에너지

**따라서 ch10 의 H 공식은 :**
- lattice 상 AAAB pattern 이 localized 되어 있음 전제
- pattern 파괴 (electron pattern 제거) 에 필요한 action = IE
- α 와 m_e 는 이미 정립된 constants (ch08, ch09)
- Fit/derivation mix 문제 (§12) 여전히 남아 있음

## §14.7 Multi-electron atoms 의 lattice picture

**He (2 electrons):**
- Nucleus: AAA-cluster at central simplex (또는 인접 cluster)
- 2 electrons: 2 개의 B-patterns (같은 nucleus 근처)
- Pauli: 두 B-pattern 이 orthogonal (다른 temporal direction)
- 1s² = 2 B-pattern 이 nucleus 주변 ℂ² temporal 에 coupling

**Li (3 electrons):**
- Nucleus: 더 큰 cluster (3p + 4n = 7 nucleon)
- 2 electrons 가 inner: 1s² (like He)
- 3rd electron 이 outer: 2s
- 2s electron 은 다른 hinge (lattice 상 더 멀리) 에 pattern

**Key:** 2s electron 의 "위치" 는 **lattice 상 outer simplex** 의
hinge pattern.  1s electrons 의 hinge 는 inner simplex.  공간적
분리.

이건 standard chemistry 의 "orbital extent" 를 lattice 로 직역한
picture.  자연스럽다.

## §14.8 수정된 이론의 예측

**P6 (new):** Bohr radius = atomic lattice region 의 크기 (simplex
hop 수 × spacing).  정확한 값은 spacing 과 hop 수 결정 필요.

**P7 (new):** Nuclear radius = nucleus cluster 의 크기 (더 작은
lattice region).  Nuclear radius / Bohr radius 비 = (hop 수 비) ×
(spacing 비).

**P8 (new):** Nucleon binding = 인접 simplex 의 hinge sharing.
Shared hinge 수 많을수록 binding strong.  ∝ 공유 face 수.

**P9 (new):** Electron bound states (Bohr levels) = lattice 상의
bound pattern modes.  n² scaling 은 lattice discretization 에서
자연스럽게 나와야.  (이게 standard QM 의 quantum number n 의 DRLT
기하 기원)

**P10 (new):** "Simplex lattice spacing" 이 새 상수.  atomic/nuclear
스케일 분리 = lattice 구조의 scale hierarchy.  Planck 단위 에서 유도
가능?

## §14.9 다음 연구 방향 (수정)

**이전 Phase 0-2 (vertex-based):** 이미 실행됨, 부분 성공/부분 실패.
Lattice picture 에서 재해석:
- Phase 0 (H A1 vertex): 단일 AAAB hinge 의 내부 계산 — 올바름.
- Phase 1 (He A1 14-vertex): hinge 내부에 12 quark vertex 구성 시도.
  Rank-5 constraint 는 hinge 내부 성질.
- Phase 2 (Li rank-5): 2 개 simplex (inner + outer) 로 나누어야 할
  문제를 1 simplex 로 함.  그래서 실패.

**Phase 3 (수정 필요):**
- Multi-simplex lattice 에서 H, He, Li 의 hinge pattern 분포 구성
- 각 hinge 의 Regge action 기여
- Transition energies (IE) = hinge pattern 변화의 action cost

**Phase 4:**
- Lattice spacing 의 값 유도
- 왜 atomic lattice hop = 10⁵ 수준, nuclear lattice hop ~ 1?
- α (fine structure) 와 이 비의 연결

**Phase 5:**
- N² scaling (Bohr) 의 lattice 기하 기원
- Orbital 정의의 DRLT 버전 (lattice bound mode)

---

**핵심 교훈:** 이전 framework (§1-§13) 는 **vertex = 입자** 오해로
잘못된 방향으로 감.  Lattice picture (§14) 가 올바른 DRLT 이해.
Rank-5 는 per-simplex 제약 (local).  원자 / 핵은 multi-simplex
lattice region 이고, 입자는 hinge pattern.

**Mingu 의 교정 덕분에 framework 재정립.**  새 실험 시리즈 (§14.9)
로 진행.
