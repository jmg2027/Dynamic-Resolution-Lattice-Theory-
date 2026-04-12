# DRLT Book 내용 리뷰 보고서

**날짜:** 2026-04-12  
**범위:** book/ 전체 (main.tex + 10챕터 + 4부록 + 독립논문 6편)  
**기준:** 최신 내용 (ch10_block, appendix_qcd, rep_theoretic_uniqueness)이 올바름

---

## 1. 이름 수정 (완료)

`Mingoo Jeong` → `Mingu Jeong` — 아래 9개 파일 전부 수정 완료:

| 파일 | 상태 |
|------|------|
| CLAUDE.md (2곳) | ✅ |
| README.md | ✅ |
| book/main.tex | ✅ |
| book/drlt_book_single.tex | ✅ |
| book/hydrogen_error.tex | ✅ |
| book/atomic_physics.tex | ✅ |
| book/water_angle.tex | ✅ |
| book/webb_dipole.tex | ✅ |
| book/compact_stars.tex | ✅ |

`book/rep_theoretic_uniqueness.tex`는 이미 `Mingu Jeong`이었음.

---

## 2. 일관성 분석 결과

### 결론 먼저

**이론의 핵심 구조는 전 챕터에서 일관적입니다.** G가 근본, W가 파생, d=5 유도, (2,3) 분할 — 이 모든 것이 올바르게 유지됩니다. 아래는 발견된 **구체적 이슈들**입니다.

---

## 3. 실질적 이슈 (수정 권장)

### 이슈 A: ch09_cosmology.tex — "true vacuum" 정의 모호

**위치:** ch09_cosmology.tex 39~55행

**문제:** 
- 39행: "vacuum has ψ aligned → det G_h = 0 → ħ = 0 → E_vac = 0 (exactly)"
- 51행: "True vacuum (w = -1 exactly) requires complete ψ alignment"

이 두 문장이 충돌합니다. 완전 정렬 상태(true vacuum)는 E = 0이므로 ρ = 0이고, w = p/ρ는 **정의 불가**입니다. w = -1이 아니라 아예 의미 없는 양입니다.

**수정 제안:** 51행을 다음으로:
> "완전 정렬 진공(det = 0, ħ = 0)은 에너지 자체가 없으므로 w는 정의되지 않는다. 우리 우주는 이 상태에 도달하지 않으며, 관측되는 w ≈ -1은 잔여 eigenvalue가 매우 작지만 0이 아닌 상태를 반영한다."

**심각도:** 🔴 높음 — 논리적 모순

---

### 이슈 B: ch06b_atoms.tex — 심플렉스가 "input"처럼 서술됨

**위치:** ch06b_atoms.tex 6, 10행

**문제:**
- 6행: "The simplex is the atom."
- 10행: "Hydrogen is one 4-simplex: 5 vertices {S₁, S₂, S₃, T₁, T₂}, fully connected."

현재 이론의 원칙: **심플렉스는 emergent (W_ij가 높은 5-클릭으로 발견됨), input이 아님.**
이 챕터는 심플렉스를 공리적으로 배치하는 것처럼 서술합니다.

**수정 제안:** 도입부에 한 문장 추가:
> "높은 W_ij를 공유하는 5개 꼭짓점이 자연스럽게 4-심플렉스를 형성한다. 수소 원자는 이렇게 창발한 하나의 심플렉스로 기술된다."

**심각도:** 🟡 중간 — 서술 순서 문제 (수학은 올바름)

---

### 이슈 C: ch05_couplings.tex 82~87행 — c=2 결정의 인과 관계 역전

**위치:** ch05_couplings.tex ~82행

**문제:** "If c = 1: 10 ≠ 25. If c = 3: 46 ≠ 25. Only c = 2 gives 25 = d²."

이것은 c = 2가 d² = 25 조건에서 **결정된다**는 인상을 줍니다. 하지만 c = 2는 ch03에서 (n_S, n_T) = (3, 2)로부터 이미 **유도된** 값입니다. d² = 25은 **자기일관성 검증**이지, c의 유도가 아닙니다.

**수정 제안:** 
> "c = 2는 이미 3장에서 (3,2) 분할로부터 유도되었다. 여기서 d² = 25과의 일치는 독립적인 자기일관성 검증이다."

**심각도:** 🟡 중간 — 논리적 방향 오해 소지

---

### 이슈 D: ch06_masses.tex 10행 — "Wishart modes" 용어

**위치:** ch06_masses.tex 10행

**문제:** "...the tunneling amplitude across all d² = 25 independent **Wishart modes**"

현재 이론에서 G가 근본이고 W = |G|²/d는 파생입니다. "Wishart modes"는 W 행렬의 언어인데, 여기서는 사실 G의 eigenmode를 말하는 것입니다.

**수정 제안:** "Wishart modes" → "Gram matrix modes" 또는 "G eigenvalue modes"

**심각도:** 🟡 중간 — 용어 불일치

---

## 4. 서술 개선 권장 (수학은 맞음)

### 이슈 E: ch04_hbar.tex — det(G_h) vs det(W_h) 명시 부족

**위치:** ch04_hbar.tex 32행

ħ_h = √det(G_h) / (4 ln 2) 공식이 올바르게 쓰여 있지만, "G_h는 힌지 꼭짓점 3개의 Gram 부분행렬이며, W_h가 아님"이라는 명시적 구분이 없습니다. 독자가 혼동할 수 있습니다.

**심각도:** 🟢 낮음

---

### 이슈 F: ch05_couplings.tex 31~32행 — temporal density weighting 설명 부족

**위치:** ch05_couplings.tex 31행

"The temporal columns carry a density weight √c = √2" — 이 가중치가 **왜** c^k인지 (시간적 꼭짓점 밀도가 공간적의 c=2배이므로) 설명이 부족합니다.

**심각도:** 🟢 낮음

---

### 이슈 G: ch07_mixing.tex 40행 — CP phase 수치 검증 참조 누락

"The nonlinear mapping... has been verified numerically." → 어떤 코드/실험으로 검증했는지 참조가 없습니다.

**심각도:** 🟢 낮음

---

## 5. 독립 논문 이슈

### ~~이슈 H: compact_stars.tex — det(G_h)(ρ) 지수 감쇠 미유도~~ → **해결됨**

3×3 Gram det의 곱셈적 구조에서 지수 감쇠가 직접 나옴. ρ_sat = n_S × ρ₀ = 3ρ₀는 C³의 3개 공간 자유도에서 유도. 서술 보강 완료.

---

### ~~이슈 I: atomic_physics.tex — 양성자 질량 공식 불일치~~ → **해결됨 (동치)**

Λ_QCD = n_S × m_t × α_GUT² = 3 × (v_H/√c) × α_GUT² = 308 MeV로 치환하면
ch06의 m_p = n_S² × (v_H/√c) × α_GUT² × (1 + α_GUT·n_S/d)와 정확히 동치.
atomic_physics.tex에 등가 관계 명시 완료.

---

### 이슈 J: atomic_physics.tex 131행 vs hydrogen_error.tex — 수소 오차 분해 불일치

- atomic_physics.tex: "m_e가 DRLT에서 4% 낮기 때문"
- hydrogen_error.tex: "4.1% ghost correction + 1.1% QED running + 0.2% 2차 ghost + 0.04% reduced mass"

둘 다 같은 5.1% 총 오차를 설명하지만 분해 방식이 다릅니다. hydrogen_error.tex가 더 정밀하므로 atomic_physics.tex의 단순 서술이 오해를 줄 수 있습니다.

**심각도:** 🟢 낮음 — hydrogen_error.tex가 더 상세한 버전

---

### ~~이슈 K: webb_dipole.tex — ε₀의 공간 변동 미유도~~ → **해결됨 (심플렉스 네트워크에서 자동)**

심플렉스 네트워크에서 각 위치의 ψ 값이 다르므로 det(G_h) 분포가 다르고,
따라서 ε₀(x)의 공간 변동은 외삽이 아니라 직접적 귀결.
Σδᵢ = 0은 Tr(G)=N + Binet-Cauchy 완전성에서 전역적으로 보장.
서술 보강 완료.

---

## 6. 확인 결과: 문제 없는 항목

다음은 전 챕터에서 **일관적으로 올바른** 것들:

- ✅ G가 근본, W = |G|²/d가 파생 — 전부 올바름
- ✅ d=5 유도 (ch01 Frobenius → C, ch02 atomic uniqueness → d=5)
- ✅ (2,3) 분할의 표현론적 해석 (ch10이 가장 명확)
- ✅ α_GUT = 6/(25π²) — 전부 일관
- ✅ Ω_Λ = 1 − c/(2π) = 1 − 1/π — ch09에서 올바르게 사용 (17/25 공식 없음)
- ✅ Ghost sum rule Σδ = 0 — 수치적으로도 일관
- ✅ Representation cascade (not "rank cascade") — ch10에서 올바름
- ✅ Holevo bound에서 1 edge = 1 bit 유도 — ch04에서 올바름
- ✅ Bekenstein-Hawking S = A/4 유도 — ch04에서 올바름

---

## 7. 우선순위 요약

| 우선순위 | 이슈 | 파일 | 행동 |
|----------|------|------|------|
| 🔴 1 | true vacuum w 정의 모순 | ch09_cosmology.tex:51 | 수정 필요 |
| 🟡 2 | 심플렉스 emergent 서술 | ch06b_atoms.tex:6,10 | 도입부 보강 |
| 🟡 3 | c=2 인과관계 역전 | ch05_couplings.tex:~82 | 프레이밍 수정 |
| 🟡 4 | "Wishart modes" 용어 | ch06_masses.tex:10 | 용어 교체 |
| 🟡 5 | compact_stars det 감쇠 미유도 | compact_stars.tex:62-68 | 유도 추가 또는 가정 명시 |
| 🟡 6 | 양성자 질량 공식 이중성 | atomic_physics.tex:71 | ch06과 일관성 확인 |
| 🟡 7 | Webb dipole ε₀ 공간변동 | webb_dipole.tex:75-95 | 외삽임을 명시 |
| 🟢 8 | det(G_h) vs det(W_h) 구분 | ch04_hbar.tex:32 | 주석 추가 |
| 🟢 9 | temporal weighting 설명 | ch05_couplings.tex:31 | 설명 보강 |
| 🟢 10 | CP phase 검증 참조 | ch07_mixing.tex:40 | 참조 추가 |
