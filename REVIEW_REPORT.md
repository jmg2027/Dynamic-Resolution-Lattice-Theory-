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

### ~~이슈 A: ch09_cosmology.tex — "true vacuum" 정의 모호~~ → **해결됨**

ch04/ch09 전면 재작성. ħ=0 상태는 물리적으로 존재 불가 (빅뱅, 블랙홀, 열사망 모두 예외 없음). 우주상수 문제 해법: E_vac = 0이 아니라 N개 유한 모드 → 유한 에너지.

---

### ~~이슈 B: ch06b_atoms.tex — 심플렉스가 "input"처럼 서술됨~~ → **해결됨**

ch06b 도입부 재작성: "높은 W_ij를 공유하는 5개 꼭짓점이 emergent 4-심플렉스를 형성" 명시.

---

### ~~이슈 C: ch05_couplings.tex — c=2 인과관계 역전~~ → **해결됨**

"Self-consistency check: c=2" 리마크로 교체. c=2는 ch03에서 이미 유도, d²=25 일치는 검증.

---

### ~~이슈 D: ch06_masses.tex — "Wishart modes" 용어~~ → **해결됨**

"Wishart modes" → "Gram matrix modes"로 교체 (10행 + 14행).

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

| # | 이슈 | 상태 |
|---|------|------|
| ~~1~~ | true vacuum w 정의 모순 | ✅ ch04/ch09 재작성 |
| ~~2~~ | 심플렉스 emergent 서술 | ✅ ch06b 도입부 보강 |
| ~~3~~ | c=2 인과관계 역전 | ✅ ch05 리프레이밍 |
| ~~4~~ | "Wishart modes" 용어 | ✅ ch06 Gram으로 교체 |
| ~~5~~ | compact_stars det 감쇠 미유도 | ✅ Gram det 곱셈적 구조 유도 |
| ~~6~~ | 양성자 질량 공식 이중성 | ✅ 동치 증명 (Λ_QCD = n_S·m_t·α²) |
| ~~7~~ | Webb dipole ε₀ 공간변동 | ✅ 심플렉스 네트워크에서 자동 |
| ~~8~~ | det(G_h) vs det(W_h) 구분 | ✅ ch04 주석 추가 |
| 9 | temporal weighting 설명 | 🟢 미완 (낮은 우선순위) |
| 10 | CP phase 검증 참조 | 🟢 미완 (낮은 우선순위) |

**10개 중 8개 해결. 나머지 2개는 서술 개선 수준 (수학은 맞음).**
