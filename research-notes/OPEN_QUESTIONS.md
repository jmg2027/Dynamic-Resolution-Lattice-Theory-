# Repository Status & Open Questions

## 이번 세션 해결 사항 (2026-04-12)

### 이름 수정
- `Mingoo Jeong` → `Mingu Jeong` — 9개 파일 전부 수정 완료

### Book 일관성 수정
1. ~~true vacuum w = -1 정의 모순~~ → **해결**: ħ=0 상태는 물리적으로 존재 불가. ch04/ch09 재작성.
2. ~~심플렉스 input 서술~~ → **해결**: ch06b 도입부에 "emergent from high W_ij" 명시.
3. ~~c=2 인과관계 역전~~ → **해결**: ch05에서 "자기일관성 검증"으로 리프레이밍.
4. ~~"Wishart modes" 용어~~ → **해결**: ch06에서 "Gram matrix modes"로 교체.
5. ~~det(G_h) vs det(W_h) 모호~~ → **해결**: ch04에 Gram 부분행렬 명시.

### 독립 논문 이슈
6. ~~compact_stars det 감쇠 미유도~~ → **해결**: Gram det 곱셈적 구조에서 지수 감쇠 유도.
7. ~~atomic_physics 양성자 질량 공식 불일치~~ → **해결**: Λ_QCD = n_S·m_t·α²_GUT으로 ch06과 동치 증명.
8. ~~webb_dipole ε₀ 공간변동 미유도~~ → **해결**: 심플렉스 네트워크에서 자동 (다른 ψ → 다른 det → 다른 ε₀).

### 새 내용 추가
9. **뉴트리노 진동 메커니즘** — ch06에 추가. det>0 경계조건 + Pachner 인접 구조.
10. **심플렉스 네트워크 섹션** — ch10에 추가. Construction, hinge=1bit, forces as hinge types, confinement, 연속근사 한계.

## 남은 작업

### 자체 해결 가능
1. **drlt_book_single.tex 재생성 필요** — 챕터 파일들이 대폭 변경됨. 재컴파일 필요.
2. ~~CLAUDE.md 실험 카탈로그~~ → 이미 EXP_039~042 등록됨.
3. ~~README.md~~ → 이번 세션에서 업데이트.
4. **results/SUMMARY.md** — EXP_033 이후 내용 없음 (다음 세션에서 업데이트 가능).

### 미래 과제
1. **N_cross ≈ 1500 → 물리적 GUT 에너지 (~10¹⁵ GeV)**:
   SI 단위 변환으로 계산 가능할 수 있음.

2. **EXP_042 Regge 실험**: 다음 세션으로 이관.
   JAX 자동미분 + 해석적 gradient 둘 다 시도.
   상세: experiments/EXP_042_regge_atoms/NEXT_SESSION.md

## 실험 정리 판단

### 삭제됨 (ad hoc 에너지 함수, EXP_039~042가 대체)
- EXP_034~038 및 결과물

### 유지 (현재 이론에 부합)
- EXP_001~033, EXP_033b, EXP_039~042

### axiom/ 정리
| 파일 | 판단 |
|------|------|
| foundations.md | 유지 (현재 이론과 호환, 참고용) |
| from_one_axiom.md | 유지 (상세 유도, 한국어) |
