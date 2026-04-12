# Repository Cleanup & Open Questions

## 실험 정리 판단

### 삭제 대상 (ad hoc 에너지 함수 사용, 현재 이론과 방법론 불일치)

| 파일 | 이유 |
|------|------|
| EXP_034_helium.py | ad hoc 에너지, 잘못된 접근 (EXP_040이 대체) |
| EXP_034b_helium_variational.py | ad hoc 에너지, STT=0 문제 (EXP_042가 대체) |
| EXP_035_periodic_table.py | 차폐 모델, 단조 증가 에너지 (구조적 오류) |
| EXP_036_simplex_atoms.py | core 공유 구조 잘못됨 (ΔE 일정) |
| EXP_037_simplex_chemistry.py | ad hoc coupling×√det, IE 계산 실패 |
| EXP_038_h_spectrum.py | 직교 T₂로 호핑=0 (교훈으로만 가치) |
| results/EXP_034*.txt, EXP_035~038*.txt | 위 실험의 결과물 |

### 유지 대상 (현재 이론에 부합하는 올바른 실험)

| 파일 | 이유 |
|------|------|
| EXP_001~033 | 전부 유효 (각자의 물리를 올바르게 검증) |
| EXP_033b_webb_vs_mu.py | 솔직한 결과 (텐션 발견 → 자기교정 → 교훈) |
| EXP_039_bond_angles.py | 정확! CH₄/NH₃/H₂O 전부 exact |
| EXP_040_hydrogen_exact.py | 정확! E_n = -m_e α²/(n_T n²) |
| EXP_041_rank_cascade.py | 유효한 관찰 실험 |
| EXP_042_regge_atoms/ | 진행 중, 올바른 방법론 (Regge action) |

### axiom/ 정리

| 파일 | 판단 |
|------|------|
| foundations.md | 유지 (현재 이론과 호환, 참고용) |
| from_one_axiom.md | 유지 (상세 유도, 한국어) |
| 나머지 5개 | 삭제 가능 (book/이 전부 대체) |

## 책에서 발견된 미해결 문제 / 비일관성

### 자체 해결 가능

1. **drlt_book_single.tex 재생성 필요** — ch10 변경 후 single file이 outdated
2. **CLAUDE.md 실험 카탈로그** — EXP_039~042 미등록
3. **README.md** — 완전히 outdated (W-based axiom 기술)
4. **results/SUMMARY.md** — EXP_033 이후 내용 없음

### 저자에게 물어볼 것

1. ~~Ω_Λ = 1-c/(2π) vs 17/25~~ → **해결: 1-c/(2π)만 사용** (지평선 결핍각)

2. ~~w = -1 exact vs w ≈ -1~~ → **해결: w ≈ -1 (진짜 진공은 우리 우주에 없음)**
   ch09 수정 완료. 편차 ~ε₀² ~ 10⁻⁵.

3. ~~Effective rank vs representation~~ → **해결: representation cascade** 
   ch10 수정 완료. (2,3)은 표현론적 구조, 스펙트럼 gap 아님.

4. **N_cross ≈ 1500 → 물리적 GUT 에너지 (~10¹⁵ GeV)**: 
   SI 단위 변환으로 계산 가능할 수 있음. 미래 과제.

5. **EXP_042 Regge 실험**: 다음 세션으로 이관. 
   JAX 자동미분 + 해석적 gradient 둘 다 시도.
   상세: experiments/EXP_042_regge_atoms/NEXT_SESSION.md
