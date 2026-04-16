# 213 Research Summary

## 213이란
213은 자기 자신을 기술하는 데 필요한 최소 장비가 213이기 때문에 213이다.

## 증명된 것

### C(3,2) = 3 (자기복제 유일 고정점)
- Obj ≅ Pairs 전단사 (roundtrip 양방향)
- choose2(n) = n의 비자명 해: n=3뿐 (1-100 계산확인)
- 파일: e213 223.lean, e213_fixed.lean

### swap 대칭 (e₂ ↔ e₃ 보존)
- swap_preserves_equiv: 12공리 전부 보존
- 함의: e₂와 e₃는 구별 불가능
- 213 고유 공리 = 3개 (plus_e1, times_e1, distrib)
- 나머지 9개 = 매체 비용 (순서가 부과)
- 파일: e213_swap.lean

### 3가지 운명
- n<3: 소멸 (C(n,2)<n → 0으로 수렴)
- n=3: 불변 (C(3,2)=3 → 고정점)
- n>3: 폭발 (C(n,2)>n → ∞로 발산)
- 파일: e213_fixed.lean

### Obj ≅ Mor (2=3)
- 객체와 사상이 동형
- 2(arity) + 3(cardinality) = 같은 구조의 두 시점
- 레벨 구조는 순서의 부산물. 순서 없이: 고정점만.
- 파일: e213_levels.lean

### 3공리 쌍별 독립
- A9 ⊥ (A8+A12): {0,1} max/const1 반례
- A12 ⊥ (A8+A9): Z/3Z 비준동형 반례
- 파일: e213_levels.lean

### 하드웨어 비용 = 213
- inductive(1) + congruence(2) + induction(3)
- 구현 비용 = 구현 대상
- 파일: e213 scratch.lean

### 공리 → 정의 전환
- 12공리 (순서 있는 Expr) → 3정의 (순서 없는 Value)
- 공리는 순서 있는 매체의 수리비
- 파일: e213 runtime.lean

## 열린 질문
- A8의 독립성 (부분 미해결)
- 연속체(R, C)로의 경로
- Equiv 결정가능성
- 분배법칙: 내재 vs 선택 (독립이므로 선택)

## 파일 목록
| 파일 | 줄 | 내용 |
|------|---|------|
| 213.md | 71 | 기초 문서 |
| e213.lean | 229 | Nat eval 버전 |
| e213 pure.lean | 187 | Equiv 11공리 |
| e213 223.lean | 232 | 12공리 완성 |
| e213 runtime.lean | 177 | VM 0공리 |
| e213 scratch.lean | 235 | Tally + 하드웨어비용 |
| e213_swap.lean | 111 | ★ swap 증명 |
| e213_fixed.lean | 75 | ★ 고정점 |
| e213_levels.lean | 83 | ★ 2=3 + 독립성 |
