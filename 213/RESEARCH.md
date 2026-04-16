# 213 Research Summary

## 213이란
213은 자기 자신을 기술하는 데 필요한 최소 장비가 213이기 때문에 213이다.

## 핵심 결과

### 1. C(3,2) = 3 — 자기복제 유일 고정점
파일: e213 223.lean, e213_fixed.lean

### 2. swap 대칭 — e₂ ≅ e₃
swap_preserves_equiv 증명. 고유 공리 3개뿐.
파일: e213_swap.lean

### 3. 3가지 운명 — 소멸/불변/폭발
n<3 소멸, n=3 불변, n>3 폭발. 무한=순서의 착시.
파일: e213_fixed.lean

### 4. Obj ≅ Mor — 2=3
객체와 사상이 동형. 주체=객체. 레벨=시점.
파일: e213_levels.lean

### 5. 3공리 독립 (부분)
A9⊥(A8+A12), A12⊥(A8+A9) 반례 구성.
파일: e213_levels.lean

### 6. 하드웨어 비용 = 213
inductive(1)+congruence(2)+induction(3). 자기참조.
파일: e213 scratch.lean

### 7. 연속/이산 = 같은 것
inside=연속=2, outside=이산=3. 경계(1)를 넘으면 뒤집힘.
파일: e213_viewpoint.lean

### 8. 213 → DRLT
DRLT = 213 + eval(e1→0, e2→2, e3→3).
d=5, K=ℂ, (3,2) 전부 eval에서 옴.
"0 파라미터" → "1 파라미터(eval 함수)".
파일: e213_drlt.lean

## 파일 목록 (11개)
| 파일 | 줄 | 핵심 |
|------|---|------|
| 213.md | 71 | 기초 문서 |
| e213.lean | 229 | Nat eval |
| e213 pure.lean | 187 | Equiv 11공리 |
| e213 223.lean | 232 | 12공리 완성 |
| e213 runtime.lean | 177 | VM 0공리 |
| e213 scratch.lean | 235 | 하드웨어비용 |
| e213_swap.lean | 111 | swap 증명 |
| e213_fixed.lean | 75 | 고정점 |
| e213_levels.lean | 83 | 2=3+독립 |
| e213_viewpoint.lean | 67 | 연속/이산 |
| e213_drlt.lean | 71 | DRLT 연결 |

## 열린 질문
- A8 독립성 완성
- Equiv 결정가능성
- eval의 유일성 (왜 e2→2이지 e2→5가 아닌가)
