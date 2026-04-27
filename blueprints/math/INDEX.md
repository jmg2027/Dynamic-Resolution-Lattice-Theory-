# 213 Mathematical Tracks — Blueprint Index

다음 세션 (들)이 213을 *수학 도서관* 으로 만들기 위한 분야별
방향 문서.  각 문서는:

- *왜 이 분야가 213-native 로 의미 있는가*
- *ZFC 접근의 고통점*
- *213 에서 자연 등장 (인사이트)*
- *이미 깔린 빌딩 블록*
- *Phase 진행 계획 (구체)*
- *다른 트랙 연결*
- *미해결 문제*

분석학 213 의 100% 마라톤 (`ANALYSIS213.md` + `CATALOG213.md`) 이
*템플릿*.  같은 *tightness + propEq 0 sorry + axioms ≤ {propext,
Quot.sound}* 기준으로 각 분야 진행.

---

## 분야 인덱스

### Phase A — 핵심 수학 (자연 확장)

| # | 분야 | 파일 | 우선순위 |
|---|---|---|---|
| 01 | **Probability 213** | `01_probability_213.md` | ★★★ 최우선 |
| 02 | **Multivariable Calculus 213** | `02_multivariable_213.md` | ★★★ |
| 03 | **Topology 213** | `03_topology_213.md` | ★★★ |
| 04 | **Complex Analysis 213** (Cayley 위) | `04_complex_213.md` | ★★ |
| 05 | **Measure Theory 213** (σ-algebra 거부) | `05_measure_213.md` | ★★ |

### Phase B — 응용 수학

| # | 분야 | 파일 | 우선순위 |
|---|---|---|---|
| 06 | **Differential Equations 213** | `06_ode_pde_213.md` | ★★ |
| 07 | **Number Theory 213** (dyadic native) | `07_number_213.md` | ★★ |
| 08 | **Functional Analysis 213** | `08_functional_213.md` | ★ |

### Phase C — 대수/이산

| # | 분야 | 파일 | 우선순위 |
|---|---|---|---|
| 09 | **Linear Algebra 213** | `09_linear_algebra_213.md` | ★★ |
| 10 | **Combinatorics 213** (atomic native) | `10_combinatorics_213.md` | ★★★ |
| 11 | **Group Theory 213** | `11_group_213.md` | ★ |
| 12 | **Information Theory 213** (binary tree native) | `12_information_213.md` | ★★ |

### Phase D — 메타/철학

| # | 분야 | 파일 | 우선순위 |
|---|---|---|---|
| 13 | **213 자체 deepening** | `13_213_meta.md` | ★★★ |
| 14 | **Logic / Proof Theory 213** | `14_logic_213.md` | ★ |

### 추가 — Directory Proposal

- `00_DIRECTORY_PROPOSAL.md` — 물리/수학트랙 합의안.

---

## 작성 완료 (2026-04-27)

✅ 16 문서 모두 작성 완료 (INDEX + 00 directory + 01-14 분야).
분야별 약 100-150 줄 평균.

---

## 사용 방법

새 세션 시작 시:

1. `INDEX.md` (이 파일) 읽고 우선순위 분야 선택
2. 해당 분야 blueprint 정독
3. blueprint 의 *Phase 계획* 따라 마라톤
4. 결과는 `framework/E213/Research/Real213_<field>*.lean` 으로
5. 마라톤 종료 시 `<FIELD>213.md` paper + `CATALOG213.md` 항목 추가

---

## Author

Mingu Jeong (Independent Researcher).  Claude in Acknowledgments.
