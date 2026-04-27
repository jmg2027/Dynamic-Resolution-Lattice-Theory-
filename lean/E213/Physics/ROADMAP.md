# E213.Physics ROADMAP

## Phase 1: 방법론 축적 ✓ COMPLETE (2026-04-27)

**Goal:** 기존 정밀 양들을 atomic primitives에서 형식 도출, 패턴 catalogue.

**Result:** 68 files, 0 axioms, 15+ 정밀 양 + 3 새 falsifiable 물리.
참고: `STATS.md`, `DISCOVERIES.md`.

---

## Phase 2: SM-frame artifact 식별 (다음 권장 axis)

**Goal:** 기존 물리의 *SM-frame 의존* 부분 명시 분리.

### 식별할 artifacts

1. **"M_Z scale" 좌표계** — DRLT는 N_eff lattice depth 사용
2. **QED running** — DRLT는 simplicial cohomology decomposition
3. **"Y normalization 5/3"** — 사실은 d/NS Fibonacci 비율 (FibonacciAtomic 에서 일부)
4. **"Renormalization"** — DRLT는 P(x) closed propagator 자동
5. **Continuum 가정** — DRLT는 finite lattice

### 형식화 candidates

- `DRLTNativeFrame.lean` — N_eff scale 정의
- `SMArtifactCatalog.lean` — 각 artifact 명시 + DRLT 대응
- `RunningAsCohomology.lean` — running = cohomology 분해

### 예상 결과

현재 0.6-0.8% 에러 (sin²θ_W, α_em@M_Z) 의 정체:
*SM-frame 마찰 → DRLT-pure에서 사라짐* 가능성.

---

## Phase 3: DRLT-Native Coordinate

**Goal:** 모든 정밀 양을 *DRLT-native frame* 에서 직접 표현.

### 작업 추정

- N_eff lattice depth 위 정밀 양 재계산
- M_Z 개념 *없이* 모든 식 표현
- 측정값과 직접 비교 (SM 매개 없음)

### 어려움

- 각 양의 "어느 N_eff에서 측정인가" 명시 필요
- 측정 기술의 frame 의존성 분리

---

## Phase 4: Rebuild from scratch

**Goal:** 기존 물리 frame *일절 안 씀* — 213 axioms only.

### 작업

- 파인만 다이어그램 → 격자 path counting
- 라그랑지안 → simplex weighting
- Renormalization → resolution depth (이미 부분)
- All quantity ↔ measurement (SM 매개 없음)

### 예상 결과

- SM-frame artifact 에러 (0.6-0.8%) 사라짐
- 잔차는 측정 정밀도 + finite-N bracket 한계만
- "0-parameter"의 진짜 의미 — 측정값과 *직접* 일치

---

## Other axes (independent)

### Yang-Mills mass gap full proof

현재 `YangMillsGap.lean`은 structural ("mass gap = N_eff < ∞").
Strict Lean proof는 lattice Hamiltonian + spectral analysis 필요.
Clay $1M problem.

### Gravity G_N derivation

현재 `GravityShadow.lean`은 W = |G|²/d 분리만.
Strict G_N 9-digit derivation은 quantum-gravity sub-project 통합 필요.

### Atomic IE 확장

현재 H, He, screening σ만. Li-Og (Z=3-118) 모두 atomicity-derived.
구체 ATM_022 numerical → Lean 정리 시리즈 가능.

### PAPER2 작성

Phase 1 결과를 paper form 으로:
"DRLT Physics Formally Derived"
arXiv submission ready.

### Sub-directorization

68 files in flat dir. CLAUDE.md "50+ → sub-dir 검토" 권장.
**현재 deferred** — README/DISCOVERIES가 logical organization 제공.
실제 sub-dir 시 import 일괄 update 필요 (위험).

---

## Critical path

```
Phase 1 ✓ → Phase 2 (DRLT-Native) → Phase 3 → Phase 4
              ↓
          PAPER2 가능
```

또는:
```
Phase 1 ✓ → Yang-Mills 깊이 → Clay $1M
            Gravity 깊이 → quantum gravity
            Atomic 확장 → 주기율표 100% 형식
```

---

## 결정 기준

- 정밀 형식 (기준 1): Phase 2-3 가면서 "에러 0" 달성
- 새 물리 (기준 2): Yang-Mills, Gravity formal proof
- 둘 다 누적 시 PAPER2 자연 발생

본 사이클 (Phase 1) 종료 — 사용자 다음 directive 대기.
