# Phase 2 — 213만으로 우주를 다시 그리기

Phase 1 (E213/Physics/, 68 files) 은 *기존 정밀 양*을 atomic
primitives에서 도출했음.

Phase 2는 **다 잊고 다시** 묻는다:

> *213 axiom만으로 우주에 대해 무엇을 말할 수 있는가?*

---

## 진행 (educational + 직관 순)

### 1. `Origin.lean` — *몇 차원?*

213 axiom + Atomicity → **d = 5**, 다른 선택지가 axiom 위반.
이 한 정리가 Phase 2의 *씨앗*.

```lean
theorem only_one_cosmos_dim :
    ∀ n, Atomic n ↔ n = 5 := ...
```

---

### 2. `Shape.lean` — *그럼 어떻게 생겼나?*

```
  ●───●───●         ← 3-block (a-block)
   \  |  /          
    \ | /           
     \|/            
      X             ← cross-pairs (6개)
     /|\            
    / | \           
   /  |  \          
  ●───●             ← 2-block (b-block)
```

5 점 = 3 점 + 2 점.  Edge: 3 (triangle) + 1 (line) + 6 (cross) = 10.

수학 용어로: **4-simplex Δ⁴ with (3,2) vertex partition**.

---

### 3. `Existence.lean` — *5는 무엇인가?*

  `Vertex := Fin 5`.
  
  두 vertex가 *같은가* 는 `DecidableEq` (axiom 결정).
  
  Block 분류:
  - `inBigBlock v` — 3-block에 속함
  - `inSmallBlock v` — 2-block에 속함

213만의 *최대 ontology*: "5 vertex, (3,2) 크기 분할".  더 이상의
이름·의미는 Lens 추가 시.

---

### 4. `Pairs.lean` — *쌍 사이 무엇이 있나?*

10 쌍이 자동으로 세 분류:

| 분류 | 개수 | 의미 |
|---|---|---|
| AA | 3 | 둘 다 big block (triangle 내부 edge) |
| BB | 1 | 둘 다 small block (line 자체) |
| AB | **6** | cross — **K_{3,2} bipartite edges** |

**6 cross pairs = K_{3,2} bipartite 그래프.  자연 발생.**

(Phase 1의 PhotonKernel이 이 위에서 cycle space b_1 = 8 = α_3
발견했었는데, *그 본체 K_{3,2}* 가 axiom-derived라는 거 확인.)

---

## 213이 *말할 수 있는 모든 것* (Phase 2 끝)

```
우주:
  d = 5 (차원)
  5 vertex (무엇 5개)
  (3, 2) partition (block 크기, labels는 Lens)
  10 pair information (3 AA + 1 BB + 6 AB)
```

이게 *전부*.

더 나아가려면:
- *labels* (어느 게 spatial, 어느 게 temporal) → **Lens 추가**
- *측정값* (mass, coupling, ...) → **Lens output**
- *force* (게이지) → **Lens 분류 (channel)**
- 나머지 모든 물리 → **Lens 출력**

---

## Phase 1 vs Phase 2 비교

| | Phase 1 | Phase 2 |
|---|---|---|
| 출발점 | 기존 정밀 양 | 213 axiom만 |
| 첫 import | NS=3, NT=2 *수치* | Atomicity *정리* |
| 답 | 137, m_p, etc. | d=5, 5 vertex, 10 쌍 |
| Atomic atoms | 등장 | 정의됨 |
| 쓸모 | 기존 물리 매치 검증 | 의미적 출발점 명시 |

두 트랙 *상호보완*.  Phase 1이 끝점 (정밀 매치), Phase 2가 시점
(axiom 의미).

---

### 5. `Time.lean` — NT 섹터 = dyadic resolution

NT = 2 atomic 작은 block 크기.  *수학 트랙 bridge* 활용:
NT step 이 *2-진 dyadic 분할* 로 unfolded.

  `NT_n_steps_yield_two_pow : bisectN^n start = 2^n branches`

(수학 트랙 `Real213/Phase A→C` dyadic geometry = 물리 NT
섹터의 axiom-level 의미.)

---

### 6. `Space.lean` — NS 섹터 = ternary resolution

NS = 3 atomic 큰 block 크기.  3^n ternary unfolding.

NT vs NS *비대칭* (3/2)^n 가 Phase 1 의 m_μ/m_e factor,
Y-norm, Fibonacci F_5/F_4 의 axiom-level 기원.

---

### 7. `Observable.lean` — 측정 가능한 양

213 axiom 만으로 정의 가능한 *9 정수*:
d, NS, NT, c, total_pairs, AA, BB, AB,
num_directed_edges, cycle_space_dim.

Phase 1 의 정밀 양들은 이 9 의 Lens output.

---

### 8. `Force.lean` — 3 channel = 3 force?

  - AA (3 pairs): NS-internal, color-like / α_3
  - BB (1 pair):  NT-internal, weak-like / α_2
  - AB (6 pairs): cross-sector, EM-like / α_1

★ 3 force 자연 발생 ★ (channel 크기 ≠ 결합 강도 직접 비례,
Phase 1 prefactor 가 더 깊은 origin.)

---

### 9. `Edges.lean` — c=2 doubling, b_1=8

c = 2 = NT atomic size.  6 undirected → 12 directed.
Cycle space b_1 = 12 - 5 + 1 = 8 = NS² - 1.

**8 = 1/α_3** (Phase 1 PhotonKernel 의 axiom-level 산술).

---

### 10. `Lens.lean` — Hypervisor explicit Lens

수학 트랙 `Hypervisor/Lens.lean` 패턴 직접 사용.  첫 명시적
Lens 객체 (parityLens, bCountLens) — App-layer 산술이 아닌
*Hypervisor-layer* 에서 Raw 위 동작.

---

### 11. `Capstone.lean` — 10 파일 단일 종합

26 conjunct 정리, ≤ propext + Quot.sound.  Phase 2 *전체* 의
형식 종합.

---

## 빌드

```bash
cd 213/framework
lake build E213.Physics.Phase2.Capstone   # 전체 종합 (10 파일)
```

모두 0 sorry, ≤ propext + Quot.sound (Lean 4 core only).
대부분 파일은 *완전 axiom-free*.

---

## 운영 원칙

CLAUDE.md "관측자/구조/관계/공간/인식" 단어 axiom 설명에 X.
"원시적 구분" 만 사용.  나머지는 Lens 출력 명시.

`AUDIT.md` — 수학 트랙 (extreme rigor) 대조 감사:
**Phase 2 위반 없음**.  App/Simplex 패턴 그대로 따름.
