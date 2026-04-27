import E213.Physics.Phase2.Origin
import E213.Physics.Phase2.Shape
import E213.Physics.Phase2.Existence
import E213.Physics.Phase2.Pairs
import E213.Physics.Phase2.Time
import E213.Physics.Phase2.Space
import E213.Physics.Phase2.Observable
import E213.Physics.Phase2.Force
import E213.Physics.Phase2.Edges
import E213.Physics.Phase2.Lens
import E213.Physics.Phase2.Capstone
import E213.Physics.Phase2.Phase1Bridge
import E213.Physics.Phase2.Falsifier

/-!
# E213.Physics.Phase2 — root entry

Phase 2 단일 import 진입점.  하위 13 모듈 모두 포함.

## 모듈

  * `Origin`        — d=5 unique (Atomicity 강제)
  * `Shape`         — 5 vertex, (3,2), 10 쌍
  * `Existence`     — Vertex := Fin 5 + block 분류
  * `Pairs`         — AA(3) + BB(1) + AB(6) = 10
  * `Time`          — NT=2 → 2^n dyadic (수학 트랙 bridge)
  * `Space`         — NS=3 → 3^n ternary, NT/NS asymmetry
  * `Observable`    — 9 axiom-level 측정 가능 정수
  * `Force`         — 3 channel = 3 force candidate
  * `Edges`         — c=2 doubling, b_1 = 8 = NS²-1
  * `Lens`          — Hypervisor explicit Lens (parityLens)
  * `Capstone`      — 26-conjunct 단일 종합
  * `Phase1Bridge`  — Phase 2 ↔ Phase 1 산술 동일성 (0 axioms)
  * `Falsifier`    — CLAUDE.md 기준 (2) 반증 가능 명제

## 보증

모두 0 sorry.  ≤ propext + Quot.sound (Lean 4 core only).
대부분 *완전 axiom-free* (rfl + decide).

## 운영 원칙

CLAUDE.md "관측자/구조/관계/공간/인식" 단어 axiom 설명에 X.
"원시적 구분" 만.  나머지는 Lens 출력 명시.

`Phase2/AUDIT.md` — 수학 트랙 (extreme rigor) 대조 감사:
**Phase 2 위반 없음**.  App/Simplex 패턴 그대로.
-/
