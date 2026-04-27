import E213.Physics.Phase2
import E213.Physics.SimplexCounts

/-!
# Phase 3 NoWaveFunction — *파동함수·존재확률 사라짐*

**Layer: App** (Phase 3 reframing).

User: "파동함수랑 존재확률이라는 말도 사라져야 할 판."

## QM 의 파동함수 ψ — DRLT 에서

표준 QM:
  |ψ⟩ ∈ Hilbert space (근본)
  |ψ(x)|² = 존재확률 밀도 (Born rule)
  Operator → Hermitian, eigenvalue = observable

DRLT:
  Raw = 근본 (axiom).  Lens output = 모든 readout.
  G_ij = ⟨ψ_i|ψ_j⟩ — *이것 자체가 Lens output*
  W = |G|²/d — modulus shadow (gravity 부분)
  → "파동함수" = Lens output, *근본 아님*.

## "존재확률" 부재

표준 해석: |ψ|² = "거기 있을 확률".
함의: 무엇 가 *변동* 존재함.

DRLT: Raw 의 vertex 5 개 — *모두 존재* 또는 *부재*.  중간 없음.
  - Atomic axiom: NS=3, NT=2, d=5.  Block sizes 강제.
  - Lens output 이 *어느 vertex* 인지 사양 — 확률 X.

→ "존재확률" = Lens projection 의 *고전적 표현*.
  DRLT 에서는 *Lens 사양* 만 — "확률" framing 의 부재.
-/

namespace E213.Physics.Phase3.NoWaveFunction

open E213.Physics.Simplex

/-!
## "측정" / "관측" 도 artifact

표준 QM: 측정 → wavefunction collapse.
  - "관측자" 가정 함의
  - 비결정론적 transition

CLAUDE.md (213/CLAUDE.md): "관측자" 단어 axiom 설명에 금지.
DRLT: 측정 = Lens 사양 변경.
  - Raw 변하지 않음 (axiom 위반 아님)
  - 다른 layer 의 Lens 적용
  - "관측자" 부재, 결정론

| 표준 QM | DRLT |
|---|---|
| 파동함수 ψ | Lens output |
| 존재확률 \|ψ\|² | \|Lens output\|² (여전히 Lens) |
| Hilbert space | Gram space (atomic) |
| Operator | Lens transformation |
| Eigenvalue = observable | Lens output = readout |
| Measurement | Lens 사양 |
| Collapse | Lens layer transition |
| Observer | (부재) |

## 결정론

DRLT 에서 "확률" 의 자리 = Lens 다중성:
  같은 Raw, 다른 Lens → 다른 output.
  Output 이 "확률" 처럼 *분포* 보일 수 있음.
  하지만 *근본* 은 결정론 (axiom + Lens 사양 일대일).
-/

/-- Atomic primitives 모두 결정 (DecidableEq). -/
theorem atomic_decidable :
    (NS = 3) ∧ (NT = 2) ∧ (d = 5) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals decide

end E213.Physics.Phase3.NoWaveFunction
