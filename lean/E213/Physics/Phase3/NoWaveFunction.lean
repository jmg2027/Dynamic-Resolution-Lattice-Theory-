import E213.Physics.Phase2
import E213.Physics.SimplexCounts

/-!
# Phase 3 NoWaveFunction — *wave function and existence probability disappear*

**Layer: App** (Phase 3 reframing).

User: "The words 'wave function' and 'existence probability' are also bound to disappear."

## Wave function ψ in QM — from DRLT perspective

Standard QM:
  |ψ⟩ ∈ Hilbert space (fundamental)
  |ψ(x)|² = existence probability density (Born rule)
  Operator → Hermitian, eigenvalue = observable

DRLT:
  Raw = fundamental (axiom).  Lens output = all readouts.
  G_ij = ⟨ψ_i|ψ_j⟩ — *this itself is Lens output*
  W = |G|²/d — modulus shadow (gravity part)
  → "wave function" = Lens output, *not fundamental*.

## Absence of "existence probability"

Standard interpretation: |ψ|² = "probability of being there".
Implication: something exists with *fluctuation*.

DRLT: 5 vertices of Raw — *all exist* or *absent*.  No in-between.
  - Atomic axiom: NS=3, NT=2, d=5.  Block sizes forced.
  - Lens output specifies *which vertex* — no probability.

→ "Existence probability" = *classical expression* of Lens projection.
  In DRLT there is only *Lens specification* — no "probability" framing.
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
