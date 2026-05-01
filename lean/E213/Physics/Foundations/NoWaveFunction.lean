import E213.Physics.Substrate
import E213.Physics.Simplex.Counts

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

namespace E213.Physics.Foundations.NoWaveFunction

open E213.Physics.Simplex.Counts

/-!
## "Measurement" / "observation" are also artifacts

Standard QM: measurement → wavefunction collapse.
  - Implies "observer" assumption
  - Non-deterministic transition

CLAUDE.md (213/CLAUDE.md): the word "observer" is prohibited in axiom descriptions.
DRLT: measurement = Lens specification change.
  - Raw does not change (no axiom violation)
  - Lens of a different layer is applied
  - No "observer", deterministic

| Standard QM | DRLT |
|---|---|
| Wave function ψ | Lens output |
| Existence probability \|ψ\|² | \|Lens output\|² (still Lens) |
| Hilbert space | Gram space (atomic) |
| Operator | Lens transformation |
| Eigenvalue = observable | Lens output = readout |
| Measurement | Lens specification |
| Collapse | Lens layer transition |
| Observer | (absent) |

## Determinism

The place of "probability" in DRLT = Lens multiplicity:
  Same Raw, different Lens → different output.
  Output may *look like a distribution* similar to "probability".
  But *fundamental* is deterministic (axiom + Lens specification one-to-one).
-/

/-- All atomic primitives determined (DecidableEq). -/
theorem atomic_decidable :
    (NS = 3) ∧ (NT = 2) ∧ (d = 5) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals decide

end E213.Physics.Foundations.NoWaveFunction
