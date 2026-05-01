import E213.Research.Real213.Core
import E213.Research.Cauchy.PellSeq
import E213.Research.Diagonal.HasModulus

/-!
# Research.Real213StrictPos: addition-friendly subtype (solution (i) to E2)

Resolving the obstruction in `E2_phase_b_obstruction.md`: Real213's
sequence has view (a, b) with a, b ≥ 1 *for all i*.

On this subtype, the sum view of addition = (a*b' + a'*b, b*b')
is always ≥ (2, 1) → liftable via abLens_witness.

## Definition

```
structure Real213StrictPos extends Real213 where
  view_pos : ∀ i, 1 ≤ (abLens.view (xs i)).1 ∧ 1 ≤ (abLens.view (xs i)).2
```

## Significance

- An *engineering refinement* of Real213 (no additional axioms).
- Phase B (arithmetic) works on this subtype.
- Cut-equivalence compatibility of Real213 ↔ StrictPos is separate work
  (every Real213 has a StrictPos *equivalent* — possible but proof
  requires sequence reshuffling).
-/

namespace E213.Research.Real213.Core

open E213.Firmware E213.Hypervisor
open E213.Research.HasModulusNS
open E213.Research.ABLens
open E213.Research.ArchimedeanCauchy

/-- Real213 with all sequence views strictly positive ((a, b) with a, b ≥ 1). -/
structure Real213StrictPos extends Real213 where
  view_pos : ∀ i, 1 ≤ (abLens.view (xs i)).1 ∧ 1 ≤ (abLens.view (xs i)).2

end E213.Research.Real213.Core

namespace E213.Research.Real213.Core

open E213.Firmware E213.Hypervisor
open E213.Research.HasModulusNS
open E213.Research.ABLens
open E213.Research.ArchimedeanCauchy

/-- Diagonal sequence: xs n = Raw with view (n+1, n+1) via abLens_witness. -/
def diagonalRaw (n : Nat) : Raw :=
  (E213.Research.PellSeq.abLens_witness ((n+1) + (n+1)) (n+1) (n+1)
    rfl (Nat.succ_le_succ (Nat.zero_le _))
    (Nat.succ_le_succ (Nat.zero_le _))).1

theorem diagonalRaw_view (n : Nat) :
    abLens.view (diagonalRaw n) = (n+1, n+1) :=
  (E213.Research.PellSeq.abLens_witness ((n+1) + (n+1)) (n+1) (n+1)
    rfl (Nat.succ_le_succ (Nat.zero_le _))
    (Nat.succ_le_succ (Nat.zero_le _))).2

/-- Diagonal sequence is a Real213StrictPos instance — concrete inhabitance. -/
def diagonalReal : Real213StrictPos where
  xs := diagonalRaw
  modulus := E213.Research.DiagonalHasModulus.diagonalHasModulus diagonalRaw diagonalRaw_view
  view_pos := by
    intro n
    rw [diagonalRaw_view]
    exact ⟨Nat.succ_le_succ (Nat.zero_le _),
           Nat.succ_le_succ (Nat.zero_le _)⟩

end E213.Research.Real213.Core
