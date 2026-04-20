import E213.Firmware.Raw
import E213.Hypervisor.Lens
import E213.Meta.LensCatalog
import E213.Research.ZI
import E213.Research.ZIDomain

/-!
# Research: the `ZI`-Lens as a candidate counterexample

Constructs `ziLens : Lens ZI` with `base_a = I`, `base_b = -I`,
`combine = ZI.mul`. This file defines the Lens structure and
notes which of R1–R4 are formalised here vs pending.

**Status (current session):**
- R1 (binary combine): ✓ by `Lens` structure, trivial
- R2 (catamorphism + commutativity): ✓ combine is `ZI.mul`,
  commutative by `ZI.mul_comm`
- R3 (NonVanishing = integral domain): **pending Lean** —
  requires `|uv|² = |u|² |v|²` (polynomial identity, hard
  without `ring`); argued mathematically in
  `notes/01_zi_counterexample.md`
- R4 (SwapMatching via `ZI.conj`): **pending Lean** — requires
  Raw-level induction not exposed through the current
  Firmware API; argued mathematically in the note.

The math argument establishes the counterexample; Lean
formalisation is the next iteration.
-/

namespace E213.Research

open E213.Firmware E213.Hypervisor

/-- The candidate Lens: codomain `ZI`, base values `i`, `-i`,
    combine = Gaussian multiplication. -/
def ziLens : Lens ZI where
  base_a  := ZI.I
  base_b  := ZI.negI
  combine := ZI.mul

-- Smoke test: base-value computations.
example : ziLens.view Raw.a = ZI.I    := rfl
example : ziLens.view Raw.b = ZI.negI := rfl

end E213.Research
