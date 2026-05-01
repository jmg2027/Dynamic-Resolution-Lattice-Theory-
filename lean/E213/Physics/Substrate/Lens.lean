import E213.Hypervisor.Lens
import E213.Physics.Substrate.Origin

/-!
# Phase 2 Lens — actual Lens objects (as recommended by audit)

**Layer: Hypervisor** (direct Lens object definition + Raw usage).

Previous Phase 2 files were *App-layer* arithmetic (partition over Fin 5).
This file goes one level deeper — defining actual Lens objects at the
*Hypervisor-layer* + demo of operation over Raw.

## Math track Lens definition (Hypervisor/Lens.lean)

```lean
structure Lens (α : Type) where
  base_a  : α
  base_b  : α
  combine : α → α → α

def Lens.view (L : Lens α) (r : Raw) : α :=
  r.fold L.base_a L.base_b L.combine
```

## This file — first explicit Lens in Phase 2

  `parityLens : Lens Bool` —
    base_a = false (parity 0 for a)
    base_b = true  (parity 1 for b)
    combine = xor   (parity addition)

  *b-count mod 2* among Raw's leaves.

(This is a simple demo Lens — the actual atomicity (3,2) classification Lens
needs a more complex definition, outside this file's scope.)
-/

namespace E213.Physics.Substrate.Lens

open E213.Firmware E213.Hypervisor

/-- First explicit Lens in Phase 2: parity (b-count mod 2). -/
def parityLens : Lens Bool where
  base_a  := false
  base_b  := true
  combine := xor

/-- Raw.a parity = false (0 b's). -/
theorem parity_at_a : parityLens.view Raw.a = false := rfl

/-- Raw.b parity = true (1 b). -/
theorem parity_at_b : parityLens.view Raw.b = true := rfl

/-- Two Lens objects with same view result → equiv relation. -/
theorem parity_a_eq_a : parityLens.equiv Raw.a Raw.a :=
  parityLens.equiv_refl Raw.a

/-- Parity differs between Raw.a and Raw.b. -/
theorem parity_a_neq_b : parityLens.view Raw.a ≠ parityLens.view Raw.b := by
  rw [parity_at_a, parity_at_b]
  intro h
  exact Bool.noConfusion h

/-- Another demo Lens: count b-leaves (returns Nat). -/
def bCountLens : Lens Nat where
  base_a  := 0
  base_b  := 1
  combine := (· + ·)

/-- Basic behavior of bCount. -/
theorem bCount_at_a : bCountLens.view Raw.a = 0 := rfl
theorem bCount_at_b : bCountLens.view Raw.b = 1 := rfl

/-- ★ Phase 2 first explicit Lens demo — synthesis ★ -/
theorem phase2_lens_demo :
    -- parity Lens
    (parityLens.view Raw.a = false)
    ∧ (parityLens.view Raw.b = true)
    -- bCount Lens
    ∧ (bCountLens.view Raw.a = 0)
    ∧ (bCountLens.view Raw.b = 1)
    -- d=5 cosmos (Origin)
    ∧ E213.Firmware.Atomicity.Five.Atomic 5 := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  exact E213.Firmware.Atomicity.Five.atomic_five

end E213.Physics.Substrate.Lens
