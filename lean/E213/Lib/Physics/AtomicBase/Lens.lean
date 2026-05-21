import E213.Lens.LensCore
import E213.Lib.Physics.AtomicBase.Origin

/-!
# Phase 2 Lens — actual Lens objects (as recommended by audit)

**Layer: Lens** (direct Lens object definition + Raw usage).

Previous Phase 2 files were *App-layer* arithmetic (partition over Fin 5).
This file goes one level deeper — defining actual Lens objects at the
*Lens-layer* + demo of operation over Raw.

## Math track Lens definition (Lens.lean)

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

namespace E213.Lib.Physics.AtomicBase.Lens

open E213.Theory E213.Lens

/-- First explicit Lens in Phase 2: parity (b-count mod 2). -/
def parityLens : Lens Bool where
  base_a  := false
  base_b  := true
  combine := xor

/-- Another demo Lens: count b-leaves (returns Nat). -/
def bCountLens : Lens Nat where
  base_a  := 0
  base_b  := 1
  combine := (· + ·)

/-- ★ Phase 2 first explicit Lens demo — synthesis ★

  Bundles parityLens behaviors (false at a, true at b, equiv refl,
  differs at a/b), bCountLens behaviors (0 at a, 1 at b), and
  the d=5 atomicity cosmos identity. -/
theorem phase2_lens_demo :
    -- parityLens behavior
    (parityLens.view Raw.a = false)
    ∧ (parityLens.view Raw.b = true)
    ∧ parityLens.equiv Raw.a Raw.a
    ∧ (parityLens.view Raw.a ≠ parityLens.view Raw.b)
    -- bCountLens behavior
    ∧ (bCountLens.view Raw.a = 0)
    ∧ (bCountLens.view Raw.b = 1)
    -- d=5 cosmos (Origin)
    ∧ E213.Theory.Atomicity.Five.Atomic 5 := by
  refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, ?_⟩
  · exact parityLens.equiv_refl Raw.a
  · intro h; exact Bool.noConfusion h
  · exact E213.Theory.Atomicity.Five.atomic_five

end E213.Lib.Physics.AtomicBase.Lens
