import E213.Hypervisor.Lens
import E213.Prelude

/-!
# Research.IdentityLens: Raw → Raw identity Lens + Yoneda-dual

Partial answer to Note 34 Q34.4.

**Self-encoding is not possible** — since `Lens α` depends on `α`,
there is no canonical `Lens.fromRaw : Raw → Lens α` for all `α`.

**But the dual is natural** — each Raw element `r` is a function
that evaluates every Lens:

```
Raw.eval r {α} (L : Lens α) : α := L.view r
```

This dual is `Lens.view L : Raw → α` viewed from the Raw side.

- §1. **identity Lens `idLens : Lens Raw`** — the simplest implementation
  of Q34.3 (codomain = Raw).
- §2. Injective Lens witness.  `r ↦ Raw.eval r idLens` is injective.
-/

namespace E213.Research.IdentityLens

open E213.Firmware E213.Hypervisor

/-- Identity Lens: view = id on Raw.  combine is Raw.slash
    (x ≠ y branch), diagonal fallback to Raw.a — the diagonal
    is never hit during view computation (guaranteed by `x ≠ y`
    in the slash branch). -/
def idLens : Lens Raw where
  base_a := Raw.a
  base_b := Raw.b
  combine x y := if h : x ≠ y then Raw.slash x y h else Raw.a

theorem idLens_symmetric :
    ∀ u v : Raw, idLens.combine u v = idLens.combine v u := by
  intro u v
  by_cases h : u = v
  · rw [h]
  · show (if h : u ≠ v then Raw.slash u v h else Raw.a)
         = (if h : v ≠ u then Raw.slash v u h else Raw.a)
    rw [dif_pos h, dif_pos (Ne.symm h)]
    exact Raw.slash_comm u v h

end E213.Research.IdentityLens

namespace E213.Research.IdentityLens

open E213.Firmware E213.Hypervisor

theorem idLens_is_id : ∀ r : Raw, idLens.view r = r := by
  intro r
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hfs : idLens.view (Raw.slash x y h)
                   = idLens.combine (idLens.view x) (idLens.view y) :=
        Raw.fold_slash idLens.base_a idLens.base_b idLens.combine
          idLens_symmetric x y h
      rw [hfs, ihx, ihy]
      show (if h' : x ≠ y then Raw.slash x y h' else Raw.a)
           = Raw.slash x y h
      rw [dif_pos h]

end E213.Research.IdentityLens

namespace E213.Research.IdentityLens

open E213.Firmware E213.Hypervisor

/-- `idLens.view` is injective (in fact, the identity). -/
theorem idLens_injective : Function.Injective idLens.view := by
  intro x y hxy
  rw [idLens_is_id x, idLens_is_id y] at hxy
  exact hxy

/-- **Yoneda-dual**: Raw element r as a function that evaluates
    every Lens α.  The dual perspective of `L.view : Raw → α`. -/
def Raw.eval (r : Raw) {α : Type} (L : Lens α) : α := L.view r

/-- `r ↦ Raw.eval r idLens` is injective.  That is, Raw elements
    are distinguished from each other as Lens-evaluators. -/
theorem raw_distinguished_by_idLens :
    Function.Injective (fun r : Raw => Raw.eval r idLens) :=
  idLens_injective

end E213.Research.IdentityLens
