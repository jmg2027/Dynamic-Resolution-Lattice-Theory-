import E213.Firmware.Raw
import E213.Hypervisor.Lens

/-!
# Meta: Lens catalog — different lenses, different mathematics

The axiom supplies `Raw` only. Any mathematical *content* (numbers,
equality, set-like collections, …) arises from applying a Lens.
A Lens is a free choice of codomain and combine; distinct Lenses
yield distinct extracted mathematics from the same `Raw`.

**Organising principle.** A Lens's visibility of `Raw.swap`
partitions the catalogue:

- *Swap-blind:* `L.view (swap r) = L.view r` for all `r`.
- *Swap-visible:* `L.view (swap r)` differs from `L.view r`.

We show the swap-blind branch formally (`depth`, `leaves` Lenses);
the swap-visible branch is illustrated by a ℤ-valued "signed"
Lens realising `swap` as negation — an integer-level analogue of
complex conjugation.
-/

namespace E213.Meta

open E213.Firmware E213.Hypervisor

-- ═══ Swap-blind lenses ═══

/-- **Depth lens is swap-blind.**  With `base_a = base_b = 0`,
    the Lens collapses the `a ↔ b` distinction already at the
    base; `swap` is invisible at every level. -/
theorem depth_swap_invariant (r : Raw) :
    Lens.depth.view (Raw.swap r) = Lens.depth.view r := by
  show Raw.fold 0 0 (fun a b => 1 + max a b) (Raw.swap r)
     = Raw.fold 0 0 (fun a b => 1 + max a b) r
  rw [Raw.fold_eq_depth, Raw.fold_eq_depth, Raw.swap_depth]

/-- **Leaves lens is swap-blind.** Same base value for `a` and
    `b`. The Lens counts size, erasing identity. -/
theorem leaves_swap_invariant (r : Raw) :
    Lens.leaves.view (Raw.swap r) = Lens.leaves.view r := by
  show Raw.fold 1 1 (· + ·) (Raw.swap r) = Raw.fold 1 1 (· + ·) r
  rw [Raw.fold_eq_leaves, Raw.fold_eq_leaves, Raw.swap_leaves]

end E213.Meta

-- ═══ Swap-visible lens: signed (Int) ═══

namespace E213.Meta

open E213.Firmware

/-- Signed lens: `a ↦ 1`, `b ↦ -1`, combine = `+`.
    Base values differ in sign, so `swap` becomes visible as
    negation on the image. This is the ℤ-level analogue of
    "swap realised as complex conjugation" (the axiom's ℂ-Lens
    identification of §4 of the paper). -/
def signedLens : Hypervisor.Lens Int where
  base_a  := 1
  base_b  := -1
  combine := (· + ·)

/-- Swap acts as negation on the image of the signed Lens. -/
theorem signed_swap_neg (r : Raw) :
    signedLens.view (Raw.swap r) = - signedLens.view r := by
  show Raw.fold (1 : Int) (-1) (· + ·) (Raw.swap r)
     = - Raw.fold (1 : Int) (-1) (· + ·) r
  exact Raw.fold_signed_swap r

end E213.Meta

namespace E213.Meta

open E213.Firmware E213.Hypervisor

-- ═══ Swap-invariance characterisation ═══

/-- **Necessary condition for swap-blindness.**  If a Lens is
    swap-invariant (view unchanged by swap), then in particular
    its value on `a` equals its value on `swap a = b`; hence the
    two base values coincide. -/
theorem swap_invariant_base_eq {α : Type} {L : Hypervisor.Lens α}
    (h : ∀ r : Raw, L.view (Raw.swap r) = L.view r) :
    L.base_a = L.base_b := by
  have h0 := h Raw.a
  rw [Raw.swap_a] at h0
  -- h0 : L.view Raw.b = L.view Raw.a
  -- both sides reduce by computation
  exact h0.symm

end E213.Meta
