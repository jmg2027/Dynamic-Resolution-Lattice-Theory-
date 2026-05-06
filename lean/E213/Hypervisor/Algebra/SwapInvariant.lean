import E213.HypervisorCore

/-!
# SwapInvariantKernel: kernel structure of swap-invariant Lens

Raw.swap is the unique nontrivial automorphism of Raw (a ↔ b).
If Lens L is **swap-invariant** (view ∘ swap = view), then L's
kernel collapses entire swap-orbits into one class.

## Theorems

- `swap_invariant_equates_orbit`: L swap-invariant → L.equiv r (Raw.swap r)
  for all r.
- `swap_blind_base_is_swap_invariant`: base_a = base_b + symmetric combine
  → L swap-invariant (already known at the AXIOM level).

## Significance

A swap-invariant Lens does not reflect the swap symmetry of Raw in
its observations.  Its kernel must be coarser than the partition by
swap-orbits.  That is, in the refines preorder, the "swap-orbit Lens"
(if it exists) is the bottom of all swap-invariant Lenses.
-/

namespace E213.Hypervisor.Algebra.SwapInvariant

open E213.Firmware E213.Hypervisor

/-- The kernel of a swap-invariant Lens collapses swap-orbits. -/
theorem swap_invariant_equates_orbit {α : Type} (L : Lens α)
    (hinv : ∀ r : Raw, L.view (Raw.swap r) = L.view r) :
    ∀ r : Raw, L.equiv r (Raw.swap r) := by
  intro r
  show L.view r = L.view (Raw.swap r)
  exact (hinv r).symm

/-- A swap-invariant Lens has a swap-invariant kernel:
    r ~ r' ↔ swap r ~ swap r'. -/
theorem swap_invariant_kernel_swap_closed {α : Type} (L : Lens α)
    (hinv : ∀ r : Raw, L.view (Raw.swap r) = L.view r) :
    ∀ r r' : Raw, L.equiv r r' → L.equiv (Raw.swap r) (Raw.swap r') := by
  intro r r' hrr'
  show L.view (Raw.swap r) = L.view (Raw.swap r')
  rw [hinv r, hinv r']
  exact hrr'

end E213.Hypervisor.Algebra.SwapInvariant
