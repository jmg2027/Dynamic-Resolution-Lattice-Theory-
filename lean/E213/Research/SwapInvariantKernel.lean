import E213.Hypervisor.Lens

/-!
# Research.SwapInvariantKernel: swap-invariant Lens 의 kernel 구조

Raw.swap 은 Raw 의 유일한 nontrivial automorphism (a ↔ b).
Lens L 이 **swap-invariant** (view ∘ swap = view) 이면 L 의
kernel 은 swap-orbit 전체를 한 class 로 합침.

## 정리

- `swap_invariant_equates_orbit`: L swap-invariant → 모든 r
  에 대해 L.equiv r (Raw.swap r).
- `swap_blind_base_is_swap_invariant`: base_a = base_b +
  combine 대칭 → L swap-invariant (AXIOM 수준에서 이미 알려짐).

## 의의

swap-invariant Lens 는 Raw 의 swap 대칭을 관측에 반영하지
않음.  그 kernel 은 반드시 swap-orbits 의 partition 보다
거칠다.  즉 refines preorder 에서 "swap-orbit Lens" (만약
존재한다면) 가 모든 swap-invariant Lens 의 bottom.
-/

namespace E213.Research.SwapInvariantKernel

open E213.Firmware E213.Hypervisor

/-- Swap-invariant Lens 의 kernel 은 swap-orbit 을 합침. -/
theorem swap_invariant_equates_orbit {α : Type} (L : Lens α)
    (hinv : ∀ r : Raw, L.view (Raw.swap r) = L.view r) :
    ∀ r : Raw, L.equiv r (Raw.swap r) := by
  intro r
  show L.view r = L.view (Raw.swap r)
  exact (hinv r).symm

/-- Swap-invariant Lens 는 swap-invariant kernel 을 가짐:
    r ~ r' ↔ swap r ~ swap r'. -/
theorem swap_invariant_kernel_swap_closed {α : Type} (L : Lens α)
    (hinv : ∀ r : Raw, L.view (Raw.swap r) = L.view r) :
    ∀ r r' : Raw, L.equiv r r' → L.equiv (Raw.swap r) (Raw.swap r') := by
  intro r r' hrr'
  show L.view (Raw.swap r) = L.view (Raw.swap r')
  rw [hinv r, hinv r']
  exact hrr'

end E213.Research.SwapInvariantKernel
