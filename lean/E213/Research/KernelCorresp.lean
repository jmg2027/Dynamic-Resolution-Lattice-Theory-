import E213.Research.UniversalQuotLens
import E213.Research.KernelCongruence

/-!
# Research.KernelCorresp: Kernel ↔ slash-congruence 의 bijection
의 explicit two-direction

PAPER1 §3.2-§3.3 의 implicit bijection 의 formal statement.

## 핵심 두 방향

1. **Lens.equiv 가 slash-congruence**: 모든 Lens 의 kernel 이
   slash-cong (`KernelCongruence.lean`).
2. **모든 slash-congruence 가 어떤 Lens 의 kernel**:
   `universalLens` 가 explicit witness (§5.1).

위 두 방향 이 합 처저 K = {Lens kernels} = {slash-congruences}
의 bijection 을 형식 화.
-/

namespace E213.Research.KernelCorresp

open E213.Firmware E213.Hypervisor
open E213.Research.UniversalQuotLens

/-- Slash-congruence predicate. -/
def IsSlashCongruence (E : Raw → Raw → Prop) : Prop :=
  (∀ r, E r r) ∧
  (∀ r r', E r r' → E r' r) ∧
  (∀ r r' r'', E r r' → E r' r'' → E r r'') ∧
  (∀ x x' y y' (h : x ≠ y) (h' : x' ≠ y'),
    E x x' → E y y' → E (Raw.slash x y h) (Raw.slash x' y' h'))

/-- **Direction 1**: any Lens kernel 이 slash-congruence.
    `Lens.equiv_slash_congruence` 의 packaging. -/
theorem lens_kernel_is_slash_cong {α : Type} (L : Lens α)
    (hsym : ∀ u v, L.combine u v = L.combine v u) :
    IsSlashCongruence (L.equiv) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r; rfl
  · intro r r' h; exact h.symm
  · intro r r' r'' h1 h2; exact h1.trans h2
  · intros x x' y y' h h' hxx hyy
    exact KernelCongruence.Lens.equiv_slash_congruence L hsym
      x x' y y' h h' hxx hyy

end E213.Research.KernelCorresp

namespace E213.Research.KernelCorresp

open E213.Firmware E213.Hypervisor
open E213.Research.UniversalQuotLens

/-- **Direction 2**: any slash-congruence 가 어떤 Lens 의 kernel.
    `universalLens E` 가 explicit witness (§5.1). -/
theorem slash_cong_is_lens_kernel
    (E : Raw → Raw → Prop) (h : IsSlashCongruence E)
    (r r' : Raw) :
    (universalLens E).view r = (universalLens E).view r' ↔ E r r' :=
  universalLens_kernel_eq_E E h.1 h.2.1 h.2.2.1 h.2.2.2 r r'

/-- **Bijection statement**: K = {Lens kernels (Lens 의 commutative
    combine 만)} = {slash-congruences}.

    Formal version: 두 direction 의 conjunction.  Direction 1
    은 모든 commutative-combine Lens 의 kernel 이 slash-cong;
    Direction 2 는 모든 slash-cong 이 universalLens 의 kernel
    로 realized. -/
theorem kernel_correspondence
    (E : Raw → Raw → Prop) :
    (IsSlashCongruence E ↔
      ∀ r r', (universalLens E).view r = (universalLens E).view r' ↔ E r r') := by
  refine ⟨fun hslash r r' => slash_cong_is_lens_kernel E hslash r r', ?_⟩
  intro hbi
  -- universalLens E.equiv = E (by hbi).  And (universalLens E).equiv 가 slash-cong
  -- by lens_kernel_is_slash_cong with universalLens_combine_sym.
  have hLcong : IsSlashCongruence (universalLens E).equiv :=
    lens_kernel_is_slash_cong _ (universalLens_combine_sym E)
  -- E = (universalLens E).equiv  by hbi
  have hext : (universalLens E).equiv = E := by
    funext r r'
    exact propext (hbi r r')
  rw [← hext]; exact hLcong

end E213.Research.KernelCorresp
