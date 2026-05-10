import E213.Lens.Universal.QuotLens
import E213.Lens.Algebra.Congruence

/-!
# KernelCorresp: explicit two-direction bijection of
Kernel ↔ slash-congruence

Formal statement of the implicit bijection in PAPER1 §3.2-§3.3.

## Two Core Directions

1. **Lens.equiv is a slash-congruence**: the kernel of every Lens
   is a slash-cong (`KernelCongruence.lean`).
2. **Every slash-congruence is the kernel of some Lens**:
   `universalLens` is the explicit witness (§5.1).

These two directions together formalize the bijection
K = {Lens kernels} = {slash-congruences}.
-/

namespace E213.Lens.Algebra.Corresp

open E213.Theory E213.Lens
open E213.Lens.Universal.QuotLens

/-- Slash-congruence predicate. -/
def IsSlashCongruence (E : Raw → Raw → Prop) : Prop :=
  (∀ r, E r r) ∧
  (∀ r r', E r r' → E r' r) ∧
  (∀ r r' r'', E r r' → E r' r'' → E r r'') ∧
  (∀ x x' y y' (h : x ≠ y) (h' : x' ≠ y'),
    E x x' → E y y' → E (Raw.slash x y h) (Raw.slash x' y' h'))

/-- **Direction 1**: any Lens kernel is a slash-congruence.
    Packaging of `Lens.equiv_slash_congruence`. -/
theorem lens_kernel_is_slash_cong {α : Type} (L : Lens α)
    (hsym : ∀ u v, L.combine u v = L.combine v u) :
    IsSlashCongruence (L.equiv) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r; rfl
  · intro r r' h; exact h.symm
  · intro r r' r'' h1 h2; exact h1.trans h2
  · intros x x' y y' h h' hxx hyy
    exact E213.Lens.Algebra.Congruence.Lens.equiv_slash_congruence L hsym
      x x' y y' h h' hxx hyy

end E213.Lens.Algebra.Corresp

namespace E213.Lens.Algebra.Corresp

open E213.Theory E213.Lens
open E213.Lens.Universal.QuotLens

/-- **Direction 2**: any slash-congruence is the kernel of some Lens.
    `universalLens E` is the explicit witness (§5.1). -/
theorem slash_cong_is_lens_kernel
    (E : Raw → Raw → Prop) (h : IsSlashCongruence E)
    (r r' : Raw) :
    (universalLens E).view r = (universalLens E).view r' ↔ E r r' :=
  universalLens_kernel_eq_E E h.1 h.2.1 h.2.2.1 h.2.2.2 r r'

/-- **Bijection statement**: K = {Lens kernels (commutative-combine
    Lenses only)} = {slash-congruences}.

    Formal version: conjunction of the two directions.  Direction 1:
    every commutative-combine Lens kernel is a slash-cong;
    Direction 2: every slash-cong is realized as the kernel of a
    universalLens. -/
theorem kernel_correspondence
    (E : Raw → Raw → Prop) :
    (IsSlashCongruence E ↔
      ∀ r r', (universalLens E).view r = (universalLens E).view r' ↔ E r r') := by
  refine ⟨fun hslash r r' => slash_cong_is_lens_kernel E hslash r r', ?_⟩
  intro hbi
  -- universalLens E.equiv = E (by hbi).  And (universalLens E).equiv is a slash-cong
  -- by lens_kernel_is_slash_cong with universalLens_combine_sym.
  have hLcong : IsSlashCongruence (universalLens E).equiv :=
    lens_kernel_is_slash_cong _ (universalLens_combine_sym E)
  -- E = (universalLens E).equiv  by hbi
  have hext : (universalLens E).equiv = E := by
    funext r r'
    exact propext (hbi r r')
  rw [← hext]; exact hLcong

end E213.Lens.Algebra.Corresp
