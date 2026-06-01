import E213.Lens.Universal.QuotLens
import E213.Lens.Algebra.Congruence

/-!
# KernelCorresp: explicit two-direction bijection of
Kernel ↔ slash-congruence

Formal statement of the implicit Kernel ↔ slash-congruence bijection.

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


/-- **Direction 2**: any slash-congruence is the kernel of some Lens.
    `universalLens E` is the explicit witness (§5.1).  Stated as the
    Reading-equivalence `equivR` (pointwise `↔`), ∅-axiom. -/
theorem slash_cong_is_lens_kernel
    (E : Raw → Raw → Prop) (h : IsSlashCongruence E)
    (r r' : Raw) :
    (universalLens E).equivR r r' ↔ E r r' :=
  universalLens_kernel_eq_E_R E h.1 h.2.1 h.2.2.1 h.2.2.2 r r'

/-- `(universalLens E).equivR` is itself a slash-congruence — Reading-native,
    ∅-axiom.  The realised kernel is in `KernelSpace` without leaving the
    `equivR` world. -/
theorem universalLens_kernel_is_slash_cong (E : Raw → Raw → Prop) :
    IsSlashCongruence (universalLens E).equivR :=
  ⟨fun r => Lens.equivR_refl _ r,
   fun _ _ h => Lens.equivR_symm _ h,
   fun _ _ _ h1 h2 => Lens.equivR_trans _ h1 h2,
   fun _ _ _ _ hxy hx'y' hxx' hyy' =>
     universalLens_equivR_slash_congruence E hxy hx'y' hxx' hyy'⟩

/-- **Bijection statement**: K = {Lens kernels (commutative-combine
    Lenses only)} = {slash-congruences}.

    Formal version: conjunction of the two directions.  Direction 1:
    every commutative-combine Lens kernel is a slash-cong;
    Direction 2: every slash-cong is realized as the kernel of a
    universalLens.  Stated and proven Reading-natively (`equivR`), so ∅-axiom —
    the backward direction transports the closure properties through the
    pointwise `↔` `hbi` rather than `funext`-collapsing the kernel to `E`. -/
theorem kernel_correspondence
    (E : Raw → Raw → Prop) :
    (IsSlashCongruence E ↔
      ∀ r r', (universalLens E).equivR r r' ↔ E r r') := by
  refine ⟨fun hslash r r' => slash_cong_is_lens_kernel E hslash r r', ?_⟩
  intro hbi
  -- (universalLens E).equivR is a slash-cong; transport each closure property to
  -- E across the pointwise iff `hbi` (no funext / propext).
  have hLcong := universalLens_kernel_is_slash_cong E
  refine ⟨fun r => (hbi r r).mp (hLcong.1 r),
          fun r r' h => (hbi r' r).mp (hLcong.2.1 r r' ((hbi r r').mpr h)),
          fun r r' r'' h1 h2 =>
            (hbi r r'').mp
              (hLcong.2.2.1 r r' r'' ((hbi r r').mpr h1) ((hbi r' r'').mpr h2)),
          fun x x' y y' hxy hx'y' hxx' hyy' =>
            (hbi _ _).mp (hLcong.2.2.2 x x' y y' hxy hx'y'
              ((hbi x x').mpr hxx') ((hbi y y').mpr hyy'))⟩

end E213.Lens.Algebra.Corresp
