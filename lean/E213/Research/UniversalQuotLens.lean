import E213.Hypervisor.Lens
import E213.Research.KernelCongruence

/-!
# Research.UniversalQuotLens: Q37.3 의 일반 해결

**임의의 slash-congruence E** (equivalence + slash 보존) 에
대해 concrete Lens L_E with kernel = E 구성.

## 구성

`L_E : Lens (Raw → Prop)`:
- `view r := fun s => E r s` (특성 함수: r 의 E-class).
- `combine f g := fun r' => ∃ X Y h, (∀ s, E X s ↔ f s) ∧
                  (∀ s, E Y s ↔ g s) ∧ E (Raw.slash X Y h) r'`.

## 핵심 정리

`L_E.view r = L_E.view r' ↔ E r r'` (kernel = E exactly).

→: funext + propext + E equivalence 의 표준 결과.
←: E r r' → ∀ s, E r s ↔ E r' s → funext → view r = view r'.

`combine` 의 fold-structure: slash_cong 으로부터.

## 의의

Q37.3 ("임의 slash-congruence 의 concrete Lens 구성") 의
**일반 해결**.  Mod family 한정 (`ModJoinEquivGCD`) 의 진정한
일반화.

Classical 사용 안 함; funext + propext (Lean 4 core baseline)
만 사용.
-/

namespace E213.Research.UniversalQuotLens

open E213.Firmware E213.Hypervisor

variable (E : Raw → Raw → Prop)
variable (hrefl : ∀ r, E r r)
variable (hsymm : ∀ r r', E r r' → E r' r)
variable (htrans : ∀ r r' r'', E r r' → E r' r'' → E r r'')
variable (hslash : ∀ x x' y y' (h : x ≠ y) (h' : x' ≠ y'),
                   E x x' → E y y' → E (Raw.slash x y h) (Raw.slash x' y' h'))

/-- 임의 slash-cong E 의 universal Lens. -/
def universalLens : Lens (Raw → Prop) where
  base_a := fun s => E Raw.a s
  base_b := fun s => E Raw.b s
  combine f g := fun r' => ∃ X : Raw, ∃ Y : Raw, ∃ h : X ≠ Y,
                           (∀ s, E X s ↔ f s) ∧
                           (∀ s, E Y s ↔ g s) ∧
                           E (Raw.slash X Y h) r'

/-- Combine 의 symmetry (renaming + slash_comm). -/
theorem universalLens_combine_sym (f g : Raw → Prop) :
    (universalLens E).combine f g = (universalLens E).combine g f := by
  funext r'
  apply propext
  constructor
  · rintro ⟨X, Y, h, hX, hY, hslashr'⟩
    refine ⟨Y, X, Ne.symm h, hY, hX, ?_⟩
    rwa [Raw.slash_comm Y X (Ne.symm h)]
  · rintro ⟨X, Y, h, hX, hY, hslashr'⟩
    refine ⟨Y, X, Ne.symm h, hY, hX, ?_⟩
    rwa [Raw.slash_comm Y X (Ne.symm h)]

/-- **핵심 정리 1**: view r = (E r ·).  Raw.rec induction. -/
theorem universalLens_view_eq
    (hrefl : ∀ r, E r r)
    (htrans : ∀ r r' r'', E r r' → E r' r'' → E r r'')
    (hslash : ∀ x x' y y' (h : x ≠ y) (h' : x' ≠ y'),
              E x x' → E y y' → E (Raw.slash x y h) (Raw.slash x' y' h'))
    (r : Raw) :
    (universalLens E).view r = (fun s => E r s) := by
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hfs : (universalLens E).view (Raw.slash x y h)
                   = (universalLens E).combine
                       ((universalLens E).view x) ((universalLens E).view y) := by
        apply Raw.fold_slash
        intro u v; exact universalLens_combine_sym E u v
      rw [hfs, ihx, ihy]
      funext r'
      apply propext
      constructor
      · rintro ⟨X, Y, h', hX, hY, hslashr'⟩
        have hxX : E x X := by
          have hX_X : E X X := hrefl X
          exact (hX X).mp hX_X
        have hyY : E y Y := by
          have hY_Y : E Y Y := hrefl Y
          exact (hY Y).mp hY_Y
        have hslash_eq : E (Raw.slash x y h) (Raw.slash X Y h') :=
          hslash x X y Y h h' hxX hyY
        exact htrans _ _ _ hslash_eq hslashr'
      · intro hslashr'
        refine ⟨x, y, h, ?_, ?_, hslashr'⟩
        · intro s; exact Iff.rfl
        · intro s; exact Iff.rfl

/-- **Q37.3 일반 해결**: kernel of universalLens E = E.
    임의 slash-cong E (equivalence + slash-preserving) 가
    concrete Lens 의 kernel. -/
theorem universalLens_kernel_eq_E
    (hrefl : ∀ r, E r r)
    (hsymm : ∀ r r', E r r' → E r' r)
    (htrans : ∀ r r' r'', E r r' → E r' r'' → E r r'')
    (hslash : ∀ x x' y y' (h : x ≠ y) (h' : x' ≠ y'),
              E x x' → E y y' → E (Raw.slash x y h) (Raw.slash x' y' h'))
    (r r' : Raw) :
    (universalLens E).view r = (universalLens E).view r' ↔ E r r' := by
  rw [universalLens_view_eq E hrefl htrans hslash r,
      universalLens_view_eq E hrefl htrans hslash r']
  constructor
  · intro h
    have hpt : ∀ s, E r s ↔ E r' s := by
      intro s
      have := congrFun h s
      exact Iff.of_eq this
    have h_r'r : E r' r := (hpt r).mp (hrefl r)
    exact hsymm _ _ h_r'r
  · intro hrr'
    funext s
    apply propext
    constructor
    · intro hrs; exact htrans _ _ _ (hsymm _ _ hrr') hrs
    · intro hr's; exact htrans _ _ _ hrr' hr's

end E213.Research.UniversalQuotLens

namespace E213.Research.UniversalQuotLens

open E213.Firmware E213.Hypervisor

/-- **Canonical form 정리**: 임의 Lens M 에 대해, universalLens
    M.equiv 의 kernel = M 의 kernel.  즉 universalLens 가 모든
    Lens 의 canonical form. -/
theorem universalLens_recovers (α : Type) (M : Lens α)
    (hMsym : ∀ u v, M.combine u v = M.combine v u)
    (r r' : Raw) :
    (universalLens M.equiv).view r = (universalLens M.equiv).view r'
      ↔ M.view r = M.view r' := by
  apply universalLens_kernel_eq_E
  · intro x; rfl
  · intro x y h; exact h.symm
  · intro x y z h1 h2; exact h1.trans h2
  · intro x x' y y' hxy hx'y' hxx' hyy'
    exact E213.Research.KernelCongruence.Lens.equiv_slash_congruence
      M hMsym x x' y y' hxy hx'y' hxx' hyy'

/-- **Idempotence**: universalLens 를 두 번 적용 해도 같은 kernel.
    universalLens 가 normalization 임의 직접 표현. -/
theorem universalLens_idempotent (α : Type) (M : Lens α)
    (r r' : Raw) :
    (universalLens (universalLens M.equiv).equiv).view r
       = (universalLens (universalLens M.equiv).equiv).view r'
    ↔ (universalLens M.equiv).view r = (universalLens M.equiv).view r' := by
  apply universalLens_kernel_eq_E
  · intro x; rfl
  · intro x y h; exact h.symm
  · intro x y z h1 h2; exact h1.trans h2
  · intro x x' y y' hxy hx'y' hxx' hyy'
    exact E213.Research.KernelCongruence.Lens.equiv_slash_congruence
      (universalLens M.equiv) (universalLens_combine_sym M.equiv)
      x x' y y' hxy hx'y' hxx' hyy'

end E213.Research.UniversalQuotLens
