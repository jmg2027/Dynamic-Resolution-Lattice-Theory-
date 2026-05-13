import E213.Theory.Raw.API
import E213.Lens.LensCore

/-!
# Lens.EqPW — pointwise Lens equality (avoids funext-by-design)

The standard `=` on `Lens α` reduces componentwise via Lean kernel:
- base_a, base_b: structural Eq (∅-axiom for concrete α)
- combine: function Eq → requires funext (Quot.sound)

For `L = M` proofs, the funext on `combine` is the SOLE Quot.sound
source in ~50 Cat 1 DIRTY items (per G83).

`LensEqPW` is **pointwise equality on combine**:
  `L ≡ M  ⟺  L.base_a = M.base_a  ∧  L.base_b = M.base_b
              ∧  ∀ u v, L.combine u v = M.combine u v`

Pointwise comparison avoids funext.  All theorems involving Lens
equality at concrete α can be restated with `eqPW` and proved
∅-axiom.

Bridge `eq_of_eqPW : eqPW L M → L = M` requires funext (DIRTY),
isolated to one place.  Consumers who need strict `=` invoke this
single bridge.

All theorems here ∅-axiom.
-/

namespace E213.Lens

/-- Pointwise Lens equality: avoids funext on combine. -/
protected def Lens.eqPW {α : Type} (L M : Lens α) : Prop :=
  L.base_a = M.base_a ∧
  L.base_b = M.base_b ∧
  ∀ u v, L.combine u v = M.combine u v

namespace Lens

/-- Reflexivity. -/
protected theorem eqPW_refl {α : Type} (L : Lens α) : L.eqPW L :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

/-- Symmetry. -/
protected theorem eqPW_symm {α : Type} {L M : Lens α} (h : L.eqPW M) : M.eqPW L :=
  ⟨h.1.symm, h.2.1.symm, fun u v => (h.2.2 u v).symm⟩

/-- Transitivity. -/
protected theorem eqPW_trans {α : Type} {L M N : Lens α}
    (h1 : L.eqPW M) (h2 : M.eqPW N) : L.eqPW N :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1,
   fun u v => (h1.2.2 u v).trans (h2.2.2 u v)⟩

end Lens

end E213.Lens

namespace E213.Lens

open E213.Theory

namespace Lens

/-! ### View-level consequences of pointwise equality

`eqPW` is strong enough to derive `L.view r = M.view r` for every
`r : Raw` *when the combines are symmetric* — exactly the
axiom-compliant Lens regime (see `Raw.fold_slash` warning).  The base
cases need no symmetry. -/

/-- Base-`a` view equality: from `L.base_a = M.base_a` only. -/
protected theorem eqPW_view_a {α : Type} {L M : Lens α} (h : L.eqPW M) :
    L.view Raw.a = M.view Raw.a :=
  h.1

/-- Base-`b` view equality: from `L.base_b = M.base_b` only. -/
protected theorem eqPW_view_b {α : Type} {L M : Lens α} (h : L.eqPW M) :
    L.view Raw.b = M.view Raw.b :=
  h.2.1

/-- Symmetry of `M.combine` is derivable from `L.combine`'s symmetry
    plus pointwise agreement. -/
protected theorem eqPW_combine_sym_transfer {α : Type} {L M : Lens α}
    (h : L.eqPW M) (hLsym : ∀ u v, L.combine u v = L.combine v u) :
    ∀ u v, M.combine u v = M.combine v u := by
  intro u v
  rw [← h.2.2 u v, ← h.2.2 v u]
  exact hLsym u v

/-- **View bridge** (axiom-compliant regime): under symmetric combine,
    pointwise Lens equality implies pointwise view equality on every
    `r : Raw`.  ∅-axiom — induction on `Raw.rec`, no funext. -/
protected theorem eqPW_view_of_sym {α : Type} {L M : Lens α} (h : L.eqPW M)
    (hLsym : ∀ u v, L.combine u v = L.combine v u) (r : Raw) :
    L.view r = M.view r := by
  have hMsym := Lens.eqPW_combine_sym_transfer h hLsym
  induction r using Raw.rec with
  | a => exact Lens.eqPW_view_a h
  | b => exact Lens.eqPW_view_b h
  | slash x y hxy ihx ihy =>
      show Raw.fold L.base_a L.base_b L.combine (Raw.slash x y hxy)
         = Raw.fold M.base_a M.base_b M.combine (Raw.slash x y hxy)
      rw [Raw.fold_slash _ _ _ hLsym x y hxy,
          Raw.fold_slash _ _ _ hMsym x y hxy]
      show L.combine (L.view x) (L.view y) = M.combine (M.view x) (M.view y)
      rw [ihx, ihy, h.2.2]

end Lens

end E213.Lens

namespace E213.Lens

open E213.Theory E213.Theory.Internal

namespace Lens

/-! ### Fold/slash compatibility under eqPW symmetry

Companion to `Raw.fold_slash` for codomain `Lens β` where `combine`
sym is naturally pointwise (`eqPW`) rather than function-level.  The
canonical-form swap is discharged with `hsym_pw` in the gt branch. -/

/-- Fold/slash compatibility: if `c : Lens β → Lens β → Lens β` is
    eqPW-symmetric pointwise, then folding over `Raw.slash x y h`
    yields a `Lens β` that's eqPW-equal to `c (fold x) (fold y)`. -/
protected theorem fold_slash_eqPW {β : Type}
    (ba bb : Lens β) (c : Lens β → Lens β → Lens β)
    (hsym_pw : ∀ u v : Lens β, (c u v).eqPW (c v u))
    (x y : Raw) (h : x ≠ y) :
    (Raw.fold ba bb c (Raw.slash x y h)).eqPW
      (c (Raw.fold ba bb c x) (Raw.fold ba bb c y)) := by
  unfold Raw.slash Raw.fold
  split <;> rename_i hc
  · exact Lens.eqPW_refl _
  · -- gt: canonical form swaps; recover via hsym_pw on the swapped inputs
    show (c (Tree.fold ba bb c y.val) (Tree.fold ba bb c x.val)).eqPW
         (c (Tree.fold ba bb c x.val) (Tree.fold ba bb c y.val))
    exact hsym_pw _ _
  · exact absurd (Tree.cmp_eq_to_eq _ _ hc) (fun e => h (Subtype.ext e))

end Lens

end E213.Lens

namespace E213.Lens

open E213.Theory

namespace Lens

/-! ### View-unique under eqPW symmetry (with combine congruence)

Companion to `Lens.view_unique` where the codomain is `Lens β` and
all equational obligations are pointwise (eqPW).  Funext-free.

`L.combine` must additionally be eqPW-congruent — provided by every
specific construction (e.g. `lensXor`) but not generically derivable
from `Lens` alone.  Specific eqPW-congruence proofs are provided
alongside each combine. -/

protected theorem view_unique_eqPW {β : Type} (L : Lens (Lens β))
    (hsym_pw : ∀ u v, (L.combine u v).eqPW (L.combine v u))
    (hcong : ∀ u u' v v' : Lens β,
             u.eqPW u' → v.eqPW v' → (L.combine u v).eqPW (L.combine u' v'))
    (f : Raw → Lens β)
    (ha : (f Raw.a).eqPW L.base_a)
    (hb : (f Raw.b).eqPW L.base_b)
    (hslash : ∀ (x y : Raw) (h : x ≠ y),
              (f (Raw.slash x y h)).eqPW (L.combine (f x) (f y)))
    (r : Raw) : (f r).eqPW (L.view r) := by
  induction r using Raw.rec with
  | a => exact ha
  | b => exact hb
  | slash x y h ihx ihy =>
      have step1 := hslash x y h
      have step2 := hcong _ _ _ _ ihx ihy
      have step3 : (L.view (Raw.slash x y h)).eqPW
                     (L.combine (L.view x) (L.view y)) := by
        show (Raw.fold L.base_a L.base_b L.combine (Raw.slash x y h)).eqPW
              (L.combine (Raw.fold L.base_a L.base_b L.combine x)
                         (Raw.fold L.base_a L.base_b L.combine y))
        exact Lens.fold_slash_eqPW L.base_a L.base_b L.combine hsym_pw x y h
      exact Lens.eqPW_trans step1 (Lens.eqPW_trans step2 (Lens.eqPW_symm step3))

end Lens

end E213.Lens
