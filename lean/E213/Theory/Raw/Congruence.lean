import E213.Theory.Raw.Core

/-!
# Theory.Raw.Congruence — internal equivalence on Raw (Option E core)

Per `research-notes/2026-05-18_lens_emergence_path.md` §2.6 and §5
Option E.  A Raw-internal way to talk about equivalence:
parameterise over a generator relation `gens : Raw → Raw → Prop`
and take its equivalence closure.

`Eqv gens` is the smallest equivalence relation on `Raw` containing
`gens`.  Specific lenses correspond to specific generator choices —
the connection to the external `Lens.equiv` lives in
`lean/E213/Lens/Congruence.lean`.

**Scope.**  This file contains only the *generic* substrate:
inductive `Eqv` + the standard equivalence-relation closure rules
and a generic induction principle.

**Note on §2.6.**  The research note's §2.6 candidate
"ℕ₊ = Raw / (a ≡ b ∧ slash_assoc)" treats `slash_assoc` as a
"missing generator" — but the framing is wrong.  `slash_assoc`
cannot be a Raw-level identity (different parenthesisations are
structurally distinct Raws — see `ParenthesizationDistinct.lean`),
*and that is the correct behaviour*: imposing associativity would
erase Raw-internal structure.  ℕ₊ is the **image** of
`Lens.leaves.view`, not a quotient of `Raw`.  The Option C refactor
realised this projection picture.  `Eqv` is therefore useful as a
generic substrate (it parameterises *any* generator-induced
equivalence), but the specific §2.6 quotient-style ℕ₊
construction is abandoned.

∅-axiom standard; no Mathlib / Classical / propext / Quot.sound /
omega.
-/

namespace E213.Theory

/-- Equivalence closure of a relation `gens` on `Raw`.  The
    smallest relation containing `gens` and closed under
    reflexivity, symmetry, and transitivity. -/
inductive Eqv (gens : Raw → Raw → Prop) : Raw → Raw → Prop where
  | of    : ∀ {x y}, gens x y → Eqv gens x y
  | refl  : ∀ x, Eqv gens x x
  | symm  : ∀ {x y}, Eqv gens x y → Eqv gens y x
  | trans : ∀ {x y z}, Eqv gens x y → Eqv gens y z → Eqv gens x z

namespace Eqv

variable {gens : Raw → Raw → Prop}

/-- Generic induction: any binary predicate that contains `gens`
    and is reflexive, symmetric, and transitive contains the whole
    `Eqv gens` closure. -/
theorem induction'
    (P : Raw → Raw → Prop)
    (h_gens  : ∀ {x y}, gens x y → P x y)
    (h_refl  : ∀ x, P x x)
    (h_symm  : ∀ {x y}, P x y → P y x)
    (h_trans : ∀ {x y z}, P x y → P y z → P x z)
    {x y : Raw} (h : Eqv gens x y) : P x y := by
  induction h with
  | of hgen          => exact h_gens hgen
  | refl _           => exact h_refl _
  | symm _ ih        => exact h_symm ih
  | trans _ _ ih₁ ih₂ => exact h_trans ih₁ ih₂

/-- **Monotonicity** in the generator relation: enlarging `gens`
    enlarges the equivalence closure.  `Eqv` is a covariant
    functor from `Raw → Raw → Prop` to itself. -/
theorem weaken {g₁ g₂ : Raw → Raw → Prop}
    (h_le : ∀ {x y}, g₁ x y → g₂ x y)
    {x y : Raw} (h : Eqv g₁ x y) : Eqv g₂ x y :=
  induction' (fun a b => Eqv g₂ a b)
    (fun hgen => Eqv.of (h_le hgen))
    (fun a => Eqv.refl a)
    (fun ih => Eqv.symm ih)
    (fun ih₁ ih₂ => Eqv.trans ih₁ ih₂) h

/-- **`=` ⇒ Eqv**: structural equality implies the congruence
    relation, regardless of the generator. -/
theorem of_eq {x y : Raw} (h : x = y) : Eqv gens x y :=
  h ▸ Eqv.refl x

end Eqv

/-- **Empty generator characterisation**: `Eqv (fun _ _ => False)`
    is exactly structural equality on `Raw`.  Direction (←) is
    `Eqv.of_eq`; direction (→) follows from `induction'` since
    `=` is reflexive, symmetric, transitive, and contains the
    empty generator vacuously. -/
theorem Eqv.empty_iff_eq (x y : Raw) :
    Eqv (fun _ _ => False) x y ↔ x = y := by
  constructor
  · intro h
    exact Eqv.induction' (fun a b => a = b)
      (fun hgen => absurd hgen (fun h => h))
      (fun _ => rfl)
      (fun ih => ih.symm)
      (fun ih₁ ih₂ => ih₁.trans ih₂) h
  · intro h
    exact Eqv.of_eq h

end E213.Theory
