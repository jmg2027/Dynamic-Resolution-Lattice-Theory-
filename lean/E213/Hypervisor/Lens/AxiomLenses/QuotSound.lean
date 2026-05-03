/-!
# `QuotSound.lean` — Quot.sound as the "equivalence-class collapse" lens

★ G12 Tier 4 A2 — Quot.sound reformulated as a 213-internal lens.

`Quot.sound : a ~ b → Quot.mk r a = Quot.mk r b` is one of Lean 4's
three core axioms.  Reading 213-internally:
  - The Raw substrate distinguishes raw elements with the same
    equivalence class but different identity.
  - `Quot.sound` is a LENS choice: collapse equivalence-related
    elements into the same Quot point.
  - Without `Quot.sound`: setoids are relations on data, not
    quotient types; `Quot.mk r a` and `Quot.mk r b` are distinct
    even when `a ~ b`.
  - With `Quot.sound`: the quotient type is *the* type whose
    identity = original equivalence relation.

Quot.sound is the **deepest of the three Lean axioms** because
funext is *derivable from it* (Quot.sound + Empty.elim suffice to
prove funext).  So the funext-refactor's [Quot.sound] DIRTY tag
is reading "this theorem applied the Quot.sound lens (via funext)."

In 213's worldview, `Quot.sound` is the canonical "lens-application
axiom" — it's literally the rule that says "the result of applying
a lens (= equivalence-relation collapse) IS identity in the
codomain."
-/

namespace E213.Hypervisor.Lens.AxiomLenses.QuotSound

/-- A setoid view: a type α with an equivalence relation `r` is
    interpreted as the *quotient* α / r — collapsing r-related
    elements. -/
structure SetoidLens (α : Type) where
  rel : α → α → Prop
  refl : ∀ x, rel x x
  symm : ∀ {x y}, rel x y → rel y x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

/-- The setoid's quotient type — Lean's `Quot` is exactly this. -/
def quotient {α : Type} (s : SetoidLens α) : Type := Quot s.rel

/-- The "view" projecting α onto its equivalence class. -/
def project {α : Type} (s : SetoidLens α) (a : α) : quotient s :=
  Quot.mk s.rel a

/-- The Quot.sound lens: applying it collapses r-related elements
    into the same quotient point.  This is the rule that makes
    SetoidLens.quotient an actual quotient (not just data). -/
theorem sound_lens {α : Type} (s : SetoidLens α) {a b : α}
    (h : s.rel a b) : project s a = project s b :=
  Quot.sound h

/- Without Quot.sound, the only way to relate `project s a`
   and `project s b` would be via constructive identity (which
   requires `a = b` exactly, not just `s.rel a b`).  Quot.sound
   is the bridge — the explicit lens application. -/

end E213.Hypervisor.Lens.AxiomLenses.QuotSound
