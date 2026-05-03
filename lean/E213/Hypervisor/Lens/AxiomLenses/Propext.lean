/-!
# `Propext.lean` — propext as the "iff-equivalent propositions collapse" lens

★ G12 Tier 4 A2 — propext reformulated as a 213-internal lens.

`propext : (P ↔ Q) → P = Q` is one of Lean 4's three core axioms.
Reading 213-internally:
  - The Raw substrate distinguishes propositions that have the same
    truth-value but different proofs / structure.
  - `propext` is a LENS choice: collapse iff-equivalent propositions
    into the same equivalence class.
  - Without `propext`: each proposition is its own thing; logical
    equivalence is a relation, not identity.
  - With `propext`: Prop becomes a quotient by ↔.

In our funext-refactor (parts 1-15), each `rw [iff_lemma]` use
implicitly applies the propext lens.  Our pattern was to replace
those with `Iff.trans`/`Iff.mp`/`Iff.mpr` — which work in the
no-propext-lens view (PURE).
-/

namespace E213.Hypervisor.Lens.AxiomLenses.Propext

/-- The propext-lens equivalence: two propositions agree iff
    they're logically equivalent.  This is the relation propext
    collapses. -/
def iffEquiv (P Q : Prop) : Prop := P ↔ Q

theorem iffEquiv_refl (P : Prop) : iffEquiv P P :=
  ⟨id, id⟩

theorem iffEquiv_symm {P Q : Prop} (h : iffEquiv P Q) : iffEquiv Q P :=
  Iff.symm h

theorem iffEquiv_trans {P Q R : Prop}
    (hpq : iffEquiv P Q) (hqr : iffEquiv Q R) : iffEquiv P R :=
  Iff.trans hpq hqr

/-- The lens "view": collapse iff-equivalent propositions to the
    *truth value* (Bool-like, but on Prop level).

    Without propext, `view P : Prop` is just `P` itself.
    *With* propext, `view P` would be the equivalence class
    `[P]_↔` ⊆ Prop.

    Stating this without using propext: we just record that P is
    its own equivalence class representative — which is true
    intensionally (Prop is finer than ↔). -/
def view (P : Prop) : Prop := P

/-- The lens kernel = iffEquiv. -/
theorem view_kernel (P Q : Prop) : view P = view Q ↔ (P = Q) :=
  Iff.rfl

/-- Note: `(P = Q) → iffEquiv P Q` holds without propext (Eq → Iff
    is constructive); the converse `iffEquiv P Q → P = Q` IS
    propext.  So this lens IS propext, made explicit. -/
theorem eq_implies_iffEquiv {P Q : Prop} (h : P = Q) : iffEquiv P Q :=
  h ▸ iffEquiv_refl P

end E213.Hypervisor.Lens.AxiomLenses.Propext
