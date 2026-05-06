/-!
# `AxiomLenses/Core/Propext.lean` — propext213 (PURE 213-native propext analogue)

The 213-native form of "propositional extensionality": logical
equivalence as a relation on `Prop`, NOT collapsed to identity.
No appeal to Lean's `propext`.

## Usage

Anywhere 213 needs to relate two propositions, state the goal as
`iffEquiv P Q` (= `P ↔ Q`) instead of `P = Q`.  Use `Iff.mp` /
`Iff.mpr` / `Iff.trans` directly; never `rw [iff]` to force into
`Eq`.  This is the propext213 discipline.

There is no Bridges/Propext.lean because propext is not used
*inside* 213 anywhere — Iff is sufficient for all internal
reasoning.  The propext-bridge appears only when interfacing
with Lean's standard library (which we avoid in the core).
-/

namespace E213.Lens.AxiomLenses.Core.Propext

/-- The propext-lens equivalence: two propositions agree iff
    they're logically equivalent.  This is the 213-native propext
    analogue (propext213). -/
def iffEquiv (P Q : Prop) : Prop := P ↔ Q

theorem iffEquiv_refl (P : Prop) : iffEquiv P P :=
  ⟨id, id⟩

theorem iffEquiv_symm {P Q : Prop} (h : iffEquiv P Q) : iffEquiv Q P :=
  Iff.symm h

theorem iffEquiv_trans {P Q R : Prop}
    (hpq : iffEquiv P Q) (hqr : iffEquiv Q R) : iffEquiv P R :=
  Iff.trans hpq hqr

/-- The lens "view": collapse iff-equivalent propositions to the
    *truth value* (Bool-like, but on Prop level).  Without propext,
    `view P : Prop` is just `P` itself. -/
def view (P : Prop) : Prop := P

/-- The lens kernel = iffEquiv. -/
theorem view_kernel (P Q : Prop) : view P = view Q ↔ (P = Q) :=
  Iff.rfl

/-- `(P = Q) → iffEquiv P Q` (constructive direction).  The
    converse `iffEquiv P Q → P = Q` IS propext — see Bridges/. -/
theorem eq_implies_iffEquiv {P Q : Prop} (h : P = Q) : iffEquiv P Q :=
  h ▸ iffEquiv_refl P

end E213.Lens.AxiomLenses.Core.Propext
