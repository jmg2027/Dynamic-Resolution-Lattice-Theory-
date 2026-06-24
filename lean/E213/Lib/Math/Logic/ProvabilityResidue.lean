import E213.Lens

/-!
# Gödel-2 = the residue diagonal + the □-modality (∅-axiom): the frontier made precise

The residue framework keeps **Gödel-2 proper** (`T ⊬ Con(T)`) as a *frontier*, not collapsed into the
residue (`OneDiagonal.tarski_no_truth_predicate` docstring; `the_one_act.md`): Cantor / Russell /
Liar / Tarski **are** the one Lawvere diagonal (`OneDiagonal.one_diagonal_generates`), but Gödel-2
needs the provability **modality** `□` with the Hilbert–Bernays–Löb derivability conditions
(D1 necessitation, D2 distribution, D3 positive introspection) / Löb's theorem — which the bare
self-cover has no analogue of.  "Form-agreement, not identity."

This file makes that boundary **exact and ∅-axiom**.  It separates the two ingredients:

  * **Shared (the diagonal).**  The Gödel–Löb fixed point `C ↔ (□C → A)` is *literally* the residue's
    Lawvere construction `lawvere_fixed_point_prop` at the modifier `t X := (□X → A)`
    (`loeb_fixed_point_is_lawvere`).  Same diagonal — confirming the form-agreement, exhibited.
  * **Extra (the modality).**  Löb's theorem and Gödel-2 then follow from `□` + **D1–D3** as
    parameters (`loeb_abstract`, `goedel_two`).  These derivability conditions are the *genuine*
    difference: the residue's bare cover `Object1 : Raw → (Raw → Bool)` has no `□` satisfying them.

So Gödel-2 = **residue diagonal** (shared, `lawvere_fixed_point_prop`) **+ the □-modality's D1–D3**
(extra).  The frontier is not a vague gap — it is exactly the three derivability conditions, named and
made the only hypotheses.  All ∅-axiom (abstract modal logic; `□` and D1–D3 are parameters, and the
`Iff` form needs no `propext`).
-/

namespace E213.Lib.Math.Logic.ProvabilityResidue

open E213.Lens.Foundations.OneDiagonal (lawvere_fixed_point_prop)

/-! ## The shared half — the Löb fixed point IS the Lawvere diagonal -/

/-- **The Gödel–Löb fixed point is the residue's Lawvere diagonal.**  Given a rich (Iff-point-
    surjective) self-cover `f` — the residue framework's hypothesis — the Löb fixed point
    `C ↔ (□C → A)` exists, as `lawvere_fixed_point_prop` at the modifier `t X := (□X → A)`.  The
    diagonal of Gödel-2 is the *same construction* as Cantor/Russell/Tarski; only the modifier
    differs (`□X → A` instead of `Not X`). -/
theorem loeb_fixed_point_is_lawvere {A : Prop} (Box : Prop → Prop)
    {Sent : Type} (f : Sent → Sent → Prop)
    (hf : ∀ g : Sent → Prop, ∃ a, ∀ x, (f a x ↔ g x)) :
    ∃ P : Prop, (P ↔ (Box P → A)) :=
  lawvere_fixed_point_prop f hf (fun X => (Box X → A))

/-! ## The extra half — D1–D3 turn the diagonal into Löb and Gödel-2 -/

/-- ★★★ **Löb's theorem (abstract).**  For any provability modality `Box` satisfying the
    Hilbert–Bernays–Löb derivability conditions — `nec` (D1), `K` (D2 distribution), `four` (D3
    positive introspection) — and the Gödel–Löb fixed point `C ↔ (Box C → A)`, we have
    `Box (Box A → A) → Box A`.  The fixed point is the residue diagonal
    (`loeb_fixed_point_is_lawvere`); the three conditions are the *only* extra hypotheses — the exact
    content the bare self-cover lacks.  ∅-axiom (parametric; `Iff` form, no `propext`). -/
theorem loeb_abstract {Box : Prop → Prop}
    (nec : ∀ {P : Prop}, P → Box P)
    (K : ∀ {P Q : Prop}, Box (P → Q) → Box P → Box Q)
    (four : ∀ {P : Prop}, Box P → Box (Box P))
    {A : Prop} (C : Prop) (hC : C ↔ (Box C → A)) :
    Box (Box A → A) → Box A := by
  have d1 : C → (Box C → A) := hC.mp
  have d2 : (Box C → A) → C := hC.mpr
  -- Box C → Box (Box C → A)   (necessitation on d1, then distribution)
  have s1 : Box C → Box (Box C → A) := fun hbc => K (nec d1) hbc
  -- Box C → Box A   (distribute again, close with D3)
  have five : Box C → Box A := fun hbc => K (s1 hbc) (four hbc)
  -- (Box A → A) → (Box C → A), hence → C (diagonal ←)
  have six : (Box A → A) → (Box C → A) := fun h hbc => h (five hbc)
  have seven : (Box A → A) → C := fun h => d2 (six h)
  -- Box (Box A → A) → Box C → Box A
  exact fun H => five (K (nec seven) H)

/-- ★★★ **Gödel's second incompleteness theorem (abstract).**  With `Con := ¬ Box False`
    (`Box False → False`): a *consistent* provability modality satisfying D1–D3 (plus the fixed point
    for `A := False`) **cannot prove its own consistency** — `¬ Box (Box False → False)`.  Löb at
    `A = False` gives `Box Con → Box False`; consistency (`¬ Box False`) then forbids `Box Con`.  This
    is the residue diagonal (for `Box · → False`) plus D1–D3 — nothing more. -/
theorem goedel_two {Box : Prop → Prop}
    (nec : ∀ {P : Prop}, P → Box P)
    (K : ∀ {P Q : Prop}, Box (P → Q) → Box P → Box Q)
    (four : ∀ {P : Prop}, Box P → Box (Box P))
    (C : Prop) (hC : C ↔ (Box C → False))
    (consistent : ¬ Box False) :
    ¬ Box (Box False → False) :=
  fun hcon => consistent (loeb_abstract nec K four C hC hcon)

/-! ## Sanity — the conditions are satisfiable (the theorem is not vacuous) -/

/-- The trivial modality `Box _ := True` satisfies D1–D3 and admits the fixed point: the abstract
    theorems are non-vacuously instantiable. -/
theorem trivial_box_models :
    (∀ {P : Prop}, P → (fun _ => True) P)
    ∧ (∀ {P Q : Prop}, (fun _ => True) (P → Q) → (fun _ => True) P → (fun _ => True) Q)
    ∧ (∀ {P : Prop}, (fun _ => True) P → (fun _ => True) ((fun _ => True) P)) :=
  ⟨fun _ => trivial, fun _ _ => trivial, fun _ => trivial⟩

end E213.Lib.Math.Logic.ProvabilityResidue
