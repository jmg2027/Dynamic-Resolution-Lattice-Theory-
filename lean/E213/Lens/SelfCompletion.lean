import E213.Theory.Raw.API
import E213.Lens.LensCore

/-!
# Lens.SelfCompletion — every Raw application uses all 4 clauses

`seed/AXIOM/07_self_reference.md` §8.6 records the self-completion
principle: every pointing is already complete (all 4 clauses
simultaneously present), not stepwise constructed.

This file records the Lean witness via the catamorphism: any Lens
`L : Lens α` requires *all three* data fields (`base_a`, `base_b`,
`combine`) plus Raw's `slash_comm` symmetry property to define
`L.view : Raw → α`.  The 4 clauses of `seed/AXIOM/02_statement.md`
§3.2 are thus visible at every Lens reading:

  - Clause 1 (two distinct atoms): the Lens's `base_a` and
    `base_b` are α-images of `Raw.a` and `Raw.b`.
  - Clause 2 (pairing residue is a residue element): the Lens's
    `combine` is the α-image of `Raw.slash`.
  - Clause 3 (symmetric pairing): Raw's `slash_comm` ensures
    `L.view` respects swap for Lenses with symmetric `combine`;
    for non-symmetric `combine`, the fold uses the canonical-form
    representative (encoding cost §8a).
  - Clause 4 (anti-reflexive): Raw's `slash` precondition
    `x ≠ y` is built into the type — every `Raw.slash x y h`
    carries `h : x ≠ y`.

No Raw is "halfway formed": every Raw, however atomic or however
deep its slash structure, fully exemplifies the 4-clause axiom at
construction.  Lens application reads this complete structure;
it does not extend it.

The Lean witnesses below show the per-clause visibility at the
two atomic constructors via definitional equality.  The slash
constructor's α-side correspondence is the catamorphism's
recursive case in `Raw.fold`; the slash-side proof is in
`Theory/Raw/Fold.lean` (`Raw.fold_slash` family).

Cf. `Meta/AxiomMinimalityCapstone.raw_forcing_chain_unified` for
the positive complement (the 1 → 2 → 3 → 4 structural force),
and `Meta/AxiomMinimality.lean` for the negative complement
(removing any clause collapses the framework).
-/

namespace E213.Lens.SelfCompletion

open E213.Theory (Raw)
open E213.Lens (Lens)

/-- ★ **All-clauses-visible witness at Raw.a**: every Lens's view
    of `Raw.a` is exactly the Lens's `base_a` field — the α-image
    of Clause 1's first atomic constructor. -/
theorem view_at_a_uses_base_a {α : Type} (L : Lens α) :
    L.view Raw.a = L.base_a := rfl

/-- ★ **All-clauses-visible witness at Raw.b**: every Lens's view
    of `Raw.b` is exactly the Lens's `base_b` field — the α-image
    of Clause 1's second atomic constructor. -/
theorem view_at_b_uses_base_b {α : Type} (L : Lens α) :
    L.view Raw.b = L.base_b := rfl

/-- ★★ **Atomic self-completion bundle** (§8.6 Lean witness, atomic
    part).  At the two atomic constructors `Raw.a` and `Raw.b`,
    every Lens reads exactly the corresponding base field —
    Clause 1 of §3.2 is visible at every Lens reading without
    any further structure. -/
theorem atomic_self_completion_bundle {α : Type} (L : Lens α) :
    L.view Raw.a = L.base_a ∧ L.view Raw.b = L.base_b :=
  ⟨view_at_a_uses_base_a L, view_at_b_uses_base_b L⟩

/-- ★ **Slash-side self-completion (symmetric `combine` case)**:
    For Lenses with symmetric `combine`, the view of a slash
    application is exactly `L.combine` applied recursively.  This
    witnesses Clauses 2-4 simultaneously: Clause 2 (slash IS in
    the residue, mapped to L.combine), Clause 3 (symmetric
    pairing, witnessed by hsym), and Clause 4 (the slash carries
    the precondition `x ≠ y` in its very type, used implicitly via
    `Raw.fold_slash`). -/
theorem view_slash_uses_combine {α : Type} (L : Lens α)
    (hsym : ∀ u v : α, L.combine u v = L.combine v u)
    (x y : Raw) (h : x ≠ y) :
    L.view (Raw.slash x y h) = L.combine (L.view x) (L.view y) := by
  show Raw.fold L.base_a L.base_b L.combine (Raw.slash x y h)
       = L.combine (Raw.fold L.base_a L.base_b L.combine x)
                   (Raw.fold L.base_a L.base_b L.combine y)
  exact Raw.fold_slash L.base_a L.base_b L.combine hsym x y h

/-- ★★★ **Full self-completion bundle (symmetric `combine`)**:
    every Lens reading of a Raw — atomic or slash — uses ALL FOUR
    clauses of §3.2 simultaneously:
      · `L.view Raw.a = L.base_a`               (Clause 1, atom 1)
      · `L.view Raw.b = L.base_b`               (Clause 1, atom 2)
      · `L.view (Raw.slash x y h) = combine ..` (Clauses 2, 3, 4)
    The four clauses are not sequenced; they are simultaneous
    visibility-conditions on every Lens application. -/
theorem full_self_completion_bundle {α : Type} (L : Lens α)
    (hsym : ∀ u v : α, L.combine u v = L.combine v u)
    (x y : Raw) (h : x ≠ y) :
    L.view Raw.a = L.base_a
    ∧ L.view Raw.b = L.base_b
    ∧ L.view (Raw.slash x y h) = L.combine (L.view x) (L.view y) :=
  ⟨view_at_a_uses_base_a L, view_at_b_uses_base_b L,
   view_slash_uses_combine L hsym x y h⟩

/-- ★ **Self-completion specialised at `Lens.leaves`**: the
    leaf-count Lens has symmetric combine `(· + ·)`, so the full
    bundle instantiates concretely.  No abstract `hsym` hypothesis
    required at the instantiated level. -/
theorem leaves_self_completion (x y : Raw) (h : x ≠ y) :
    Lens.leaves.view Raw.a = 1
    ∧ Lens.leaves.view Raw.b = 1
    ∧ Lens.leaves.view (Raw.slash x y h)
        = Lens.leaves.view x + Lens.leaves.view y :=
  ⟨rfl, rfl,
   view_slash_uses_combine Lens.leaves Nat.add_comm x y h⟩

end E213.Lens.SelfCompletion
