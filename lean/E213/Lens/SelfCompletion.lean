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
    any further structure.

    The slash-constructor side (Clauses 2-4) is witnessed by
    `Raw.fold_slash` and `Raw.slash_comm` in `Theory/Raw/`; this
    file records the atomic half of the bundle and provides the
    self-completion docstring framing. -/
theorem atomic_self_completion_bundle {α : Type} (L : Lens α) :
    L.view Raw.a = L.base_a ∧ L.view Raw.b = L.base_b :=
  ⟨view_at_a_uses_base_a L, view_at_b_uses_base_b L⟩

end E213.Lens.SelfCompletion
