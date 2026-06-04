# G165 — Synthesis after the reading-equivalence unification

**Anchor**: the equivalence-unification arc closed the Lens tree to **0 real
DIRTY** by making reading-equivalence (`ReadingEq.same`) 213's canonical
sameness — Lean `=` is its realization at concrete codomains, the pointwise
form (`equivR`/`sameLens`) where `=` would import `funext`/`propext`, and
`propext` survives only at the `Prop`-atom thesis (`propAsDistinguishing`).
This note records what that closure makes visible.

## Patterns

  1. **"Borrowed `=` vs residue-native sameness" is a repo-wide diagnostic, not
     a Lens-local one.**  Every place the framework states a property as Lean `=`
     of a function- or `Prop`-valued thing (`Lens.equiv`, `combine_sym`,
     `view_eq`, kernels) was importing `funext`/`propext` for *statement shape*,
     not content; the residue-native form is the pointwise relation.  The DIRTY
     catalog's categories (A)/(C) (`catalogs/correspondence-surface.md`) ARE this
     surface, and it is now retired in the Lens ring.  The same lens applies
     outside Lens: any `Lib/Math` theorem stated as `f = g` for functions, or as
     an `Iff`-collapsed-to-`Eq` on `Prop`, is a candidate.

  2. **`autoParam`-defaulted typeclass fields = "default `Eq`, override where the
     codomain needs it".**  `HasDistinguishing`'s `same`/`same_refl/symm/trans`/
     `combine_cong` carry `:= by …` `autoParam` defaults, so `Eq`-codomain
     instances need *no* edits while `Lens`/`Prop` codomains override.  This is a
     reusable encoding for any algebraic structure whose axiom is currently a
     `=`-over-a-function-codomain (a symmetry/congruence law).  Crucially the
     defaults must be `autoParam` (`:= by …`), not term-defaults (`:= fun …`),
     which fail to elaborate against the abstract field (the G164 wall 1).

  3. **Recursive-tower sameness via `sameLens` + congruence-transitivity.**  The
     `Lens (Lens β)` tower closed with `same_trans step1 ⟨step2, step2, fun _ _ =>
     step2⟩`: the base relation threads through `constLens` so each `sameLens`
     component is the one-level-down result.  `Lens.sameLens R` (base-relation
     pointwise sameness, `sameLens Eq = eqPW`) is the reusable primitive; `eqPW`
     hardcodes `=` on the base and is funext-DIRTY for nested `Lens (Lens β)`.

  4. **The cascade is the truth, not the bug (methodology).**  The multi-pass
     finding that the unification "ripples to ~24 files (every composite
     instance)" was first read as a cost to avoid (design D); it is in fact the
     framework *adopting its own sameness* — a product's sameness IS the product
     of component samenesses, coinciding with `=` only at concrete components.
     General lesson: when a foundational change ripples widely, ask whether the
     ripple is exposing that the *old* foundation was the borrowed thing, before
     quarantining it.

## New questions (next-campaign seeds)

  1. **Validation-core ∅-axiom audit (the natural next campaign).**  The
     equivalence substrate is now clean; the DRLT Validation Standard
     (`catalogs/{physics-constants,falsifiers}.md`) is the real target.  Are the
     precision theorems (`1/α_em` at `AlphaEM/GramStructuralCapstone`, `m_μ/m_e`,
     `m_p`, `R∞`) and falsifiers (`N_gen = 3`, `θ_QCD`, Cabibbo `λ = 5/22`)
     *strict ∅-axiom* in Lean, or do they inherit `propext`/`omega` from
     arithmetic plumbing?  Concretely: scan each capstone, list the gaps, and
     close them with the `Meta/Nat` + `Int213` + `NatHelper` playbook.  This is
     where foundational hygiene turns into the actual scientific claim.

  2. **CD-tower recursion via `sameLens`-style threading** (resonance with
     pattern 3 + the open `Trig.conj_mul_anti` / `SedenionHeavy.flexible`).  The
     Cayley–Dickson doubling is a recursive tower like the Lens tower; its
     `conj`/`normSq` coherence is currently stated as `=` (and the Sedenion layer
     needs a `NonAssocStarRing213` bridge).  Does the same recursive-sameness
     threading (`⟨step, step, …⟩` over the doubling) give a clean
     `NonAssocStarRing213 Sedenion` and thence `Trig.conj_mul_anti`, without the
     `[StarRing213 α]` gate?  See `theory/essays/tower_atlas.md` "tower duality".

  3. **`HasDistinguishing213` (GRA) and other `=`-combine_sym structures.**  Per
     pattern 1+2: does the GRA-layer `HasDistinguishing213`
     (`Lib/Math/GRA/HasDistinguishing213.lean`) — and any other algebraic
     structure carrying a `combine`/op symmetry as Lean `=` over a
     function-codomain — admit the same `same`-field treatment?  A grep for
     `_comm`/`_sym : … = …` over function/`Prop` codomains across `Lib/Math`
     would surface the candidates.

## Cross-references

  - Patterns 1–4, question 1: `research-notes/RFC_reading_equivalence_primitive.md`,
    `theory/lens/unified_equivalence.md`, `theory/lens/dirty_recovery_patterns.md`
    (Pattern P5), `catalogs/correspondence-surface.md`.
  - Pattern 2 encoding walls: `research-notes/G164` (the 5-pass investigation).
  - Pattern 3 + question 2: `Lens/EqPW.lean` (`sameLens`),
    `Lib/Math/CayleyDickson/*`, `theory/essays/tower_atlas.md`.
  - Question 1 anchors: `catalogs/physics-constants.md`,
    `catalogs/falsifiers.md`, `CLAUDE.md` "DRLT Validation Standard".
