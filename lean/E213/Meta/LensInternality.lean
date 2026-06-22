import E213.Theory.Raw.API
import E213.Lens.LensCore

/-!
# LensInternality — Lens is a Raw-internal concept

The "every framework is a Lens" meta-claim would require standing
outside 213 to evaluate (which `seed/AXIOM/05_no_exterior.md` §5.1 rules out).  Instead this file formalises the residue-side
dual: **every Lens is a Raw-internal event** — its data is exactly
the triple `(base_a, base_b, combine)` on the codomain α, and its
view is exactly `Raw.fold` of that data.  Lens is therefore not an
external import but the canonical name for "α-side data Raw's fold
needs to read itself into α".

Two ∅-axiom formal parts:
  (1) Type-level : `Lens α ≃ α × α × (α → α → α)` (round-trip)
  (2) View-level : `L.view r = Raw.fold L.base_a L.base_b L.combine r`

Universality (∃! `Raw → α` Lens-homomorphism per Lens) is the third
leg of the picture; it is proved upstream as `Lens.initiality` in
`Lens/Foundations/Initiality.lean`, which depends on `Quot.sound` (sealed
funext-by-design via `Raw.fold` quotient-lifting) and is therefore
NOT re-exported here.  The categorical statement "Raw is the
initial object in the commutative Lens-algebra category" is
documented there; the ∅-pure capstone in this file establishes the
*data-and-view internality* — the strongest part that survives
under the strict ∅-axiom standard.
-/

namespace E213.Meta.LensInternality

open E213.Theory E213.Lens

/-! ## (1) Type-level: Lens ≃ data triple -/

/-- A Lens unfolds to its `(base_a, base_b, combine)` triple. -/
def toData {α : Type} (L : Lens α) : α × α × (α → α → α) :=
  (L.base_a, L.base_b, L.combine)

/-- A `(base_a, base_b, combine)` triple folds back to a Lens. -/
def ofData {α : Type} (d : α × α × (α → α → α)) : Lens α :=
  ⟨d.1, d.2.1, d.2.2⟩

/-! ## (2) Round-trip + view-fold are definitional (`rfl`).
    Stated below as conjuncts of `lens_is_raw_internal` rather
    than as named one-line theorems. -/

/-- ★★★★★★★ **Lens internality capstone**

    A Lens carries no information beyond the data triple
    `(base_a, base_b, combine) ∈ α × α × (α → α → α)`, and its view
    is exactly `Raw.fold` of that data.  Lens is not an external
    concept; it is the canonical name for "the α-side data needed
    to fold Raw".

    Three ∅-axiom clauses:
      · `ofData ∘ toData = id`  (Lens reconstructible from data)
      · `toData ∘ ofData = id`  (no Lens content beyond the triple)
      · `L.view = Raw.fold ...` (no view definition outside fold) -/
theorem lens_is_raw_internal {α : Type} :
    (∀ L : Lens α, ofData (toData L) = L)
    ∧ (∀ d : α × α × (α → α → α), toData (ofData d) = d)
    ∧ (∀ (L : Lens α) (r : Raw),
         L.view r = Raw.fold L.base_a L.base_b L.combine r) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩

end E213.Meta.LensInternality
