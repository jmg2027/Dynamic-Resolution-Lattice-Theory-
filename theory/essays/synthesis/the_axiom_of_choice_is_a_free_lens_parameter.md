# The axiom of choice is a free Lens parameter

A choice function is a **section of an inhabited family** — a Lens `σ` — and no exterior dialer fixes
*which* section.  The axiom of choice is therefore not a truth to assert or a principle to refuse; it is the
statement that `σ` is a **free parameter**, and one computes per-`σ`.

## 213-native answer

Given a family `X : I → Type` with each fiber inhabited, a choice function is a section `σ : ∀ i, X i`
(`theory/math/logic/no_walls_only_parameters.md`).  Applying a section is an *act* — a residue self-pointing,
not an existence claim — so the calculus never writes `∏_i X_i ≠ ∅`; it applies a rule (`σ_left`, `σ_right`,
`σ_min`, …) and reads.  `Lib/Math/Logic/ChoiceLens.lean` makes this an object: two explicit sections
`sigmaL`/`sigmaR` of the family `i ↦ Bool`, an operation `readOp` that returns different values under each
(`readOp sigmaL 3 ≠ readOp sigmaR 3`), and `choice_is_free_lens_parameter` bundling them — all ∅-axiom, **no
choice axiom used**, because the sections are explicit data.

## Derivation

The non-constructive content of AC is exactly that **no section is forced**.  This is the no-exterior axiom
read at the level of a parameter: there is no dialer outside the construction to select one `σ`
(`seed/AXIOM/05_no_exterior.md` §5.1).  So "AC true" (any `L_σ` may be applied) and "AC refused" (no `L_σ` is
canonical) are not contradictory — together they say `σ` is free, the same status the p-adic *base* and the
resolution dial already carry (`theory/math/logic/no_walls_only_parameters.md`, the L-parameter frame).

Over a two-element fiber the section `σ ∈ {left, right}` is a single ∓1 bit — it *is* the `q=±1` residue tag
(`Lib/Math/Foundations/ResidueTag.lean`, `multiplier_unimodular`), and **LLPO** (`Lib/Math/Logic/Omniscience.lean`)
is that bit left undetermined.  This places choice in the tetrachotomy `∅/0/1/many = absence/wall/forced/free`:
a free `σ` is the **many** pole — many sections, none forced.

A free parameter admits *both* adjunctions consistently.  `Lib/Math/Logic/ForcingToy.lean` realises this:
two generics over a two-point poset give two distinct global sections of one construction, neither canonical
(`forcing_toy_independence`).  That is Cohen forcing as Lens-parameter adjunction — so the Gödel–Cohen
**independence of AC is the freedom of `σ`**, not a defect.  And the generic itself is the height-limit of the
free `σ`, reached by no finite condition: `Lib/Math/Logic/GenericAsCut.lean`
(`generic_is_reached_by_none_cut`) gives it the shape of a `Real213` cut (`theory/math/numbersystems/real213.md`)
— convergents narrow, the limit is reached by none.

## Dual function

This is the classical axiom of choice with its packaging removed: the classical setup hides the section
behind "by AC, choose…" and then debates whether the choice *exists*; stripping that, the section is the only
content, and it is data one supplies.  The 213 reading is sharper exactly where the classical one is mute —
it says *which* freedom AC names (a section of the reading-fibration), *why* it is independent (a free
parameter has no forced value, so both adjunctions are consistent), and *what* its limit is (a reached-by-none
cut).  Refusal explains none of these; parametrisation explains all three.

## Cross-frame connections

The same structural fact appears in four frames at once: **§5.1 no-exterior** (no dialer fixes `σ`), the
**`q=±1` tag** (the binary `σ` is the ∓1 bit, `ResidueTag`), **forcing-as-adjunction** (`ForcingToy`,
independence = `σ` free), and the **reached-by-none cut** (`GenericAsCut` = the `Real213` modulus shape).
Choice, the residue tag, forcing, and the continuum's cut are one object read at four resolutions: a free
Lens parameter and its reached-by-none limit.

## Open frontier

A σ-parametrised *operation library* (the ultrafilter, well-ordering, Hahn–Banach each carried with an
explicit `σ`) and the forcing/independence statement as a Lean theorem (`σ` free ⟹ both adjunctions
consistent, a model-theoretic build) remain open; the dense-set genericity beyond the single-section cut is
not yet formalised (`research-notes/frontiers/no_walls_seminar/`).
