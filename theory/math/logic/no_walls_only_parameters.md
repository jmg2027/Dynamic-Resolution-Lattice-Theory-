# No walls, only free Lens parameters — the tetrachotomy and the calculus's self-grounding

## Overview

Every apparent **boundary** of the decomposition calculus — the axiom of choice, LLPO, the ultrafilter,
forcing, large cardinals, completeness, undecidability — is, when decomposed through `OBJECT = ⟨C|L⟩ ⊕
Residue`, one of exactly **four** things, the **tetrachotomy**

  `∅ / 0 / 1 / many  =  absence / wall / forced / free`,

the *section-count* of the reading-fibration over the construction `C`.  There is exactly **one wall** (the
Lawvere diagonal = the residue's non-surjection), and it is **internal** — the calculus's own founding
theorem, not an external limit.  Everything else is a **free Lens parameter** (no exterior dialer, §5.1),
splitting into **selection-σ** (symmetric; = forcing) and **height-h** (one-way; = large cardinals) — the two
axes of set-theoretic independence.  The classification is **self-grounding**: the calculus builds every
concrete instance ∅-axiom but **not its own master classifier — because that classifier *is* the wall**, a
closed theorem; and self-classification is **idempotent** — the tetrachotomy is the fixed point of
`classify`.

## Lean source

`lean/E213/Lib/Math/Logic/` — nine ∅-axiom modules (all `#print axioms`-clean):
`ChoiceLens`, `ForcingToy`, `SectionCount`, `SectionCountWithAbsence`, `FiberSymmetry`,
`MasterClassifierNoGo`, `TagOfDecidable`, `GenericAsCut`, `ArityCoupling`.

## Narrative

**1. Choice is a free Lens parameter, not a wall to refuse.**  A choice function is a *section* of an
inhabited family `X : I → Type` — i.e. a **Lens** `σ`.  Different choices (`σ_left`/`σ_right`/…) are
different Lenses.  Applying a Lens is an *act*, not an existence claim, so the calculus never asserts "a
section exists"; it applies a rule `σ` and reads.  The non-constructive content is precisely that **no `σ` is
forced/canonical** (no exterior dialer, §5.1): `σ` is a *free parameter*.  "AC true" (any `L_σ` applicable)
and "AC refused" (no `L_σ` canonical) jointly say `σ` is free; one computes *per-σ* (constructively — sections
are explicit data).  Over a binary fiber `σ ∈ {left,right}` **is** the `q=±1` residue tag, and **LLPO** is
that bit left unforced.  A free parameter admits *both* adjunctions consistently — so AC's Gödel–Cohen
**independence = `σ` is free**, and **forcing = adjoining a generic `σ`**.

**2. Forcing = σ-adjunction.**  `ForcingToy` realises this minimally: two generics `g0, g1` over a two-point
poset give two *distinct* global sections of the *same* construction, neither canonical — Cohen independence
as Lens-parameter adjunction.  Carrying both `σ` over the poset and projecting per condition (`carryBoth`/
`proj`) is sheaf-over-poset semantics, funext-free.

**3. The tetrachotomy.**  Generalising: any boundary is the **section-count** of the reading-fibration over
`C`.  `SectionCount` builds the `0/1/many` trichotomy as an object; `SectionCountWithAbsence` adds the `∅`
(not-yet-built, §5.4) below the `0/1` cut (fiber-inhabitation).  `0` = wall (no section — the diagonal),
`1` = forced (the construction axes, uniquely determined), `many` = free (the L-parameters).

**4. The free parameters split by symmetry = fiber order.**  `FiberSymmetry`: a free parameter over an
*unordered* fiber is symmetrically free (swap-involution, both readings interchangeable = forcing); over a
*well-ordered* fiber it is asymmetrically free (strictly-up, no-top, one-way = large cardinals).  Genericity
is the height-limit of a free `σ`; the height-escape is the one diagonal (Burali-Forti).

**5. One axis-polymorphic wall, and self-grounding.**  Cantor / Russell / Gödel / halting / the generic are
the *same* diagonal at different carriers.  The classifier of the normal form, applied to itself, lands on
that diagonal: `MasterClassifierNoGo.master_classifier_is_the_wall` — a would-be master classifier that
*both* decides the diagonal and is a row of its own cover is forced into a `not`-fixed-point, impossible.
The theory builds every concrete instance ∅-axiom but not its own master classifier *because that is the
wall*, and **its un-buildability is the theorem**.  `TagOfDecidable` exhibits the buildable part: the
classifier is total *below* the wall (`tagOf_never_wall` — the wall tag `0` is structurally unreachable on
decidable fibers); the wall appears only at the `Type`-valued self-cover.

**6. The reflexive closure + the fixed point.**  The normal form `⟨C|L⟩ ⊕ Residue` is *itself* the
tetrachotomy: `C` = forced (tag-`1`, `ArityForcing`/`pair_forcing`), the `L`-parameters = free (tag-`many`,
`choice_is_free_lens_parameter`), the `Residue` = wall (tag-`0`), absence = `∅`.  The forced base shapes the
free fibers: the forced atom `NT = 2` is exactly the binary fiber over which `σ` = the `q=±1` tag —
`ArityCoupling` makes this one parametric theorem (`#free-values = NT`).  The **generic** (`GenericAsCut`) is
tag-`many`'s reached-by-none *positive* limit, a `Real213`-cut, dual to the wall's reached-by-none *negative*
— `converge`(q+1)/`escape`(q−1).  Finally, **self-classification is idempotent**: applying `classify` to any
reading (the coupling, even `classify`) yields the same four tags, the master always the wall, the
self-application always collapsing (no regress).  The general idempotence theorem is itself the wall —
ABSENT-by-self-grounding, the closing honest negative.

## Key results

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `choice_is_free_lens_parameter` | `ChoiceLens` | two explicit sections + a σ-dependent operation: choice = a free Lens parameter, no AC |
| `forcing_toy_independence` | `ForcingToy` | two generics → two distinct global sections (forcing = σ-adjunction) |
| `forced_exists_unique` / `free_two_sections` | `SectionCount` | the `1` (forced) and `many` (free) poles of the section-count |
| (`StatusCount` ∅/0/1/many) | `SectionCountWithAbsence` | the tetrachotomy: absence below the wall/forced/free |
| `fiber_symmetry_law` | `FiberSymmetry` | free-parameter symmetry = fiber order (unordered=forcing / well-ordered=large-cardinals) |
| `master_classifier_is_the_wall` / `self_grounding_capstone` | `MasterClassifierNoGo` | the master classifier is the diagonal — self-grounding, proved |
| `tagOf_total` / `tagOf_never_wall` | `TagOfDecidable` | the classifier is total below the wall; tag-`0` unreachable on decidable fibers |
| `generic_is_reached_by_none_cut` | `GenericAsCut` | forcing's generic = a reached-by-none `Real213`-cut |
| `arity_coupling` / `fpf_modifier_iff` / `forced_NT_couples_free_and_wall` | `ArityCoupling` | the forced `NT` parametrically determines free-fiber arity and the wall's modifier |

## Research-note provenance

Developed in the "no walls, only free Lens parameters" seminar (R1–R6); the open R7+ thread remains in
`research-notes/frontiers/no_walls_seminar/`.  Folded into `SYNTHESIS.md` §2 (vii′)–(xi).

## Open frontier

The *general* idempotence theorem `classify ∘ classify = classify` is the wall (un-buildable by
self-grounding) — a partial decidable idempotence *below* the wall is open; and whether the one-way-ness of
the height axis (Gödel II) is a new fact or the escape/converge asymmetry on the strength axis.  Tracked in
`research-notes/frontiers/no_walls_seminar/`.

## How to verify

```
cd lean && lake build E213.Lib.Math.Logic
python3 tools/scan_axioms.py E213.Lib.Math.Logic.MasterClassifierNoGo   # and the other eight
```
All nine modules report `0 dirty`; `#print axioms` on each headline theorem → "does not depend on any axioms".
