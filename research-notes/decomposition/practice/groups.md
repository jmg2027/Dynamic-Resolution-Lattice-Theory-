# Decomposition: groups / symmetry

*213-decomposition of "a group", per `../README.md`. Tests the hypothesis: a group is not one
character but the **closed family of all construction-preserving readings (automorphisms) of a
construction**, with composition as the operation.*

## The decomposition

- **Construction `C`** — any construction with a distinguishing-history to preserve. The concrete
  Lean instance is the **list-of-values position structure** `iota n = [0,1,…,n−1]`: `n` distinguished
  positions. The "thing to be preserved" is the *set of distinguishings* — which positions are
  distinct from which (here: all of them, a bare `n`-element discrete construction).

- **Reading** — not *a* reading but a **family of readings that each fix `C`'s distinguishings**: a
  permutation `σ ∈ perms n`. Each `σ` is a relabelling that keeps "distinct stays distinct" — a
  *construction-preserving self-reading*. Crucially these readings form a **closed family under an
  operation**: composition `composeList σ τ` (apply one reading, then the other).

- **Residue** — what a single automorphism forgets is *which* relabelling was applied (a `σ`-fibre);
  but the load-bearing residue here is **structural, not per-element**: the *abstract group* is the
  residue of the readings' own composition table, invariant under which construction realises it
  (the same `Sym(3)` shows up as positions, as roots, as triangle symmetries — the residue is the
  multiplication pattern that survives all realisations). This is the `LensIso` groupoid one level
  up: `Sym(n)` is the **automorphism vertex-group of `C` in the Lens groupoid**.

## Re-seeing

```
   a group          =  ⟨ C (a distinguishing-structure) | the closed family of C-preserving self-readings ⟩
                       with composition = "read, then read again"

   identity         =  the do-nothing reading  iota n           (composeList_iota_left / _right)
   inverse          =  the undo-reading         invPerm σ        (composeList_invPerm_left/_right)
   associativity    =  reading-then-reading nests freely         (composeList_assoc)
   closure          =  C-preserving ∘ C-preserving is C-preserving (composeList_mem_perms,
                                                                    invPerm_mem_perms)
   a character      =  a reading OF the group into a number-construction (det/sign): the group's own
                       readout  (psign_mulPerm_hom, the Cayley→sign hom)
```

`Aut`-as-abstract-shape already sits in the Lens layer: `LensIso L L` is reflexive
(`lensIso_refl`), symmetric (`lensIso_symm`), transitive (`lensIso_trans`) — a **groupoid**, and a
group is its **one-object full subcategory** (all self-iso's of a single `C`). `perms n` is that
groupoid's vertex group made concrete and finite.

## Revelation (forcing — the group axioms are *not posited*)

The payoff is **forcing, not collapse**: the four group axioms are *forced* by "self-readings that
preserve `C` and compose", each a bare ∅-axiom list identity in `PermGroup.lean` — nothing is
assumed, the axioms *fall out* of "relabel-and-compose":

- **identity** is forced because "do nothing" trivially preserves `C`: `composeList (iota n) τ = τ`
  (`composeList_iota_left`) and `composeList σ (iota n) = σ` (`composeList_iota_right`).
- **inverse** is forced because a `C`-preserving reading is a *bijection of distinguishings*, so it
  has an undo: `composeList (invPerm σ) σ = iota n` (`composeList_invPerm_left`), and `invPerm σ` is
  itself `C`-preserving (`invPerm_mem_perms`).
- **associativity** is forced because composition is just "apply the readings in order" — function
  composition is associative on the nose: `composeList_assoc`.
- **closure** is forced because preserving-then-preserving still preserves: `composeList_mem_perms`.

So a group is **literally what you get when you take all readings that fix a construction and ask how
they compose** — the axioms are the *signature of "preserve + compose"*, not an independent
definition. This certifies the hypothesis: a group is the closed family of construction-preserving
readings, with the group laws *derived* from preserve-and-compose.

**The character is the group reading itself.** The hypothesis said "this tests whether
character-mode generalizes from one reading to a closed family." The two are not rivals — they are
**stacked one level apart**: the *family* (the group, `perms n`) is the object; a **character** is a
reading *of that family* into a number-construction. `psign_mulPerm_hom` is exactly this: the map
`(ℤ/p)ˣ → perms p → {±1}`, `a ↦ mulPerm a ↦ psign (mulPerm a)`, with `mulPerm_comp`
(`mulPerm (a·b) = mulPerm a ∘ mulPerm b`) being the **Cayley embedding** (multiplication *is*
composition) and `psign` the sign character on top. The determinant decomposition's `det = ±1` (its
`L₂`) is the *same* `{±1}` character on the matrix realisation. So: **group = closed reading-family;
character = a number-readout OF that family.** Single-reading "character" (`parity.md`,
`determinant.md`) is the codomain side; "group" is the domain side. They compose, they don't compete.

## Note for the technique — does the model need a new construct?

**Verdict: groups EXTEND the model; they do not break it — but they force one explicit promotion.**

The single-reading picture (`L` = one projection) does **not** by itself carry "a closed family of
readings under composition". The README's emerging map has `L` carrying `{resolution,
character-mode}`; neither slot is "a *set* of readings closed under an operation." So the honest
finding is:

- **No genuinely new primitive is needed** — the family is built entirely from the *existing*
  pieces: a reading is `Lens`-shaped; "preserves `C`" is `Lens.refines`/`LensIso` (a self-iso);
  "compose two readings" is already in the Lens layer (`lensIso_trans`). A group is `⟨ C |
  self-LensIso's under ∘ ⟩` — all parts pre-existing.
- **But the model needs an explicit new *level marker*: a reading can have a `Lens`-codomain.** The
  determinant note already half-saw this ("a character is a reading whose readout is itself a number
  *construction*"). Groups push it further: the readout of a character is a number-construction, but
  the **operand** of a character is *itself a family of readings*. So the calculus's normal form
  `⟨C | L⟩` must allow `C` to *be* "the closed family of self-readings of some inner `C₀`". That is a
  **second-order `⟨ ⟨C₀ | self-readings⟩ | character ⟩`** — a reading of a reading-family.

Concretely, the proposed map extension:

> **Add to the map a closure operator `Aut(·)`:** `Aut(C) = the closed family of C-preserving
> self-readings under composition`. It is *forced* (its laws = `PermGroup`'s four identities), it
> *pays* (the group axioms collapse to "preserve + compose"; Cayley `mulPerm_comp` shows
> multiplication-structures are *also* `Aut` of something), and it *stratifies the existing slots*:
> the README's lone "character-mode" is now seen as **the codomain of an `Aut`-valued operand** —
> single reading and reading-family are domain/codomain of one arrow, one level apart.

This is the analogue, for groups, of what "height became first-class" did for dimension: the family
is not a *new kind of thing*, it is the **closure of the reading slot under composition**, and the
README's single-`L` picture is the un-closed special case (`|Aut| = 1`, the trivial group —
`SymmetrySpecies.AutGroup.trivial`). So: **extend, with one promotion (the reading slot gains a
composition-closure `Aut`); do not break.**

A second, softer extension surfaced: the repo *already* catalogs groups exactly this way.
`SymmetrySpecies.lean` defines a **`FamilySpecies = (preservation-axis bucket, AutGroup, atomic
invariant)`** — i.e. it literally pairs "what is preserved" (`C`) with "the automorphism group"
(`Aut(C)`), and tags each with an atomic invariant in `{det, NT, NS, d} = {1,2,3,5}`. That is the
decomposition calculus's group-form, already a Lean structure — independent corroboration that
"group = (preserved construction, its automorphism family)" is the native reading, not an imposed one.

## Verified Lean anchors (all ∅-axiom-style pure list/`ℤ` identities)

- `Lib/Math/Algebra/Linalg213/PermGroup.lean`:
  - `composeList` (def, the group operation = "read then read")
  - `composeList_iota_left`, `composeList_iota_right` (identity = the do-nothing reading `iota n`)
  - `composeList_assoc` (associativity)
  - `invPerm` (def), `composeList_invPerm_left` (inverse = the undo-reading)
- `Lib/Math/Algebra/Linalg213/DetTranspose.lean`:
  - `invPerm_mem_perms` (inverse stays C-preserving — closure under inverse)
  - `perms_closed_invPerm` (`perms n` is its own image under `invPerm`)
- `Lib/Math/Algebra/Linalg213/DetMul.lean`:
  - `perms_closed_rightMul` (closure under right-composition), `composeList_mem_perms` (closure)
- `Lib/Math/NumberTheory/ModArith/Zolotarev.lean`:
  - `mulPerm_comp` (★ **Cayley**: multiplication ↦ composition, `mulPerm (a·b) = mulPerm a ∘ mulPerm b`)
  - `mulPerm_mem_perms` (a unit's multiplication is a C-preserving reading)
  - `psign_mulPerm_hom` (★ the sign **character** of the group: `psign (mulPerm (a·b)) =
    psign (mulPerm a) · psign (mulPerm b)`)
- `Lens/Unified.lean`:
  - `LensIso` (def), `lensIso_refl`, `lensIso_symm`, `lensIso_trans` (the **groupoid** of which a
    group is the one-object vertex group), `lensIso_iff_kernel_eq` (iso = kernel coincidence)
- `Lib/Math/Algebra/Mobius213/Px/SymmetrySpecies.lean`:
  - `FamilySpecies` (struct: `(bucket, AutGroup, status, atomic)`), `AutGroup` (inductive incl.
    `trivial, z2_involution, sym3_action, sl2z_orbit, galois, groupoid`) — the repo's native
    "(preserved construction, automorphism group)" catalog form.

## Dropped / unverified citations

- **`FTA.Perm` in `Lens/Number/Nat213/FTA.lean`** — the prompt's candidate path does not exist
  (`Glob` of `Nat213/FTA.lean` = no match; `grep FTA.lean` only finds it imported, no native
  permutation inductive there). The real permutation/symmetric-group infrastructure is
  `Lib/Math/Algebra/Linalg213/{Permutation,PermGroup,PermSign}.lean`. Dropped as named; replaced by
  the verified `PermGroup` anchors.
- **`HasDistinguishing213`, `GRA` graded-group, Cayley-Dickson automorphisms** — not used as anchors
  here. CayleyDickson has a `conj` *anti*-automorphism (`CayleyDickson/INDEX.md`), not a clean group
  `Aut` theorem I verified, so I did not cite it. `GRA/LensIsoCapstone.lean` uses
  `lensIso_iff_kernel_eq` but is a grade-profile result, not a group-axiom witness — left out to
  avoid overclaiming.
- **`AutGroup` constructors are an inductive *tag*, not proven group structures.** `sym3_action`,
  `galois`, etc. are catalog labels in `SymmetrySpecies`; the *honest* grounding for the group axioms
  is `PermGroup` (concrete `Sym(n)`), not the `AutGroup` enum. The enum corroborates the *form* of
  the decomposition, it does not certify the axioms — flagged so the Lean grounding for "abstract
  group" is read as **thin beyond `Sym(n)`**: the four axioms are proven for the permutation
  realisation; the *abstract*/general group is catalog-level, not theorem-level, in this repo.
