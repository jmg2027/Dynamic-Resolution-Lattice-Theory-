# G164 — `HasDistinguishing` `same`-rebuild (Compose/OnLens propext retirement)

Scratch design note for retiring the remaining Lens-tree DIRTY:
`Compose.OnLens` (9) + `Properties.TowerLevel3` (1), all `Quot.sound`-only.

## Root cause

`HasDistinguishing.combine_sym : ∀ x y, combine x y = combine y x` is a Lean
`=`.  For codomain `Lens β` (the Lens-of-Lens tower), `combine x y = combine y x`
is an equality of two `Lens β` *structures* whose `combine` fields differ only
pointwise — proving it needs `funext` (= `Quot.sound`).  So every
`HasDistinguishing (Lens β)` instance (`lensBoolHasDistinguishing`,
`lensHasDistinguishing`) is irreducibly DIRTY, and the image tower built on them
(`OnLensImage`, `OnLensImageGeneric`, `OnLensImageLevel2`, `ImageMinimum`,
`TowerLevel3`, + `Hyper213Tower`) inherits it.

The PURE eqPW twins already exist (`Lens/EqPW.lean`: `eqPW`, `eqPW_refl/symm/trans`,
`fold_slash_eqPW`, `view_unique_eqPW`; `OnLens`: `lensXor_comm_eqPW`,
`lensCombineGeneric_comm_eqPW`, `lensUniversalMorphism_slash_eqPW`,
`lensCombineGeneric_eqPW_cong`).  The blocker is purely that
`HasDistinguishing.combine_sym` demands Lean `=`.

## Materialized foundation (DONE, PURE, committed)

`Raw.fold_slash_rel` (`Theory/Raw/Fold.lean`): the relation-valued fold/slash
homomorphism — for any reflexive `R` with `R`-symmetric `combine`,
`R (fold (slash x y h)) (c (fold x) (fold y))`.  ∅-axiom.  Specialises to
`fold_slash` (`R := Eq`) and `fold_slash_iff` (`R := pointwise ↔`).  This is the
generic primitive `universalMorphism_slash` needs once `combine_sym` is stated
up to a per-codomain sameness.

## Target design — `same`-augmented `HasDistinguishing`

Generalize `combine_sym` to a per-codomain reading-sameness `same` (exactly the
`ReadingEq` pattern already built in `Lens/ReadingEquiv.lean`):

```
combine_sym : ∀ x y, same (combine x y) (combine y x)
```

with `same := Eq` default for the funext-free codomains (`Bool`, `Nat`, `Prop`,
`Pair`, `Sum`, `Subtype`, …) and `same := Lens.eqPW` for `Lens β`.  Then
`universalMorphism_slash` becomes `same (uM (slash..)) (combine (uM x)(uM y))`
via `fold_slash_rel d.same d.same_refl … d.combine_sym`; at `Eq`-instances it is
defeq the current `=`-form, so concrete consumers (`Pair`, `Reach`, `BoolProp`,
`CanonicalTruthChar`) are unaffected; at `Lens β` it is the ∅-axiom eqPW form.

## The three elaboration walls (empirically hit 2026-06-01)

1. **Field defaults can't see `same`'s default.**  `same_refl : ∀ x, same x x
   := fun _ => rfl` fails to elaborate — inside the class body `same` is the
   abstract projection, not its `Eq` default, so `rfl` has the wrong type.
2. **No-default ⇒ "fields missing" on ~20 existing instances.**  Dropping the
   defaults forces every existing `HasDistinguishing` instance to spell out
   `same`/`same_refl`/`same_symm`/`same_trans` (≈ 4 boilerplate lines each).
3. **`extends ReadingEq α` / `[ReadingEq α]` param ripples to 15 files.**
   Reusing `ReadingEq` either (a) as a class parameter makes every generic
   `[d : HasDistinguishing α]` signature need `[ReadingEq α]` added, or (b) via
   `extends` re-hits wall 2 (instances must provide the `ReadingEq` fields).

## Recommended path (next session, green per commit)

Option B (touch all instances, mechanical, keeps green):
  1. Add `same`/`same_refl`/`same_symm`/`same_trans` as **non-defaulted** fields
     + `same`-based `combine_sym`.  Add the four `same := Eq; … := rfl/.symm/.trans`
     lines to **every existing instance** (≈ 20 sites — all `=`-codomain, so
     the boilerplate is identical and copy-paste).  Restate
     `universalMorphism_slash` via `fold_slash_rel`.  Build green.
  2. Convert `lensBoolHasDistinguishing` / `lensHasDistinguishing` to
     `same := eqPW`, `combine_sym := …_eqPW`.  They become PURE.
  3. Restate `levelOne..Four`, `lensUniversalMorphism_slash`, `TowerLevel3`,
     and the `OnLensImage*` tower on the `same`/eqPW form.  Verify
     `Hyper213Tower` (consumes `lensHasDistinguishing`).

Consider a `HasDistinguishingEq` smart-constructor (`same := Eq` + the three
law defaults baked in) so the ≈ 20 `=`-instances stay one-liners
(`:= { … }` via the constructor) rather than 4 extra fields each.

## Scope marker

This is a **headline-(a)-sized** atomic-ish refactor (the class change + its
generic `universalMorphism_slash` consumer break the build until the cascade is
consistent).  Do it as a dedicated session with green-per-commit discipline; do
**not** start it without budget to land the class change + `universalMorphism_slash`
+ the 7 direct consumers in one green commit.  Anchor: `fold_slash_rel` (PURE,
materialized).  Related: `theory/lens/unified_equivalence.md` (the `ReadingEq`
pattern), `Lens/EqPW.lean` (the eqPW twins).
