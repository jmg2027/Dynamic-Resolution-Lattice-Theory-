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

## UPDATE 2026-06-01 (second pass) — design VALIDATED + cascade mapped

A second attempt validated the design and mapped the real blocker (then reverted
to green, keeping `fold_slash_rel`).  Concrete findings:

  * **Design C works** (the `autoParam` fix for wall 1).  `same`/`same_refl`/
    `same_symm`/`same_trans`/`combine_cong` as **`autoParam`-defaulted fields**
    (`:= by intro …; …`, NOT term-defaults `:= fun …`) elaborate at class def
    AND defer to per-instance elaboration — so `Eq`-codomain instances need **no
    edits** (verified by a scratch: `MiniHD Nat` with no `same`/law fields, a
    generic `[MiniHD α]` theorem, and a `MiniHD (Lens Bool)` override all
    compiled; no diamond because `same` is a *field*, not a `[ReadingEq α]`
    param — the param version DID hit the diamond: `MiniHD (Lens Bool)`
    synthesis failed with both default-`Eq` and override `ReadingEq` present).
  * **SemanticAtom relativizes cleanly + green**: `combine_sym` → `same`-based;
    `universalMorphism_slash` via `Raw.fold_slash_rel`; `universalMorphism_unique`
    + `raw_initial` reproven by `Raw.rec` (chain `hslash` + `combine_cong` on IHs
    + `_slash`).  All three PURE.  At `Eq`-instances `same` reduces to `Eq`
    definitionally, so the **full default-target build stayed green** with the
    class changed (existing consumers unaffected by defeq).
  * **`Lens.sameLens R` is the tower's sameness** (NOT `eqPW`): `eqPW` hardcodes
    `=` on `base_a : β`, which is funext-DIRTY when β is itself `Lens γ` (nested
    tower).  `sameLens R L M := R base_a base_a ∧ R base_b base_b ∧ ∀ u v, R (comb
    u v)(comb u v)` threads the base's own `same`.  Materialize `sameLens` +
    `sameLens_refl/symm/trans` + `lensCombineGeneric_{comm,cong}_same` (all
    one-liners, PURE).  Then `lensBoolHasDistinguishing` uses `same := eqPW`
    (base `Bool`, `=` is fine) and `lensHasDistinguishing` uses
    `same := sameLens d.same` (recursive).  Both go PURE.  NOTE: pass the law
    args with `(R := d.same)` pinned — higher-order implicit inference of `R`
    through `∀ {x y z}, R x y → …` fails otherwise.

### THE REAL BLOCKER — the image tower needs `same`-closure hypotheses

`universalMorphism_slash` now yields `same (uM slash)(combine …)`, not `=`.
Consumers that did `rw [universalMorphism_slash]` break — and not just
syntactically (`rw` won't unfold the `HasDistinguishing.same` projection to see
`Eq`).  Worse, the statements are **genuinely `=`-only**: e.g.
`ImageMinimum.image_minimum_property` ("image ⊆ every distinguishing-closed S")
proves `S (uM slash)` from `S (combine …)`, which needs `uM slash = combine …`.
For a non-`Eq` `same` (the Lens tower) that step is **false unless `S` respects
`same`**.  So the image tower (`Reach.image_closed_under_distinct_combine`,
`ImageMinimum.image_minimum_property`, `OnLensImage*`, `TowerLevel3`) must each
gain a `∀ x y, same x y → (S x ↔ S y)` (or `f`-respects-`same`) hypothesis to
stay true generically — a **semantic generalization, not a mechanical
`= → same` swap**.  This is where the cascade expands and why it needs a
dedicated session (estimate: SemanticAtom + EqPW + OnLens are ~mechanical given
the above; Reach + ImageMinimum + the 3 `OnLensImage*` + TowerLevel3 + verifying
Hyper213Tower each need a same-closure hypothesis threaded through their
statements and every downstream consumer).

### Concrete green-per-commit sequence (next session)

1. (DONE, committed) `Raw.fold_slash_rel`.
2. Materialize `Lens.sameLens` + laws + `lensCombineGeneric_{comm,cong}_same`
   in `EqPW.lean`/`OnLens.lean` (additive, green).
3. Atomic commit: SemanticAtom class change (design C) + `universalMorphism_slash`
   + `universalMorphism_unique` + `raw_initial` (all relativized) **and**
   convert `lensBoolHasDistinguishing`/`lensHasDistinguishing` to `eqPW`/`sameLens`
   in the same commit (so OnLens stays green — `lake build` default target does
   NOT catch OnLens, so verify with `tools/full_build.sh`/explicit `lake build
   E213.Lens.Compose.OnLens`).
4. Per-file commits: thread the `same`-closure hypothesis through `Reach`,
   `ImageMinimum`, `OnLensImage`, `OnLensImageGeneric`, `OnLensImageLevel2`,
   `TowerLevel3`; fix `Hyper213Tower`.  Each green.

**Gotcha**: `lake build` (default target) does NOT build `Compose.OnLens` (G159
gate-hole residue) — a broken OnLens passes `lake build`.  Always verify this
refactor with an explicit `lake build E213.Lens.Compose.OnLens` (+ the image
tower modules) or the comprehensive build.

## The three elaboration walls (empirically hit 2026-06-01, first pass)

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
