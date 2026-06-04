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

### The cascade — `same`-relativize + thread a `same`-closure hypothesis

`universalMorphism_slash` now yields `same (uM slash)(combine …)`, not `=`, so
consumers that did `rw [universalMorphism_slash]` break (`rw` won't even unfold
the `HasDistinguishing.same` projection to see `Eq`).  Two shapes of fix:

  * **Pure-existence / pure-homomorphism statements** (e.g.
    `Reach.image_closed_under_distinct_combine : ∃ r, uM r = combine …`) — just
    relativize the `=` in the statement to `same`; witness is
    `universalMorphism_slash` directly.  Mechanical.
  * **"image ⊆ every distinguishing-closed `S`"** (`ImageMinimum.
    image_minimum_property`, and the `OnLensImage*` reach/image theorems) — the
    `slash` step proves `S (uM slash)` from `S (combine …)`, which under a
    non-`Eq` `same` needs **`S` to respect `same`**.  This is NOT a dead-end:
    add a hypothesis `hSsame : ∀ x y, d.same x y → S x → S y` to the statement.
    Eq-codomain consumers discharge it trivially with `fun _ _ h hx => h ▸ hx`
    (since `same = Eq` there); Lens-tower consumers pass the `eqPW`/`sameLens`
    closure.  So the cascade is **mechanical hypothesis-threading**, not a
    semantic redesign — each image-tower theorem gains one `hSsame`-style arg,
    and every downstream call passes the trivial (Eq) or eqPW proof.

Estimate: SemanticAtom + EqPW + OnLens (instances) are mechanical given the
materialized `fold_slash_rel` + `sameLens` foundation; Reach + ImageMinimum +
`OnLensImage{,Generic,Level2}` + `TowerLevel3` + `Hyper213Tower` each take a
`same`-relativization (+ a threaded `hSsame` for the closure ones).  Sizeable
but mechanical — a focused session.

## UPDATE 2026-06-01 (third pass) — the **defeq blocker** (must solve FIRST)

A third pass executed the atomic change (SemanticAtom design C +
`universalMorphism_{slash,unique}` + `raw_initial` relativized + OnLens instances
to `eqPW`/`sameLens`) — SemanticAtom + OnLens compiled green.  But the
Eq-codomain consumers of `universalMorphism_slash` broke on a **defeq-reduction
wall**, and it was reverted to green (foundations kept).

**The wall**: with `same` a field defaulting to `Eq`, an `Eq`-codomain instance
that omits `same` does NOT have `inst.same` reduce to `Eq` at *reducible*
transparency.  Verified empirically:

```
example : @HasDistinguishing.same Bool boolXorHasDistinguishing = Eq := rfl   -- FAILS
example (x y : Bool) : @HasDistinguishing.same Bool boolXorHasDistinguishing x y
        = (x = y) := rfl                                                       -- FAILS
```

So `universalMorphism_slash` (now `: d.same (uM slash)(combine …)`) cannot be
used by `rw` (needs syntactic `Eq`) nor coerced via `have e : (…) = (…) := …`
(the ascription defeq doesn't unfold the default-field through the `def`
instance projection) at the Eq-codomain consumers — `BoolProp`
(`boolXorHasDistinguishing`, line ~125), `OnLensImage.composite_slash`,
`Pair`/`CanonicalTruthChar`/`Reach` (those wanting a literal `=`).  NB:
`ImageMinimum.image_minimum_property` was fixed *without* `=` — it transports
`S` along `same` via the threaded `hSsame` (that pattern works); the breakage is
only where the consumer needs a genuine `=` for further `rw`.

**Resolve FIRST (before the cascade), candidate fixes:**
  1. Give the Eq-codomain consumers an `=`-form: a generic
     `universalMorphism_slash_eq (α) [d] (hEq : d.same = Eq) …` returning Lean
     `=` (caller supplies `hEq := rfl`-or-proof per instance) — but per the
     failing `example`, `d.same = Eq` is NOT `rfl` for default instances, so
     `hEq` needs the instances to **spell out `same := Eq` explicitly** (then
     `inst.same` is syntactically `Eq` and `hEq := rfl`).  i.e. mark the ~5-7
     Eq-instances consumed-as-`=` with explicit `same := Eq` (+ they then reduce).
  2. OR mark those instances `@[reducible]` so `.same` unfolds.
  3. OR (cleanest) restate the Eq-codomain consumers in `same`/`eqPW` form too
     (e.g. `composite_slash` → its existing `_eqPW` path; `BoolProp` boolToProp
     commute via `same`-transport) and **delete** the `=`-of-`Lens`/recursive
     forms that have `eqPW` twins (no external consumers — verified for
     `OnLensImage.{lensUniversalMorphism_factors,_image}`).

Recommended: option 3 for the Lens-`=` forms (retire them, eqPW twins exist) +
option 1 (explicit `same := Eq`) for the genuinely-`=`-needing `Bool`/`Prop`
consumers.  Resolve this defeq wall on a scratch FIRST, then run the cascade.

## UPDATE 2026-06-01 (fourth pass) — the defeq "wall" is NOT fundamental

Isolated scratch research (a faithful `Raw.fold` model: class `HD` with
`same`/`same_refl`/`combine_sym` fields, `um := Raw.fold …`, `um_slash` via
`fold_slash_rel`, an `Eq`-codomain `def` instance omitting `same`) **compiles
end-to-end**, including the Eq-consumer extraction:

```
example (x y : Raw) (h : x ≠ y) :
    @um Bool boolHD (Raw.slash x y h) = xor (@um Bool boolHD x) (@um Bool boolHD y) := by
  have e : @um Bool boolHD (Raw.slash x y h)
         = boolHD.combine (@um Bool boolHD x) (@um Bool boolHD y) :=
    @um_slash Bool boolHD x y h     -- `same`→`=` coercion at DEFAULT transparency: OK
  exact e
```

Findings, precisely:
  * `@HD.same Bool boolHD = Eq` is provable `by rfl` (default transparency) and
    `by with_unfolding_all rfl`, **but not** by a bare-term `rfl` (reducible).
  * The Eq-consumer can extract `=` from the `same`-form via
    `have e : (lhs = rhs) := um_slash …` (the ascription's `isDefEq` runs at
    default transparency and unfolds the `def` instance + default field) — then
    `rw [e]`.  So `composite_slash`/`BoolProp` ARE fixable with this pattern.
  * Explicit `same := Eq` in an instance makes `.same` reduce at *reducible*
    transparency too (so even bare `rw [um_slash]` would work) — a fallback if
    the `have`-extraction ever misbehaves.

So the 3rd-pass real failure (`composite_slash` `have e` rejected) was a **local
elaboration detail** in the full setting (the only structural diff from the
working model is the extra `combine_cong` autoParam field — diagnose whether its
default elaboration for omitting instances interferes), NOT a fundamental wall.
**The rebuild is mechanically completable.**

### Definitive recipe (validated piecewise; execute fresh, green-per-commit)

1. (DONE) `fold_slash_rel`; `Lens.sameLens` + laws + `lensCombineGeneric_{comm,
   cong}_same`.
2. Scratch-confirm the FULL `HasDistinguishing` (with `combine_cong`) + a `def`
   Eq-instance + the `have`-extraction consumer compiles (≈ 20 lines); if the
   `combine_cong` autoParam default is the culprit, give it a manual proof or
   drop it to a separate lemma.  THIS de-risks the atomic commit.
3. Atomic commit (verify `lake build E213.Lens.Compose.OnLens` explicitly):
   SemanticAtom design-C class + `universalMorphism_{slash,unique}` + `raw_initial`
   (relativized) + OnLens instances (`eqPW`/`sameLens`).  Fix the Eq-consumers
   (`BoolProp`, `composite_slash`) with the `have e : (=) := … ; rw/ exact e`
   extraction.
4. Per-file: thread `hSsame` through `ImageMinimum`; relativize `Reach`; retire
   the Lens-`=` forms with eqPW twins (`OnLensImage.{factors,image}`,
   `OnLensImageGeneric.factors_generic`), keeping the `_eqPW` versions; handle
   `OnLensImageLevel2` / `TowerLevel3` (recursive — need `sameLens` at the base)
   and `Hyper213Tower`.

## UPDATE 2026-06-01 (fifth pass) — DECISIVE: design C cascades to ALL
## composite instances; design D (confined PW path) is the correct architecture

Executing design C end-to-end (per the recipe) revealed its true scope, which is
**not confined to the Lens tower**:

  * `Pair.pairHasDistinguishing.combine_sym` (and every instance built FROM other
    instances — `Sum`, `Subtype`, `SubtypeClosed`, …) proves its own `combine_sym`
    by `rw [d_α.combine_sym, d_β.combine_sym]`.  Once `combine_sym` is `same`-based,
    `d_α.combine_sym` is `same_α (…)(…)` with `same_α` **abstract** (α is a
    variable), so it can be neither `rw`'d as `=` nor reduced — the composite
    instance's `same` must itself become a product-sameness.  **Cascade reaches
    the whole composite-instance surface.**
  * Generic `=`-consumers (`Pair.universalMorphism_pair_commute`, the `BoolProp`
    commute family) state `=` and cannot extract it from `universalMorphism_slash`
    when the instance's `same` is abstract (generic α) — they too must relativize
    to `same`.
  * The `have e : (lhs = rhs) := universalMorphism_slash …` extraction works only
    for a **concrete `def` instance whose `same` reduces** (e.g. `boolHD` in the
    scratch); it does NOT work for an abstract `[d : HasDistinguishing α]`
    (Pair/generic) nor reliably through an ambient resolved instance.

**Conclusion — architecture decision:** design C (unify `combine_sym` via a
`same` field on the *single* `HasDistinguishing`) is mechanically completable but
its blast radius is the **entire instance + generic-consumer surface (~24 files)**
— wrong cost.  The correct, *confined* architecture is **design D**: leave
`HasDistinguishing` (Eq-world) completely UNCHANGED, and give the **Lens tower its
own pointwise path**.  Two equivalent shapes for D:

  (D1) a separate `HasDistinguishingPW` class (`combine_sym : sameLens …`) used
       only by `lensBoolHasDistinguishingPW` / `lensHasDistinguishingPW` +
       `universalMorphismPW` + `universalMorphismPW_slash` (sameLens form), and
       rebuild the image tower (`OnLensImage{,Generic,Level2}`, `TowerLevel3`,
       `Hyper213Tower`) on it; OR
  (D2) no new class — delete the DIRTY `lens*HasDistinguishing` instances and the
       `=`-form tower theorems (they have `_eqPW` twins), and rebuild the
       **recursive** tower (`factors_level2/3`, `TowerLevel3`) directly on
       `lensCombineGeneric` + `view_unique_eqPW` + the materialized `sameLens`
       (the recursive base sameness), with **no** `HasDistinguishing (Lens β)`
       instance.

D2 is the smaller/cleaner one (no parallel class; reuses `sameLens` + the eqPW
twins already present).  The crux it must solve: a `factors_generic_sameLens`
(or eqPW) that works at a `Lens` base **without** requiring
`[HasDistinguishing (Lens α)]` — threading the base's `combine_sym` (`=`-form,
which the Eq-base provides) through `sameLens` at each tower level.  Foundations
for D2 (`fold_slash_rel`, `Lens.sameLens` + laws, `lensCombineGeneric_{comm,
cong}_same`, all the `_eqPW` twins) are **materialized + committed**.

Execute D2 in a fresh focused session: it touches only the ~6 Lens-tower files,
leaves the Eq-world untouched (no defeq wall, no composite-instance cascade), and
retires the 10 Lens-tower DIRTY.

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
