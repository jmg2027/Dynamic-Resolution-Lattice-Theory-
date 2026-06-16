# STRICT ∅-AXIOM — the 213 axiom standard

> **Canonical definitions (single source of truth):** see "Terms"
> section below.  When other documents (HANDOFF.md, CLAUDE.md,
> scan_all_axioms.py comments) drift from these definitions, this
> file wins.  Falsifiability anchor: `seed/AXIOM/08_falsifiability.md` §8.2.

## Terms (canonical)

| Term | Definition |
|---|---|
| **PURE** | `#print axioms <thm>` returns "does not depend on any axioms".  Identical to "strict ∅-axiom".  This is the standard target. |
| **DIRTY** | `#print axioms` returns "depends on axioms: [...]" with a non-empty list.  Any of `propext`, `Quot.sound`, `Classical.choice`, `Lean.ofReduceBool` (from `native_decide`), `sorryAx`. |
| **sealed-DIRTY-by-design** | A DIRTY theorem accepted because (a) Lean-core boundary (well-founded recursion, Lean.Elab metaprogramming inheriting Classical.choice via the Lean.Elab.Command monad), or (b) Lens funext-by-design (higher-order Lens equality requires funext on the combine field, refactoring would redefine what "Lens equality" means).  Listed in `tools/scan_all_axioms.py` `SEALED_DIRTY_PREFIXES`. |
| **real DIRTY** | DIRTY ∧ NOT sealed-by-design.  This is the regression budget. |

**The 213 axiom set is ∅** — a theorem meets the standard iff PURE.

**Forbidden absolutely** (per `seed/AXIOM/08_falsifiability.md` §8.2, falsifiability
trigger): `Classical.choice` and `Lean.ofReduceBool` in **213
mathematical content** (theorems about Raw, Lens, observables).
Tactic files (`E213.Meta.Tactic.*`) that inherit Classical.choice
purely via the Lean.Elab.Command monad are *plumbing*, not 213-math
content; sealed under (a) above with explicit justification.

**Always allowed but not target**: `propext` and `Quot.sound` are
part of the Lean 4 core kernel base.  213 aims to avoid them where
possible (PURE target) but does not falsify if a result requires
them via Lean-core well-founded recursion proofs.

---

## Sealed-by-design categories

The seal list in `tools/scan_all_axioms.py` waives modules whose
DIRTY status is *structural* — refactoring would redefine what the
module is, not improve its derivation.  Any DIRTY outside this list
is a real regression.

### (a) Prop-as-distinguishing thesis — `propext`

`HasDistinguishing` is the typeclass for "framework instance: a
type with a/b/combine such that True ≠ False analogue holds and
combine is symmetric."  When the type is `Prop`, the field
`combine_sym : combine P Q = combine Q P` is a propositional
equality between Props — provable in Lean 4 only via the kernel
axiom `propext`.

Sealed modules:

  · `E213.Lens.SemanticAtom`
      `propAsDistinguishing` + `propAsDistinguishing{And, Or, Iff}`
      use `combine = propXor / And / Or / Iff`; `combine_sym` is
      `(P * Q) = (Q * P)` at type `Prop`.  Carries `iff_comm_eq`
      and `propXor_comm` for the symmetry lemmas.
      `canonical{Truth, And, Or, Iff}Map_*` are derived via
      `universalMorphism_*` and inherit the propext use.

  · `E213.Lens.Properties.Morphism.BoolProp`
      `boolToProp : Bool → Prop` is `b ↦ (b = true)`.  Theorems
      `boolToProp_true / false / and / or / xor / iff` and
      `universalMorphism_commute*` equate Props (e.g. `boolToProp
      (and x y) = (boolToProp x ∧ boolToProp y)`) — propext.

The thesis "Prop is an atom of meaning" *is* what `propext`
expresses.  Removing the seal would require removing Prop as a
HasDistinguishing instance, which removes the thesis.

### (b) Lens kernel as function-`=` of views — `Quot.sound` (= `funext`) + `propext`

`Lens.combine : α → α → α` for the universal / indexed / Cauchy
Lens family is function-valued — `α = Raw → β` or `α = (i : ι) →
...`.  Then `Lens.combine_sym : combine x y = combine y x` becomes
a function equality, which in the Lean 4 kernel is `funext`,
derived from `Quot.sound`.  `Lens.equiv` on Raw is the same
pattern at one level up: it states `L.view r = L.view r'` at type
`Prop` (Iff↔Eq via propext) and `Lens.refines` says
`L.equiv r r' → M.view r = M.view r'` (function equality on
view).  Both patterns inherit propext + Quot.sound from the kernel.

This category is a **statement-shape** cost, not a redefinition cost,
and the universalLens refinement surface is **retired from it**.  The
213-native meaning of "the same under `L`" is the
distinguishing-equivalence — pointwise `↔` — carried by the
codomain-polymorphic Reading-equivalence API in `Lens/ReadingEquiv.lean`:

  · `ReadingEq α` — per-codomain reading-sameness (`=` at the default
    instance, pointwise `↔` at `Raw → Prop`), an equivalence relation,
    laws PURE;
  · `Lens.equivG` / `Lens.refinesG` — codomain-polymorphic equivalence /
    refinement, reducing **definitionally** to `equiv` (default) and
    `equivR` (`Raw → Prop`);
  · `Lens.equivG_slash_congruence` — the slash-congruence, generic over
    the codomain.

The load-bearing hub `universalLens_kernel_eq_E_R` (`equivR r r' ↔ E r r'`)
plus the closure companions `universalLens_recovers_R` /
`universalLens_idempotent_R` (built on `universalLens_equivR_slash_congruence`
/ `combine_cong_pw` / `fold_pw`) are PURE, and **every consumer is stated on
this API** — the refinement lattice (`Join`, `IndexedJoin`, `FamilyMeet`,
`FamilyJoin`), the Cauchy limit Lens, the kernel↔slash-congruence bijection
(`Corresp`), the choice-as-Lens-spec, and the canonical-form / idempotence
theorems (`CanonicalForm`) are all ∅-axiom.  The `=`-of-view-functions forms
are gone; the only `=`-cost is the single isolated bridge
`Lens.equivR_to_equiv` (the `↔ ⟹ =` direction, kept by design).  Only
`propAsDistinguishing` (category a) remains irreducible by thesis.  See
`theory/lens/dirty_recovery_patterns.md` Pattern P5 and
`theory/lens/unified_equivalence.md`.

Remaining sealed module in this category:

  · `E213.Lens.Instances.Leaves.DepthJoin`
      Three-tier classification of `Raw` via `JoinEquiv
      Lens.leaves Lens.depth` (a `Nat`-valued lens family).  The 10
      tier invariants (`small_invariant`, `tier_invariant`,
      `class_of_a_iff_small`, `three_classes_distinct`, `tierLens_*`,
      `depth_refines_tierLens`, `leaves_refines_tierLens`,
      `joinEquiv_subset_tierLens`, `leaves_depth_join_not_universal`)
      carry `propext` / `Quot.sound` from the `omega` / `simp`-closed
      arithmetic helpers, **not** from the refinement API — this is the
      `omega`/`simp`→explicit purification playbook (cf. `Mobius213.Px`),
      a separate backlog from the Reading-equivalence rebuild.

### Net effect

Scope note: until the build gate was made comprehensive, only the
umbrella-reachable subset was ever scanned, and that subset was fully PURE
(non-sealed).  The comprehensive gate now scans **all 1532 modules**, which
exposes the purity status of the previously-ungated clusters.  Current
`tools/scan_all_axioms.py`:

  · The 213-mathematical core is ∅-axiom.  The only non-sealed `propext`/`Quot.sound`
    that remains is the **`Prop`-atom thesis surface**
    (`propAsDistinguishing*` / `canonical*Map` / `BoolProp.universalMorphism_commute_*`,
    category (a) — `propext` IS "`Prop` is an atom of meaning").  The **CayleyDickson
    category-D backlog is closed** (2026-06-01): `Trig.conj_mul_anti` via the
    `NonAssocStarRing213 Sedenion` bridge (`SedenionAlgebra213`), and
    `SedenionHeavy.flexible` via the `CDDoubleFlexible` cross-pair +
    `FlexAlt213 Cayley` — both verified PURE (`#print axioms`).  The Lens ring is
    **0 real DIRTY** (`scan_all_axioms.py --filter Lens`): its equivalence surface is
    stated on reading-equivalence (`ReadingEq.same` / `equivR` / `sameLens`), not `=` of
    views.  Run `tools/scan_all_axioms.py` for the live count.
  · **No `Classical.choice` and no `Lean.ofReduceBool` (`native_decide`) in any
    213-mathematical content** — the falsifiability-forbidden axioms are absent.
    The only `Classical.choice` carriers are three `CommandElab` elaborators
    (`Lib.Math.Tactic.QuadExtension`, `Meta.Tactic.{DeriveConjugationCodomain,
    VerifyConjugation}`), inherited via the `Lean.Elab.Command` monad — sealed
    plumbing per category (a), not math content.
  · The remaining real DIRTY are **`propext` / `Quot.sound` only** (the
    "allowed-but-not-target" core-kernel axioms) — the `Prop`-atom thesis surface
    (category B).  The CayleyDickson category-D items (`Trig.conj_mul_anti`,
    `SedenionHeavy.flexible`) are now both closed.  The category-D backlog uses the `Mobius213.Px` playbook
    (`omega` → `rfl`/`Nat.two_mul`/`Nat.add_right_comm`; `Nat.mul_assoc`/`Nat.add_mul`
    → `NatRing.nat_*`; `simp` → explicit `rw`; `Nat.mul_lt_mul_left`/`mul_lt_mul_right`
    (the `Iff`) pull `Classical.choice` → constructive `c*m+1 ≤ c*m+c ≤ c*n` helper,
    cf. `KerSizeUniversal.mul_lt_mul_left_pure`) + the Int/`same` playbooks
    (`Meta/Int213`, `ReadingEq`/`sameLens`).
  · **Gate vindication**: closing the build-gate hole exposed a genuine
    falsifiability violation that had been invisible — `KerSizeUniversal`'s
    `Classical.choice` (via `Nat.mul_lt_mul_left`) in an orphaned cluster, now
    fixed.  A gate that only follows umbrella imports cannot guarantee the
    ∅-axiom standard; the comprehensive build is required.
  · **Sealed-by-design** per categories (a) + (b): the Prop-as-distinguishing
    family + the three CommandElab plumbing modules.  **213-native re-reading
    (not just ∅-axiom)**: only the **3 CommandElab** + `propAsDistinguishing` are
    *irreducible*.  The 3 CommandElab inherit `Classical.choice` via the
    `Lean.Elab.Command` monad (no `↔`-form alternative); `propAsDistinguishing` is
    `propext` expressing the thesis "Prop is an atom of meaning".
  · **The universalLens refinement surface is PURE** (the headline (a)
    pointwise-API rebuild, done).  The 213-native notion of "the same under `L`"
    is the pointwise **Reading-equivalence** (`equivR`, `∀ s, view x s ↔ view y
    s`); `Lens/ReadingEquiv.lean` lifts it to the codomain-polymorphic
    `ReadingEq` / `equivG` / `refinesG` (reducing definitionally to `equiv` at
    the default instance and `equivR` at `Raw → Prop`).  The kernel hub
    (`universalLens_kernel_eq_E_R`), the slash-congruence
    (`universalLens_equivR_slash_congruence`), and the closure companions
    (`universalLens_recovers_R` / `universalLens_idempotent_R`) are all PURE, and
    **every consumer is stated on this API**: the refinement lattice (`Join`,
    `IndexedJoin`, `FamilyMeet`, `FamilyJoin`), the Cauchy `limitLens`, the
    kernel↔slash-congruence bijection (`Corresp`), `Choice.choice_as_lens_spec`,
    and `CanonicalForm.{refinesEquiv, lens_canonical_universal,
    lens_canonical_idempotent}`.  The `=`-of-view-function forms are gone; the
    lone `=`-cost is the isolated bridge `equivR_to_equiv` (the `↔ ⟹ =`
    direction).  Only `propAsDistinguishing` stays irreducible.  Anchors:
    `theory/lens/dirty_recovery_patterns.md` Pattern P5,
    `theory/lens/unified_equivalence.md`.

---

## PURE-bounded on Lean 4 core (2026-05-22)

**Verification**: the dependency-purity audit (transitive Lean-core
axiom scan) + the N5 + N6 centralisations below.

Beyond avoiding `Classical.*`/`native_decide`/`sorryAx`, the DRLT
corpus has been audited for *Lean-core* axiom dependencies (those
inherited transitively via Lean's standard-library lemmas that
themselves bring `propext`/`Quot.sound`).

Net status: **DRLT is PURE-bounded on Lean 4 core** — no non-test
DIRTY citation chain reaches outside the kernel.  Two centralisations
made this possible during the cycle:

  · **N5**: `Nat.max_comm` → `NatHelper.max_comm` (5 sites).
  · **N6**: `Int.mul_sub` / `Int.sub_mul` → `Meta.Int213.{mul_sub, sub_mul}`
    (12 sites).
  · **N8/N9** (this branch): `NatHelper.mul_left_comm` + `Nat.add_right_comm`
    adoption (25 sites, Pattern #10).

Future Lean-core upgrades that change axiom dependencies of
standard-library lemmas are caught by re-running the
dependency-purity audit (`tools/scan_all_axioms.py`).

---

## Sealed-DIRTY inventory

Run `tools/scan_all_axioms.py` for the live count; the standing
status is **0 real DIRTY** — every DIRTY theorem is one of the
sealed-by-design entries below, waived under the categories above:

  · 23  E213.Lens.SemanticAtom                  — category (a) propext
  · 10  E213.Lens.Properties.Morphism.BoolProp  — category (a) propext
  · 10  E213.Lens.Instances.Leaves.DepthJoin    — category (c) Classical.choice (5) + category (b) Quot.sound (5)
  ·  5  E213.Lens.Universal.QuotLens            — category (b) Quot.sound
  ·  4  E213.Lens.Lattice.IndexedJoin           — category (b) Quot.sound
  ·  3  E213.Lens.Instances.Cauchy              — category (b) Quot.sound
  ·  1  E213.Lens.Instances.FunctionSpace       — category (b) Quot.sound

DRLT mathematical content (`E213.Lib.Math.*`, `E213.Lib.Physics.*`,
`E213.Theory.*`, all capstones) is **fully PURE**.  Zero unsealed
DIRTY: every Lean-core axiom use is structurally justified per
§"Sealed-by-design categories".

---

## Audit command

```
cat > /tmp/axcheck.lean << END
import <module>
#print axioms <theorem>
END
cd lean && lake env lean /tmp/axcheck.lean
```

If output is "does not depend on any axioms", STRICT 0-AXIOM.

## Future cleanup

Many theorems at ≤ {propext, Quot.sound} could be upgraded by:
  1. Replacing omega with kernel-level lemmas
  2. Replacing simp[...] (uses propext) with rw
  3. Avoiding funext (uses Quot.sound) when not needed

Estimated upgrades: ~50-100 theorems possible.

---

## Cross-reference

  - `CAPSTONE_INDEX.md` — all capstones (mixed axiom levels)
  - `LESSONS_LEARNED.md` — finitist guardrails
  - `HANDOFF.md` — current state


---

## Session history

Per-session running-total entries that previously lived in this
file have been removed.  The PURE/DIRTY status of any theorem is
the live `#print axioms` output:

```bash
tools/scan_axioms.py <module>            # one module
tools/scan_all_axioms.py                 # full tree scan
```

Migration patterns that recur across sessions are catalogued in
`LESSONS_LEARNED.md` (omega → decide / kernel rewrite, simp →
rw, funext avoidance via Setoid/Bundled-subtype) and detailed in
`theory/essays/methodology/pure_funext_avoidance.md`.  Git log preserves the
per-session record of conversions.
