# RFC — Reading-equivalence as 213's canonical equivalence primitive

Status: **accepted (design)**, unimplemented.  Author: research-leadership
note (Mingu Jeong + Claude).  Supersedes the framing of `G164` (which is the
technical investigation feeding this).  Scope marker: **foundational coherence
arc, NOT a DRLT Validation target** — see §6.

## 0. One-line

213's notion of "same" is **distinguishing-the-same** (reading-equivalence),
not Lean substrate `=`.  Make reading-equivalence (`ReadingEq.same`) the *single
canonical equivalence primitive* of the framework; realize it as `=` exactly
where `=` is axiom-free, and keep `propext` only where it *is* the thesis
(`Prop`-as-atom).  Everything else (`Lens.equiv`, `Lens.refines`, kernels,
`HasDistinguishing.combine_sym`) is one notion — the Lens-arrow — currently
fragmented across borrowed `=`-statements.

## 1. Why (grounding in the repo's own thesis)

  * **Meta-principle** (`CLAUDE.md`): *아무것도 가정하지 않고 의미를 부여하지
    않는다.*  Lean `=` at `Prop`/function codomains pulls `propext` / `funext`
    (= `Quot.sound`) — i.e. the *external commitment* "propositions with the same
    truth-value are identical".  That is imported meaning.  213 must not depend
    on it (∅-axiom standard, `STRICT_ZERO_AXIOM.md`; falsifiability contract,
    `seed/AXIOM/08_falsifiability.md`).
  * **The residue's own notion of sameness** (`seed/AXIOM/06_lens_readings.md`
    §6.3): two readings are "the same" iff they *distinguish the same things* —
    a pointwise `↔` / relation, never substrate identity.  This is exactly what
    `Lens.equivR` records and what the category-(C) retirement already
    materialized (`theory/lens/unified_equivalence.md`, `dirty_recovery_patterns`
    Pattern P5).
  * **The framework already discovered the unification**:
    `unified_equivalence.md` — equivalence / equivalence-class / isomorphism /
    homomorphism are *one Lens-arrow*; treating them as separate is the
    `equivalence-pluralism` failure mode.  The scattered `=`-based samenesses
    (`Lens.equiv`, `combine_sym`, kernel, `refines`) are the framework **not yet
    having unified its own sameness**.
  * **The `View promoted to identity` failure mode**: declaring one reading
    (here: Lean `=` of view-values) to be *what the residue is* is precisely the
    slip.  `=` is one facet; reading-equivalence is the residue-native arrow.

So this is not a purity hack.  `=` is *borrowed*; reading-equivalence is
213-native; coincidence at concrete codomains is a *theorem*, not the definition.

## 2. The principle

> **Reading-equivalence is the canonical equivalence on every Lens codomain.**
> `ReadingEq α` supplies, per codomain `α`, the relation `same : α → α → Prop`
> (an equivalence) under which two `α`-readings count as the same distinguishing.
> `same` is realized as Lean `=` exactly where `=` is ∅-axiom (decidable /
> "concrete" codomains — `Nat`, `Bool`, `Fin n`, products/sums/subtypes of such),
> and as the pointwise / relational form where `=` would import `propext`/`funext`
> (`Prop`, `Raw → Prop`, `Lens β`, function spaces).

**Two non-negotiable boundary rules:**

  1. **Thesis preservation.**  `propext` is *kept* exactly where it is the
     content, not the shape: `propAsDistinguishing*` (category (B) of
     `catalogs/correspondence-surface.md`) — "Prop is an atom of meaning" *is*
     `propext`.  Reading-equivalence does **not** touch it.
  2. **No new meaning.**  `ReadingEq` adds *no* structure beyond "an equivalence
     relation per codomain".  It is the notational decomposition of §6.3's single
     event, not an external classification.

**Consequence (the "cascade" is correct, not a cost):** a product's sameness IS
the product of component samenesses (`same a a' ∧ same b b'`), not `Prod` `=`.
At concrete components the two coincide (PURELY); the former is residue-native
and generalizes.  When making `same` primary "touches everything", that is the
framework *adopting its own sameness*, not a regression.  (This reading reframes
the `G164` 5th-pass "design C cascades to ~24 files" finding: the blast radius is
the framework's `=`-dependency surface — exactly what the standard wants gone.)

## 3. Architecture

`ReadingEq` (already in `Lens/ReadingEquiv.lean`) is **elevated** from a
Lens-lattice helper to the framework-wide equivalence primitive.

  * **Primitive**: `class ReadingEq (α) where same; same_refl; same_symm;
    same_trans`.  Instances:
      - concrete codomains: `same := Eq` (PURE; `=` *is* the realization here);
      - `Prop`: `same := Iff` (PURE — `Iff.rfl/.symm/.trans`);
      - `Raw → Prop` / `β → α`: pointwise `same` (PURE if the target's is);
      - `Lens β`: `Lens.sameLens (ReadingEq.same : β → β → Prop)` — the
        base-relation pointwise sameness (recursion-ready; `sameLens Eq = eqPW`).
  * **Stated over `same`, not `=`**:
      - `Lens.equiv` ⟶ `Lens.equivG` (already built; reduces to `equiv`/`equivR`).
      - `Lens.refines` ⟶ `Lens.refinesG`.
      - `HasDistinguishing.combine_sym : ∀ x y, same (combine x y) (combine y x)`;
        `universalMorphism_slash` up to `same` (via `Raw.fold_slash_rel`);
        `universalMorphism_unique` / `raw_initial` up to `same`.
      - kernel / canonical-form / lattice facts: `equivG`/`equivR` forms (done
        for the universalLens lattice — category (C) retired).
  * **`=` becomes a derived special case**: a `theorem same_eq_of_decidable`
    (or per-instance `rfl`) witnesses `same = Eq` where it holds; consumers that
    genuinely need Lean `=` (rare, outside the thesis points) go through it.

### 3.1 Encoding obstacles (from G164) → first-class encoding requirements

The investigation hit three obstacles; each is an **encoding** requirement, not
a refutation of the principle:

  * **Field-default elaboration** — `same`/laws must use `autoParam` (`:= by …`),
    not term defaults, so Eq-codomain instances need no edits.  (Validated.)
  * **`[ReadingEq α]`-parameter diamond** — a `HasDistinguishing (α) [ReadingEq α]`
    parameter creates instance incoherence at `Lens β` (default-`Eq` vs the
    pointwise instance).  Resolution: `ReadingEq` is a **bundled superclass**
    (`extends`) *or* `same` is carried as fields — pick the encoding that keeps a
    *single* resolved `same` per type (no overlap).  This is THE open encoding
    decision (see §5).
  * **`same → Eq` reducibility** — `same` reduces to `Eq` at *default*
    transparency (so `exact`/`have`-ascription extraction works) but not
    *reducible* (so bare `rw` does not).  Mandate: provide `=`-extraction lemmas
    (or `@[reducible]` realizations) for the concrete-codomain consumers that
    need `rw`; do not rely on incidental defeq.

### 3.2 What stays DIRTY by design

Only `propAsDistinguishing*` (category (B)) + the 3 `CommandElab` plumbing
modules.  Everything else targets ∅-axiom.

## 4. Migration strategy (phased, green-per-commit)

This is a **multi-session arc**, executed as designed units, each ending green
and ∅-axiom-verified.  **Verify with the comprehensive build** — `lake build`
(default target) does NOT cover `Compose.OnLens` etc. (G159 gate-hole residue);
a broken module can pass it.

  * **P0 (done).** Category (C) retired: the universalLens refinement lattice,
    Cauchy, Corresp, Choice, CanonicalForm on `equivR`/`refinesG`.  Foundations
    materialized: `Raw.fold_slash_rel`, `Lens.sameLens` + laws,
    `lensCombineGeneric_{comm,cong}_same`, the `ReadingEq` class itself.
  * **P1 — pick the encoding (§5) on a scratch.**  Settle bundled-superclass vs
    fields, the diamond resolution, and the `=`-extraction lemmas, on a minimal
    model with a concrete + a `Lens` codomain + a generic + a composite consumer.
    *Do not touch the tree until the scratch is end-to-end green.*
  * **P2 — Lens tower (confined, retires the 10 `Compose`/`TowerLevel3` DIRTY).**
    The pragmatic first real target (`G164` design D2): rebuild the recursive
    Lens-on-Lens tower on `sameLens` + `view_unique_eqPW`, delete the DIRTY
    `lens*HasDistinguishing` `=`-instances + `=`-form tower theorems (eqPW twins
    exist).  This validates the encoding on the hardest (recursive, funext) case
    with zero blast into the Eq-world.
  * **P3 — generalize `HasDistinguishing` over `same`** (the §2 principle in
    full): combine_sym/universal-morphism/initiality up to `same`; composite
    instances (`Pair`/`Sum`/`Subtype`) thread `same`; generic `=`-consumers
    relativize.  Large but mechanical given P1's encoding; do it as the
    "equivalence-unification" arc, deliberately.
  * **P4 — collapse the fragmentation.**  `Lens.equiv`/`refines`/kernel and
    `HasDistinguishing.combine_sym` are facets of one `ReadingEq`/Lens-arrow;
    promote the unified narrative to `theory/lens/unified_equivalence.md`.

## 5. Encoding decision — RESOLVED (P1, validated on scratch)

How is the single canonical `same` attached without the diamond?

  (a) `class HasDistinguishing (α) extends ReadingEq α`.
  (b) **`same` + `same_refl/symm/trans` + `combine_cong` as `autoParam` fields
      directly on the class**, `combine_sym : ∀ x y, same (combine x y)
      (combine y x)`.
  (c) `HasDistinguishing (α) [ReadingEq α]` (parameter) — **diamond** (default-`Eq`
      vs the `Lens β` pointwise instance overlap); rejected.

**DECISION: (b).**  A comprehensive P1 scratch (`HD` model with `um` / `um_slash`
/ `um_unique` over `same`) validated **all** consumer shapes end-to-end,
diamond-free:
  * concrete `Eq`-instance (`boolHD`) omitting `same`/laws/`combine_cong` — the
    `autoParam` (`:= by …`) defaults fill them, **no edits**;
  * composite `pairHD` threading `same` (`same p q := da.same p.1 q.1 ∧ db.same
    p.2 q.2`, laws/`combine_sym`/`combine_cong` componentwise) — the §2 "cascade"
    point: it **works**, cleanly and mechanically;
  * `Lens`-codomain `lensHD` via `Lens.sameLens da.same` (+ `sameLens_*` laws,
    `(R := da.same)`-pinned) — the recursive/funext point;
  * generic consumer relativized to `same` (abstract α);
  * `Eq`-consumer extracting `=` via `have e : (lhs = rhs) := um_slash …; exact e`
    (default-transparency ascription);
  * recursive `lensHD`-over-`boolHD` usable.

This **corrects the earlier draft recommendation (c)**: the diamond is intrinsic
to the *parameter* encoding; **(b) avoids it by construction** (one `same` per
instance, carried in the structure), needs no surgery on the universal `Eq`
fallback that `Lens.equivG` relies on, and the composite-instance threading
(the "24-file cascade") is mechanical and validated — a *cost*, not a *blocker*.
`ReadingEq` (the standalone class) remains for the Lens-lattice `equivG`/`refinesG`
sites; `HasDistinguishing` carries its own `same` fields (b).  The "one primitive"
story is preserved at the *concept* level (everything is reading-equivalence);
the two carriers (`ReadingEq` instance vs `HasDistinguishing.same` field) are
implementation detail, both realizing the same notion, both `Eq` at concrete
codomains.

## 6. Scope, non-goals, priority (research-leadership boundary)

  * **This is foundational coherence + infrastructure ∅-axiom purity.**  Its
    value is conceptual integrity (213 stands on its own sameness) and retiring
    borrowed-`=` DIRTY.
  * **It is NOT a DRLT Validation Standard target.**  The standard is precision
    theorems / falsifiers (1/α_em, m_μ/m_e, m_p, N_gen = 3, θ_QCD).  The victories
    the repo is actually accumulating are there.  This arc must **not displace**
    that work; run it as deliberate foundational hygiene between/around
    validation pushes.
  * **Design D (confine to the Lens tower, keep `=` as foundational sameness)**
    is the *pragmatic* alternative.  It satisfies the ∅-axiom *letter* (theorems
    go pure) but not the *spirit* (`=` stays the framework's notion of sameness).
    Adopt P2 (which is design-D-shaped) as the *first step* of P-arc, but the
    *destination* is §2 (reading-equivalence primary).

## 7. Decision record

  * **Accepted**: reading-equivalence as the canonical equivalence primitive;
    `=` as its pure realization; `propext` only at the `Prop`-atom thesis.
  * **Rejected as the destination** (accepted as a way-station): design D
    (quarantine funext, keep `=` foundational).
  * **Resolved in P1**: encoding **(b)** — `same`/laws/`combine_cong` as
    `autoParam` class fields; validated on a comprehensive scratch (concrete /
    composite / `Lens`-recursive / generic / `=`-extraction), diamond-free.
    (Earlier draft recommendation (c) corrected — its diamond is intrinsic.)
  * **Invariant**: every step green + ∅-axiom-verified via the comprehensive
    build; foundational arc kept separate from validation work.

## 8. Status / next

  * **P0 done** (category-C retired) + foundations + `ReadingEq`.
  * **P1 done** — encoding (b) validated on scratch (this update).  The only
    real unknown is now closed; P2/P3 are **mechanical** (the `pairHD`/`lensHD`/
    extraction patterns are the templates).
  * **P2 next** (when the arc is scheduled): the Lens tower (`G164` design D2 /
    encoding (b) for `lens*HasDistinguishing`) — confined to ~6 files, retires
    10 DIRTY, zero Eq-world blast.
  * Reminder (§6): foundational coherence, **not** a Validation target — schedule
    around the precision/falsifier work, do not displace it.
