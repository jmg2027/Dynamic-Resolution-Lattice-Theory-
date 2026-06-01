# G162 — The Prop-codomain seals, resolved against the axiom text

**Tier-1.**  Research capstone of the "is `fold`/`slash` the problem?" thread
(G161).  Question: the ~54 propext/`Quot.sound` "sealed-by-design" Lens/Prop
theorems — are they a defect of `Raw.slash` (term-commutative via canonical
sorting), of `Raw.fold`, or of something else; and what is the 213-native-correct
form?  Resolved here with axiom citations + Lean `#print axioms` evidence,
including a log of two earlier over-strong claims I had to correct.

## What is *not* the problem (axiom-grounded)

**Canonical-sorted `slash` is correct, not a defect.**  `seed/AXIOM/03_form.md`
§3.4: "`a/b` and `b/a` refer to the same distinguishing event.  Treating them as
distinct would silently import an absolute order, for which clause 1 supplies no
basis."  So term-level commutativity (`slash x y = slash y x` as `Raw`) is
**axiom content**.  `§10.4` *mechanically verifies* order-independence
(`RawCmpIndependence`: any two `cmp` give isomorphic `RawBy`), so `Tree.cmp` is a
β-encoding-cost, not axiom material.  ⇒ a **free slash** (terms distinct,
symmetry only as a reading) is **ruled out by the axiom** — it would treat `a/b`
and `b/a` as distinct.  (My G161 second-pass musing about free-slash is wrong.)

**Quot avoidance is correct — a falsifiability contract.**  `§10.2`: "`Quot`
exists but brings the `Quot.sound` axiom, banned by ∅-axiom (§8.2).  Subtype of
canonical forms is the workaround."  `§8.2`: needing to add an axiom *falsifies
the theory*.  ⇒ `Raw := {canonical Tree}` (PURE `slash_comm`, `DecidableEq Raw`,
no `Quot.sound` at the Raw level) is the deliberate, mandated choice.

**`Raw.fold` is correct.**  The Nat-codomain fold (leaf count, depth) is fully
PURE.  Nothing about `fold` itself leaks an axiom.

## Where the axioms actually enter (Lean-pinned)

The leak is *only* at the boundary where a Lens reads into a **`Prop`- or
function-valued** codomain, and it is exactly two core axioms with two distinct
syntactic causes:

  - `#print axioms (funext : (∀ r, f r = g r) → f = g)` at `Raw → Bool` →
    **`[Quot.sound]`**.  So **stating combine/​fold coherence as a *function*
    equality `c f g = c g f` pulls `Quot.sound` via `funext` — for any codomain,
    Bool included.**
  - `apply propext` (turning a per-point `↔` into `=` at `Prop`) adds
    **`propext`** when the codomain is `Prop`.
  - The **pointwise** statement has neither: `ptwise_bool (a b : Bool) (h : a=b)`
    is PURE, and (G161) `combine_sym_pointwise` — `∀ r, combine f g r ↔ combine
    g f r` for the existential `universalLens` — is "does not depend on any
    axioms", using the very same PURE `Raw.slash_comm`.

So the seals are a **statement-shape** phenomenon: "coherence as function-`=` at
a Prop/Bool-valued codomain", not a Raw or fold defect.

## The decomposition (corrects G161's conflation)

The sealed set splits into **three** kinds, only one of which is a genuine
irreducible thesis-cost:

1. **Function-`=` combine / fold coherence** (`QuotLens`, `IndexedJoin`,
   `Compose.OnLens`, `Lattice.Join`, … and `Raw.fold_slash`'s
   `hsym : ∀ u v, c u v = c v u`).  Cause: function-`=` ⇒ `funext`/`Quot.sound`
   (+ `propext` if `Prop`-valued).  **Native form is pointwise** (`∀ r, … ↔ …` /
   `= ` at Bool) — PURE.  And `seed/AXIOM/06_lens_readings.md` §6.3 already
   *mandates* the fix direction: "the strict reading uses `Rawⁿ → Bool` —
   decidable predicates" precisely because `Raw → Prop` "requires propext and
   Classical … which the ∅-axiom standard forbids."  ⇒ **refactorable to PURE**,
   and axiom-endorsed.

2. **`Raw.fold_slash` itself** needs the function-`=` `hsym` to be *well-defined*
   over the commutative slash.  This is the one genuine structural pin: a `Raw →
   α` function must agree on `slash x y = slash y x`.  The native escape is an
   `≈`-valued (Reading) fold law — `hsym : ∀ u v, c u v ≈ c v u` (pointwise),
   conclusion up to `≈` — which is PURE.  A real, scoped foundational refactor of
   `Raw.fold` + its consumers; the §6.3 Bool-valued migration is the lighter
   variant.

3. **`propAsDistinguishing`** (`Prop` itself as a `HasDistinguishing` instance;
   `SemanticAtom`).  `STRICT_ZERO_AXIOM.md`: "The thesis 'Prop is an atom of
   meaning' *is* what `propext` expresses.  Removing the seal would require
   removing Prop as a HasDistinguishing instance, which removes the thesis."
   ⇒ **genuinely sealed-by-thesis** — keep.  This is the *only* equality-seal
   that is irreducible by design, and it is a handful of theorems, not ~54.

## Verdict

`slash`/canonical/`Quot`-avoidance/`fold` are all **correct** (axiom- and
falsifiability-mandated).  The ~54 propext/`Quot.sound` seals are **not a defect
and not (mostly) a thesis-cost** — they are the cost of expressing
distinguishing-outcome coherence as **Lean function-`=`** instead of the
**pointwise Reading-equivalence** that 213 natively means (and §6.3 mandates via
Bool).  Only `propAsDistinguishing` is an irreducible thesis-cost.  The fix is a
real arc (pointwise/`≈` fold + combine coherence, or Bool-valued Lenses per
§6.3), **not** a relabel and **not** a Raw/fold rewrite-from-scratch.

## Self-correction log (skepticism applied to my own claims)

  - **G161 pass 1**: "the seals are framework-`=`-artifacts, easily purified."
    *Too strong* — ignored that `Raw.fold_slash` genuinely needs `=`-`hsym`.
  - **G161 pass 2**: "the `=`-form is *genuinely required*; honest seal."  *Too
    strong the other way* — ignored §6.3 (Bool-valued strict reading is the
    intended PURE path) and that only `Raw.fold_slash` (not the standalone
    combine_syms) needs `=`.
  - **G162 (this, pass 3)**: the cost is precisely `funext`(=`Quot.sound`) from
    *function*-`=` + `propext` from `=`-at-`Prop`; pointwise is PURE; §6.3
    endorses the Bool/pointwise fix; only `Raw.fold_slash` (one primitive) and
    `propAsDistinguishing` (one thesis) are structural.  Pinned by
    `#print axioms` (`funext`→`Quot.sound`, `ptwise_bool`→PURE).

## Next research increment

Prototype the **pointwise/`≈` fold-homomorphism for `(Raw → Prop)`-valued
Lenses** (`fold_slash_equiv`: `hsym` and conclusion up to pointwise `↔`) and
derive `universalLens_view_eq_pointwise : ∀ r s, view r s ↔ E r s` PURE — which
would demonstrate the entire Prop-Lens chain is purifiable without touching the
correct `Raw`/canonical/`Quot`-free core.  Then either migrate Prop-valued
Lenses to Bool (§6.3) or carry the `≈`-fold as the canonical homomorphism.

## Pointers
  - Axioms: `seed/AXIOM/03_form.md` §3.3-3.4, `06_lens_readings.md` §6.3,
    `08_falsifiability.md` §8.2, `10_encoding_costs.md` §10.2/10.4.
  - Lean: `Theory/Raw/{Core,Slash,Fold}.lean`; `Lens/Universal/QuotLens.lean`;
    `Term/Internal/Tree.lean`.
  - Prior: `G161` (this thread), `G157` (view≠identity), `theory/lens/unified_equivalence.md`.
