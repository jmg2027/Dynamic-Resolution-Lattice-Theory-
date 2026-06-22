# The distinguishing schema — dissolving rival-enumeration and Attack 1 in one move

**Source.** A two-agent debate (category theorist + proof theorist) on the session's stuck points
(`the_descent_leg.md` rival-enumeration residual; `the_substance_test.md` Attack-1 circularity).
Both converged on **one** reframing. This note records the insight; the first Lean deposit is
`lean/E213/Lens/UniversalDistinguishing.lean`.

## The stuck points (restated)

1. **Rival-enumeration residual.** The repo excludes rival primitives one class at a time
   (subsingleton / unary / non-distinctness — `OneDiagonal` §6, `RivalArity`). But `∀ rival` over an
   *untyped* class is never discharged: each theorem kills one more class, the quantifier stands.
2. **Attack 1 (circularity).** `∅-axiom` ≠ "from one primitive": `Raw` is `inductive` (presupposes
   ℕ-induction), and `Bool`/`Eq`/Π/universe are ambient CIC apparatus. "The distinguishing is the
   sole ground" looks circular.

## The insight: the distinguishing is a *schema that classifies*, not a primitive that competes

Stop treating the distinguishing as *one primitive among rivals*. It is a **schema** `DStr`
(a weakening of `HasDistinguishing`) that **classifies every structure** — rivals *and* the kernel's
own devices — by a **dichotomy**:

> **Every structure either (a) satisfies `DStr` — and then the universal property forces it to *be*
> `Raw` up to unique iso on its generated part (so it was never a rival, just `Raw` relabeled) — or
> (b) fails a *named, finite* clause D1–D5 (so it is not a distinguishing-structure at all).**

This discharges `∀ rival` with **one** theorem (the universal property), not an enumeration. The
three existing corners become *instances of the negative branch*: subsingleton = fails **D1**
(no 2-element witness); unary, non-distinctness = fail **D2** (wrong signature — the pairing is a
*partial* operation defined exactly on distinct pairs, so a unary or a total `op x x` is not even a
`DStr`, by type). Growth-race comparisons (`rawCount` vs `unaryCount`/`relCount`) are no longer
needed to exclude — the signature mismatch does it.

### The weaker axioms (answering the circularity charge against `Lens.view_unique`)

`Lens.view_unique` proves `Raw` initial among `Lens` algebras — but `Lens` *already* carries a binary
total commutative `combine`, so it presupposes the answer's shape (the skeptic's circularity). `DStr`
does **not** name binarity/commutativity/super-linearity:

- **D1** carrier distinguishes: `e₁ ≠ e₂`.
- **D2** a *partial* pairing `pair : (x y) → x ≠ y → α` (distinctness in the *type*, as in `slash`).
- **D3** faithfulness up to swap: `pair x y = pair u v → {x,y} = {u,v}`.
- **D4** `pair`-result ≠ its operands (freeness/no-collapse).
- **D5** well-founded rank: `pair` strictly increases a ℕ-rank.

From these, **binary** (D2 signature), **commutative** (D3 reads *unordered* operands → `slash_comm`
is a *theorem* of the free object, not an axiom), and **super-linear** `2 + C(·,2)` growth
(`rawCount_ge`, a corollary of D3+D5 for the free object) are all **derived, not assumed**. That is
the precise advance over `view_unique`.

### Attack 1 reframed (Agent 2): recognition, not genesis

The genetic claim ("CIC from the distinguishing") is **conceded** — circular, the repo already admits
it in prose. The survivable claim: the kernel devices (`Bool`, `Eq`/`≠`, `Prop`, the 2-constructor
inductive) are themselves **instances of the schema** (`Bool` with `true ≠ false` is a `DStr`-like
2-point distinguishing; `propAsDistinguishing` already exhibits `Prop`). So the foundation is **closed
under recognition by its own schema** — *recognition, not genesis*. The "self-describing fixed point"
prose is a category error (object-level diagonal theorems ≠ meta-level constitution); the *provable*
form is "every kernel device used is a model of `DStr`", a bundled theorem, strictly weaker than the
"from nothing" rhetoric and actually true.

## The keystone already exists

Agent 1 rated `pair_faithful` (slash faithful up to swap) the one medium-risk gate. **It is already
proven**: `Theory.Raw.Slash.slash_inj` : `slash x y = slash z w → (x=z ∧ y=w) ∨ (x=w ∧ y=z)`, PURE.
All other `DStr` fields for `Raw` exist: `PrimitiveTower.a_ne_b` (D1), `slash` (D2),
`slash_ne_left/right` (D4), `slash_inj` (D3), `Lambek.depth_drops` (D5). So `rawDStr : DStr Raw` is
assemblable now (first deposit).

## ★ RESOLUTION (2026-06-22, 3-agent panel: encoding / category / axiom-faithfulness)

The originator asked: *is the Raw/Lens Lean technique causing the limit; should it be encoded
differently; what does the axiom demand?* Three experts converged:

**(1) The "wall" is NOT foundational — the universal property is ALREADY proven, ∅-axiom.**
`SemanticAtom.raw_initial` (PURE) is the full ∃!: a unique distinguishing-preserving `Raw → α` for
every `HasDistinguishing α` (`universalMorphism = Raw.fold`; uniqueness pointwise to dodge funext).
So "Raw is the initial object" is **done**. There are *two* initiality stories in the repo:
(i) **canonical** — `SemanticAtom.raw_initial` over a **total** `combine` — *both legs closed, clean*;
(ii) **`UniversalDistinguishing.DStr`** — over a **partial** `op` — only the existence leg open. The
wall is the existence leg of (ii) **only**.

**(2) The wall is the known partial-algebra subtlety — encoding-induced, not intrinsic.** The
diagnostic tell: uniqueness (`dhom_unique_pointwise`) is clean because it only *reads* the target op;
existence is stuck because a morphism into a *partial*-op target must *manufacture* a definedness
witness (`map x ≠ map y`) at every node. That asymmetry is the signature of choosing a category of
*partial* algebras. `DStr` was a **deliberate, optional strengthening** (assume *less* than
`HasDistinguishing`, to answer the circularity charge that the total-combine category "presupposes the
answer's shape"). So the wall is the price of a voluntary harder target — not a limit of the
foundation, and not intrinsic math.

**(3) The source encoding is FAITHFUL and FORCED by ∅-axiom — a feature, not a careless import.**
`Raw.slash`'s `x ≠ y`-in-type is filed in `seed/AXIOM/10_encoding_costs.md` §10.3 as *(α)
re-expression of the axiom* (clauses 1–2), not a cost/commitment: `01_residue.md` §1.3 + `03_form.md`
§3.3 name the primitive as **anti-reflexive primitive distinction** (`x/x` undefined), *not* a total
pointing act with distinctness as a later Lens. The proposed "total free magma + distinctness as the
first Lens" reframing is **less** faithful: it would import a total act the axiom never posits, and to
recover symmetry (§3.4) + anti-reflexivity it would need a **quotient → `Quot.sound`, FORBIDDEN**. The
canonical-subtype `Raw := {canonical Tree}` is the *only* ∅-axiom route to a quotient-like carrier
(§10.1), and `RawCmpIndependence` proves the chosen order is mathematically inert — the opposite of
"quotient promoted to ontology". **So the partial/canonical encoding is forced by
(axiom clauses 3+4) ∧ (no `Quot.sound`).**

**What the axiom demands (the one genuine refinement).** §1.3's "confirmation of *not equal*" is, in
the constructive/∅-axiom setting, a **positive apartness `#`**, not the weak negative `¬(x=y)`. And
`Raw`'s `cmp`-canonical form *already is* a decidable apartness (`cmp = .lt/.gt` = positive witnesses,
`.eq → tightness`). So the cleanest way to close the `DStr` existence leg *faithfully* (without the
total-combine convenience and without Route B's mutual recursion) is to make morphisms **preserve the
apartness** (`map_apart : x # y → map x # map y`): then the definedness witness is *supplied by the
structure*, and existence = `Raw.fold`. The repo is already operating in "decidable-apartness magmas"
— it just hasn't named the category.

**Bottom line for the originator.** The technique is faithful; the limit is not in Raw/Lens. The
universal property is already proven (`raw_initial`). The only wall is the optional `DStr`
strengthening's existence leg, closable three ways with **no new axioms**: (a) just use the canonical
`raw_initial` (total target) + distinctness as theorems on `Raw`; (b) reframe morphisms to preserve
the apartness `cmp`-already-provides (faithful + clean); (c) Route B mutual WF recursion. Recommended:
(a) for the load-bearing claim now, (b) as the faithful strengthening when worth the engineering.
**Action item (narrative, not code): retire "from one primitive / from nothing" rhetoric; the honest
statement is "the canonical initiality is closed ∅-axiom; the partial-op strengthening's existence
leg is Lean engineering, not an axiom obstruction."**

## The irreducible residual (honestly relocated, not eliminated)

The dichotomy is over a **typed** class of finitary candidates (a fixed signature: carrier + bounded-
arity partial/total op + base points). "All *conceivable* signatures" is still not a Lean type — the
§5.1 wall. But this is the framework's **already-accepted** universality limit (no-exterior, a claim
under test), **not** a private debt of the descent leg. The reframing converts an open `∀` over an
untyped class into a closed dichotomy over a typed class, pushing the irreducible part to exactly the
§5.1 wall the boot sequence already treats as internal-first-and-said-plainly.

## Status / next deposits

- ✅ **Insight recorded** (this note) + **first deposit**: `UniversalDistinguishing.rawDStr` (`Raw`
  satisfies the weaker axioms; binary/commutative derived not assumed) + `rawDStr_generated`.
- ✅ **Universal property — uniqueness half** (`dhom_unique_pointwise`, PURE, funext-free): any two
  `DHom rawDStr N` agree at every `Raw` (induction, since `Raw` is generated). The `∀ rival morphism`
  quantifier is discharged.
- ⚠️ **Existence half — a genuine subtlety found (refines Agent 1).** The catamorphism `Raw → N` must
  preserve distinctness (`map x ≠ map y` at every slash, so `N.op` applies). But D3 (`op_faithful`) +
  D4 (`op_ne_operand`) do **not** prevent an op-result from colliding with a *base point*
  (`op u v = e₁` is not forbidden by the stated axioms) → the catamorphism need not be injective →
  the morphism need not exist → **`Raw` is not initial in the naive `DStr` category.** Fix: add
  > **D6** `op_ne_base`: `op x y h ≠ e₁ ∧ op x y h ≠ e₂` (op-results are never base points — true in
  > `Raw` by `depth`, the atoms being the floor).
  With D1+D3+D4+D6 the catamorphism is injective (atom/atom by `e_ne`; atom/slash by D6; slash/slash
  by D3 + induction), so existence holds. **D6 added** (`op_ne_base`), `rawDStr` satisfies it
  (`Raw.slash_ne_a/b`); the schema is now correct and **uniqueness + the negative branch are proven**
  (`dhom_unique_pointwise`, `no_DStr_on_subsingleton`).

  **Existence leg — deeper requirements found (two routes, each with a hidden cost):**
  - *Route A — total-extension via `Lens.view`.* `cata := Lens.view ⟨e₁, e₂, opTotal⟩` where
    `opTotal x y := if h : x = y then e₁ else op x y h`. Costs: (i) **`DecidableEq β`** (for the
    `dite`), and (ii) **commutativity** — `Lens.view_slash` requires `hsym` (`opTotal` commutative),
    which needs `op x y = op y x` (not given by D3, which is faithfulness *up to* swap, not the swap
    equation). So Route A needs adding **D7 `op_comm`** + a `DecidableEq` hypothesis. Then injectivity
    of `cata` is still a separate induction (using D3/D4/D6/`e_ne`), and `map_op` follows by collapsing
    `opTotal` to `op` on the (injective ⟹ distinct) images.
  - *Route B — direct injective catamorphism by well-founded recursion on `depth`.* Define `cata` and
    `cata_inj` *simultaneously* (mutual WF recursion): at `slash x y h`, the `≠`-proof `cata x ≠ cata y`
    comes from `cata_inj` on the strictly-smaller `x, y`. No `DecidableEq`/commutativity needed, but the
    Lean engineering (mutual `termination_by depth`, the embedded proof) is the intricate part.
  **Recommendation:** Route B is axiom-cleaner (keeps D1–D6, no D7/DecidableEq) and is the honest
  target; Route A is a faster but heavier-hypothesis fallback. Either yields
  `raw_initial = ⟨existence, dhom_unique_pointwise⟩`. This is research-grade Lean (a free-algebra
  catamorphism into a faithful *partial*-operation structure), deferred as the precise next deposit.
- ⏳ **The dichotomy theorem** (negative branch = named clause failure; positive = `generated_iso` for
  *free* generated N — note a generated-but-not-free N gets a surjection, not an iso), and
  **`kernel_devices_are_distinguishing_instances`** (Attack-1 recognition bundle).
- 📌 Promote the honest maximal claim (Agent 2's 2d) to a permanent tier; retire "from one primitive"
  rhetoric in CLAUDE.md framing.
