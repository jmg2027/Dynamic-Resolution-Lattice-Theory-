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
  by D3 + induction), so existence holds. The construction is then an injective catamorphism with the
  `≠`-proof embedded (well-founded on `depth`); the Lean obligation is defining `map` and its
  injectivity simultaneously. **This is the precise next target** — add D6 to `DStr`, prove
  `rawDStr` satisfies it (`Raw.slash_ne_a/b` via depth), build the injective catamorphism, then
  `raw_initial = ⟨existence, dhom_unique_pointwise⟩`.
- ⏳ **The dichotomy theorem** (negative branch = named clause failure; positive = `generated_iso` for
  *free* generated N — note a generated-but-not-free N gets a surjection, not an iso), and
  **`kernel_devices_are_distinguishing_instances`** (Attack-1 recognition bundle).
- 📌 Promote the honest maximal claim (Agent 2's 2d) to a permanent tier; retire "from one primitive"
  rhetoric in CLAUDE.md framing.
