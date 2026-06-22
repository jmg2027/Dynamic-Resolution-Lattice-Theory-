# Raw & Lens, explained — a reader's guide to the foundational layer

*Audience: anyone (human or AI) meeting this repository for the first time and asking "what are `Raw`
and `Lens`, why are they encoded this way, and what is actually proven vs. open?"  Plain language; every
claim points to a file you can check.*

## 1. The one-sentence idea

213 tries to rebuild mathematics by **adding nothing to Lean's kernel** — no axioms, no Mathlib — on
top of a single primitive: **the act of distinguishing** (pointing at one thing *as not* another).
Everything else — number, infinity, the limitative theorems (Cantor/Gödel/…), "no exterior", "the
residue" — is meant to be a *theorem about that act*, not a separate assumption.

"Adds nothing" is checked mechanically: `#print axioms <thm>` must report *"does not depend on any
axioms"* (no `propext`, `Classical.choice`, `Quot.sound`, `native_decide`). The scanner
`tools/scan_all_axioms.py` enforces it corpus-wide (current: 18,798 PURE / 47 sealed-by-design / 0
real-DIRTY).

## 2. `Raw` — the distinguishing made into an object

`Raw` is the primitive act, frozen into a data type (`lean/E213/Theory/Raw/`):

- two **atoms** `a`, `b` — you cannot point at one thing alone; distinguishing needs *another*
  (`seed/AXIOM/01_residue.md` §1.2, "at least two required");
- one operation **`slash x y h`** — pair two things `x`, `y`, *where `h : x ≠ y`*. This is the act of
  distinguishing: combining two things that are already *not the same*.

So `Raw` is the set of finite "distinguishing trees" built from `a`, `b` by `slash`.

### Why is `x ≠ y` written into the *type* of `slash`?

This looks odd — why not a plain binary operation? Two forced reasons (both checkable):

1. **The axiom says so.** The primitive is *anti-reflexive* distinction: `x / x` is meaningless —
   pairing something with itself distinguishes nothing (`seed/AXIOM/03_form.md` §3.3). Putting `h : x ≠ y`
   in the type makes `slash x x` literally *unconstructible*. That is the axiom, re-expressed
   (`seed/AXIOM/10_encoding_costs.md` §10.3 files it as "(α) re-expression", not an added commitment).
2. **The no-axiom rule forces it.** The "honest" alternative — a total `slash` that allows `slash x x`,
   then *quotient away* the junk and the orderings — needs Lean's quotient axiom `Quot.sound`, which is
   **forbidden** here. Forbidding `slash x x` by typing is the *only* zero-axiom way to get a
   "quotient-like" object. (`Raw := { canonical trees }` is the same trick for ordering; a meta-theorem
   `RawCmpIndependence` proves the chosen ordering has no mathematical effect — so it is a representative,
   not a smuggled ontology.)

**Takeaway:** the partial/`≠`-in-type encoding is *forced by the axiom plus the no-axiom rule* — a
feature, not a quirk. (A genuine refinement: constructively, the right notion is **apartness** `#` — a
*positive* "these are apart" — not the weak negative `¬(x=y)`; and `Raw`'s canonical-form comparison
`cmp` already *is* a decidable apartness. See §6.)

## 3. `Lens` — a reading of `Raw`

A `Lens` (`lean/E213/Lens/LensCore.lean`) is a **way of reading** a `Raw` tree into some value: pick a
value for each atom and a way to combine, then fold the tree. `Lens.leaves` counts leaves (giving the
positive naturals); other Lenses read parity, depth, etc.

Key facts, all proven:

- **The count IS a reading of the distinguishing.** `ℕ₊` is exactly `Lens.leaves` applied to iterated
  `slash` (`Lens/Number/Nat213/Generation.lean`: `succ` *is* slash-against-`b`, `n+1` *is* the leaf-count
  of the `n`-fold distinguishing). Number is the distinguishing's unfolding, read by a Lens.
- **The reading is forced, not chosen.** Fix "atom ↦ 1, slash ↦ +" and the whole reading is the unique
  leaf-count (`count_reading_forced`) — this is *initiality* (§5).
- **No reading captures everything.** The "self-cover" `Object1 : Raw → (Raw → Bool)` is faithful but
  never onto (Cantor) — there is always a predicate outside it. *That leftover is "the residue"*
  (`Lens/Foundations/FlatOntologyClosure.lean`: `distinguishing_always_leaves_residue`). **The residue is a theorem,
  not a starting assumption.**

## 4. The residue is the *engine*, not a substrate

One diagonal construction (`Lens/Foundations/OneDiagonal.lean`, Lawvere's fixed point) *generates*, as instances,
**Cantor + the residue + Russell/Liar/Tarski** — they are one move, not four proofs. And the residue
*needs* the distinguishing: on a value-space that draws no distinction, the diagonal escape vanishes
(`residue_needs_distinguishing`). So "the residue is what the distinguishing always leaves, and that
leftover is the engine of the deepest impossibility theorems."

## 5. The universal property — *already proven*

The sharpest statement of "everything is sourced from the distinguishing" is **initiality**:

> For any distinguishing-respecting target, there is a **unique** map from `Raw` into it.

This is **proven, ∅-axiom**: `Lens/Foundations/SemanticAtom.lean` `raw_initial` (existence + uniqueness, stated
pointwise to avoid `funext`). So "Raw is the initial object / the free distinguishing-structure" is
*done*, not aspirational.

There is also a *deliberately weaker* restatement, `Lens/Foundations/UniversalDistinguishing.lean` (`DStr`), which
assumes *less* about the target (a partial pairing, no commutativity) to answer a circularity worry.
Its **uniqueness** half is proven; its **existence** half is the one open "wall" — and that wall is a
known *partial-algebra* subtlety (maps into a partial operation must preserve "definedness"), i.e. **Lean
engineering, not a foundational limit, and it needs no new axiom**.  (Three closure routes are on
record: use the proven total-target `raw_initial` directly; or make morphisms preserve the apartness
`Raw`'s `cmp` already supplies; or a well-founded mutual recursion.  The open frontier is tracked under
`research-notes/frontiers/`.)

## 6. The schema view — why rival "primitives" don't compete

Rather than defend "distinguishing is THE primitive" against an endless list of rivals, treat the
distinguishing as a **schema that classifies** every structure by a *dichotomy*: a structure either
*satisfies* the schema (and then the universal property makes it `Raw` relabeled — not a rival) or
*fails a named clause* (so it is not a distinguishing-structure at all). The rival "primitives" we
checked all fall on the negative side:

- a **no-distinction** carrier can't even form `slash` (`OneDiagonal.no_distinguishing_on_subsingleton`);
- a **unary** ("negation-first") primitive grows linearly where distinguishing grows super-linearly
  (`UniverseChain/RivalArity.lean`, `2 + C(·,2)`);
- a **distinctness-blind** binary op (`op x x` allowed) over-counts — 213 is exactly *that minus the
  self-combinations* (`distinctness_removes_self_combination`).

The one irreducible leftover ("is *every conceivable* signature covered?") is not a special weakness — it
is the framework's own, openly-accepted "no-exterior" limit (`seed/AXIOM/05_no_exterior.md` §5.1).

## 7. What is proven, what is open (honest scoreboard)

| Claim | Status |
|---|---|
| Corpus is axiom-free (the mechanical sense) | ✅ proven, scanner-checked (0 real-DIRTY) |
| `Raw` is the initial distinguishing-structure (total target) | ✅ `SemanticAtom.raw_initial` |
| Number = leaf-Lens reading of iterated distinguishing | ✅ `Nat213.Generation` |
| The residue is a theorem + the engine of Cantor/Russell/Tarski | ✅ `OneDiagonal`, `FlatOntologyClosure` |
| Rival primitives excluded (three classes) | ✅ `OneDiagonal`, `RivalArity` |
| `DStr` (weaker) initiality — existence half | ⚠️ open Lean engineering (no axiom needed) |
| "All of `Lib/Math` is *generated* from `Raw`" | ❌ false — 96% is axiom-free *re-derivation* over native `Nat` (`the_descent_leg.md`) |
| "From one primitive / from nothing" (the strong slogan) | ❌ conceded — Lean's kernel (inductives, `Bool`, `=`) is presupposed; the honest claim is "the minimal *added*, axiom-free primitive" |

## 8. Where to read what (file map)

- **The axiom (start here):** `seed/AXIOM/01_residue.md`, `seed/AXIOM/05_no_exterior.md`,
  `seed/AXIOM/10_encoding_costs.md`; essay `theory/essays/foundations/the_form_of_the_residue.md`.
- **`Raw` (the primitive):** `lean/E213/Theory/Raw/` (`Core`, `Slash`, `Fold`, `Rec`).
- **`Lens` (readings) + universal property:** `lean/E213/Lens/LensCore.lean`, `Lens/Foundations/SemanticAtom.lean`
  (`raw_initial`), `Lens/Foundations/Initiality.lean`.
- **Residue + the one diagonal:** `Lens/Foundations/FlatOntologyClosure.lean`, `Lens/Foundations/OneDiagonal.lean`,
  `Lens/Foundations/ResidueReentry.lean`; essays `the_one_diagonal.md`, `the_distinguishing_is_the_primitive.md`.
- **Number from the distinguishing:** `lean/E213/Lens/Number/Nat213/` (`Raw`, `Peano`, `Generation`,
  `Divisibility`).
- **Schema / rival-exclusion / the encoding question:** `Lens/Foundations/UniversalDistinguishing.lean`,
  `Lib/Math/Foundations/UniverseChain/RivalArity.lean`; the corresponding open frontiers (the
  distinguishing-schema diagnosis, the descent leg, the substance test) live under
  `research-notes/frontiers/`.
- **Honesty infrastructure:** `STRICT_ZERO_AXIOM.md` (the PURE/sealed catalog), `tools/scan_all_axioms.py`.
