# G163 — `Lens.equiv`'s `=` is the single root of the funext/propext seals

**Tier-1.**  Capstone of the seal-investigation arc (G161 → G162 → G163).  G162
resolved *one* family (`QuotLens`) and built the PURE primitive
`Raw.fold_slash_iff`.  This note shows the result is **universal** and pins the
**single root**: `Lens.equiv` (and `Lens.refines` built on it) defines "two Raws
are the same under a Lens" as Lean propositional `=` of views; for `Prop`- and
function-valued Lenses that `=` *is* the `funext`(=`Quot.sound`)/`propext` source
of every sealed theorem.  The 213-native notion is the **distinguishing-
equivalence** (pointwise `↔`), which is PURE — and the codebase has already been
discovering it piecemeal.

## The root, pinned

`LensCore.lean`:
```lean
protected def Lens.equiv (L : Lens α) (x y : Raw) : Prop := L.view x = L.view y
protected def Lens.refines (L : Lens α) (M : Lens β) : Prop :=
  ∀ x y, L.equiv x y → M.equiv x y
```
For `α = Raw → Prop` (the universal / indexed / Cauchy Lens family), `view x :
Raw → Prop`, so `Lens.equiv L x y = (view x = view y)` is a **function-of-`Prop`
equality** ⟹ `funext` + `propext`.  `#print axioms` pins it:

  - `equiv_from_pointwise` (build `Lens.equiv` from the pointwise data via
    `funext s; exact propext (h s)`) → **`[propext, Quot.sound]`**.
  - the Reading-native `equivR L x y := ∀ s, L.view x s ↔ L.view y s`, with
    `equivR_refl`/`equivR_trans` → **"does not depend on any axioms"** (the whole
    equivalence-relation structure is PURE).

Every sealed `combine_sym` / `view_eq` / kernel / `refines` theorem in the
funext/propext seal set bottoms out in this `view x = view y`.

## Universality — the codebase already approximates it

The "use pointwise to avoid funext" move is independently present across
structurally-different sealed families — they are all the *same* principle:

  - `QuotLens` — `universalLens_{combine_sym,view_eq}_pw` (G162, ∅-axiom).
  - `Lattice.IndexedJoin` — `iProdLens_view` is *"stated at each index `i` to
    avoid funext on the dependent function space"*, reducing the slash via
    `Raw.fold_slash` *"with pointwise sym"*; `iProdLens_refines_each` uses it.
  - `Instances.Cauchy` — `pointwise_limit_match`, `tailCong_slash_cong` carry the
    completion Lens pointwise.
  - `DepthJoin` — the tier theorems pass through `Lens.equiv`/`Lens.refines`,
    i.e. straight through the root.

So there is **no new obstruction** in any family: every funext/propext seal is
the single `Lens.equiv`-`=` root, and every family already has (or trivially
admits) the pointwise `↔` companion, now uniformly enabled by
`Raw.fold_slash_iff`.

## The 213-native reading (why this is the *correct* notion, not just PURE)

"Two Raws are the same under Lens `L`" should mean **`L` distinguishes them the
same way** — `L.equiv x y := ∀ s, L.view x s ↔ L.view y s` for a distinguishing
(`Prop`-valued) reading.  Using `view x = view y` (Lean `=`) imports
**Prop/function identity** beyond the distinguishing content — exactly the
meta-principle slip (`seed/AXIOM/01_residue.md`; CLAUDE.md "View promoted to
identity").  It also matches `theory/lens/unified_equivalence.md`: equivalence is
*one Lens-arrow* (the distinguishing relation), not Lean equality of view-values.
And `seed/AXIOM/06_lens_readings.md` §6.3 ("strict reading = `Raw → Bool`
decidable") is the same instinct: stay in the distinguishing/decidable layer, out
of `=`-at-`Prop`.

Codomain dependence (the precise statement): for **decidable codomains**
(`Bool`, `Nat`) `Lens.equiv`'s `=` is already PURE — no change needed.  The seal
is *exactly* the `Prop`/function-of-`Prop` case, where `=` ≠ the distinguishing
`↔` constructively.  So the native `equiv` is: `=` at decidable codomains,
pointwise `↔` at `Prop`-valued ones.

## End state (one root fix purifies the family)

Define a Reading-native equivalence for `Prop`-valued Lenses —
`L.equivR x y := ∀ s, L.view x s ↔ L.view y s` — with `refinesR` built on it, and
restate the sealed kernel/refines/combine_sym/view_eq theorems via `equivR`
(PURE, using `Raw.fold_slash_iff` + `Iff.trans`).  The `=`-based `Lens.equiv`
stays for decidable codomains (where it is already PURE) and as a `propext`-shim
for any consumer that genuinely wants Lean `=`.  Only `propAsDistinguishing`
(the "Prop is a meaning-atom" thesis) remains a genuine sealed cost.

This is now a **single, well-scoped foundational edit** (a Reading-native
`Lens.equiv`/`refines` for `Prop` codomains), not ~54 separate refactors — the
piecemeal pointwise lemmas already scattered across the modules become instances
of it.

## Evidence / pointers
  - Pins: `equiv_from_pointwise` → `[propext, Quot.sound]`; `equivR_{refl,trans}`
    → PURE (probed).  `Raw.fold_slash_iff` (Theory, PURE).
  - Root defs: `Lens/LensCore.lean` (`Lens.equiv`, `Lens.refines`).
  - Already-pointwise: `Lens/Lattice/IndexedJoin.lean` (`iProdLens_view`),
    `Lens/Instances/Cauchy.lean` (`pointwise_limit_match`),
    `Lens/Universal/QuotLens.lean` (`*_pw`, G162).
  - Thread: `G161` (skeptical seal review), `G162` (one-family resolution +
    `fold_slash_iff`), `theory/lens/unified_equivalence.md`, `G157` (view≠identity).
