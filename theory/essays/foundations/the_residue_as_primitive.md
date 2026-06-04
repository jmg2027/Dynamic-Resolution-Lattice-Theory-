# The residue as primitive — Raw = µF, the escape = νF

The companion to `the_form_of_the_residue.md`.  That chapter reads the residue as **source
without enclosure** with Raw as the ground.  This one performs the *inversion*: take the
**self-pointing act** as primitive — the constructor functor `F(X) = {a} ⊎ {b} ⊎ {x/y :
x ≠ y}` — and *derive* both faces as its two fixed points.  Raw is the **initial algebra**
(µF: the finite, well-founded, grounded trees); the residue's escape is the **final
coalgebra** (νF: the possibly-infinite, anti-reflexive, consistent co-trees).  Which of
{Raw, the act} is "primitive" is a Lens choice (`seed/AXIOM/05_no_exterior.md` §5.4), not a
fact — so the inversion is a change of reading, not of content.

The headline: **the residue's νF face is realised ∅-axiom with no coinduction primitive.**
The path-function (M-type) presentation makes both *existence* (anamorphism) and *uniqueness*
(finite-path induction) of the unfold provable — and the feared "anti-reflexivity needs
bisimulation" dissolves, because inequality of co-trees is *positive* (a differing
observation), not a bisimulation.

## Lean source

- Files: `lean/E213/Theory/Raw/MuNuMirror.lean` (7 PURE),
  `lean/E213/Theory/Raw/CoResidue.lean` (99 PURE, 0 DIRTY); umbrella
  `lean/E213/Theory/Raw/API.lean`.
- Built on `Theory/Raw/Lambek` (µF: `decompose`, `isPart_wf`, `no_infinite_descent`,
  `terminal_iff_atom`) and `Theory/Raw/PrimitiveTower` (`rawTower`).
- ∅-axiom: 0 DIRTY (CoResidue 99 / MuNuMirror 7 PURE in the dependency-closed scan).

## Narrative

### µF — Raw is the grounded fixed point

`Lambek.decompose` says every Raw is an atom or a slash (the constructor's own image), and
`isPart_wf` (the peel relation `IsPart` is well-founded) + `terminal_iff_atom` say the descent
terminates at *exactly* the atoms.  So Raw is µF — the least fixed point, finite trees,
well-founded.  `MuNuMirror` sharpens the dual readings of the one peel relation: read
**downward** it always terminates (`no_infinite_descent` — no total descending stream), read
**upward** it is always continuable (`tower_ascent_isPart` — the self-pointing tower `rawTower`
is a total ascending `IsPart`-stream), and the depths are cofinal in `ℕ` (`ascent_unbounded`:
no finite Raw caps the tower).  Descent grounds; ascent escapes.

### νF — the escape is the final coalgebra, built without coinduction

The escape's *finite shadows* live at three scales (`object1_not_surjective`,
`MuNuMirror.ascent_unbounded`, the tower-ceiling diagonal).  `CoResidue` gives the escape a
*positive structural* form — the completed infinite self-pointing as an actual object — by the
**M-type as path-functions**: a co-tree is `List Bool → Option Bool` (a node at path `p` is a
branch when `none`, a leaf-atom `b` when `some b`).  This carrier is built in stages:

  - **the over-approximation is final.**  For the full-binary-tree functor `Bool × X × X`,
    `CoShape := List Bool → Bool` is *a* final coalgebra: the anamorphism `ana` exists
    (`ana_isBranch`/`ana_coLeft`/`ana_coRight`, `rfl`), and `ana_unique`/`final_coalgebra` give
    uniqueness — by induction on the *finite path* (the "blocked by coinduction" worry is
    over-cautious; the M-type sidesteps it).  Uniqueness is *up to pointwise equality* (`h = ana
    c` would need `funext`).

  - **the embedding is faithful.**  The leaf-labelled `LCoShape := List Bool → Option Bool`
    embeds the finite trees (`lToShape`); `lToShape_faithful` (pointwise, no `funext`) — trees
    agreeing everywhere as labelled shapes are equal.

  - **anti-reflexivity is positive.**  The slash functor's `x ≠ y` constraint, on co-data, is
    `Distinct s t := ∃ q, s q ≠ t q` — a *positive* differing observation, **not** a
    bisimulation.  `treeDiffPath` *constructs* the differing path from `x ≠ y` (structural
    recursion + `DecidableEq Tree`); `slash_children_distinct`: a slash's children embed
    `Distinct`.

  - **the everywhere-distinct invariant is canonicity.**  A Raw embeds *anti-reflexively*
    because its canonical tree has distinct children at every node: a canonical slash `x / y`
    has `cmp x y = .lt` (`Tree.canonical_slash_decompose`), hence `x ≠ y` (`Tree.cmp_self_eq`)
    — `raw_embeds_antiRefl`.

  - **the named infinite inhabitant.**  `spineL` — the left-spine `a/(a/(a/…))`, the `rawTower`
    limit — is anti-reflexive (`spineL_antiRefl`) and reached by no finite Raw
    (`spineL_escapes`): the completed infinite self-pointing, escaping the finite.

  - **the carrier and its finality.**  `SlashNu := {s : LCoShape // Consistent s ∧ AntiRefl s}`
    is the exact slash-νF carrier (`Consistent` = leaves absorb).  The finite residue embeds
    faithfully (`rawToSlashNu`, `rawToSlashNu_faithful`); `spineSlashNu` is the infinite
    inhabitant.  And `slashNu_final`: the leaf-absorbing anamorphism `lAna` of any
    **anti-reflexive** slash-coalgebra lands in `SlashNu` (consistent + anti-reflexive) and is
    its **unique** hom (pointwise) — so `SlashNu` is the residue's exact slash-νF.

### The reading

The act, iterated, terminates going *down* (the finite Raw, µF) and escapes going *up* (the
residue, νF).  Both fixed points of the one self-pointing are now formal objects, ∅-axiom,
with the finite Raw embedding into νF faithfully and anti-reflexively, the infinite spine the
canonical escapee.  No coinduction primitive enters: the final coalgebra of a polynomial
functor *is* the path-function M-type, and its universal property is finite-path induction.

## Populating νF — the escapes are a whole family

`spineL` is one canonical escapee, but νF is *richly populated*, built with the same
positive-`Distinct`, pointwise, ∅-axiom discipline:

  - **One escape per finite Raw** (`spine_family_populates_nu`).  `spineOf t` is the left-spine
    *seeded* by a finite tree `t` (so `spineL` is `spineOf` of the atom `a`).  Each `spineOf t`
    is consistent, anti-reflexive (in `SlashNu`), escapes every finite Raw (`spineOf_escapes`),
    and distinct seeds give `Distinct` spines (`spineOf_distinct`).  So the finite µF corresponds
    to a `Distinct`-preserving family of *escaping* νF behaviours — a `Raw`-indexed family, not a
    lone point.
  - **A bit-stream family** (`boolSpine_injects_bitstreams`).  Labelling the spine's rung-leaves
    by an arbitrary `f : Nat → Bool` gives `boolSpine f ∈ SlashNu` for *every* `f`, each escaping
    the finite, with **pointwise-distinct streams giving `Distinct` spines** (`boolSpine_inj`,
    antecedent `∃ k, f k ≠ g k`).  This is the honest ∅-axiom form of "the residue's escapes are
    uncountable": an injection of `Nat → Bool` into `SlashNu` *preserving distinctness* — **not**
    a cardinality theorem (`Cardinal`/`¬Countable` would pull choice/propext), and the antecedent
    is the pointwise difference, not `f ≠ g` (which would need `funext` to expose the index).
  - **The automorphism acts** (`coSwap_nu_endomorphism`).  `swap` (the only Raw automorphism)
    acts on νF by flipping leaf labels (`a↔b`, `coSwap`); it is pointwise-involutive, preserves
    both `SlashNu` constraints, and carries `spineL` to a *distinct* escape (the `b`-spine).
    Honest scope: this is the *label-level* (atomic) content of `swap` (`coSwap_atom_a/b` mirror
    `Raw.swap_a/b`); the full-tree intertwining fails because `Tree.swap` reorders children by
    `cmp` to stay canonical while `coSwap` is positional.  On the **bit-stream** family that
    label-level content is *exact and free* (`coSwap_boolSpine_free_action`): `coSwap (boolSpine
    f) = boolSpine (Bool.not ∘ f)` pointwise (`coSwap_boolSpine`), and `coSwap` fixes *no*
    bit-stream escape (`coSwap_boolSpine_distinct` — `f` and `Bool.not ∘ f` differ at every
    index), so the order-2 swap group acts **without fixed point** on the `(Nat→Bool)`-many
    escapes; `spineL` is the `f ≡ true` member, so its move is one instance.  Clean precisely
    where the tree-seed intertwining fails — a single leaf has no children to reorder.

  - **`spineL` is unique** (`spineL_unique`).  It is the *unique* co-tree whose root branches,
    whose left subtree is the constant leaf-`a`, and whose right subtree is *itself* (the
    self-similar fixpoint `coRightAt s [] = s`) — a νF-side **uniqueness** proved by finite-path
    induction, bisimulation-free (the positive-`Distinct` discipline makes even νF uniqueness a
    plain path induction).

These bundle into `nu_population_capstone`: νF is a `Distinct`-rich carrier — faithful finite
embedding, a `Raw`-indexed family of escapes, a bit-stream injection, the lone automorphism
acting, and `spineL` pinned by uniqueness.  So νF is not a single escapee above the finite µF
but a populated carrier — at least a bit-stream's worth of free-running behaviours, acted on by
the residue's lone automorphism.  (On the µF side, dually, `StateMachine.exact_descent` pins the
*exact* descent length: every state reaches an atom in *exactly* `depth` unit-steps along the
deep spine — the tight converse to the reachability upper bound.)

## Key results

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `isPart_wf`, `terminal_iff_atom` | `Theory/Raw/Lambek` | Raw = µF: peel well-founded, terminal = atoms |
| `ascent_total_descent_partial` | `Theory/Raw/MuNuMirror` | one relation `IsPart`: total up, none down |
| `final_coalgebra` | `Theory/Raw/CoResidue` | `CoShape` final for `Bool×X×X` (M-type, pointwise) |
| `lToShape_faithful` | `Theory/Raw/CoResidue` | the finite embedding is faithful (pointwise) |
| `treeDiffPath`, `slash_children_distinct` | `Theory/Raw/CoResidue` | anti-reflexivity is positive (no bisimulation) |
| `raw_embeds_antiRefl` | `Theory/Raw/CoResidue` | a Raw embeds anti-reflexively (= canonicity) |
| `spineL_antiRefl`, `spineL_escapes` | `Theory/Raw/CoResidue` | the infinite left-spine: anti-reflexive, escapes |
| `slashNu_final` | `Theory/Raw/CoResidue` | `SlashNu` is the residue's exact slash-νF (final) |
| `spine_family_populates_nu` | `Theory/Raw/CoResidue` | one escape per finite Raw (`spineOf` family, `Distinct`-preserving) |
| `boolSpine_injects_bitstreams` | `Theory/Raw/CoResidue` | `(Nat→Bool) ↪ SlashNu` preserving `Distinct` (honest "uncountable") |
| `coSwap_nu_endomorphism` | `Theory/Raw/CoResidue` | `swap` acts on νF (leaf-relabel involution; moves `spineL`) |
| `coSwap_boolSpine_free_action` | `Theory/Raw/CoResidue` | `swap` acts *freely* on the bit-stream escapes (exact intertwining, no fixed escapee) |
| `spineL_unique` | `Theory/Raw/CoResidue` | `spineL` is the unique left-spine fixpoint (path induction) |
| `nu_population_capstone` | `Theory/Raw/CoResidue` | νF is a `Distinct`-rich populated carrier (capstone) |
| `exact_descent` | `Theory/Raw/StateMachine` | every state reaches an atom in *exactly* `depth` unit-steps |

## Open frontier

  - Finality is *up to pointwise/extensional equality* (uniqueness `∀ x p, h x p = lAna c x p`;
    the `h = lAna c` form needs `funext`, deliberately avoided) and among *anti-reflexive*
    slash-coalgebras (the `hAR` hypothesis: only anti-reflexive coalgebras map into the
    anti-reflexive νF).  These are the honest scope, not gaps.
  - The carrier is the path-function (M-type) presentation, not a Lean-native coinductive type
    (which a Mathlib-free Lean lacks); the M-type is the standard coinduction-free construction.

## How to verify

```bash
cd lean && lake build E213.Theory.Raw.API
python3 tools/scan_axioms.py E213.Theory.Raw.CoResidue
python3 tools/scan_axioms.py E213.Theory.Raw.MuNuMirror
```
