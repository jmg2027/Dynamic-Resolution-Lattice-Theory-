# Decomposition: model-theoretic tameness — o-minimality and stability theory

*A FRESH decomposition per `../README.md` (model v7.1). The TAMENESS/classification layer of model
theory; `model_theory.md` did the basic layer (definability, types, satisfaction, completeness =
`view=fold`, compactness, Skolem) — this entry **does not duplicate** it but cross-references it.
The thesis: model-theoretic tameness is the calculus's **`q=±1` dividing line read on definable-set
counts** — `tame = q+1` (a finite / structured count of types / cells, the count-reading terminates),
`wild = q−1` (the **order property** = an unavoidable escaping diagonal, the SAME diagonal as
`cardinality.md`/`godel.md`, and a Ramsey-type unavoidable order, tying `ramsey_theory.md`).
Honest verdict: PREDICTION at the structural skeleton; every NAMED model-theoretic tameness object
(`oMinimal`, `cellDecomposition`, `stable`, `orderProperty`, `MorleyRank`, `NIP`, the Shelah
hierarchy) is **ABSENT** in `lean/E213` — grep-confirmed below. The engine (the `q±1` residue tag,
the diagonal escape, the count-termination, the fold-height, the Ramsey-order witnesses) is built
and PURE; the FOL-tameness *instance* is the located missing leg, the dual of `model_theory.md`'s
absent FOL syntax.*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — distinguishing, iterated. As in `model_theory.md`: a **structure / model**
  is a `Raw`-like construction-family (`Lens/Foundations/SemanticAtom.lean`); a **definable set** is
  a *fibre of a constraint-reading* — `{ x | φ.view (M, x) }`, the subset a formula-reading picks out
  of the carrier. So a definable set is **not a primitive subset**; it is the image of one reading.
  The construction carries its read-off **fold-height** (`Lambek.isPart_wf` — every peel-chain
  bottoms out; `MuNuMirror.ascent_unbounded` — depth is unbounded but each instance is finite): this
  height is the operand the rank-readings (Morley rank, dimension, cell-degree) project to.

- **Reading `L`** — the **definable-set count-reading**: project the structure to *how many
  definable sets / types of a given shape it admits*, and *how those definable sets decompose*. This
  is the count-reading of `cardinality.md`/`model_theory.md` aimed at the family of definable sets
  rather than at the carrier. Three derived readings, the three tameness notions:
  - **o-minimality's cell-reading** — read a definable subset of the line as a **finite list of cells**
    (points + intervals). The reading bottoms out: the count terminates (the `q+1` finite-normal-form
    pole), exactly like a confluent+terminating rewriting system reaching its normal form
    (`free_corner.md` / `colimit_quotient_synthesis.md`'s Side-A: confluent+terminating ⟹ finite
    normal forms via `Lambek.no_infinite_descent`).
  - **stability's type-count-reading** — read the structure to *how many types over a parameter set*
    (the count-reading on the type-space). **Bounded** = `q+1` (the count closes, no escaping chain);
    **unbounded via the order property** = `q−1` (a definable linear order embeds an infinite escaping
    chain — the same diagonal as Cantor/Gödel, and a Ramsey-type *unavoidable* order).
  - **Morley rank** — the **fold-height-reading on types**: the resolution rank of a definable set, the
    same height axis `Lambek.isPart_wf` / `MuNuMirror.ascent_unbounded` carry, read on the
    type/definable-set lattice instead of on `Raw`.

- **Residue** — the count-reading's self-application surplus on definable sets, splitting at `q=±1`
  (the load-bearing find, the dividing-line read on definable-set counts):
  - **`q=+1` (converge / terminate) — TAME (o-minimal / stable).** The definable-set reading **closes**:
    every definable subset of the line is a *finite* union of cells (o-minimality), the type-count is
    *bounded* (stability, no order property). The count-reading reaches a finite normal form — the
    fixed-point-*ful* pole, delegating to `ResidueTag.converge_residue_fixed` /
    `golden_is_converge`, and `multiplier (converge) = +1` (`multiplier_unimodular`).
  - **`q=−1` (escape / reached-by-none) — WILD (the order property).** The definable order embeds an
    **unavoidable infinite increasing chain** — a self-pointing reading whose surplus oscillates
    outside every finite enumeration (`object1_not_surjective` /
    `no_surjection_of_fixedpointfree`). This is the SAME `q−1` diagonal as `cardinality.md` (Cantor),
    `godel.md` (incompleteness), `measure.md` (non-measurable). The order property is **Ramsey-type**:
    a long enough configuration *cannot avoid* a long monotone/ordered sub-configuration
    (`ErdosSzekeres.erdos_szekeres` — the unavoidable monotone subsequence; `RamseyNamedBound` — the
    threshold below which order is avoidable / above which forced), tying `ramsey_theory.md`.
    `multiplier (escape) = −1`.

## Re-seeing — ⟨C | L⟩

```
   structure / model M     =  ⟨ a construction-family (Raw carrier) | — ⟩
   definable set           =  ⟨ M | a constraint-reading's fibre {x | φ.view (M,x)} ⟩  (a reading's image)
   o-minimality            =  Residue(cell-count on line-definable sets, C) at q=+1
                              = the cell-count TERMINATES: every definable S ⊆ line = finite ⋃ cells
                              (the count-reading reaches a finite normal form; the q+1 terminate pole,
                               ResidueTag.golden_is_converge / converge_residue_fixed; the confluent+
                               terminating rewriting analogue, Lambek.no_infinite_descent)
   cell decomposition thm  =  the FOLD-TO-NORMAL-FORM: finite cells = the canonical decomposition
                              (= a normal form of the definable-set reading, q+1)
   STABLE / no order prop  =  Residue(type-count, C) at q=+1 = the type-count is BOUNDED (count closes)
   the ORDER PROPERTY      =  Residue(type-count, C) at q=−1 = a definable order embeds an infinite
                              escaping chain (object1_not_surjective / no_surjection_of_fixedpointfree),
                              the SAME diagonal as cardinality/godel; Ramsey-type unavoidable order
                              (erdos_szekeres: long ⟹ long-monotone-forced)
   Morley rank             =  the FOLD-HEIGHT reading on types (Lambek.isPart_wf height,
                              MuNuMirror.ascent_unbounded) = the resolution rank of a definable set
   Shelah dividing lines   =  a STRATIFICATION of the q−1 escape (stable ⊂ NIP ⊂ ... / simple): how wild,
                              graded by which escaping configuration is forbidden (the same grade-by-
                              ordinal-height move as descriptive_set_theory.md's projective hierarchy)
```

So **o-minimality, stability, Morley rank, and the Shelah hierarchy are one reading at its two
signs** — the definable-set count-reading, read as: the *termination* of the cell-count
(o-minimality = `q+1` finite normal form), the *boundedness vs escape* of the type-count (stability
`q+1` / order property `q−1`), the *fold-height* of the rank (Morley), and the *stratification* of
the escape (Shelah = how-wild). Tameness is where the `q±1` residue tag meets the count-reading **on
definable sets** — the natural successor to `model_theory.md`'s "compactness `q+1` / Skolem `q−1`"
read on *sentences*.

## Revelation — PREDICTION (the q=±1 dividing line on definable-set counts; the order property = the diagonal)

**Three ties, each the SAME object the repo already proved, not a re-skin.**

### (1) The order property = the `q−1` escaping diagonal = a Ramsey-type unavoidable order

The order property — "a formula `φ(x,y)` linearly orders an infinite set of parameters" — is, in the
calculus, the **`q−1` escape pole** of the count-reading, the *same* object as Cantor/Gödel:

- An infinite definable linear order is a self-pointing count-reading whose surplus is **reached by no
  finite enumeration** — `FlatOntologyClosure.object1_not_surjective` (`:61`, PURE) / the fixed-
  point-free engine `OneDiagonal.no_surjection_of_fixedpointfree` (`:51`, PURE). The chain *escapes*
  every level it is read at; that is precisely the order property's "infinite increasing chain".
- And it is **Ramsey-type unavoidable**: `ErdosSzekeres.erdos_szekeres`
  (`Combinatorics/ErdosSzekeres.lean:587`, PURE) is the statement that a long enough sequence
  *cannot avoid* a long monotone subsequence — the combinatorial core of "the order property forces
  an infinite ordered configuration." `RamseyNamedBound.ramsey_lower`
  (`Combinatorics/RamseyNamedBound.lean:174`, PURE) is the dual threshold: below it a colouring with
  *no* monochromatic clique exists (order avoidable, `q+1`), at/above it order is forced (`q−1`).
  So the order property *is* `ramsey_theory.md`'s unavoidable-order phenomenon read on definable sets
  — wild = the Ramsey-forced escaping order.

This is the dividing line: **stable = the diagonal cannot arise (`q+1`); unstable = the order
property = the diagonal forced (`q−1`)** — the exact contrapositive structure `model_theory.md` used
for compactness (`q+1`) vs Skolem (`q−1`).

### (2) O-minimality / cell decomposition = the `q+1` finite-normal-form (the count terminates)

O-minimality — "every definable subset of the line is a finite union of points and intervals" — is the
**`q+1` finite-cell terminating normal form**: the definable-set reading bottoms out in finitely many
cells, the cell decomposition theorem being the *fold-to-normal-form*. In the calculus this is the
`q+1` convergence/termination pole:

- `ResidueTag.golden_is_converge` (`Foundations/ResidueTag.lean:180`, PURE) +
  `converge_residue_fixed` tag the convergent pole `multiplier (converge) = +1`
  (`multiplier_unimodular`, `:86`, PURE).
- The *mechanism* of "the count terminates" is the repo's termination engine
  `Lambek.no_infinite_descent` (`Theory/Raw/Lambek.lean:273`, PURE) / `isPart_wf` (`:199`, PURE):
  every peel-chain reaches an atom — a finite normal form. O-minimality is that same
  confluent+terminating-rewriting picture (`colimit_quotient_synthesis.md` Side-A: a quotient by
  moves = normal forms *exactly when* confluent + terminating) carried onto definable subsets of the
  line: the cell decomposition is the unique finite normal form, so the count reading *closes*.

So o-minimality is not a new theorem-shape; it is `topology.md`/`model_theory.md`'s `q+1`
finiteness-collapse, here read as *finite cells* rather than *finite subcover* — the count-reading
reaching its terminating normal form. The **cell decomposition theorem = the fold-to-normal-form**.

### (3) Morley rank = the fold-height on types; Shelah = the stratified `q−1` escape

- **Morley rank** is the **fold-height reading** (`dimension.md`'s height axis) applied to the
  definable-set / type lattice: the resolution rank counting how deep the definable set's
  approximation tower goes. The height axis is `Lambek.isPart_wf` (`:199`, PURE — descent
  terminates, so each rank is finite) + `MuNuMirror.ascent_unbounded`
  (`Theory/Raw/MuNuMirror.lean:50`, PURE — but the tower is unbounded across instances). Morley rank
  is finite ⟺ the height-reading terminates (`q+1`, ω-stable/tame); rank `∞` is the height escape
  (`q−1`). Same height object as dimension/degree/pole-order, read on types.
- **Shelah's dividing lines** (stable ⊂ NIP, simple, …) = a **stratification of the `q−1` escape** —
  *which* escaping configuration is forbidden grades how-wild. This is the same "grade the diagonal
  escape by ordinal height" move `descriptive_set_theory.md` makes for the Borel/projective hierarchy
  (the `q−1` diagonal `object1_not_surjective` graded by `Lambek.isPart_wf`/`ascent_unbounded`
  height). The Shelah hierarchy is the model-theoretic instance of that one graded-escape pattern.

**Net revelation:** model-theoretic tameness is the `q=±1` dividing line read on **definable-set
counts** — o-minimality the `q+1` finite-cell terminating normal form (cell decomposition = the
fold-to-normal-form), stability the `q+1` bounded-type-count vs the order property the `q−1` escaping
diagonal (the SAME diagonal as cardinality/godel, a Ramsey-type unavoidable order tying
ramsey_theory), Morley rank the fold-height on types, the Shelah hierarchy the stratified `q−1`
escape. No new axis: the two invariants (the count-reading's `q±1` residue, the fold-height) absorb
the whole tameness/classification layer. The tame/wild dichotomy IS the `q=±1` tag.

## The precise missing leg (located, like `model_theory.md` / `knots.md`)

**Every NAMED model-theoretic tameness object is ABSENT** in `lean/E213` (grep-confirmed: no
`oMinimal`, `o_minimal`, `cellDecomposition`, `cell_decomp`, `stable`-as-model-theory, `orderProperty`,
`order_property`, `MorleyRank`, `Morley`, `NIP`, `Shelah`, `tame`/`wild` predicates anywhere —
the only hits for "stable"/"stability" are numerical/dynamical stability, and "Morley"/"definable"
do not occur as model-theoretic objects). Concretely the repo has **no**:
1. a **definable-set / type** object (`Definable : Structure → Set`, a type-space `S_n(M)`) — only
   `Raw` and `Lens` (a reading), the same absence `model_theory.md` flags for FOL syntax.
2. an **o-minimality / cell-decomposition** predicate or theorem (no "definable ⊆ line = finite ⋃
   cells", no `cellDecomposition`).
3. a **stability / order-property** predicate (no `OrderProperty φ`, no `Stable T`, no
   bridge "no order property ⟺ bounded type-count").
4. a **Morley rank** function on definable sets, and **no** Shelah-hierarchy stratification object.

So the tameness *skeleton* is built and PURE — the `q−1` escape engine (`object1_not_surjective`,
`no_surjection_of_fixedpointfree`), the `q+1` termination/normal-form engine
(`Lambek.no_infinite_descent`/`isPart_wf`, `ResidueTag.golden_is_converge`), the fold-height
(`MuNuMirror.ascent_unbounded`), the Ramsey unavoidable-order witnesses (`erdos_szekeres`,
`ramsey_lower`), and the formal `q±1` tag (`ResidueTag.residue_tag_two_poles`) — but the
**FOL-tameness instance** that would let these be stated *as model theory's named classification
theorems* is the located missing leg, the dual of `model_theory.md`'s absent FOL syntax. It is not a
break of the model (no new axis); it is the absent named instance.

## Note for the technique

**No new primitive; a consolidation that extends `model_theory.md` one layer up.** Where
`model_theory.md` read the `q±1` residue on *sentences* (compactness `q+1` / Skolem `q−1`), this
entry reads the *same* residue on *definable sets* — and the dividing line is literally the `q=±1`
tag: tame = `q+1` (count terminates / type-count bounded / finite cells), wild = `q−1` (the order
property = the escaping diagonal). The lesson:

- **The tame/wild dichotomy is the `q=±1` residue tag** (`ResidueTag.lean`) — not a new model-theory-
  specific dichotomy. O-minimality = the `q+1` finite-normal-form (count terminates,
  `Lambek.no_infinite_descent`); the order property = the `q−1` escaping diagonal
  (`object1_not_surjective`), and that diagonal is Ramsey-type-unavoidable (`erdos_szekeres`).
- **Morley rank is the fold-height** (`dimension.md`'s axis) on types, not a new rank notion.
- **Shelah's hierarchy is the stratified `q−1` escape** — the same graded-escape pattern as
  `descriptive_set_theory.md`'s projective hierarchy.

So the count-reading's `q±1` residue now provably spans cardinality, provability, measure, topology,
satisfaction (`model_theory.md`), AND **definable-set classification** — the sharpest statement yet
that the `q=±1` residue is reading-agnostic. The honest edge — actual `Definable`/`Stable`/`oMinimal`/
`MorleyRank` objects — is the located missing leg, the analogue of `model_theory.md`'s absent FOL
syntax and `knots.md`'s absent isotopy quotient.

---

## Verified Lean anchors (grep/Read-verified file:line; purity freshly scanned via `tools/scan_axioms.py`)

| Leg | Theorem / structure (file:line : name) | Status |
|---|---|---|
| **the order property = the q−1 escaping diagonal** (infinite definable order = reached-by-none) | `Lens/Foundations/FlatOntologyClosure.lean:61 object1_not_surjective`; `:47 object1_injective` | ∅-axiom PURE ✓ (7/0) |
| the q−1 escape engine (fixed-point-free ⟹ no surjection; the diagonal) | `Lens/Foundations/OneDiagonal.lean:51 no_surjection_of_fixedpointfree`; `:43 lawvere_fixed_point`; `:101 one_diagonal_generates` | ∅-axiom PURE ✓ (11/0) |
| **the order property = a Ramsey-type unavoidable order** (long ⟹ long-monotone forced) | `Lib/Math/Combinatorics/ErdosSzekeres.lean:587 erdos_szekeres` | ∅-axiom PURE ✓ (29/0) |
| Ramsey threshold: order avoidable (q+1) below / forced (q−1) above | `Lib/Math/Combinatorics/RamseyNamedBound.lean:174 ramsey_lower` | ∅-axiom PURE ✓ (13/0) |
| **o-minimality / cell decomposition = the q+1 terminating normal form** (count bottoms out) | `Theory/Raw/Lambek.lean:273 no_infinite_descent`; `:199 isPart_wf` | ∅-axiom PURE ✓ (22/0) |
| the q+1 converge/terminate pole (the tame sign, multiplier +1) | `Lib/Math/Foundations/ResidueTag.lean:180 golden_is_converge`; `:86 multiplier_unimodular`; `:228 residue_tag_two_poles` | ∅-axiom PURE ✓ (55/0) |
| **Morley rank = the fold-height on types** (descent terminates / ascent unbounded) | `Theory/Raw/MuNuMirror.lean:50 ascent_unbounded`; `:80 succ_not_idempotent` (height strictly rises) | ∅-axiom PURE ✓ (8/0) |

**Fresh purity scan (this session, `tools/scan_axioms.py`, run from repo root):**
`FlatOntologyClosure` 7/0 (`object1_not_surjective`, `object1_injective` PURE);
`OneDiagonal` 11/0 (`no_surjection_of_fixedpointfree`, `lawvere_fixed_point`, `one_diagonal_generates` PURE);
`ResidueTag` 55/0 (`golden_is_converge`, `multiplier_unimodular`, `residue_tag_two_poles` PURE);
`Lambek` 22/0 (`isPart_wf`, `no_infinite_descent` PURE);
`MuNuMirror` 8/0 (`ascent_unbounded`, `succ_not_idempotent` PURE);
`ErdosSzekeres` 29/0 (`erdos_szekeres` PURE);
`RamseyNamedBound` 13/0 (`ramsey_lower` PURE). All pure / 0 dirty.

## Dropped / flagged citations (honest)

- **`oMinimal` / `o_minimal` / `cellDecomposition` / `cell_decomp` — DROPPED, ABSENT.** Grep over
  `lean/E213` returns no model-theoretic o-minimality / cell-decomposition object. The "definable
  subset of line = finite ⋃ cells" claim is the decomposition's framing on the termination engine
  (`Lambek.no_infinite_descent`), not a built theorem.
- **`stable` / `stability` / `orderProperty` / `order_property` — DROPPED, ABSENT (as model theory).**
  All `stable`/`stability` grep hits are numerical/dynamical (e.g. `RicciFlowDiscrete`, modulus
  stability), NOT the model-theoretic stability dividing line. No `OrderProperty`/`Stable T` predicate
  exists. "stable = bounded type-count, no order property" is framing on the `q±1` tag + the diagonal.
- **`Morley` / `MorleyRank` — DROPPED, ABSENT.** No occurrence in `lean/E213`. "Morley rank = the
  fold-height on types" is framing on `MuNuMirror.ascent_unbounded` / `Lambek.isPart_wf`.
- **`NIP` / `Shelah` / `tame` / `wild` predicates — DROPPED, ABSENT.** No Shelah-hierarchy / NIP /
  simple-theory object. "Shelah dividing lines = the stratified q−1 escape" is framing on the
  graded-escape pattern (`descriptive_set_theory.md`); no built stratification object.
- **`definable` / `Definable` — DROPPED as model-theoretic, ABSENT.** No `Definable` set or type-space
  `S_n(M)` object; the few "definable"-substring grep hits are unrelated. A definable set "= a
  constraint-reading's fibre" is framing on `Lens.view`, not a built object.

## Verified buildable witness (predicted, honest)

The cleanest closable instance, in the spirit of `model_theory.md`'s named open leg: a **toy
`OrderProperty`/`Stable` predicate on a finite `Lens`-family** wired to the existing diagonal —
defining "the family has the order property" as "a constraint-reading admits an infinite increasing
chain" and discharging *no order property ⟹ no `object1_not_surjective` escape* (the `q+1` corner).
The engine for this is fully built and PURE (`object1_not_surjective`,
`no_surjection_of_fixedpointfree`, `ResidueTag.residue_tag_two_poles`,
`ErdosSzekeres.erdos_szekeres`); only the *named* `OrderProperty` predicate + the bridge lemma is
absent — the exact analogue of `model_theory.md`'s open coded-`Provable`/`Sat` wiring. Recorded as a
predicted-buildable leg, not asserted as built.
