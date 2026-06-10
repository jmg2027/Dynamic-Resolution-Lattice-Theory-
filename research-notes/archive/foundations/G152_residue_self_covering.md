# G152 — "213" as residue self-covering: the 1 as axis, distinct vs 미분화, flat ontology

**Date**: 2026-05-30. **Status**: synthesis + one ∅-axiom brick; closure frontier scoped.

Durable distillation of a long working session (tower → branching shape → the
meaning of "213" → the residue → flat ontology → self-covering). File map + open
target at the end.

## Driving question

What is the residue (the "1" in **2-1-3**)? Is it a *gap / difference between* 2
and 3, or the *undivided* thing both are? NS=3, NT=2, d=5=NS+NT.

## Constructive results (this session)

- **Most primitive tower** — `Theory/Raw/PrimitiveTower.lean` (8 PURE):
  `rawTower n = a/(a/(…/b))`, the single `slash` (self-pointing) arrow iterated;
  `depth = level`, `depth < leaves` every rung. The most primitive tower fixes
  the iterated arrow to the *only* one Raw provides.
- **Branching-shape simulation** — `research-notes/data/probes/raw_branching_shape.py`
  (self-checks SET-EQUAL to Lean `RawDepth3.depthLe3List`). Findings:
  - `|S_n| = 2 + C(|S_{n-1}|,2) = 2,3,5,12,68,2280` (verified vs `rawCount`).
  - **residue ratio → 1**: points grow ~a², realized pairs only ~a, so the
    structure *recedes* from the complete graph ("void") in proportion while
    every specific pair is drawn at a finite level.
  - the midpoint (1D) Lens collapses `|S_n|` onto exactly `2^n+1` dyadic
    positions (2,3,5,9,17,33) — a Lens reading erasing residue (2280→33).
  - self-similar growth exponent = **2** (=NT): `log|S_n| ≈ 2·log|S_{n-1}|`.

## Atomic numbers fall out of the branching head

- `|S_0|,|S_1|,|S_2| = 2,3,5 = NT, NS, d`. The atomic signature is the **head**
  of the count sequence, before the C(n,2) explosion.
- **NS=3 is the unique fixed point of the self-pairing map** `C(n,2)=n`
  (n=2 sub-critical, n=3 critical, n≥4 super-critical → explosion). d=5=2+C(3,2)
  = NT+NS = first super-critical count.
- Converges with the independent atomicity proof
  `Theory/Atomicity/Five.atomic_iff_five` (`5 = 2·1 + 3·1`, unique alive
  decomposition over parts {2,3}). Generation side (count head) and constraint
  side (atomicity) land on the same germ.

## The "1": gap AND glue, proven the same

Five-agent repo sweep (seed / theory / lean core / lean Lib / research-notes):

- **Same 1, formally**: `Mobius213OneAsGlue.mobius_det_eq_ns_minus_nt`
  (`det(P) = NS − NT`); `G75_det_is_axis_generator_fold` ("the 1 in det is
  structurally identical to the 1 in NS−NT"); `catalogs/cross-domain-identifications`
  CDI-9 (`det = glue = unit` are byte-identical proof terms).
- **Originator's own statement** (`Mobius213OneAsGlue.lean` header): "1이 접착제이고 회전축... '어떤 관점'에선
  2축으로 보였던게 3축으로 보이고 vice versa. 2-1-3은 불가분." (The 1 is glue and
  rotation axis; from one view the 2-axis is seen as the 3-axis and vice versa;
  2-1-3 is indivisible.) → the 1 is the **rotation axis** under which 2↔3
  interconvert — neither an interval nor a collapse.
- **0 vs 1**: **0** = swap-fixed
  diagonal collapse = the unique non-atomic integer = the *gap/void*; **1** =
  det/unit/origin = the *undivided residue*. The collapse-role is 0, not 1.
- **Frobenius reversal**: classically
  `F(2,3)=1` is the unique integer *unreachable* by `2a+3b` (a "hole/gap"); in
  213 it is `1 = det = unit = the origin` both generators presuppose. The
  classical "gap" IS the 213 origin.

**Verdict**: the residue/1 is the *axis* — what 2 and 3 are distinct readings
*around* — not an interval between poles, and not their collapse (that is 0).

## distinct vs 미분화 (defined via the pointing act, not sameness)

The axioms reject "difference" (it presupposes "sameness"); both terms are
defined by presence/absence of the distinguishing *act*:

- **distinct** = *pointed-apart* — a **relation of two** (`slash`'s `x ≠ y`
  precondition). 2-ary → NT=2.
- **미분화 / undifferentiated** = *no internal distinction* — a **property of
  one** (`Lens/UndifferentiatedRaw.lean` `constLens_collapses`; seed §6.5
  "point ≡ K_∞ ≡ trivial topology = absence of differentiation"). 1-ary → the 1.

Not two realms: pointing at the undifferentiated 1 makes it a distinct 3rd → the
2↔3 toggle. The 1 is chart-invisible (`G121_dim4_self_pointing_axis`: self-
pointing axis = `dim ker δ⁰` = constant cochains = the non-discriminating
component) — you rotate around it, never land on it.

## FlatOntology — "둘이 다르지 않다" precisely (no separate sorts)

`Lens/FlatOntology.lean` (§9.3): "**One universe — no separate sorts** for
types, objects, relations, Lens. All live in the predicate algebra on Raw^n."

- "둘이 다르지 않다" = *not different in SORT* (one substrate), **not** value-
  identity. Reconciles GRA `distinct_equiv` (2≠3 as *values*) with flat non-
  separation (2,3 same *sort*).
- distinct / 미분화 = *finest / coarsest* predicate (`idLens` / `constLens`,
  the two bookends of `RawTopology.topology_two_bookends`) on ONE substrate.
- residue/1 = the flat substrate + its **self-covering** (`G29_residue` "자기-덮음").

## The self-covering closure — frontier + brick

FlatOntology **defers** the closure direction: "a predicate encoded back as a
Raw via Gödel numbering of its truth table." Status:

- Raw → predicate: trivial (`Object1`). Raw → ℕ: done
  (`Cardinality/Godel.Raw.toNat`, injective).
- **Positive direction ALREADY CLOSED** (repo-first catch — was on `main`):
  `Lens/PredicateSelfEncoding.lean` (7 PURE, commit `10500a4`) encodes every
  *finite-prefix / definable* predicate back to a Raw —
  `predicateToRaw n P = numeral(truthTableNat n …)`,
  `predicate_self_encoding_closure`, `predicateToRaw_kernel`,
  `predicateToRaw_injective_on_prefix`. "predicates are themselves Raw" has a
  constructive witness for the describable case.
- **Honest limit**: a *total* `(Raw→Bool) → Raw` is impossible by Cantor
  (`Cardinality/Cantor.cantor_raw_bool`: no surjection `Raw → (Raw→Bool)`).
- **213-native closure**: Raw embeds *faithfully* as predicates (`Object1`
  injective); definable predicates round-trip (`PredicateSelfEncoding`); but the
  full predicate space does not — the surplus (predicates not definable / not of
  the form `Object1 r`) is exactly the Cantor-unpointable = **the residue**.
  "The self-covering closes exactly up to the residue" — itself the whole-session
  thesis (finite pointing; completed infinity = a finite name; the unpointable
  surplus IS the residue).

**Brick (this session)** — `Lens/FlatOntologyClosure.lean` (6 PURE):
`object1_injective` (faithful self-cover) ∧ `object1_not_surjective` (the residue
surplus, via `cantor_raw_bool`); `self_covering_closure` bundles both.  This is
the *limit* half; `PredicateSelfEncoding` is the *positive* half — together they
frame the residue as the definable/total gap.  (Injective proof uses
`of_decide_eq_true`, NOT `decide_eq_true_eq`, to stay propext-free.)

**The link — residue named** (`undifferentiated`, `undifferentiated_not_object1`,
`residue_witnessed`): the abstract Cantor gap gets a *concrete inhabitant* —
`undifferentiated := fun _ => true`, the predicate that draws no distinction (the
`Raw → Bool` shadow of `constLens`).  Each `Object1 r` is true at exactly one
Raw, so it never equals a predicate true everywhere (≥ 2 Raws, `a ≠ b`).  Thus
the residue is not a bare cardinality surplus: its cleanest member is the
**미분화 / undifferentiated** reading itself — *the one predicate that points at
nothing-in-particular cannot be pointed at as any single Raw.*  This ties the
limit (Cantor) directly to the session's distinct-vs-미분화 axis: distinct = the
pointable (`Object1 r`, finest); 미분화 = the lead inhabitant of the unpointable
residue (`fun _ => true`, coarsest).  `residue_witnessed` bundles
injective + the named witness.

## Follow-up — the open problem answered: TWO closures

`Theory/Raw/Lambek.lean` (6 PURE) separates the two closures the residue/"1"
carries, settling the open question below:

  - `decompose` (Lambek forward `Raw → F(Raw)`): every Raw is `a`, `b`, or
    `slash x y h` — the pointing **act** is a fixed point of its own
    constructor shape `F(X) = {a} ⊎ {b} ⊎ {x/y : x≠y}`.  `rebuild` is the
    round-trip (act applied to its own readout = identity).  **Holds for any
    fixed point of F, finite or not** (μF and νF alike).
  - `depth_drops` + `atoms_are_floor`: each `slash` is strictly deeper than its
    parts and atoms have depth 0 — the **well-founded** measure, no infinite
    descent.  This is the *independent* fact selecting the least fixed point.
  - `two_closures`: bundles both.  **Answer: two, mutually supporting.** Lambek
    (act self-coincidence) gives the rotation-shape; well-foundedness (finite
    pointing) gives the floor; neither implies the other, and `Raw = μF` is
    exactly their conjunction.  So the "1" is not a single fixed point but an
    interlocked pair — the self-fixed-point of the act and the finiteness of
    what it points at.

This matches the originator's two gut-principles that *forced* Raw earlier in
the session: "no before/after → fixed point" (Lambek) and "pointing is finite,
must leave a residue → bottoms out" (well-founded).  They are distinct levers;
Raw is where they coincide.

(Methodology guard added this session: CLAUDE.md failure mode "View promoted to
identity" — a reading is a facet, never the residue itself.)

## File map

- glue/axis: `Lib/Math/Mobius213OneAsGlue.lean`, `…/Mobius213/Px/{MobiusSelfForm,
  CharPolySelf,ConvergentDet,TripartiteK213}.lean`, `Lib/Math/Mobius213.lean`.
- residue def: `Lib/Math/UniverseChain/Residue.lean`, `research-notes/G29_residue.md`.
- 0 vs 1 / Frobenius: `theory/math/foundations/universe_chain.md` (the 1-as-glue /
  axis-generator narrative) + `Lib/Math/Mobius213.lean`.
- flat ontology: `Lens/FlatOntology.lean`, `Lens/RawTopology.lean`,
  `Lens/UndifferentiatedRaw.lean`, `Lens/Cardinality/{Cantor,Godel}.lean`.
- self-pointing axis: `research-notes/G121_dim4_self_pointing_axis.md`.
- ℝ as Lens output: `Lib/Math/Real213/Core/AsLensOutput.lean`, `…/ValidCut.lean`.
