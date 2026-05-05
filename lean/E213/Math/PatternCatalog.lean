import E213.Math.CascadeCalculus

/-!
# 213 Pattern Catalog

Initial 4-game survey (2026-05-XX, 970 .lean files): Locality
(`_at`/`_pure`/`_congr`), Aggregation (`*_capstone*`), Typeclass
(`structure`/`class`), Catamorphism (`Raw.fold`/`Raw.rec`).  Two
additions discovered by H1 sweep: Dynamical (FSM cluster), ForcedUniq
(Atomicity cluster).  One composite (Cohabitation) discovered in
AxiomSystems cluster.

H2 (composition rules) work then yielded **two self-corrections**:

  1. **`Aggregation` is not atomic** — it is a higher-order operator
     `Aggregate W : Type` that bundles N witnesses of any other game.
     LocalityAggregate ≡ Aggregate (LocalityWitness Idx Val);
     DynamicalAggregate ≡ Aggregate (DynamicalWitness S Out); etc.

  2. **`ForcedUniq` is not atomic** — it is a higher-order operator
     `Forced T : Type` that asserts uniqueness on type T.  ForcedValue
     Witness Param ≡ Forced Param.  CataForcedForm and
     LocalityForcedValue use Forced lifted by view / by index.

Refined stratification:

  Atomic games (4): Locality | Typeclass | Cata | Dynamical
  Operators (2):    Aggregate W  (bundle)
                    Forced    T  (uniqueness)
  Composites:       Lens             = Typeclass × Cata + compatibility
                    Cohabitation     = Lens × Lens + cohabit witness
                    LocalityAggregate, DynamicalAggregate,
                    InterfaceAggregate, CataAggregate
                    LocalityForcedValue, CataForcedForm,
                    DynamicalForcedPeriod

Each composite has a concrete instance in `PatternCatalogInstance.lean`,
all `#print axioms` ∅-axiom.  The catalog stratifies: codebase patterns
are exactly small Cartesian products of {atomic} × {atomic, Aggregate-,
Forced-of-atomic}, with at most one explicit coherence constraint.

The four original games still compose into the dependency-DAG of
`CascadeCalculus.lean` (Locality ↔ leaves, Aggregation ↔ terminals,
Typeclass ↔ infrastructure, Catamorphism ↔ edges) — that mapping
predates the H2 self-corrections and remains valid at the cascade
level even though Aggregation / ForcedUniq are now operator-level
rather than atomic. -/

namespace E213.Math.PatternCatalog

open E213.Math.CascadeCalculus

/-- **Locality game**: a "global" function `f` plus a pointwise
    witness `f_at` that agrees with `f` at every test point.
    Captures `_at`/`_pure` parallel pattern. -/
structure LocalityWitness (Idx : Type) (Val : Type) where
  f      : Idx → Val
  f_at   : Idx → Val
  agrees : ∀ i, f i = f_at i

/-- **Aggregation game**: a bundle of `n` facts collected as
    Type-level conjunction.  Captures `*_capstone*` pattern.
    Concrete instances use Lean's `∧` directly; this records
    that the bundle has cardinality `n` for cataloging. -/
structure CapstoneBundle where
  arity   : Nat
  /-- Phase tag (e.g., "BA", "BH", "CM") for cross-reference. -/
  phase   : String
  deriving Repr

/-- **Typeclass game**: an interface providing two base values
    and a binary combine.  Captures the Lens `structure` pattern.
    Example instance: `Lens α` itself. -/
structure InterfaceWitness (α : Type) where
  base1   : α
  base2   : α
  combine : α → α → α

/-- **Catamorphism game**: the Raw → α direction.  Encoded as
    a function-shaped data record (no Raw dependency at this
    catalog level).  Concrete instance: `Lens.view`. -/
structure CatamorphismWitness (α : Type) where
  reduce : α → α → α
  base_a : α
  base_b : α
  /-- "View" is the catamorphism itself; abstracted as a
      function from a nat-encoded tree. -/
  view   : Nat → α

/-- **Dynamical game** (5th game, discovered via FSM cluster):
    state evolution over time, eventually periodic.
    Captures `BitFSM`/`ArithFSM`/`Pell`/`Pisano`/`Fib`/`Trib` cluster
    (91 files in `Math/Cohomology/Dyadic/`).

    Time `k : Nat` is a NEW dimension absent from the first four
    games (which were time-less).  213's Finitism principle —
    "infinite ℕ-iteration on a finite state set must cycle" —
    lives here. -/
structure DynamicalWitness (S : Type) (Out : Type) where
  init   : S
  step   : S → S
  output : S → Out
  /-- Evidence of eventual periodicity: there exist `start` and
      `period > 0` s.t. for all `k ≥ start`, output at k = output at
      k + period.  Only the witness shape recorded; concrete proof
      lives in cluster files like `pellFSMmod11_bits_period_10`. -/
  period_witness : Nat × Nat  -- (start, period)

/-- **Forced-Uniqueness game** (6th game, discovered via
    Atomicity cluster).  Captures the `*_iff_value` pattern:
    "the unique X satisfying condition C is V".

    Examples (all in `Firmware/Atomicity/`):
      atomic_iff_five     : Atomic n ↔ n = 5
      atomic_23_iff_five  : Atomic 2 3 n ↔ n = 5
      arity_iff_two       : (cond) ↔ k = 2
      pair_iff_two        : (cond) ↔ p = 2

    This game is 213's **epistemic core**: numbers like
    d=5, NS=3, NT=2, arity=2 are *theorems*, not axioms.
    The Raw axiom doesn't stipulate "5"; uniqueness derivation
    forces it. -/
structure ForcedValueWitness (Param : Type) where
  /-- The forced value. -/
  value     : Param
  /-- Predicate the value satisfies uniquely. -/
  cond      : Param → Prop
  /-- Forced uniqueness: `cond p ↔ p = value`. -/
  forced    : ∀ p, cond p ↔ p = value

/-- **Cohabitation pattern** (composite, NOT a 7th atomic game):
    a single base substrate viewable through *two different*
    Catamorphisms simultaneously, each yielding a distinct value.

    Captures `Math/AxiomSystems/`: same Raw expression validates
    Peano-theorem AND ZFC-theorem AND depth-theorem at once.
    Per Mingu (2026-05-XX):
      "다른 수학 이론들 심지어 공리계라는 것도 렌즈들의 조합인거지"

    Structurally this is **Catamorphism × Catamorphism** plus a
    Forced-Uniqueness witness of cohabitation.  Emergent, not
    primitive.  First sign that the catalog has *composition rules*
    on top of atomic games. -/
structure CohabitationWitness (Base α β : Type) where
  base       : Base
  view_α     : Base → α
  view_β     : Base → β
  expected_α : α
  expected_β : β
  eq_α       : view_α base = expected_α
  eq_β       : view_β base = expected_β

/-- **Lens composite** = `Typeclass × Catamorphism` with field
    compatibility.  An `InterfaceWitness` provides `(base1, base2,
    combine)`; a `CatamorphismWitness` provides `(base_a, base_b,
    reduce, view)`.  The two records share the same shape on
    `(base, base, combine/reduce)`.  When the shapes agree, we have
    a Lens.

    This composite is NOT a 7th atomic game — it is the **canonical
    pairing** of the existing Typeclass and Catamorphism games.  The
    fact that 213's `Lens` is exactly this pairing explains why Lens
    is the central abstraction: it is the smallest non-trivial
    composite the catalog can form.

    With `LensWitness` defined, `CohabitationWitness` can also be
    re-read as `LensWitness × LensWitness + cohabit witness`.
    Composition rules thus stratify: atomic → Lens → Cohabitation. -/
structure LensWitness (α : Type) where
  interface       : InterfaceWitness α
  catamorphism    : CatamorphismWitness α
  base_compat_1   : interface.base1 = catamorphism.base_a
  base_compat_2   : interface.base2 = catamorphism.base_b
  combine_compat  : interface.combine = catamorphism.reduce

/-- **`_capstone_pure` composite** = `Locality × Aggregation`.

    The pattern dominant across `Math/Real213/`: a phase capstone
    that bundles N pointwise (`*_pure` / `*_at`) witnesses into one
    ∧-conjunction, e.g. `polynomial_mvt_unitBracket_capstone_pure`
    (FluxMVTPolynomial, arity 3, phase "BB") whose proof is the anon
    constructor `⟨mvt_id_unitBracket_pure, mvt_square_unitBracket_pure,
    mvt_cube_unitBracket_pure⟩`.

    The composite stores Aggregation's `(phase, arity)` together with
    an indexed family of Locality witnesses — one per conjunct in the
    bundle.  No Fin/List required: the family is a plain
    `Nat → LocalityWitness Idx Val`, with `arity` recording how many
    indices are intended to carry meaning.

    This is the second composition rule (after Lens = Typeclass × Cata)
    and the most populous one in the codebase: ~232 sealed-then-deleted
    capstone facade theorems all instantiated this composite. -/
structure LocalityAggregate (Idx : Type) (Val : Type) where
  /-- Phase tag inherited from Aggregation game. -/
  phase  : String
  /-- Bundle cardinality from Aggregation game. -/
  arity  : Nat
  /-- Indexed family of Locality witnesses. -/
  facts  : Nat → LocalityWitness Idx Val

/-- **Aggregate `W`**: polymorphic bundle generator.

    Adding a third composition rule (Dynamical × Aggregation, evidenced
    by Pisano marathon Type B capstones in `Math/Cohomology/Dyadic/
    Pisano/`) reveals a meta-pattern: `LocalityAggregate` and the
    new `DynamicalAggregate` differ only in the *witness type* they
    bundle.  Both wrap `(phase, arity, Nat → W)` for some atomic-
    game witness `W`.

    Refining the catalog accordingly: **Aggregation is not an atomic
    game on equal footing with the others — it is a higher-order
    operator that lifts any atomic-game witness into a bundle.**
    `LocalityAggregate Idx Val` is exactly `Aggregate (LocalityWitness
    Idx Val)`; `DynamicalAggregate` is `Aggregate (DynamicalWitness
    S Out)`; etc.

    This is the catalog's first self-correction: the original
    `CapstoneBundle` (just `(arity, phase)`) was a degenerate case
    where the bundled content was elided.  `Aggregate W` makes the
    content explicit and parametric. -/
structure Aggregate (W : Type) where
  /-- Phase tag (e.g., "BB", "BU"). -/
  phase  : String
  /-- Bundle cardinality. -/
  arity  : Nat
  /-- Indexed family of underlying witnesses. -/
  facts  : Nat → W

/-- Dynamical × Aggregation as a specialisation of `Aggregate`.
    Anchor specimen: `pisano_predict_realises_pell_N` (Pisano
    marathon Type B), bundling N FSM-period witnesses under one
    capstone. -/
abbrev DynamicalAggregate (S : Type) (Out : Type) :=
  Aggregate (DynamicalWitness S Out)

/-- **Cata × ForcedUniq composite** — `CataForcedForm`.

    Catamorphism view + forcing on view-results + extractor +
    injector + the forcing equation.  Anchor specimen:
    `getBase_eq` (`Firmware/Atomicity/ArityForcingGeneral.lean`):

    ```
    ∀ (x : RawNk N k) (h : isBase x = true), x = .object (getBase x h)
    ```

    Reading: when the catamorphism `isBase` returns `true`, the source
    `x` is forced into the unique form `.object i` for some specific
    `i = getBase x h`.  Forcing is on the *form* (which constructor)
    rather than on a value, distinguishing this from atomic
    `ForcedValueWitness` (value-level forcing).

    These are NOT reducible to each other — atomic ForcedUniq forces
    *which value*; Cata × ForcedUniq forces *which form* given a view
    value.  Different axes. -/
structure CataForcedForm (Source α β : Type) where
  /-- Catamorphism view (from Cata game). -/
  view    : Source → α
  /-- Trigger predicate on view-results (from ForcedUniq game). -/
  trigger : α → Prop
  /-- Witness extractor when trigger fires. -/
  extract : (s : Source) → trigger (view s) → β
  /-- Canonical-form injector. -/
  inject  : β → Source
  /-- The forcing equation: source equals injection of extracted witness. -/
  forced  : ∀ s h, s = inject (extract s h)

/-- **Locality × ForcedUniq composite** — `LocalityForcedValue`.

    At each index `i`, the value is forced unique: there is a per-index
    condition `cond i : Val → Prop` and a `forcedValue i` such that
    only `forcedValue i` satisfies `cond i`.  The locality function
    `f_at` happens to satisfy `cond i (f_at i)` at every index, hence
    `f_at i = forcedValue i` for all i (derivable from `forced` +
    `witness`).

    Distinguishes from atomic ForcedUniq by the *family-of-conditions*
    indexed structure.  Atomic ForcedUniq has one condition; here we
    have `Idx`-many conditions, one per locality index.  Every
    function-eq lemma in cut algebra has this latent shape — the
    "value at (m,k) of cutMul (constCut 1 1) (constCut 1 1)" is forced
    to 1 by the cut-algebra rules at each (m,k). -/
structure LocalityForcedValue (Idx : Type) (Val : Type) where
  /-- The locality witness function. -/
  f_at         : Idx → Val
  /-- Per-index forcing condition. -/
  cond         : Idx → Val → Prop
  /-- Per-index forced unique value. -/
  forcedValue  : Idx → Val
  /-- Forcing: at each index, `cond i v ↔ v = forcedValue i`. -/
  forced       : ∀ i v, cond i v ↔ v = forcedValue i
  /-- Coherence: `f_at` satisfies `cond` at every index. -/
  witness      : ∀ i, cond i (f_at i)

/-- Typeclass × Aggregation = bundle of N interfaces.  Codebase
    candidate: ClassicCalc family (multiple typeclass-style instances
    bundled per phase). -/
abbrev InterfaceAggregate (α : Type) := Aggregate (InterfaceWitness α)

/-- Cata × Aggregation = "fan-out" bundle of N catamorphisms all
    targeting the same `α`.  Differs from Cohabitation in two ways:
    (i) Aggregate has uniform target type; Cohabitation has
    heterogeneous targets (α and β).  (ii) Cata × Aggregate has no
    "shared base" coherence; each catamorphism is an independent
    witness.  So Cohabitation properly generalises Cata × Aggregate
    (heterogeneous targets + base-sharing). -/
abbrev CataAggregate (α : Type) := Aggregate (CatamorphismWitness α)

-- Note: Dynamical × Aggregation = `DynamicalAggregate`, defined above.

/-- **`Forced T`** — second higher-order operator (catalog's second
    self-correction, mirroring `Aggregate W`).

    Three ForcedUniq composites have now appeared:
      atomic ForcedValueWitness  — value-level forcing on `Param`
      LocalityForcedValue        — per-index forcing on `Val`
      CataForcedForm             — form-level forcing given view value

    All three share the same uniqueness *core*:
      `∀ t, cond t ↔ t = witness`.

    Naming this core as a higher-order operator:

      `Forced T := { cond : T → Prop, witness : T,
                     forced : ∀ t, cond t ↔ t = witness }`

    Then `ForcedValueWitness Param ≡ Forced Param`.  `LocalityForced
    Value Idx Val` is `Idx → Forced Val` with a coherent witness
    function.  `CataForcedForm`'s `(extract, inject, forced)` triple
    is `Forced` applied to the form-witness type, lifted by view.

    `Forced` is the *uniqueness* operator; `Aggregate` is the *bundle*
    operator.  Together they explain why so many composites exist:
    each atomic game pair (X, Y) yields composites X × Aggregate-of-Y,
    X × Forced-on-Y, and X × Y direct (Lens, Cohabitation, …). -/
structure Forced (T : Type) where
  /-- Forcing predicate. -/
  cond    : T → Prop
  /-- The forced unique value. -/
  witness : T
  /-- The uniqueness equation. -/
  forced  : ∀ t, cond t ↔ t = witness

/-- Dynamical × ForcedUniq = period uniqueness witness on a dynamical
    system.  Codebase candidate: pisano_predict_correct (the predicted
    period IS the unique valid period for the corresponding FSM at the
    Legendre-derived prime). -/
structure DynamicalForcedPeriod (S : Type) (Out : Type) where
  /-- The dynamical system. -/
  dyn       : DynamicalWitness S Out
  /-- Period uniqueness on `Nat`. -/
  forcedNat : Forced Nat
  /-- Coherence: the forced witness is exactly the dyn's period. -/
  agree     : forcedNat.witness = dyn.period_witness.2

/-! ## Operator composition (C4)

`Aggregate W` and `Forced T` are the two higher-order operators.
Question: do they commute, i.e. is `Aggregate (Forced T)` the same
as `Forced (Aggregate W)`?

  `AggregateForced T` = bundle of N independent uniqueness witnesses
  `ForcedAggregate W` = unique bundle satisfying some condition

These are NOT isomorphic.  An aggregate-of-foreds carries N separate
(cond, witness, forced) triples; a forced-aggregate carries one
condition on the entire bundle.  Different content, different shape.

What does hold: a *diagonal* lift sends `Forced T → AggregateForced T`
by repeating the same witness across all indices.  The reverse
direction collapses only when all facts agree (a witness, not a
theorem of the abbreviations themselves).
-/

abbrev AggregateForced (T : Type) := Aggregate (Forced T)
abbrev ForcedAggregate (W : Type) := Forced (Aggregate W)

/-- Diagonal lift: a single `Forced T` becomes a constant
    `AggregateForced T` at any arity. -/
def AggregateForced.diagonal {T : Type} (f : Forced T)
    (n : Nat) (φ : String) : AggregateForced T :=
  { phase := φ, arity := n, facts := fun _ => f }

/-! ## Operator self-composition

Q: Is `Aggregate (Aggregate W)` reducible to `Aggregate W`?
   Is `Forced (Forced T)`     reducible to `Forced T`?

Empirically, neither is idempotent at the type level (the structures
are formally different).  However:

  - `Aggregate` admits a **flatten**: `Aggregate (Aggregate W)` can be
    collapsed to `Aggregate W` by reading off the *first inner bundle*
    and discarding the rest.  More faithful flattenings (e.g.
    concatenation) require summing arities; we record the simplest
    canonical projection here.

  - `Forced (Forced T)` does NOT admit a clean reduction.  It carries
    the additional content "which Forced-T statement we mean", which
    the inner Forced T does not.  This asymmetry mirrors the
    Aggregate-vs-Forced non-commutativity from C4.

Together these show: **the catalog operators are not idempotent.**
Self-composition produces strictly richer types. -/

/-- Project an `Aggregate (Aggregate W)` onto its first inner bundle.
    Loses information about the other bundles; this is a witness of
    *non-idempotence*, not a flatten morphism. -/
def Aggregate.firstInner {W : Type} (a : Aggregate (Aggregate W)) :
    Aggregate W :=
  a.facts 0

end E213.Math.PatternCatalog
