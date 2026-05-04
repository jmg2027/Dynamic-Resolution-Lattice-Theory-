import E213.Math.CascadeCalculus

/-!
# 213 Pattern Catalog

The 213 codebase exhibits four dominant *language games*.  Survey
counts (2026-05-XX, 970 .lean files):

  | Game           | Marker                  | Frequency        |
  |----------------|-------------------------|------------------|
  | Locality       | `_at`/`_pure`/`_congr`  | 123 + 57 thms,   |
  |                |                         | 25 files         |
  | Aggregation    | `*_capstone*`           | 171 thms         |
  | Typeclass      | `structure`/`class`     | 72 + 7 decls     |
  | Catamorphism   | `Raw.fold`/`Raw.rec`    | 259 use sites    |

This file abstracts each game as a typeclass-style structure,
providing the *meta-vocabulary* for talking about 213 codebase
patterns inside 213 itself.

The four games are not orthogonal: they compose into the
**dependency-DAG / cascade-delete calculus** of `CascadeCalculus.lean`:

  - Locality nodes        ↔ leaf nodes      (most-imported)
  - Aggregation nodes     ↔ terminal nodes  (consumer-free)
  - Typeclass nodes       ↔ infrastructure  (provide fields)
  - Catamorphism morphism ↔ edges           (Raw → α direction)
-/

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

end E213.Math.PatternCatalog
