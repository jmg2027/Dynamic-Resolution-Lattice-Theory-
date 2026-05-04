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

end E213.Math.PatternCatalog
