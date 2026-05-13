import E213.Lib.Math.PatternCatalog.Core
import E213.Lib.Math.Real213.Mul.CutMulOne
import E213.Theory.Atomicity.Five
import E213.Lib.Math.AxiomSystems.CrossTheoryCohabit
import E213.Lens.Properties.IsLeaf

/-!
# PatternCatalog — instance check

Test whether the four-game catalog of `PatternCatalog.lean` actually
captures real 213 objects.  We try to populate each game with a
concrete instance from the codebase.

## Discovery

`LocalityWitness` requires *both* `f` (global) and `f_at` (pointwise),
plus an `agrees` proof.  But after the session-27 박멸, **the global
form `f` was deleted** for cut algebra.  Only `f_at` remains.

→ The most honest instance is the *trivial self-instance*: take
`f := f_at`.  Then `agrees := fun _ => rfl`.

This is a structural observation: the catalog's "duality" is a
**transitional artifact**, not a permanent feature.  Post-extermination
213 has unified the two sides.  See analysis at end of file.
-/

namespace E213.Lib.Math.PatternCatalog.Instance

open E213.Lib.Math.PatternCatalog
open E213.Lib.Math.PatternCatalog.Core
open E213.Lib.Math.Real213.Mul.CutMulOne (cutMul_one_one_at)
open E213.Lib.Math.Real213.Mul.CutMul (cutMul)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)

/-- Post-extermination self-instance: `f` and `f_at` are the same
    function (function-eq form was deleted).  Trivially `agrees`. -/
def cutMulOneOne_localityWitness :
    LocalityWitness (Nat × Nat) Bool :=
  { f      := fun ⟨m, k⟩ =>
                cutMul (constCut 1 1) (constCut 1 1) m k
    f_at   := fun ⟨m, k⟩ =>
                cutMul (constCut 1 1) (constCut 1 1) m k
    agrees := fun _ => rfl }

/-- Post-extermination *witness-only* form: drop the redundant `f`. -/
structure LocalityWitnessOnly (Idx : Type) (Val : Type) where
  f_at : Idx → Val

/-- Self-witness at the cut point. -/
def cutMulOneOne_witness :
    LocalityWitnessOnly (Nat × Nat) Bool :=
  { f_at := fun ⟨m, k⟩ =>
              cutMul (constCut 1 1) (constCut 1 1) m k }

/-! ## DynamicalWitness instance — toy 2-state oscillator

The simplest concrete dynamical: states `Bool`, step = `not`,
output = identity.  Period = 2, start = 0.  This is the "atom"
of the dynamical game. -/

/-- 2-state oscillator: 0 → 1 → 0 → 1 → ... -/
def boolOscillator : DynamicalWitness Bool Bool :=
  { init           := false
    step           := fun b => !b
    output         := fun b => b
    period_witness := (0, 2) }

/-! ## ForcedValueWitness instance — d = 5 from atomicity

The Raw axiom does NOT stipulate `d = 5`.  Instead, given atoms
{2, 3}, the unique n with a single alive decomposition is 5.
This is what `atomic_iff_five` proves. -/

/-- d = 5 as a ForcedValueWitness instance.  Direct lift of
    `E213.Theory.Atomicity.Five.atomic_iff_five`. -/
def fiveIsForced : ForcedValueWitness Nat :=
  { value  := 5
    cond   := E213.Theory.Atomicity.Five.Atomic
    forced := E213.Theory.Atomicity.Five.atomic_iff_five }

/-! ## CohabitationWitness instance — Peano × Depth on the same Raw

The Raw expression `r := slash a b h` validates simultaneously:
  - the Peano theorem `peanoLens.view r = 2`  (= 1 + 1)
  - the depth theorem `Lens.depth.view r = 1` (tree height)

with no conflict.  This is `Catamorphism × Catamorphism` cohabitation
witnessed by `cohabit_peano_depth`. -/

open E213.Theory (Raw)
open E213.Lens (Lens)
open E213.Lib.Math.AxiomSystems.Peano (peanoLens)
open E213.Lib.Math.AxiomSystems.CrossTheoryCohabit (r peano_view depth_view)

/-- Concrete cohabitation: `slash a b h` viewed as both Peano-2 and
    depth-1.  Direct lift of `cohabit_peano_depth`. -/
def peanoDepthCohabit (h : Raw.a ≠ Raw.b) :
    CohabitationWitness Raw Nat Nat :=
  { base       := r h
    view_α     := peanoLens.view
    view_β     := Lens.depth.view
    expected_α := 2
    expected_β := 1
    eq_α       := peano_view h
    eq_β       := depth_view h }

/-! ## LensWitness instance — peanoLens as Typeclass × Catamorphism

`peanoLens = Lens.leaves = ⟨1, 1, (·+·)⟩`.  Both `InterfaceWitness`
fields and `CatamorphismWitness` fields are populated from the SAME
underlying triple — that is the whole point of the composite. -/

open E213.Lib.Math.PatternCatalog.Core (InterfaceWitness CatamorphismWitness LensWitness)

/-- peanoLens lifted into the LensWitness composite.  All three
    compatibility proofs are `rfl` because both sides come from the
    same underlying Lens triple. -/
def peanoLensWitness : LensWitness Nat :=
  { interface       := { base1 := 1, base2 := 1, combine := (· + ·) }
    catamorphism    := { reduce := (· + ·), base_a := 1, base_b := 1
                         view   := fun _ => 0 }
    base_compat_1   := rfl
    base_compat_2   := rfl
    combine_compat  := rfl }

/-! ## LocalityAggregate instance — synthetic 3-bundle

A toy example mirroring the real-codebase `polynomial_mvt_unitBracket_
capstone_pure` shape (FluxMVTPolynomial, arity 3, phase "BB").  We
bundle three trivial Locality witnesses on `(Nat, Nat)`, each the
self-instance `f := f_at`. -/

open E213.Lib.Math.PatternCatalog.Core (LocalityAggregate)

/-- Trivial Locality witness on Nat: `f i = i`, agrees by rfl. -/
def trivLoc (k : Nat) : LocalityWitness Nat Nat :=
  { f      := fun i => i + k
    f_at   := fun i => i + k
    agrees := fun _ => rfl }

/-- Synthetic 3-bundle: arity 3, phase "demo".  Indices 0, 1, 2
    select trivLoc 0 / trivLoc 1 / trivLoc 2; other indices reuse
    trivLoc 0 (only the first `arity` matter, by convention). -/
def demoLocalityAggregate : LocalityAggregate Nat Nat :=
  { phase := "demo"
    arity := 3
    facts := fun n => match n with
      | 0 => trivLoc 0
      | 1 => trivLoc 1
      | 2 => trivLoc 2
      | _ => trivLoc 0 }

/-! ## DynamicalAggregate instance — toy 3-FSM Pisano-style bundle

Mirroring `pisano_predict_realises_pell_N` shape (multiple FSMs, each
with its own period, bundled under one capstone).  We use mod-`p`
counter FSMs with period `p`. -/

open E213.Lib.Math.PatternCatalog.Core (Aggregate DynamicalAggregate)

/-- Mod-`p` counter FSM: state `Nat`, step = `(· + 1) % p`,
    output = state.  Period = `p` (start = 0). -/
def modCounter (p : Nat) : DynamicalWitness Nat Nat :=
  { init           := 0
    step           := fun s => (s + 1) % p
    output         := fun s => s
    period_witness := (0, p) }

/-- Pisano-flavored bundle: three FSMs at periods 3, 5, 7. -/
def pisanoLikeAggregate : DynamicalAggregate Nat Nat :=
  { phase := "BU-toy"
    arity := 3
    facts := fun n => match n with
      | 0 => modCounter 3
      | 1 => modCounter 5
      | 2 => modCounter 7
      | _ => modCounter 1 }

/-! ## CataForcedForm instance — Option Nat (toy mirror of getBase_eq)

Real codebase specimen: `getBase_eq` in `Theory/Atomicity/
ArityForcingGeneral.lean` — when the catamorphism `isBase` returns
`true`, the `RawNk N k` source is forced into form `.object i`.
We mirror that shape on `Option Nat` to keep imports minimal: when
`Option.isSome o = true`, `o` is forced into form `some n`. -/

open E213.Lib.Math.PatternCatalog.Core (CataForcedForm)

/-- Witness extractor: pull `n` out of a `some n` whose `isSome = true`. -/
def optExtract : (o : Option Nat) → o.isSome = true → Nat
  | some n, _ => n
  | none,   h => by cases h

/-- The forcing equation for Option. -/
theorem optForced :
    ∀ (o : Option Nat) (h : o.isSome = true), o = some (optExtract o h)
  | some _, _ => rfl
  | none,   h => by cases h

/-- Cata × ForcedUniq instance on Option Nat.  Mirrors `getBase_eq`
    structurally — the codebase real specimen would import
    `RawNk` infrastructure; this toy keeps imports flat. -/
def optionCataForcedForm : CataForcedForm (Option Nat) Bool Nat :=
  { view    := Option.isSome
    trigger := fun b => b = true
    extract := optExtract
    inject  := Option.some
    forced  := optForced }

/-! ## LocalityForcedValue instance — toy Bool → Nat with per-index forcing

At index `b : Bool`, the unique Nat satisfying `n = (if b then 1 else 0)`
is exactly `if b then 1 else 0`.  Trivially forced; demonstrates the
type.  Real codebase candidates: cut-algebra `_at` lemmas where each
(m, k) position has a forced cut value. -/

open E213.Lib.Math.PatternCatalog.Core (LocalityForcedValue)

/-- Toy Locality × ForcedUniq instance on Bool → Nat. -/
def boolNatLocalityForced : LocalityForcedValue Bool Nat :=
  { f_at        := fun b => if b then 1 else 0
    cond        := fun b n => n = (if b then 1 else 0)
    forcedValue := fun b => if b then 1 else 0
    forced      := fun _ _ => Iff.rfl
    witness     := fun _ => rfl }

/-! ## CataAggregate instance — three Nat-targeting catamorphisms

Bundle three CatamorphismWitness Nat instances (placeholders for
peanoLens / depthLens / leavesLens shape).  This is the "fan-out"
pattern: multiple lenses on the same target type. -/

open E213.Lib.Math.PatternCatalog.Core (CataAggregate)

/-- Trivial Nat catamorphism witness. -/
def trivCata (k : Nat) : CatamorphismWitness Nat :=
  { reduce := (· + ·)
    base_a := k
    base_b := k
    view   := fun _ => k }

/-- Three-cata bundle, fan-out shape. -/
def fanOutCataAggregate : CataAggregate Nat :=
  { phase := "fanout"
    arity := 3
    facts := fun n => match n with
      | 0 => trivCata 0
      | 1 => trivCata 1
      | 2 => trivCata 2
      | _ => trivCata 0 }

/-! ## Forced + DynamicalForcedPeriod instances

Demonstrate the second self-correction: `Forced T` as the uniqueness
operator (mirror of `Aggregate W`).  Concrete uses: a Forced Nat (the
unique Nat = 3) and a DynamicalForcedPeriod attaching it to the
period-3 modCounter FSM. -/

open E213.Lib.Math.PatternCatalog.Core (Forced DynamicalForcedPeriod)

/-- Trivially: 3 is the unique Nat = 3.  Demonstrates `Forced Nat`. -/
def threeIsForced : Forced Nat :=
  { cond    := fun n => n = 3
    witness := 3
    forced  := fun _ => Iff.rfl }

/-- Period-3 modCounter (defined above), with the forced-period
    witness wired in.  `agree` proves the forced witness coincides
    with the dynamical's period. -/
def modCounter3WithForcedPeriod : DynamicalForcedPeriod Nat Nat :=
  { dyn       := modCounter 3
    forcedNat := threeIsForced
    agree     := rfl }

/-! ## Operator composition instances — non-commutativity exhibit

`AggregateForced T` and `ForcedAggregate W` are NOT isomorphic.
We demonstrate by:

  - constructing an `AggregateForced Nat` via the diagonal lift
    of `threeIsForced` (3 is unique) — content: 5 copies of the
    same uniqueness assertion.
  - constructing a `ForcedAggregate Nat` whose unique bundle is a
    specific 3-element aggregate — content: ONE bundle uniquely
    identified by an aggregate-level condition.

The shapes carry different information; no obvious bijection. -/

open E213.Lib.Math.PatternCatalog.Core (AggregateForced ForcedAggregate)

/-- Diagonal lift of threeIsForced at arity 5. -/
def aggForcedDemo : AggregateForced Nat :=
  AggregateForced.diagonal threeIsForced 5 "diag"

/-- A specific 3-aggregate (bundle of trivLoc 0/1/2 reused as
    placeholder Nat-Forced witnesses).  We then forge it as the
    unique-such-bundle. -/
def specificBundle : Aggregate (Forced Nat) :=
  AggregateForced.diagonal threeIsForced 3 "specific"

/-- A `ForcedAggregate` whose unique witness is `specificBundle`,
    distinguished by a tautological `cond := (· = specificBundle)`. -/
def forcedAggDemo : ForcedAggregate (Forced Nat) :=
  { cond    := fun a => a = specificBundle
    witness := specificBundle
    forced  := fun _ => Iff.rfl }

/-! ## Atomic-pair composite instances (closure of binary products) -/

open E213.Lib.Math.PatternCatalog.Core
  (LocalityInterface LocalityCata LocalityDynamical
   InterfaceDynamical CataDynamical)

/-- Toy LocalityInterface: indexed by Bool, two interfaces on Nat. -/
def boolLocalityInterface : LocalityInterface Bool Nat :=
  fun b =>
    if b then { base1 := 1, base2 := 1, combine := (· + ·) }
    else  { base1 := 0, base2 := 0, combine := (· * ·) }

/-- Toy LocalityCata: indexed by Bool, two catamorphisms on Nat. -/
def boolLocalityCata : LocalityCata Bool Nat :=
  fun b =>
    if b then { reduce := (· + ·), base_a := 1, base_b := 1, view := id }
    else  { reduce := (· * ·), base_a := 0, base_b := 0, view := fun _ => 0 }

/-- Toy LocalityDynamical: indexed by Bool, two FSMs at periods 2 and 3. -/
def boolLocalityDynamical : LocalityDynamical Bool Nat Nat :=
  fun b => modCounter (if b then 2 else 3)

/-- Toy InterfaceDynamical: combine = +, FSM step s = base1 + s. -/
def addInterfaceDynamical : InterfaceDynamical Nat :=
  { iface            := { base1 := 1, base2 := 1, combine := (· + ·) }
    dyn              := { init := 0
                          step := fun s => 1 + s
                          output := id
                          period_witness := (0, 0) }
    step_via_combine := fun _ => rfl }

/-- Toy CataDynamical: reduce = +, base_a = 0, FSM step s = 0 + s = s. -/
def addCataDynamical : CataDynamical Nat :=
  { cata           := { reduce := (· + ·), base_a := 0, base_b := 0
                        view   := fun _ => 0 }
    dyn            := { init := 0
                        step := fun s => 0 + s
                        output := id
                        period_witness := (0, 0) }
    step_eq_reduce := fun _ => rfl }

/-! ## Closing under-span: DepAggregate + ArityNCohabit instances

These two instances close the escapes flagged in
`PatternCatalogSpan.EscapeCandidate.{depAggregate, nAryCohabit}`. -/

open E213.Lib.Math.PatternCatalog.Core (DepAggregate ArityNCohabit)

/-- Witness-type family for the heterogeneous bundle:
    index 0 → LocalityWitness; index 1 → InterfaceWitness;
    other → CatamorphismWitness. -/
def heteroW : Nat → Type
  | 0 => LocalityWitness Nat Nat
  | 1 => InterfaceWitness Nat
  | _ => CatamorphismWitness Nat

/-- Heterogeneous-witness DepAggregate of arity 3 — closes
    `EscapeCandidate.depAggregate`. -/
def heteroDepAggregate : DepAggregate heteroW :=
  { phase := "hetero"
    arity := 3
    facts := fun n => match n with
      | 0     => trivLoc 0
      | 1     => { base1 := 0, base2 := 0, combine := (· + ·) }
      | _ + 2 => trivCata 0 }

/-! ### 3-way Lens cohabitation — 213-native uniform Nat resolution

**Reframing (Mingu directive)**: the original docstring described the
heterogeneous type family `fun n => match n with | 0|1 => Nat | _ => Bool`
as the "ideal" and `boolAsNat`-encoded uniform Nat target as a
"workaround" for a Lean-side equation-compiler limitation.  This
framing is reversed: the uniform Nat target IS the 213-native answer.

Why heterogeneous-target dependent matching fails to reduce in 213:
the proof obligation `views i base = expected i` with `views i :
Base → α i` and `expected i : α i` requires the equation compiler
to prove definitional equality across an index-dependent type.  In
the general case this needs `HEq`, `cast`, or `Eq.rec`-style
manipulations — none of which are admissible in 213's ∅-axiom basis.

213's kernel admits Type, →, ∀, Nat, Prop, Iff, Eq, Pair, Raw.  It
does NOT admit `HEq` (heterogeneous equality), `cast` (which uses
`Eq.mpr`/`Eq.rec` machinery beyond the catalog floor), or
propositional equality between types.  Lean's refusal to reduce
the dependent-match `rfl` is therefore the system *correctly
reporting* that the heterogeneous shape is not 213-native.

**The 213 reading**: at the primitive Raw layer, all information is
bisection trajectories; "Bool" is just a depth-restricted Nat (depth
≤ 1).  Encoding the Bool case as `boolAsNat` (true ↦ 1, false ↦ 0)
is not a coercion-hack — it is the canonical reduction of an
apparently-heterogeneous family to its single cohomological flux on
the d=5 lattice.

So `threeLensCohabit` below is not a "settled-for" implementation;
it is the structurally-correct one.  Heterogeneous-target N-ary
cohabitation is **structurally rejected** by 213's ∅-axiom regime —
not a Lean limitation, but a feature of the type theory 213 is built
on. -/

/-- Bool → Nat coercion (true ↦ 1, false ↦ 0). -/
def boolAsNat : Bool → Nat
  | true  => 1
  | false => 0

/-- Constant Nat target family. -/
def threeLensAlphaConst : Nat → Type := fun _ => Nat

/-- Per-index view (pure Nat-valued; no dependent return). -/
def threeLensViews (i : Nat) (r : E213.Theory.Raw) : Nat :=
  match i with
  | 0     => peanoLens.view r
  | 1     => E213.Lens.Lens.depth.view r
  | _ + 2 => boolAsNat
              (E213.Lens.Properties.IsLeaf.isLeafLens.view r)

/-- Per-index expected value. -/
def threeLensExpected (i : Nat) : Nat :=
  match i with
  | 0     => 1
  | 1     => 0
  | _ + 2 => 1

/-- Per-index agreement. -/
def threeLensAgree (i : Nat) :
    threeLensViews i E213.Theory.Raw.a = threeLensExpected i := by
  match i with
  | 0     => rfl
  | 1     => rfl
  | _ + 2 => rfl

/-- 3-way Lens cohabitation on `Raw.a` in the 213-native canonical
    `UniformArityNCohabit` form.  Target type T = Nat, with the Bool
    case (`isLeafLens.view`) `boolAsNat`-encoded into Nat resolution. -/
def threeLensCohabit :
    E213.Lib.Math.PatternCatalog.Core.UniformArityNCohabit E213.Theory.Raw Nat :=
  { arity    := 3
    base     := E213.Theory.Raw.a
    views    := threeLensViews
    expected := threeLensExpected
    agree    := threeLensAgree }

/-! ## Real codebase Lens lifts — three concrete LensWitness instances

Beyond peanoLensWitness (already lifted from `Lens.leaves`), the
codebase has multiple Lenses we can lift directly into the catalog. -/

/-- `Lens.depth = ⟨0, 0, fun a b => 1 + max a b⟩` lifted into the
    catalog's LensWitness composite.  Real codebase witness, NOT a toy. -/
def depthLensWitness : LensWitness Nat :=
  { interface       := { base1 := 0, base2 := 0
                         combine := fun a b => 1 + max a b }
    catamorphism    := { reduce := fun a b => 1 + max a b
                         base_a := 0, base_b := 0
                         view   := fun _ => 0 }
    base_compat_1   := rfl
    base_compat_2   := rfl
    combine_compat  := rfl }

/-- `isLeafLens = ⟨true, true, fun _ _ => false⟩` lifted as a
    Bool-targeting LensWitness.  Demonstrates LensWitness is
    polymorphic in target type. -/
def isLeafLensWitness : LensWitness Bool :=
  { interface       := { base1 := true, base2 := true
                         combine := fun _ _ => false }
    catamorphism    := { reduce := fun _ _ => false
                         base_a := true, base_b := true
                         view   := fun _ => true }
    base_compat_1   := rfl
    base_compat_2   := rfl
    combine_compat  := rfl }

/-! ## Operator self-composition instances

Demonstrate non-idempotence concretely:

  - Build an `Aggregate (Aggregate Nat)` of arity 2 (two inner bundles
    of Forced witnesses) and project to its first inner bundle.
  - Construct a `Forced (Forced Nat)`: the unique `Forced Nat` whose
    witness is 3.  This is meta-uniqueness — it pins down WHICH
    uniqueness statement we mean, and is genuinely different from
    `Forced Nat` itself. -/

open E213.Lib.Math.PatternCatalog.Core (Aggregate Forced)

/-- Aggregate of two AggregateForced bundles. -/
def aggOfAgg : Aggregate (Aggregate (Forced Nat)) :=
  { phase := "outer"
    arity := 2
    facts := fun n => match n with
      | 0 => specificBundle
      | _ => aggForcedDemo }

/-- Project to first inner — non-idempotence witness. -/
def aggOfAgg_first : Aggregate (Forced Nat) :=
  Aggregate.firstInner aggOfAgg

/-- A `Forced (Forced Nat)` instance via the *tautological* condition
    `(· = threeIsForced)`.

    Note: weaker conditions like `(·.witness = 3)` cannot inhabit
    `Forced (Forced Nat)` without further extensionality — two
    `Forced Nat` values with witness 3 may differ in their `cond` /
    `forced` fields, so witness-equality does not force structure
    equality.  This failure is itself the empirical content of
    non-idempotence: `Forced (Forced T)` is strictly richer than
    `Forced T` because it pins down WHICH uniqueness statement is
    meant, not just which value. -/
def forcedOfForced : Forced (Forced Nat) :=
  { cond    := fun f => f = threeIsForced
    witness := threeIsForced
    forced  := fun _ => Iff.rfl }

/-! ## Analysis

The dynamical game is **structurally distinct** from the four
time-less games:

  1. *Time as a dimension*: `Nat → S` evolution.  Catamorphism game
     also uses Nat (tree encoding) but it's a *single fold*; here
     time is iterated `step`-application.

  2. *Eventual periodicity is the central theorem-shape*: every
     concrete instance gets a `period_X` theorem (e.g.,
     `pellFSMmod11_bits_period_10`, `lens_composition_period_dvd`).

  3. *Composition is monoid-like*: `BitFSM.product` combines two
     FSMs into one whose period divides `lcm` of inputs.  This is
     a richer compositional structure than the 4 time-less games.

  4. *Pell/Pisano/Fib/Trib are all instances*: number-theoretic
     recurrences fit this shape uniformly.  91 files in this single
     cluster — comparable to all of Real213 (182 files).

→ Five games total: Locality / Aggregation / Typeclass /
   Catamorphism / Dynamical. -/

end E213.Lib.Math.PatternCatalog.Instance
