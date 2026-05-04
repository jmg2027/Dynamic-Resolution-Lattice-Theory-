import E213.Math.PatternCatalog
import E213.Math.Real213.CutMulOne
import E213.Firmware.Atomicity.Five
import E213.Math.AxiomSystems.CrossTheoryCohabit

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

namespace E213.Math.PatternCatalogInstance

open E213.Math.PatternCatalog
open E213.Math.Real213.CutMulOne (cutMul_one_one_at)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutSumTest (constCut)

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
    `E213.Firmware.Atomicity.Five.atomic_iff_five`. -/
def fiveIsForced : ForcedValueWitness Nat :=
  { value  := 5
    cond   := E213.Firmware.Atomicity.Five.Atomic
    forced := E213.Firmware.Atomicity.Five.atomic_iff_five }

/-! ## CohabitationWitness instance — Peano × Depth on the same Raw

The Raw expression `r := slash a b h` validates simultaneously:
  - the Peano theorem `peanoLens.view r = 2`  (= 1 + 1)
  - the depth theorem `Lens.depth.view r = 1` (tree height)

with no conflict.  This is `Catamorphism × Catamorphism` cohabitation
witnessed by `cohabit_peano_depth`. -/

open E213.Firmware (Raw)
open E213.Hypervisor (Lens)
open E213.Math.AxiomSystems.Peano (peanoLens)
open E213.Math.AxiomSystems.CrossTheoryCohabit (r peano_view depth_view)

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

open E213.Math.PatternCatalog (InterfaceWitness CatamorphismWitness LensWitness)

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

open E213.Math.PatternCatalog (LocalityAggregate)

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

open E213.Math.PatternCatalog (Aggregate DynamicalAggregate)

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

Real codebase specimen: `getBase_eq` in `Firmware/Atomicity/
ArityForcingGeneral.lean` — when the catamorphism `isBase` returns
`true`, the `RawNk N k` source is forced into form `.object i`.
We mirror that shape on `Option Nat` to keep imports minimal: when
`Option.isSome o = true`, `o` is forced into form `some n`. -/

open E213.Math.PatternCatalog (CataForcedForm)

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

open E213.Math.PatternCatalog (LocalityForcedValue)

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

open E213.Math.PatternCatalog (CataAggregate)

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

open E213.Math.PatternCatalog (Forced DynamicalForcedPeriod)

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

end E213.Math.PatternCatalogInstance
