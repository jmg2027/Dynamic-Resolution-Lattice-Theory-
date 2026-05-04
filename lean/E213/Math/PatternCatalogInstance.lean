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
