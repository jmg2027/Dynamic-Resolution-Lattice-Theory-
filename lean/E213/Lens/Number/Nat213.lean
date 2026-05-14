import E213.Lens.Number.Nat213.AtomicityCorrespondence
import E213.Lens.Number.Nat213.Bridge
import E213.Lens.Number.Nat213.Lenses
import E213.Lens.Number.Nat213.NumberingSystem
import E213.Lens.Number.Nat213.Peano
import E213.Lens.Number.Nat213.Raw
import E213.Lens.Number.Nat213.RawCut
import E213.Lens.Number.Nat213.Tower.NatPairToQPos

/-! Spec-as-code entry point for `E213.Lens.Number.Nat213`.

  Nat213 — the 213-native positive naturals.  Two equivalent
  representations + their bridge + lens characterizations:

  ## Sub-modules

    * `Raw`              — Method A Raw chain (canonical Raw-derived;
                           `Raw.fold one one add` closed-codomain
                           catamorphism).  `one := Raw.a`,
                           `succ n := slashOrSelf n Raw.b`.
    * `Peano`            — standalone inductive `Nat213 | one | succ`.
                           Ergonomic Peano representation.
    * `Bridge`           — `toRaw : Peano.Nat213 → Raw` isomorphism;
                           add/mul homomorphism; `value`/`leavesCountRaw`
                           commute with `toNat`.
    * `Lenses`           — characterization of `Raw → Peano.Nat213`
                           lenses; multiplicity, swap-invariance.
    * `AtomicityCorrespondence`
                         — atomicity 2 + 3 = 5 realised at
                           type-signature level.
    * `NumberingSystem`  — meta pattern over `(Z, C)` choices; Method A
                           as canonical numbering.
    * `RawCut`           — Lean-free cut prototype on
                           `Raw → Raw → Raw`; vertical projection
                           parallel to `leavesCountRaw` / `booleanProj`.
    * `Tower/NatPairToQPos`
                         — ℚ₊ via multiplicative quotient on
                           `(Peano.Nat213 × Peano.Nat213)`.

  All theorems ∅-axiom.
-/
