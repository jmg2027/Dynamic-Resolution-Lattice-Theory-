import E213.Lens.Number.Nat213

/-! Spec-as-code entry point for `E213.Lens.Number`.

  Number — Raw-derived number systems realised as Lens-layer
  catamorphism outputs.  Per ARCHITECTURE.md (2026-05-13): Raw +
  a specific catamorphism choice = a Lens-layer artifact.

  ## Sub-clusters

    * `Nat213/`    — 213-native positive naturals (Method A Raw chain
                     + inductive Peano + bridge + Lenses /
                     AtomicityCorrespondence / NumberingSystem /
                     RawCut / Tower).

  ## Future

    * `Int213/`    — ℤ built from Nat213 via additive-axis quotient.
    * `Rat213/`    — ℚ via multiplicative quotient (currently
                     prototyped in `Nat213/Tower/NatPairToQPos`).
    * `Real213/`   — ℝ via cuts / Cauchy seqs over Nat213
                     (currently in `Lib/Math/Real213`; candidate for
                     migration once mature).
-/
