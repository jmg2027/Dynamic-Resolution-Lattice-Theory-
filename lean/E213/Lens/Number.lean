import E213.Lens.Number.Nat213
import E213.Lens.Number.Int213

/-! Spec-as-code entry point for `E213.Lens.Number`.

  Number — Raw-derived number systems realised as Lens-layer
  catamorphism outputs.  Per ARCHITECTURE.md: Raw +
  a specific catamorphism choice = a Lens-layer artifact.

  ## Sub-clusters

    * `Nat213/`    — 213-native positive naturals (Method A Raw chain
                     + inductive Peano + bridge + Lenses /
                     AtomicityCorrespondence / NumberingSystem /
                     RawCut / Tower).
    * `Int213/`    — ℤ via Raw's signed Lens `⟨1, -1, +⟩` — same
                     Raw, different Lens.  Integers emerge in the
                     Lens codomain (`Int`) rather than as a new
                     type.  Negation is `Raw.swap`.
    * `SharedUnitAcrossReadings`
                   — the honest unification of the axis-readings:
                     the unit `1` is one value across count-difference
                     (`NS − NT`), the Möbius/ratio determinant, the
                     Cassini oscillation, and the reciprocal law.  One
                     orbit, many readings, one unit — not an operator
                     monoid.

  ## Future

    * `Rat213/`    — ℚ via multiplicative quotient (currently
                     prototyped in `Nat213/Tower/NatPairToQPos`).
    * `Real213/`   — ℝ via cuts / Cauchy seqs over Nat213
                     (currently in `Lib/Math/Real213`; candidate for
                     migration once mature).
-/
