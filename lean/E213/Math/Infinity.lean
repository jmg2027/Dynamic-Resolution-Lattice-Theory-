import E213.Math.Infinity.BoolSpace
import E213.Math.Infinity.Cantor
import E213.Math.Infinity.Chain
import E213.Math.Infinity.Countable
import E213.Math.Infinity.Godel
import E213.Math.Infinity.LensCardinality
import E213.Math.Infinity.Pair
import E213.Math.Infinity.Tower

/-! Spec-as-code entry point for `E213.Math.Infinity`.

  Infinity in 213 — lens cardinality, Cantor (∅-axiom
  inhabitant-absence), Gödel-style fixed points.

  ## Files

    * `LensCardinality` — Σ4: Lens-image cardinalities
    * `Cantor`          — Cantor's theorem: no surjection
                          α → P(α), proved as inhabitant
                          absence under ∅-axiom (no
                          Classical, no propext)
    * `Tower`           — Cantor tower: iterated function spaces
    * `BoolSpace`       — concrete `ℕ → (Raw → Bool)` injection
    * `Countable`       — Raw is at least ℕ-sized
    * `Pair`            — injective pairing `ℕ × ℕ → ℕ`
    * `Godel`           — Σ2: Raw → ℕ injective encoding
    * `Chain`           — chain-space cardinality + R5b
                          reinterpretation
-/
