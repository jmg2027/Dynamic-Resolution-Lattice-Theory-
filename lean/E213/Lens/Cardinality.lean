import E213.Lens.Cardinality.BoolSpace
import E213.Lens.Cardinality.Cantor
import E213.Lens.Cardinality.CardinalityLB
import E213.Lens.Cardinality.Chain
import E213.Lens.Cardinality.Countable
import E213.Lens.Cardinality.Godel
import E213.Lens.Cardinality.LensCardinality
import E213.Lens.Cardinality.Pair
import E213.Lens.Cardinality.Tower

/-! Spec-as-code entry point for `E213.Lens.Cardinality`.

  Lens-ring cardinality cluster — cardinality observables produced
  by Lens on Raw.

  Raw is the substrate; Lens views project Raw → observable.
  Cardinality of these projections (and of Raw itself) is a Lens
  observable, hence lives in the Lens ring.

  ## Files

    * `Cantor`          — Cantor's theorem: no surjection α → P(α),
                          ∅-axiom inhabitant-absence formulation
    * `Tower`           — Cantor tower (iterated function spaces)
    * `BoolSpace`       — concrete `ℕ → (Raw → Bool)` injection
    * `Countable`       — Raw ≥ ℕ
    * `Pair`            — injective pairing `ℕ × ℕ → ℕ`
    * `Godel`           — Σ2: Raw → ℕ injective encoding
    * `Chain`           — chain-space cardinality + R5b reinterpretation
    * `LensCardinality` — Σ4: Lens-image cardinalities
    * `CardinalityLB`   — lower bound on Lens kernel space (≥ ℵ₀)
-/
