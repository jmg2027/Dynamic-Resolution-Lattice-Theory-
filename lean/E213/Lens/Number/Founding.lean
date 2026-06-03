import E213.Lens.Number.TowerFounding
import E213.Lens.Number.Nat213.Tower.PairCompletion
import E213.Lens.Number.Nat213.Order
import E213.Lens.Number.SharedUnitAcrossReadings

/-!
# Lens.Number.Founding — umbrella for the number-tower founding sub-tree

The number tower `ℕ → ℤ → ℚ → ℝ` founded as a chain of Lens bundlings of the residue, with
its closure properties.  This umbrella collects the founding modules so the sub-tree is
citable as one unit (and promotable per `theory/PROMOTION_CRITERIA.md`).

  * **`TowerFounding`** — the capstone `number_tower_is_lens_bundling`, chaining the four
    rungs: count (`Raw.leaves_slash`), difference (`DifferenceLensFounding`, the count-Lens
    bundled into a group), ratio (`RatioLensFounding`, lowest-terms = `det P = NS − NT`),
    Cauchy completion (`CauchyLensFounding`, the fixpoint at `ℝ`).
  * **`Nat213/Tower/PairCompletion`** — the invert move once: a generic
    `CommCancelSemigroup` pair-completion instantiated at `+` (`ℤ`) and `·` (`ℚ_+`)
    (`invert_is_one_move`); the group identity emerges as the diagonal, unit-free; the swap
    has order exactly `NT = 2` (`swap_order_eq_NT`, period-2 forced by the count).
  * **`Nat213/Order`** — native strict order (Lean `Nat` order is propext-dirty): trichotomy,
    strict square-monotonicity from distributivity, and square-injectivity `mul_self_inj`.
  * **`SharedUnitAcrossReadings`** — the honest unification: the unit `1` is one value across
    the count-difference, the Möbius/ratio determinant, the Cassini oscillation, and the
    reciprocal law (`the_unit_is_one_across_readings`).

Full narrative: `book/foundations/` (working treatise) and the classification frame in
`theory/lens/number_systems.md`.  ∅-axiom throughout.
-/
