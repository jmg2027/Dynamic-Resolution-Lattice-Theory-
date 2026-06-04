import E213.Lib.Math.Tactic.Extras.CauchySchwarz
import E213.Lib.Math.Tactic.Extras.LpOneCollapse
import E213.Lib.Math.Tactic.Extras.SymFin
import E213.Lib.Math.Tactic.Extras.InnerCauchy
import E213.Lib.Math.Tactic.Extras.Capstone
import E213.Lib.Math.Tactic.Extras.HoeffdingFiniteN
import E213.Lib.Math.Tactic.Extras.AggregatorCapstone
import E213.Lib.Math.Tactic.Extras.RealLogCapstone

/-! Umbrella for math-track deferral cleanup (`Math/Extras`).

  All files ∅-axiom; close honest-scope deferrals from various
  math-track domain passes.  See `Extras/INDEX.md` for the
  per-file deferral source map.

  ## Foundational witnesses (Pass 1)

    * `CauchySchwarz` — `2·a·b ≤ a² + b²` + bundled
      `CauchySchwarz{2D, 3D, 4D, List, Inductive}` sub-namespaces
    * `InnerCauchy`   — inner-product form
    * `LpOneCollapse` — `‖f‖_1 = ∫ f` (∀ S form)
    * `SymFin`        — Sₙ via `Fin n`
    * `Capstone`      — 4-witness bundle

  ## Aggregator + finite-N witnesses

    * `HoeffdingFiniteN`    — Hoeffding bound at N = 1, 2
    * `AggregatorCapstone`  — n=2 CS Σ-side + Hoeffding bundle

  ## Marathon capstones

    * `RealLogCapstone`     — `Real213.log` closure
-/
