import E213.Lib.Math.Geometry.DiscreteCurvature.DiscreteRicci
import E213.Lib.Math.Geometry.DiscreteCurvature.DiscreteGaussBonnet
import E213.Lib.Math.Geometry.DiscreteCurvature.RicciFlowDiscrete
import E213.Lib.Math.Geometry.DiscreteCurvature.ConformalCurvature
import E213.Lib.Math.Geometry.DiscreteCurvature.OllivierRicci
import E213.Lib.Math.Geometry.DiscreteCurvature.BakryEmery
import E213.Lib.Math.Geometry.DiscreteCurvature.BakryEmeryBipartite
import E213.Lib.Math.Geometry.DiscreteCurvature.DiscreteLichnerowicz
import E213.Lib.Math.Geometry.DiscreteCurvature.KpCharacterEigen
import E213.Lib.Math.Geometry.DiscreteCurvature.WeightedGreen
import E213.Lib.Math.Geometry.DiscreteCurvature.DiscreteGaussian
import E213.Lib.Math.Geometry.DiscreteCurvature.DiscreteSurgery
import E213.Lib.Math.Geometry.DiscreteCurvature.RicciFlow
import E213.Lib.Math.Geometry.DiscreteCurvature.RicciSphereFlow
import E213.Lib.Math.Geometry.DiscreteCurvature.RicciHomogeneous

/-! Entry point for `E213.Lib.Math.Geometry.DiscreteCurvature`.

  A discrete (and 2D-conformal smooth) differential-geometry library:
  combinatorial curvature, the discrete Bochner identity, optimal-transport
  curvature, the spectral (Lichnerowicz) bridge, the binomial heat kernel,
  graph surgery, and homogeneous Ricci flow — all `∅`-axiom over `ℤ`/`ℕ`.

  Narrative: `theory/math/geometry/discrete_curvature.md`.

  ## Combinatorial curvature

    · `DiscreteRicci.lean`       — Forman edge curvature `4 − deg(u) − deg(v)`;
                                   uniform value on complete bipartite `K_{m,n}`;
                                   sign tracks the cyclomatic number `b₁`.
    · `DiscreteGaussBonnet.lean` — vertex curvature `2 − deg`; discrete
                                   Gauss–Bonnet `Σκ = 2χ`; total `= 2 − 2b₁`.
    · `OllivierRicci.lean`       — optimal-transport curvature; Kantorovich weak
                                   duality on the `gridSumZ` toolkit; sign
                                   trichotomy (triangle / square / double-star).
    · `BakryEmery.lean`          — carré-du-champ `Γ`/`Γ₂`; the discrete Bochner
                                   identity; `CD(K,N)` as a sum-of-squares fact.
    · `BakryEmeryBipartite.lean` — Bakry–Émery curvature of `K_{a,b}`: two-shell
                                   Bochner + shell-SOS; `K_{3,2} = CD(3/2,∞)`.
    · `DiscreteLichnerowicz.lean`— curvature → spectrum: `K_m` Rayleigh identity,
                                   spectrum `{0,m}`, the Lichnerowicz `K ≤ λ`
                                   gap, gradient-semigroup commutation.
    · `KpCharacterEigen.lean`    — the character↔spectrum weld at `p = d = 5`:
                                   the quadratic character of `ℤ/5` is a
                                   mean-zero `λ = 5` eigenfunction of `K₅`.

  ## Flows, heat kernel, surgery

    · `RicciFlowDiscrete.lean`   — discrete Ricci flow as heat flow on curvature;
                                   bounded / total-curvature-conserved /
                                   energy-monotone; reaches constant curvature.
    · `DiscreteGaussian.lean`    — binomial heat kernel: total-mass `Σu(t,·)=2^t`,
                                   mean, Li–Yau log-concave Harnack,
                                   no-local-collapsing density pinch.
    · `WeightedGreen.lean`       — weighted integration by parts; the flow as the
                                   gradient flow of the weighted Dirichlet energy.
    · `DiscreteSurgery.lean`     — surgery ledger: general Gauss–Bonnet,
                                   cut-a-neck `χ+1` / curvature `+2`, round-or-neck
                                   dichotomy, finite termination after `b₁` cuts.

  ## Smooth route

    · `ConformalCurvature.lean`  — smooth 2D-conformal Liouville Gauss curvature
                                   `K = (|∇λ|²−λΔλ)/(2λ³)` for polynomial `λ`;
                                   curvature trichotomy; flow fixed point ⟺ flat.
    · `RicciFlow.lean`           — a monovariant cell-filling flow on `K_{3,2}`
                                   (b₁ decreasing) converging to a normal form via
                                   the FLOW archetype (`MonovariantFlow`).
    · `RicciSphereFlow.lean`     — round `Sⁿ` smooth-metric Ricci flow → finite
                                   extinction; the homogeneous/ODE case.
    · `RicciHomogeneous.lean`    — homogeneous Ricci flow: the Einstein trichotomy
                                   (shrink / steady / expand by the sign of `λ`).
-/
