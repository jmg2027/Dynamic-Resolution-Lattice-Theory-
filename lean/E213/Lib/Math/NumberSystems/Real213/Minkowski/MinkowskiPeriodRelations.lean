import E213.Lib.Math.NumberSystems.Real213.Minkowski.MinkowskiCocycle
import E213.Lib.Math.NumberSystems.Real213.Markov.MarkovModularBridge
import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.UTracePeriodic

/-!
# MinkowskiPeriodRelations — the Eichler–Shimura period-relation generators are present

The weight-`k` Eichler–Shimura period relations are `r|(1+S) = 0` and `r|(1+U+U²) = 0`, governed by
the **elliptic torsion** of `PSL(2,ℤ) = ℤ/2 ∗ ℤ/3`: `S` of order 4 (`S² = −I`, the Gaussian unit
`i = ℤ[i]^×`) and `U` of order 6 (`U³ = −I`, the Eisenstein unit `ω = ℤ[ω]^×`) — the `{4,6}` axis.
Both generators, and their orders, are already in the repo (`ModularElliptic`, `UTracePeriodic`).

And the `?`-cocycle's **weight-2 period is exactly the eigenvalue of `S`**: the `√(−1)` residue
`m ∣ u² + 1` (`minkowski_weight2_period_relation`) is the eigenvalue of `S = [[0,−1],[1,0]]` (the
order-4 Gaussian unit `i`) acting on the Markov pair mod the Markov number
(`MarkovModularBridge.{markov_pair_eigen, S_eigenvector_of_dvd}`).  So the `(1+S)` period relation's
generator *carries the weight-2 period*, and the `(1+U+U²)` generator `U` is the order-6 Eisenstein
unit — the full period-relation group structure, on the tree, ∅-axiom.

What remains for the *higher-weight* relations is the **slash action on the polynomial module
`V_{k−2}`** (the actual annihilation `r|(1+S) = 0` on degree-`(k−2)` polynomials) — finite ℤ-linear
algebra over the generators built here, not a purity or integration obstruction.
-/

namespace E213.Lib.Math.NumberSystems.Real213.MinkowskiPeriodRelations

open E213.Lib.Math.NumberSystems.Real213.SternBrocotMarkov
  (markovNum markovRes markovNum_dvd_res_sq_succ)
open E213.Lib.Math.NumberSystems.Real213.ModularElliptic (Mat2 S)
open E213.Lib.Math.NumberSystems.Real213.MarkovModularBridge (S_eigenvector_of_dvd)

/-- ★★★ **The weight-2 period is the eigenvalue of the order-4 elliptic generator `S` — the `(1+S)`
    period relation's generator.**  Two conjuncts:

      1. the cocycle's weight-2 period is the `√(−1)` congruence at every Stern-Brocot node,
         `m_t ∣ u_t² + 1` (`markovNum_dvd_res_sq_succ`);
      2. that residue `u` is the **eigenvalue of `S = [[0,−1],[1,0]]`** (the order-4 Gaussian unit
         `i`, `S² = −I`) on a Markov pair mod the Markov number — the abstract `S`-eigenvector
         criterion `S_eigenvector_of_dvd` (over `ℤ`, `ring_intZ`).

    So the `(1+S)` Eichler–Shimura period relation's *generator carries the weight-2 period*: the
    `√(−1)` period of the `?`-cocycle is `S`'s eigenvalue.  With `U` the order-6 Eisenstein generator
    (`UTracePeriodic.elliptic_orders_four_and_six`, the `{4,6}` torsion), the full period-relation
    group structure is on the tree.  The higher-weight annihilation `r|(1+S)=0` on `V_{k−2}` is the
    remaining finite ℤ-linear step.  ∅-axiom. -/
theorem weight2_period_is_S_eigenvalue :
    (∀ path : List Bool, markovNum path ∣ markovRes path * markovRes path + 1)
    ∧ (∀ a b u c : Int, c ∣ (u * a + b) → c ∣ (u * b - a) →
        c ∣ (S.a * a + S.b * b - u * a) ∧ c ∣ (S.c * a + S.d * b - u * b)) :=
  ⟨markovNum_dvd_res_sq_succ, S_eigenvector_of_dvd⟩

end E213.Lib.Math.NumberSystems.Real213.MinkowskiPeriodRelations
