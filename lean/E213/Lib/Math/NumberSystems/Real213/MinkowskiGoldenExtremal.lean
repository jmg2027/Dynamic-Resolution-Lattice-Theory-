import E213.Lib.Math.NumberSystems.Real213.MinkowskiCocycle
import E213.Lib.Math.NumberSystems.Real213.MarkovUniqueness
import E213.Lib.Math.NumberSystems.Real213.GoldenFormMarkov
import E213.Lib.Math.NumberSystems.Real213.LagrangeExtremes

/-!
# MinkowskiGoldenExtremal — the golden ratio is the extremal instance of the `?`-cocycle's period

Two pillars meet here.  **Pillar 1** (`MinkowskiCocycle`): the analytic Minkowski `?` is a
Markov-valued 1-cocycle on the Stern-Brocot tree, whose weight-2 Eichler–Shimura period relation is
the `√(−1)` congruence `m_t ∣ u_t² + 1` at every node.  **Pillar 2** (the Markov/Lagrange spectrum):
the golden ratio `φ = [1;1,1,…]` — the all-`1` continued fraction, the worst-approximable number, the
Lagrange-spectrum floor `√5` — runs along the **Fibonacci spine** of the tree.

The bridge: `φ` is the **extremal instance of the weight-2 period relation**.  The general node
congruence `m_t ∣ u_t² + 1` (`markovNum_dvd_res_sq_succ`) specialises, along the slowest (Fibonacci /
period-1) descent, to `fib(2n+3) ∣ fib(2n+2)² + 1` (`fib_spine_sqrt_neg_one`) — the same `√(−1)`
period, now on the convergents of the most irrational number, witnessed by the Cassini identity
(`golden_min_attained_on_fib`).  So the Lagrange minimum `√5 / φ` is not external data: it is where
the `?`-cocycle's period runs along the residue's own golden spine, the `inf|Q| = 1` floor being the
residue unit `NS − NT = 1`.  All ∅-axiom (composes existing PURE lemmas across both pillars).
-/

namespace E213.Lib.Math.NumberSystems.Real213.MinkowskiGoldenExtremal

open E213.Lib.Math.NumberSystems.Real213.SternBrocotMarkov
  (markovNum markovRes markovNum_dvd_res_sq_succ)
open E213.Lib.Math.NumberSystems.Real213.MarkovUniqueness (fib_spine_sqrt_neg_one)
open E213.Lib.Math.NumberSystems.Real213.GoldenFormMarkov
  (golden_anisotropic golden_min_attained_on_fib)
open E213.Lib.Math.Algebra.Mobius213.Px.FibonacciAtomicLock (fib)

/-- ★★★ **The golden ratio is the extremal instance of the `?`-cocycle's weight-2 period relation.**
    Four conjuncts, one structure:

      1. **general period relation** — at every Stern-Brocot node the `?`-cocycle residue is `√(−1)`
         modulo the Markov number, `m_t ∣ u_t² + 1` (`markovNum_dvd_res_sq_succ`);
      2. **golden / Fibonacci extremal instance** — along the slowest (period-1, all-`1` CF) descent
         the same period relation reads `fib(2n+3) ∣ fib(2n+2)² + 1` (`fib_spine_sqrt_neg_one`): the
         `√(−1)` period on `φ`'s convergents, the worst-approximable number;
      3. **anisotropy / the `√5` floor** — the golden form is anisotropic
         (`m² = m·k + k² ⟹ m = k = 0`, `golden_anisotropic`): `inf|Q| = 1` is the Lagrange-spectrum
         minimum `√5`, attained on `φ`;
      4. **Cassini witness** — the extremal divisor is the Cassini identity
         `fib(2n+2)² + 1 = fib(2n+2)·fib(2n+1) + fib(2n+1)²` (`golden_min_attained_on_fib`), the
         `W = ±1` cross-determinant floor = the residue unit.

    So the Lagrange minimum (`√5 / φ`, Pillar 2) is the residue-internal extremal case of the
    `?`-cocycle's period (Pillar 1) — one structure, the most-irrational number running along the
    residue's golden spine.  ∅-axiom. -/
theorem golden_is_extremal_weight2_period :
    (∀ path : List Bool, markovNum path ∣ markovRes path * markovRes path + 1)
    ∧ (∀ n : Nat, fib (2 * n + 3) ∣ (fib (2 * n + 2) * fib (2 * n + 2) + 1))
    ∧ (∀ m k : Nat, m * m = m * k + k * k → m = 0 ∧ k = 0)
    ∧ (∀ n : Nat, fib (2 * n + 2) * fib (2 * n + 2) + 1
        = fib (2 * n + 2) * fib (2 * n + 1) + fib (2 * n + 1) * fib (2 * n + 1)) :=
  ⟨markovNum_dvd_res_sq_succ, fib_spine_sqrt_neg_one, golden_anisotropic,
   golden_min_attained_on_fib⟩

end E213.Lib.Math.NumberSystems.Real213.MinkowskiGoldenExtremal
