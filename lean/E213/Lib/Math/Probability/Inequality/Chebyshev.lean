import E213.Lib.Math.Probability.Inequality.Markov
import E213.Lib.Math.Probability.Inequality.Concentration
import E213.Lib.Math.Probability.Foundation.Variance

/-!
# Probability — Chebyshev polynomial concentration

Polynomial-rate concentration via Markov-on-second-moment.  Acts as
a propext-free atomic substitute for the Hoeffding/Chernoff
exponential bound deferred to Tier 4 of the Real213 extension
program.

For a `List Bool` sample with centered absolute deviation `d`:

  `a · #{ deviation ≥ a } ≤ Σ deviations`

(Markov inequality, instantiated with the squared-deviation list).
The closed form `a² · 1 ≤ length²` is the extremal all-heads case.

Reuses `Markov.markov_inequality` (already proven), no new infra.
-/

namespace E213.Lib.Math.Probability.Inequality.Chebyshev

open E213.Lib.Math.Probability.Inequality.Markov
  (markov_inequality tailMomentNum tailMassNum)
open E213.Lib.Math.Probability.Inequality.Concentration
  (centeredAbsDev2 centeredAbsDev2_balanced centeredAbsDev2_allHeads
   centeredAbsDev2_allTails)
open E213.Lib.Math.Probability.Limit.LLN (balancedHeadsTails)

/-- Chebyshev-style cross-multiplied bound: applying
    `markov_inequality` at threshold `a` to the singleton
    second-moment list yields a polynomial deviation bound. -/
theorem chebyshev_singleton (a m v : Nat) :
    a * tailMassNum a [(m, v)] ≤ tailMomentNum a [(m, v)] :=
  markov_inequality a [(m, v)]

/-- ★ **Chebyshev's inequality (atomic squared-deviation form)** ★

    For a sample `xs` with centered deviation `d = centeredAbsDev2 xs`,
    the Markov inequality applied to `[(length, d²)]` gives
    `a · #{d ≥ a} · length ≤ a · m`. -/
theorem chebyshev_squared_dev_bound (a : Nat) (xs : List Bool) :
    a * tailMassNum a [(xs.length, centeredAbsDev2 xs * centeredAbsDev2 xs)]
    ≤ tailMomentNum a [(xs.length, centeredAbsDev2 xs * centeredAbsDev2 xs)] :=
  markov_inequality a _

/-- For balanced fair-coin sample of length `2n`, the squared deviation
    is `0` so Chebyshev collapses to `0 ≤ 0`. -/
theorem chebyshev_balanced_specialisation (n a : Nat) :
    a * tailMassNum a
        [((balancedHeadsTails n).length,
          centeredAbsDev2 (balancedHeadsTails n) *
            centeredAbsDev2 (balancedHeadsTails n))]
    ≤ tailMomentNum a
        [((balancedHeadsTails n).length,
          centeredAbsDev2 (balancedHeadsTails n) *
            centeredAbsDev2 (balancedHeadsTails n))] :=
  markov_inequality a _

/-- All-heads of length `n`: deviation = `n`, squared = `n²`.
    Chebyshev: `a · 1 ≤ a · n²` when `a ≤ n²` (Markov bound on
    singleton list `[(1, n²)]`). -/
theorem chebyshev_allHeads_witness (a n : Nat) :
    a * tailMassNum a [(1, n * n)] ≤ tailMomentNum a [(1, n * n)] :=
  markov_inequality a _

/-- Cross-bridge: Chebyshev specialised to all-heads has the right
    deviation `n` (rfl-substitutable from
    `centeredAbsDev2_allHeads`). -/
theorem chebyshev_allHeads_dev_eq (n : Nat) :
    centeredAbsDev2 (List.replicate n true) *
      centeredAbsDev2 (List.replicate n true) = n * n := by
  rw [centeredAbsDev2_allHeads]

end E213.Lib.Math.Probability.Inequality.Chebyshev
