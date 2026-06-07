/-!
# GramCubicReduction — the cubic form is the correction ansatz, not a free choice

`DEGREES_OF_FREEDOM_LEDGER.md` Layer 3 marks the Gram self-consistency
cubic `25·y³ + 1 = 25·X·y²` as `modeling-form` (a chosen functional
shape). This file **reduces** that item: the cubic form carries **no
freedom beyond the correction ansatz** `correction = α²/d²`.

## What is proven (PURE)

Write the base value `X = y + k`, where `k = X − y` is the correction.
The cubic's two sides factor cleanly:

  `25·y²·(y + k) = 25·y²·y + 25·y²·k`     (`cubic_is_correction_ansatz`)

i.e. `25·y²·X = 25·y³ + 25·y²·k`. So the cubic `25·y²·X = 25·y³ + 1`
holds **iff** `25·y²·k = 1`, i.e. **iff** `k = 1/(25·y²) = α²/d²`
(with `d² = 25`, `α = 1/y`). The cubic is the algebraic re-expression of
the single correction ansatz `correction = α²/d²` — choosing the cubic is
*not* an independent modeling choice; it is forced once the correction
form is fixed.

## What is NOT proven (the honest residual — `seed/AXIOM/05_no_exterior.md` §5.4)

The reduction moves the `modeling-form` DoF from "the cubic" to a single
sub-question: **why is the correction `α²/d²`?**

  · `α²` (second order in the coupling) is structurally expected — a
    self-energy correction is `O(α²)`.
  · `/d²` (the `25 = d²` prefactor) is the genuine open item. It has
    **three candidate readings** in the corpus (`Augmented.lean` §
    GramSelfEnergy: "block-pair total, Gram matrix DOF, α_GUT factor")
    but **no forcing theorem** selecting one. `GramSelfConsistency.lean`
    lists "cohomological derivation of the d² prefactor" as open
    (Step 4+); `CupRingTrace.lean` is by its own header a *bottom-up
    test* (functionals defined first, result observed second), not a
    forcing derivation.

So: the cubic-form freedom is closed (reduced to the ansatz), but the
ansatz's `/d²` prefactor is **not yet forced from the cup-ring trace**.
Stated plainly rather than dressed as a derivation. Open frontier:
`research-notes/frontiers/gram_d2_prefactor.md`.
-/

namespace E213.Lib.Physics.AlphaEM.GramCubicReduction

/-- **The cubic IS the correction ansatz.**  With base `X = y + k`
    (correction `k = X − y`), the cubic's `25·y²·X` side factors as
    `25·y²·y + 25·y²·k` = `25·y³ + (the correction term)`.  Hence the
    cubic `25·y²·X = 25·y³ + 1` is equivalent to `25·y²·k = 1`, i.e.
    `k = 1/(25·y²) = α²/d²`.  The cubic form contributes no freedom beyond
    fixing `correction = α²/d²`.  PURE (single `Nat.mul_add`). -/
theorem cubic_is_correction_ansatz (y k : Nat) :
    25 * (y * y) * (y + k) = 25 * (y * y) * y + 25 * (y * y) * k := by
  rw [Nat.mul_add]

end E213.Lib.Physics.AlphaEM.GramCubicReduction
