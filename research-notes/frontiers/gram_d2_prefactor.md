# Frontier — the Gram correction's `/d²` prefactor

**Status**: OPEN. **Domain**: physics (α_em deployment).
**Opened**: 2026-06-07.

## The reduced problem

The Gram self-consistency cubic `25·y³ + 1 = 25·X·y²` is **not** an
independent modeling choice: `GramCubicReduction.cubic_is_correction_ansatz`
(PURE) shows it is the algebraic re-expression of the correction ansatz

  `correction = X − y = 1/(25·y²) = α²/d²`   (d² = 25, α = 1/y).

So the only residual `modeling-form` degree of freedom in the α_em Gram
layer is: **why is the correction `α²/d²`?**

- `α²` — structurally expected: a self-energy correction is `O(α²)`.
- `/d²` (the `25 = d²` prefactor) — **the open item**.

## Why it is not yet closed (honest boundary, §5.4)

The `d² = 25` prefactor currently has **three candidate readings** but no
forcing theorem selecting one:

1. **block-pair total** — `d²` pairs of the atomic structure;
2. **Gram matrix DOF** — the dimension of the relevant Gram matrix;
3. **α_GUT factor** — `1/α_GUT = d²·ζ(2)` (`Couplings.AlphaGUT`).

`Augmented.lean` § GramSelfEnergy lists all three as "readings."
`GramSelfConsistency.lean` lists "cohomological derivation of the d²
prefactor" as a Step-4+ open item. `CupRingTrace.lean` is, by its own
header, a **bottom-up test** (functionals defined first, result observed
second), not a forcing derivation. So the cup-ring trace does **not**
currently force the prefactor.

## What would close it

A cohomological/trace theorem deriving the self-energy prefactor as `d²`
(disambiguating the three readings) from the cup-ring structure of
H*(Δ⁴) — i.e. promoting `CupRingTrace` from a test to a forcing
derivation. Then `correction = α²/d²` is fully atomic, and the Gram
`modeling-form` DoF closes entirely.

A second, smaller sub-item (separate): replace the observed-α on the RHS
of `gram_correction_e9` with a 213-internal cubic-root iterate, and bound
the residual 27×10⁻⁹ (next-order Dyson tail).

## Anchors

- `lean/E213/Lib/Physics/AlphaEM/GramCubicReduction.lean` — the reduction (PURE)
- `lean/E213/Lib/Physics/AlphaEM/GramStructural.lean` — cubic anchor + "what remains"
- `lean/E213/Lib/Physics/AlphaEM/Augmented.lean` § GramSelfEnergy — the three d² readings
- `lean/E213/Lib/Physics/AlphaEM/CupRingTrace.lean` — the bottom-up test
- `DEGREES_OF_FREEDOM_LEDGER.md` Layer 3 — the DoF accounting
</content>
