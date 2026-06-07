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

## Progress — the *value* is over-determined (2026-06-07)

`GramD2Readings.lean` (PURE) consolidates the three candidate readings:
`fullDimSquared`, `gramMatrixEntries`, and `inv_alpha_GUT_factor` all equal
`d² = 25` (`three_readings_coincide`, `all_readings_are_d_squared`), with
the block-pair reading given content via `d² = d + 2·C(d,2)` (`25 = 5+2·10`,
`blockpair_decomposition`). So the three are **not competing choices** —
they are facets of one structural quantity `d²` (equivalence-pluralism
discipline). The open question narrows: **not** "which value", but "which
*mechanism* links the self-energy to `d²`".

## Mechanism — IDENTIFIED (2026-06-07)

`GramD2Mechanism.lean` (PURE) identifies the mechanism by connecting two
**independent math-side structures** that both yield `d²` for a
**degree-2 (2-point)** object on the `d = 5` state space:

1. **2-point operator-space dimension** — a self-energy is a 2-point
   function in `V ⊗ V ≅ End V`; `tensorDim d d = d²`
   (`Lib/Math/Algebra/Linalg213/Gap/TensorProduct`, `5⊗5=25` = K_{3,2}
   channel count).
2. **2-fold cup-graduation denominator** — the self-pairing `k=1` cup term
   carries denominator `d^(k+1) = d²`
   (`RefinedCupLadderDerivation.cup_graduation_denom`).

These **coincide** (`mechanisms_converge`): a degree-2 object normalizes by
`d²`, read two independent ways that agree. Combined with the forced
numerator `α²` (self-energy is `O(α²)`), this grounds `correction = α²/d²`
in degree-2 structure — not a posit.

**Remaining premise** (the now-narrow open part): the identification of the
Gram self-energy *with* the degree-2 / 2-point cup object — the natural
reading of a self-energy, but not yet a separate forcing theorem.

## What would fully close it

A theorem identifying the Gram self-energy functional *as* the `k=1`
self-pairing cup term (promoting `CupRingTrace`/`SelfPairingTrace` from a
bottom-up test to a forcing derivation that the self-energy IS the 2-fold
cup self-pairing). Then `correction = α²/d²` is fully atomic and the Gram
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
