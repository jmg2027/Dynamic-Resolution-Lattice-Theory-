# Registry — N_U / 5²⁵-resolution deletion (historical record)

**Decision (Mingu Jeong)**: the claim that **5²⁵ = N_U = d^(d²) =
configCount 2** is "the resolution / universe number" at which physics
(esp. 1/α_em) is evaluated is **WRONG and DELETED — not pending
re-derivation**.

Reason: identifying a configuration **COUNT** with a spectral-sum
**TRUNCATION index** is an unjustified category error.  Two further
foundations make the claim unrecoverable, so there is nothing to
re-derive:

- The fractal-level axis has **no privileged level** — `n ↦ configCountD
  d n` is a strict order-embedding (partial answer below).
- The residue / self-covering foundation says the tower has **no top**.

This file is the historical record of *what was removed*.  The
"needs re-research" framing of the original note is **superseded**: the
chain is gone, not deferred.

## What was deleted (Lean modules)

Whole files removed (finitist machinery — the 5²⁵-resolution chain):

- `Lib/Physics/AlphaEM/NResolutionCandidates.lean`
- `Lib/Physics/Foundations/FiniteUniverse.lean`
- `Lib/Physics/Foundations/NResolutionFromFractal.lean`
- `Lib/Physics/Foundations/NResolutionFractalDepth.lean`
- `Lib/Physics/Foundations/FractalLensCardinality.lean`
- `Lib/Physics/Capstones/FinitistObservableChain.lean`
- `Lib/Physics/Capstones/ValidationStandardOne.lean`
- `Lib/Math/UniverseChain/Universe.lean` (the N_U = d^(d²) terminus)
- `Lib/Math/UniverseChain/Synthesis.lean` (steps 1→5 landing on 5²⁵)
- `Lib/Math/UniverseChain/MobiusChain.lean` (narrative loader)

Theorems deleted from mixed files:

- `alpha_em_master_capstone` (AlphaEM/Capstone — finitist N_U closure)
- `canonical_5adic_NU` + its digit/trunc theorems (Padic/DRLT)

## What was kept (scrubbed of the resolution framing)

The underlying *arithmetic* survives where it is bare math:

- `configCountD d n := d^(d^n)` and `configCount n` —
  `Lib/Math/Cohomology/Fractal/ConfigCount.lean`.  `configCount 2 = 5^25`
  is a TRUE arithmetic theorem, parametric, no privileged level.
- `numV L = d^L` parametric vertex-count recursion
  (`UniverseChain/Recursion.lean`).
- Atomic forcing (NS=3, NT=2, d=5) and the residue
  (`UniverseChain/{Atomicity,Decomposition,PairAxes,Residue}.lean`,
  `Theory/Atomicity/`) — FORCED / foundational.
- The structural layer coefficients of the 5-layer 1/α_em formula
  (`AlphaEM/GradedFormula`, `PiFiveGap`); the ζ(2)/π⁵ factors are
  analytic inputs (π a literal), not finitistically replaced.
- The 0.2 ppb structural precision theorem chain
  (`AlphaEM/GramStructural*`, `GramSelfConsistency`, `GramHigherOrder`,
  `GradedFormulaPrecision`) — rests on π² as a LITERAL input, never on
  5²⁵.  Unaffected.
- `GradedRingNUBridge.lean` renamed to `GradedRingConfigCountBridge.lean`
  (graded-ring ↔ configCount, no privileged level).

## Partial answer (level axis is parametric)

On the *level* axis the answer is a theorem — purely parametric.
`configCountD_injective` / `configCountD_strictMono` (for `d ≥ 2`) make
`n ↦ configCountD d n` a strict order-embedding: no two levels share a
count, no fixed point, no plateau.  No level can be crowned.  Only the
base `d = 5` is selected (atomicity).  See
`research-notes/G156_configcount_level_injectivity.md`.

## Dead spec

`seed/RESOLUTION_LIMIT_SPEC.md` is cited as canonical by several files
but was **never committed** (no git history).  Its citations are stale.
