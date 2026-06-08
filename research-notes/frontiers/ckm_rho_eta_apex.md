# Frontier — the CKM Wolfenstein apex `(ρ, η)` and the Jarlskog magnitude

**Status**: OPEN. **Domain**: physics (CKM / CP violation).
**Opened**: 2026-06-07 (found auditing whether θ_QCD's `J` is derivable).

## The gap

The Jarlskog invariant's *structure* is DRLT-derived — all factors are
atomic:
- `s₁₂ = λ = 5/22 = d/(d²−d+c)` (Cabibbo, `CabibboAngle`/`CKMHierarchy`)
- `A = φ/c = φ/2` (golden-ratio-over-c, `CKMHierarchy`)
- `s₂₃ = A·λ²`, `s₁₃ = A·λ³`
- `δ = π/φ²` (`CPViolation`, `δ ≈ 68.75°`, `sin δ ≈ 0.932`)

But the *magnitude* does **not** match. Computed honestly from the full
formula `J = c₁₂s₁₂c₂₃s₂₃c₁₃²s₁₃ sin δ`:

  **J_DRLT = 8.18 × 10⁻⁵   vs   J_observed = 3.08 × 10⁻⁵   (×2.66 over)**

(A prior `CPViolation.lean` comment claimed "≈3.5×10⁻⁵, within 10%" — an
arithmetic error; its own factors multiply to 7.6×10⁻⁵. Corrected.)

## Root cause — the un-derived apex `(ρ, η)`

The discrepancy is localized to `s₁₃` / `|V_ub|`:
- observed `|V_ub| = A·λ³·√(ρ²+η²) ≈ A·λ³·0.39 ≈ 0.0037`
- DRLT uses `s₁₃ = A·λ³ = 0.0095` — **omitting `√(ρ²+η²) ≈ 0.39`**.

Equivalently `J = A²·λ⁶·η`, and DRLT has not derived the CP-apex
parameters `(ρ, η)` (only `λ`, `A`, `δ`). `s₂₃ ≈ A·λ² ≈ 0.042` matches
observed `|V_cb| ≈ 0.041` fine — the gap is specifically the apex.

## Consequences (tracked elsewhere)

- **θ_QCD (`PRE_REGISTRATION.md` P2)**: `θ_QCD = J·α_GUT⁴` inherits the
  un-derived `J`; with the honest `J = 8.18×10⁻⁵`, the θ_QCD central value
  shifts ×2.66, moving it outside the catalog's own `[2.51,3.00]×10⁻¹¹`
  bracket. P2 therefore depends on a `J` DRLT does not yet produce.
- **`DEGREES_OF_FREEDOM_LEDGER.md`**: the Jarlskog row is upgraded from
  "magnitude un-derived" to "magnitude over-predicted ×2.66; missing
  `(ρ, η)`".

## Candidate — `R_u = c/d` (2026-06-07, ~6% match)

`JarlskogApex.lean` (PURE) records the atomic candidate that closes the gap:

  **R_u = √(ρ²+η²) = c/d = 2/5**, equivalently
  **|V_ub|/|V_cb| = λ·R_u = c/D = 2/22** (`D = d²−d+c` = Cabibbo denom).

Numerical effect (full Jarlskog formula with this factor):
- `s₁₃ = A·λ³·(c/d) = 0.00380` vs observed `|V_ub| = 0.00382` (**0.5%**)
- `R_u = 0.40` vs observed `0.38–0.42` (≤4%, `Ru_in_observed_bracket`)
- `J = 3.27×10⁻⁵` vs observed `3.08×10⁻⁵` (**6.2%**, was 166% without)
- `η = (c/d)·sin(π/φ²) = 0.373` vs observed `η̄ ≈ 0.348` (7%)

Structural story (suggestive, not yet a theorem): `V_ub` is the `λ³`
third-level transition; crossing the extra level multiplies the ratio by the
**multiplicity `c`** over the base `d` (the `c` = inter-level multiplicity
reading, `AlphaEM/AssignmentForcing`).

**Still open (now narrow)**: *why* `|V_ub|/|V_cb| = c/D` is forced — the
numerator `c` lacks a forcing theorem. The candidate is strong (atomic ratio,
0.5% on `|V_ub|`, 6% on `J`) but labelled CANDIDATE until that closes.

## What would fully close it

A forcing theorem for the `c`-numerator in `|V_ub|/|V_cb| = c/D` (the
multiplicity picked up crossing the `λ³` level), promoting the candidate to
a derivation. Then `J = A²λ⁶η` is atom-pinned and θ_QCD's `J` input is
resolved.

## Anchors

- `lean/E213/Lib/Physics/Mixing/CPViolation.lean` — J structure + magnitude-gap note
- `lean/E213/Lib/Physics/Mixing/CKMHierarchy.lean` — λ, A = φ/c, s₂₃, s₁₃
- `lean/E213/Lib/Physics/Mixing/CabibboAngle.lean` — λ = 5/22
- `lean/E213/Lib/Physics/Couplings/ThetaQCD.lean` — the θ_QCD consumer of J
</content>
