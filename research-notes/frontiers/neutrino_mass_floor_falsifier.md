# The neutrino zero-dial mass-floor falsifier — S5 executed

Executes conjecture **S5** of `divergence_conjecture_slate.md` (first
recommended attack).  Status: **numerical-only** — per the DRLT Validation
Standard this is a research note, not a validated result; the Lean
conditional theorem is the named next step.  Tier-1 volatile.

## Audit finding first (stale anchor)

`catalogs/falsifiers.md` F3 and `PRE_REGISTRATION.md` cite a Lean anchor
**`NeutrinoRatioDerivation`** for `m₃/m₂ ≈ 5.71`.  **No such module exists
anywhere under `lean/`** (repo-wide grep, 2026-07-12).  The ratio appears
only at docstring level (`Foundations/DrltZeroParameters.lean:60`,
`Foundations/GoldenRatio.lean:18` "uses φ ratios" — the exact φ-expression
is not recorded anywhere).  This is the same class as the θ_QCD/E0 finding
(`research_program_year_horizon.md` Track E0): a falsifier resting on an
anchor that does not exist.  Repair queued below.

## The construction (zero dials)

The DRLT reading fixes one number, `r = m₃/m₂`.  The measured splitting
ratio fixes a second, `ρ = Δm²₃₁/Δm²₂₁`.  Together they *over-determine*
the lightest mass — no free parameter remains:

```
ρ = (m₃² − m₁²)/(m₂² − m₁²) = (r² − x)/(1 − x),   x := (m₁/m₂)²
⟹  x = (ρ − r²)/(ρ − 1)
```

**The falsifier**: the reading requires `x ≥ 0`, i.e. **`ρ ≥ r²`**,
i.e. `Δm²₂₁ ≤ Δm²₃₁ / r²`.  If the measured solar splitting exceeds
`Δm²₃₁/r²`, the `m₃/m₂ = r` reading is killed by arithmetic.

## The numbers (global-fit era values, normal ordering)

Inputs: `r = 5.71` (docstring value, provenance open), `r² = 32.604`;
`Δm²₂₁ = 7.41(21)×10⁻⁵ eV²`, `Δm²₃₁ = 2.511(27)×10⁻³ eV²` → `ρ = 33.89`.

| Quantity | Value |
|---|---|
| kill threshold `Δm²₂₁* = Δm²₃₁/r²` | `7.70×10⁻⁵ eV²` |
| measured `Δm²₂₁` vs threshold | `7.41×10⁻⁵` — **below, by ≈ 1.4σ** |
| `x = (m₁/m₂)²` | `+0.0390` → **survives** |
| `m₁/m₂` | `0.198` |
| `m₂ = √(Δm²₂₁/(1−x))` | `8.78 meV` |
| `m₁` | `1.73 meV` |
| `m₃ = r·m₂` | `50.1 meV` |
| **`Σm_ν` (prediction, 0 dials)** | **`60.7 meV`** |

Consistency check (independent route): `Δm²₃₂/Δm²₂₁ = (r²−1)/(1−x)` with
`Δm²₃₂ = 2.437×10⁻³` gives the same `x = 0.039`.  ✓

## Verdict

1. **The reading survives** the current central values — non-trivially:
   `x ≥ 0` fails on ~8% of the currently allowed solar-splitting band.
   This was a genuine kill opportunity and it did not fire.
2. **The test is live, and sharp.**  The survival margin is ≈ 1.4σ of the
   solar splitting.  JUNO will measure `Δm²₂₁` to sub-percent precision:
   if the true value sits above `7.70×10⁻⁵ eV²` (equivalently
   `√ρ < 5.821`… i.e. `r > √ρ`), the Fibonacci mass-ratio reading dies by
   pure arithmetic — a cleaner falsifier than the F3 ordering coin-flip.
3. **New independent falsifier (E7 payoff)**: the reading now *predicts*
   `Σm_ν ≈ 61 meV` and `m₁ ≈ 1.7 meV` with zero dials.  `Σm_ν` is a
   measured-band target (cosmology); a determination well away from
   ~61 meV kills the reading independently of JUNO.  This adds one
   genuinely independent pinned number to the honest-K ledger
   (`evidential_overdetermination_count.md`) — conditional on the ratio's
   provenance being repaired (below).

## Sensitivity of the verdict to `r` (why provenance matters)

`x ≥ 0 ⟺ r ≤ √ρ = 5.821 ± 0.02`.  The docstring `r = 5.71` sits inside;
but candidate φ-expressions nearby straddle the line (e.g. `φ⁴ = 6.854`
is dead; `2φ² + φ⁻² = 5.618` survives with `Σm ≈ 63 meV`;
`4/7·10 = 5.714` survives).  **Until the exact expression is pinned in
Lean, the falsifier tests a docstring, not the framework.**  The
provenance repair is therefore not bookkeeping — it decides *what* JUNO
would falsify.

## Next steps (queued)

1. **Pin the expression**: locate or reconstruct the φ-ratio derivation
   behind 5.71 (the `GoldenRatio.lean` docstring's "uses φ ratios"); if it
   cannot be reconstructed, F3's ratio clause should be demoted in
   `catalogs/falsifiers.md` (the ordering half of F3 stands on
   `PMNS_simplicial_pattern` regardless).
2. **Lean conditional theorem** (PURE, rational arithmetic only):
   `mass_floor_bracket : r² ≤ ρ_lo → x_interval ⊆ [x_lo, x_hi] →
   Σ ∈ [Σ_lo, Σ_hi]` — the measured windows enter as *hypotheses*
   (typed, per the E0 repair pattern), the bracket arithmetic is ∅-axiom.
   Size S–M.
3. File the outcome either way into the program's §0 table: this kernel is
   **W1** (rational inequalities on counts-squared — no cancellation, no
   limit).
