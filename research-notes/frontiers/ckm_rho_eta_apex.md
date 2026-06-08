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

## Candidate — the apex is a φ² object: modulus `1/φ²`, phase `π/φ²` (2026-06-07)

`JarlskogApex.lean` (PURE). Trying to force the first `c/d` guess revealed a
better, **φ²-coherent** candidate: the CKM CP-apex is a single golden object —
**modulus `R_u = 1/φ²`, phase `δ = π/φ²`** (the phase already derived in
`CPViolation`). The same `φ²` in both, and `φ²` is atomic
(`φ²+1/φ² = NS`, `d·NT = NS²+1`).

Numerical match (full Jarlskog formula, `R_u = 1/φ²`):
- `R_u = 1/φ² = 0.38197` vs observed `√(ρ̄²+η̄²) = 0.38260` (**0.17%**)
- `J = 3.12×10⁻⁵` vs observed `3.08×10⁻⁵` (**+1.4%**, was 166% without)
- `η = (1/φ²)·sin(π/φ²) = 0.356` vs observed `η̄ = 0.348` (**2.3%**)

The earlier `c/d = 2/5` is **not a competitor**: it is the *lowest Fibonacci
convergent* of `1/φ²` (`F₃/F₅`, with `F₃=NT, F₄=NS, F₅=d`), with higher
convergents `5/13, 13/34 → 1/φ²` (Cassini alternation, all PURE).

**Status — strong, φ²-coherent, modulus not yet forced.** The Fibonacci/φ²
identities are exact (PURE). `R_u = 1/φ²` matches at 0.17% (modulus) / 1.4%
(J) and shares the derived phase's `φ²` — far past a fit. Open: *why* the
apex modulus is exactly `1/φ²` (vs another φ-power). The open part shrank from
"unexplained `c/d`" to "why the apex is the `φ²` object", and `φ²` is already
atomic.

## Single-parameter apex + triangle predictions (2026-06-07)

Attempting to force `R_u` from the angle `γ`: **`γ` alone does not force `R_u`**
— a triangle is underdetermined by one angle (honest §5.4). But two facts
sharpen the picture:

1. **Single parameter.** `δ/π = R_u = 1/φ²`, i.e. **`δ = π·R_u`** — phase = π ×
   modulus. So the apex is `z = r·e^{iπr}` with one golden parameter `r = 1/φ²`;
   the two φ²-inputs collapse to one (`phase_over_pi_eq_modulus`, PURE via the
   shared Fibonacci convergents). Open: why `γ = π·R_u`, and why `r = 1/φ²`.

2. **The triangle is then determined and PREDICTS its other elements**
   (outputs, not inputs):
   - `β = 22.45°` vs observed `22.0°`
   - `sin 2β = 0.706` vs observed `0.695 ± 0.019` (**inside the error bar** —
     and `sin 2β` is the precisely-measured "golden mode" `B→J/ψ K_S`)
   - `α = 88.8°` vs observed `~85–90°`; `R_t = 0.932` vs `~0.91–0.93`

   So the φ²-apex is not just an η-fit: it reproduces the *independently
   measured* `sin 2β` within its error bar. (Trig values transcendental —
   documented, not PURE-Nat.)

## `1/φ²` grounded — the residue self-reference contracting eigenvalue (2026-06-07)

Why `1/φ²` (not an arbitrary golden power)? It is the **sub-dominant
eigenvalue of the residue's self-reference matrix** `M = [[c,1],[1,1]]` — the
Möbius `P` of `seed/AXIOM/05_no_exterior.md` §5.6 (`Mobius213`). Fully atomic
characteristic data (`JarlskogApex.apex_modulus_is_selfref_contracting_eigenvalue`,
PURE):

  `trace = c+1 = NS`,  `det = c−1 = 1`,  `disc = NS²−4 = 5 = NS+NT = d`,
  eigenvalues `(NS ± √d)/2 = φ², 1/φ²`.

So `R_u = 1/φ² = (NS−√d)/2` is the **contracting eigenvalue** (the rate `P^n`
converges to the residue fixed point φ). The value is structurally
distinguished, not fitted — the connection to §5.6 is the shared atomic
characteristic polynomial `x²−NS·x+1`, `disc = d`, not "φ appears in both".

## What remains — one physical identification

The *value* `1/φ²` is now fully atomic-grounded (contracting self-reference
eigenvalue). The single remaining open premise: **why the CKM CP-apex modulus
equals this eigenvalue** — why CP-violation depth = the residue's
self-reference contraction rate. One clean structural identification (not a
fitted number); it would pin the apex (`γ = π·R_u` is the other face of the
single-parameter apex `z = r·e^{iπr}`), making `J = A²λ⁶η` atom-pinned and
resolving θ_QCD's `J`.

## Anchors

- `lean/E213/Lib/Physics/Mixing/JarlskogApex.lean` — apex = φ² object, self-ref eigenvalue
- `lean/E213/Lib/Math/Algebra/Mobius213.lean` — the §5.6 self-reference matrix, eigenvalues φ²,1/φ²
- `lean/E213/Lib/Physics/Mixing/CPViolation.lean` — J structure + magnitude-gap note
- `lean/E213/Lib/Physics/Mixing/CKMHierarchy.lean` — λ, A = φ/c, s₂₃, s₁₃
- `lean/E213/Lib/Physics/Mixing/CabibboAngle.lean` — λ = 5/22
- `lean/E213/Lib/Physics/Couplings/ThetaQCD.lean` — the θ_QCD consumer of J
</content>
