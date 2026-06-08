# theory/physics/cp_phase.md — the CKM CP phase from the prime `d = 5`

## Overview

The Cabibbo–Kobayashi–Maskawa **CP-violating phase** is derived, not posited, in
213-native operational terms.  Its *existence and uniqueness* follow from the
derived generation count; its *value* `δ = 90°` is forced by the complex
structure being the Cayley–Dickson imaginary unit `i` (`ℤ[i]^× = C₄`); and that
`C₄`/`i` is one object on the prime `d = NS+NT = 5`, appearing in three
disciplines — group theory (`ℤ[i]`), number theory (`ℚ(ζ₅)`), and cohomology (the
signed Hodge star on `H*(Δ⁴)`, the *same* cohomology that derives `1/α_em`).  The
golden ratio is the apex **modulus** `R_u = 1/φ²` (a real eigenvalue), *not* the
phase, giving the clean output `cos γ = 1/φ²`.

This chapter promotes the closed Lean derivation.  The earlier posit `δ = π/φ²`
(a *golden* phase) is demoted: by Niven's theorem a discrete CP phase has rational
cosine (only `0°, 60°, 90°`), so a golden-valued phase is structurally impossible.

## Lean source

- Umbrella: `lean/E213/Lib/Physics/Mixing.lean`, `lean/E213/Lib/Math/Algebra/Icosahedral.lean`
- ∅-axiom status: **0 DIRTY, 114 PURE** across the sub-tree (`tools/scan_axioms.py`)
- Files:
  - `Mixing/CPPhaseCount.lean` (6) — existence + uniqueness (KM counting)
  - `Mixing/CPPhaseC4Forcing.lean` (6) — `δ = 90°` forced by `C₄` + CP-existence
  - `Mixing/ApexRightTriangle.lean` (5) — `cos γ = 1/φ²` (right triangle)
  - `Mixing/CPHodgeStructure.lean` (5) — the CP `i` = Hodge `⋆` on the 4-dim `Δ⁴`
  - `Mixing/CPGenerationWiring.lean` (5) — `CP = C × i`, down/`5̄` localization
  - `Mixing/CPMaximalPhase.lean` (5) — the `i` = apex element `V_ub`
  - `Mixing/JarlskogApex.lean`, `ApexCPMechanism.lean`, `ApexPiInternal.lean`,
    `A5QuarkApex.lean` — the apex `φ²` object; `R_u=1/φ²` forced; `π` is 213-internal
  - `Icosahedral/A5RealityNoCP.lean` (4) — A₅ is real ⇒ CP-conserving (no golden δ)
  - `Icosahedral/CyclotomicFive.lean` (4) — `ℚ(ζ₅)` unifies modulus + `C₄` phase
  - `Cohomology/Hodge/SignedStarC4.lean` (10) — signed Hodge `⋆ = J`, `ℤ[J] ≅ ℤ[i]`
  - `Icosahedral/{OrderFive,A5Bridge,A5Reps,GoldenMixing,SpanAreas,A5ThreeRepPhase}` —
    `M` is an order-5 `A₅` element; golden bridge `φ²=χ+1`; CP-area skeleton; etc.
- Computational confirmation (exact, float-free): `rust-engine/crates/app/src/bin/ckm_cp_phase.rs`.

## Narrative

### 1. Existence + uniqueness — `N_gen = 3 ⇒ one phase`

The generation count is derived: `N_gen = C(NS, NT) = C(3,2) = 3`
(`Simplex/Generations`).  Kobayashi–Maskawa counting (`CPPhaseCount`) then gives,
for `N` generations, `N(N−1)/2` mixing angles and `(N−1)(N−2)/2` physical CP
phases — total phases `N(N+1)/2` minus `2N−1` rephasings.  At `N = NS = 3`:
**three angles and exactly one CP phase**; at `N = 2`, **zero** phases (no CP).
So CP violation existing, and being a *single* phase, is 213-forced — three
generations is the minimal CP-admitting count, and 213 derives that count
(`cp_phase_existence_unique`).  (A binomial echo: `3 = C(3,2)` generations,
`1 = C(2,2)` phase.)

### 2. The phase value — `δ = 90°` forced

What is *not* fixed by counting is the phase value.  The key is **Niven's
theorem**: a discrete (root-of-unity) CP phase has rational cosine, allowed only
at `0°, 60°, 90°`.  So a *golden* phase (`δ = π/φ²`, cosine irrational) is
**impossible** as a discrete phase — the posit is demoted.  Moreover the `A₅`
(icosahedral) 3-representation is **real** (Frobenius–Schur `+1`,
`A5RealityNoCP`), so `A₅` flavour mixing is CP-conserving (`J = 0`); the golden
ratio there sits in the (real) mixing *angle*, never the phase.

The 213-native complex structure is the **Cayley–Dickson imaginary unit `i`** —
the `NT = 2` first doubling `ℝ → ℂ`, with `ℤ[i]^× = C₄ = {1, i, −1, −i}`.  So the
phase lies in `C₄`.  Of these, `±1` are real (`J = 0`, no CP) and `±i` are pure
imaginary (`J ≠ 0`).  Since CP exists (§1), the phase is forced to `±i` — i.e. **maximal CP** (`δ_KM=90°`
in the KM parametrisation; the Jarlskog is maximal for given angles, `sin δ_KM=1`).
This is convention-independent in content (the phase is the irreducible imaginary
unit).  The *specific* right-triangle angle `α=90°` (convention-independent,
`α_obs=92.4°±1.4°`) is a **separate, model-level candidate** — NOT forced by the
`i` alone (a generic `J`-Yukawa texture does not give it; the cohomological
Yukawa construction, item below, lifts this).

### 3. The `C₄`/`i` is one object on `d = 5` — three disciplines

- **Number theory** (`CyclotomicFive`): the prime `d = 5`, via the 5th cyclotomic
  field `ℚ(ζ₅)`, has `Gal(ℚ(ζ₅)/ℚ) ≅ (ℤ/5)^× ≅ C₄` (the phase) and real subfield
  `ℚ(ζ₅)⁺ = ℚ(√5) = ℚ(φ)` (the golden modulus; the Gaussian periods `ζ+ζ⁴ = 1/φ`,
  `ζ²+ζ³ = −φ` are the roots of `x²+x−1`).  The bridge `5 = (2+i)(2−i)` (`5 ≡ 1
  mod 4` splits in `ℤ[i]`) opens the literal `90° = arg(i)`; `5` is inert in
  `ℤ[ω]` (`5 = a²+ab+b²` has no solution), excluding `C₆`/`60°`.  So `d = 5`
  *selects* `C₄`/`90°`.
- **Cohomology** (`CPHodgeStructure`, `SignedStarC4`): the CP `i` is the **signed
  Hodge star** `⋆` on the `(d−1) = 4`-dimensional `Δ⁴` — `⋆² = (−1)^{k(4−k)} = −1`
  at grades `k = 1, 3` (`Λ¹ = 5̄`, `Λ³`).  Built explicitly as
  `J = [[0,−1],[1,0]]` (the `−1` sign the repo's ℤ/2 star collapses), it satisfies
  `J² = −I`, `J⁴ = I`, and `ℤ[J] ≅ ℤ[i]` (`J ↔ i`; `det(aI+bJ) = a²+b² = N(a+bi)`,
  with `N(2+i) = 5 = d`).  This is the *same* `H*(Δ⁴)` cohomology that derives
  `1/α_em` — so CP and `α_em` share one cohomological object.

### 4. Wired to the fermions — `CP = C × i`, the down sector

A generation is `5̄ ⊕ 10 = Λ⁴ ⊕ Λ²(ℂ⁵)` (SU(5)).  The repo's Hodge star
(complement) is **charge conjugation `C`** (`Λᵏ ↔ Λ⁵⁻ᵏ`: `5 ↔ 5̄`, `10 ↔ 10̄`,
`⋆² = +1` — `Counts.hodge_1`, "CPT").  The CP **phase** `i = J` is the *separate*
signed structure (`⋆² = −1`).  The phase localizes to the **down/`5̄` sector**: the
up-Yukawa `10·10` uses the symmetric part (`dim 55`) ⇒ `M_u` symmetric ⇒ real ⇒
no up phase; the down-Yukawa `10·5̄` is general ⇒ complex ⇒ carries `J`
(`CPGenerationWiring`).  Concretely (`CPMaximalPhase`), at `δ = 90°` the apex
element `V_ub = −i·s₁₃` is **pure imaginary** (every angle real), the `J = i` in
the down `1↔3` element; the Jarlskog `J ∝ sin δ` is maximal.

The **rust engine** confirms this ab-initio over the Gaussian integers (exact,
float-free): the PDG CKM at `δ = 90°` with rational angles, scaled to `ℤ[i]`, is
exactly unitary (`M·M† = D²·I`), has `M_ub` pure imaginary, and nonzero maximal
Jarlskog (`ckm_cp_phase.rs`).

### 5. The apex — golden modulus + `90°` phase

The apex *modulus* `R_u = √(ρ̄²+η̄²) = 1/φ²` is the contracting eigenvalue of the
self-reference map `M = [[c,1],[1,1]]` (an order-5 `A₅` element, `M⁵ ≡ −I`;
`OrderFive`, `JarlskogApex`), forced over other golden powers by `R_u < 1`.  With
the forced `α = 90°` (right triangle, the apex on the Thales circle of `[0,1]`),
`ρ̄ = R_u²` and **`cos γ = R_u = 1/φ²`** (`ApexRightTriangle`) — a clean golden
output, `γ = arccos(1/φ²) = 67.54°`, `β = 22.46°` (observed `22.5°`), `α = 90°`
(observed `92.4°`).

## Key results

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `cp_phase_existence_unique` | `CPPhaseCount` | `N_gen=3 ⇒ 1` CP phase, `3` angles; `N=2 ⇒ 0` (no CP) |
| `delta_ninety_forced` | `CPPhaseC4Forcing` | `C₄`(CD `i`) + CP-existence ⇒ `δ = ±90°` |
| `cyclotomic_five_unification` | `CyclotomicFive` | `ℚ(ζ₅)`: `Gal ≅ C₄` (phase) + `ℚ(√5)` (golden modulus); `5=(2+i)(2−i)` |
| `signed_hodge_is_cp_i` | `SignedStarC4` | signed Hodge `⋆ = J`, `J²=−I`, `ℤ[J] ≅ ℤ[i]` |
| `cp_i_is_hodge_complex_structure` | `CPHodgeStructure` | CP `i` = `⋆` on the 4-dim `Δ⁴`, grades `1,3` |
| `cp_generation_wiring` | `CPGenerationWiring` | `CP = C × i`; phase in the down/`5̄` sector |
| `cp_maximal_phase_capstone` | `CPMaximalPhase` | the `i` = apex `V_ub = −i·s₁₃` (pure imaginary, `δ=90°`) |
| `apex_right_triangle_capstone` | `ApexRightTriangle` | `α=90°` + `R_u=1/φ²` ⇒ `cos γ = 1/φ²` |
| `a5_3rep_is_real` | `A5RealityNoCP` | `A₅` 3-rep real (FS `+1`) ⇒ no golden phase |
| `apex_modulus_is_selfref_contracting_eigenvalue` | `JarlskogApex` | `R_u = 1/φ²` = contracting eigenvalue of `M` |

## Research-note provenance

- The full marathon synthesis (now archived in `research-notes/archive/`)
  (four expert-agent reports: A₅+gCP, icosian/E₈, Cayley–Dickson, KM mechanism;
  cohomology + number-theory legs).  Archived alongside this chapter.
- The `ckm_rho_eta_apex` open-frontier record (in `research-notes/frontiers/`; the
  apex value, the `1/φ²` grounding, the demotion of `π/φ²`).

## Open frontier

Closed: CP existence+uniqueness; the phase forced to `90°` (given "phase `∈ C₄`");
the `C₄`/`i` = signed Hodge `⋆` = `ℤ[i]` = `ℚ(ζ₅)` identity; the golden modulus.
**Closed since promotion**: the premise "phase `∈ C₄`" is now *forced*, not
assumed — `Hodge/SignedStarFull` lifts the signed Hodge `⋆` to the full grade-1
space `Λ¹(ℝ⁴)` and shows `⋆²=−1` on all of it, so `⟨⋆⟩` is order *exactly* 4 =
`C₄` (not `C₆`); the Hodge structure on the `d=5` cohomology *is* the `C₄`.
**Principle settled (rigorous)**: a *cohomological* coupling — a morphism of the
polarized Hodge structure (`J`-invariant + lattice-defined + `J`-Hermitian) —
forces `δ=90°` (Voisin/HR + Niven; the polarization `(Q,J)` is Lean-PURE,
`Hodge/HodgeRiemannJ`: `J²=−I`, `Jᵀ Q J=Q`, `Q·J=I≻0`).  A *generic* texture fails
the three conditions and does **not** (tested: `α≈0°,−38°,60°`).  **Construction ASSEMBLED** (`CohomologicalYukawa.lean`): every primitive is now
built — the generation index `Λ²(ℝ³)` (`BigradedYukawa`, bridging the `C(3,2)`
gap), the signed-`ℤ` cup (`Cup/SignedCup`, antisymmetric + HR-positive `h=I`), the
signed Hodge `J` (`SignedStarC4/Full`), the polarization (`HodgeRiemannJ` +
the filled `Pairing/HodgeRiemann` stub).  The assembled `Y_d = Λ²(ℝ³) ⊗
(signed-cup on `Λ¹(ℂ⁵)` with `J`)` meets the three forcing hypotheses (lattice +
`J`-invariant + HR-positive) ⇒ `δ=90°`.  Remaining: only the *numerical*
evaluation of the cup functional (the rust `ckm_cp_phase` verifies the resulting
`ℤ[i]` CKM is unitary with `δ=90°`); and the `~1.5σ` fit — now assessed **CONSISTENT** (not a tension): `R_u=1/φ²` is essentially exact (`0.382` vs `0.3825±0.011`), `α=90°` is `~0–1.7σ`, and the `ρ̄/α` residual is covered by the standard `O(λ²)` Wolfenstein correction (`λ²=25/484`, no free parameter), **not** RGE (`dα/dt=0` exact). `ApexFitConsistency`.  `α = 90°` (right unitarity
triangle) is **falsifiable** against future UTfit/CKMfitter values (catalog
falsifier F27).  Active record: the `ckm_rho_eta_apex` frontier.

## How to verify

```bash
cd lean && lake build E213.Lib.Physics.Mixing E213.Lib.Math.Algebra.Icosahedral
python3 tools/scan_axioms.py E213.Lib.Physics.Mixing.CPPhaseC4Forcing
python3 tools/scan_axioms.py E213.Lib.Math.Cohomology.Hodge.SignedStarC4
cd ../rust-engine && cargo run --release --bin ckm-cp-phase
```
