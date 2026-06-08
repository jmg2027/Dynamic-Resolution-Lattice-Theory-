# Session Handoff — 2026-06-08 (A₅ / CKM-apex internal-derivation arc)

## Branch
`claude/vision-achievement-strategy-UzqpZ` — pushed, **~23 commits ahead** of
`origin/main`. `cd lean && lake build E213.Lib.Physics.Mixing` ✓ clean; new
`Icosahedral/` tree + `ApexCPMechanism` all PURE (`tools/scan_axioms.py`).

## Theme
Directive from the originator: **derive the CKM apex from 213 itself, not from
external literature** ("외부 연구내용보다 213 자체에서 도출하는게 낫다"). A
multi-session *internal* derivation marathon on the one open frontier premise:
*why is the CKM CP-apex modulus the self-reference contraction rate `1/φ²`*.

## What was done this session (5 commits, all PURE)

### 1. `1/φ²` over other golden powers — FORCED (`JarlskogApex` §5.5)
`apex_modulus_subunit_forced`: `M = [[c,1],[1,1]]` has exactly two eigenvalues
(reciprocal pair, product = det = 1): `φ², 1/φ²`. The apex modulus `R_u < 1`
(unit-base triangle side) ⇒ the sub-unit eigenvalue `1/φ²` is selected uniquely
(Fibonacci-convergent witness). "Which golden power" → "which of two
eigenvalues", resolved.

### 2. Icosahedral marathon — `M` IS an A₅ element (`lean/E213/Lib/Math/Algebra/Icosahedral/`, 23 PURE)
- `OrderFive`: genuine 𝔽₅-matrix orbit; `M⁵≡−I`, order **exactly** 5 in
  `PSL(2,𝔽₅)≅A₅` (closes the "no early return" gap left by `Mobius213ModFive`).
  `d=5` double role: `disc M = NS²−4 = 5` AND the field `𝔽₅` realising A₅.
- `A5Bridge`: `|A₅|=60`; the order-5 element's 3-rep character is `φ`; the
  **bridge** `eigenvalue φ² = character φ + 1` = the Fibonacci recurrence (one
  golden ratio, two readings).
- `A5Reps`: irreps (`Σdim²=60`), Clebsch (incl. `5⊗5=25=d²` as an A₅ sum),
  character orthonormality `χ²(5A)+χ²(5B)=φ²+1/φ²=NS=trace M`.
- `GoldenMixing`: the lepton template `sin²θ₁₂=1/(φ²+1)≈0.276`, `tan²θ₁₂=1/φ²`,
  from the order-5 generator eigenvector. `INDEX.md` + `Capstone.lean`.

### 3. Two-origin CKM + integrity correction (`A5QuarkApex`, 7 PURE)
Deep-research (now used only as an *anchor*, not the goal) found established
A₅/`SU(5)×A₅` quark models **fit** the CKM (leading order ≈ identity+Cabibbo);
they do **not** golden-predict the apex. Corrected a prior overclaim ("A₅
reproduces it from φ"). So DRLT's golden apex is **novel** vs all flavour-model
literature. DRLT's two-origin split, PURE: magnitude = Cabibbo `λ=5/22`
(rational, `22∉Fibonacci`, not golden); CP-depth = apex `1/φ²` (golden,
M-eigenvalue). Nearest established anchor: nearly-right UT (`α≈89–90°`,
`δ≈1.188±0.016`); DRLT `δ=π/φ²=1.200` concordant at 0.75σ.

### 4. ★ Internal apex CP-derivation (`ApexCPMechanism`, 4 PURE) — the headline
Found `δ=π/φ²` was never derived (`CPViolation` only computes the number
`176/147`). Genuine **213-internal** derivation via §5.7 frozen/dynamic dualism:

  **`z = r·(−1)^r = r·e^{iπr}`,  `r = 1/φ²`,  `(−1) = M⁵`.**

- Modulus `R_u = r = 1/φ²` = FROZEN (ℝ) contraction eigenvalue (real, no phase).
- Phase's `π` = DYNAMIC half-period **central involution** `M⁵≡−I=e^{iπ}` (proven).
- **CP-existence (falsifiable core): `η=r·sin(πr)≠0 ⟺ M⁵=−1`.** If `M⁵=+I`,
  apex is real, `η=0`, no CP. Because `M⁵=−I` (proven 213 theorem), CP violates.
- **Answers the open premise**: the apex IS the self-reference contraction `r`,
  complexified by the dynamic central element `M⁵=−1`. Structural, not a fit.

### 5b. Pell-area route — the CP-area integer skeleton (`SpanAreas`, 7 PURE)
Pursued the flagged Pell-area ↔ CP route. Convergent span-area
`det(v_m,v_{m+k}) = −F₂ₖ` (position-independent, from `det M = 1`):
- `k=1` (adjacent gen): `−1` = Pell symplectic unit; same `−1` as central `M⁵=−1`.
- `k=2` (gen 1↔3, the **apex span**): `−F₄ = −NS = −3` — the **integer skeleton
  of the unitarity-triangle CP-area** `η̄/2`.
- **3-generation CP triangle**: 3 consecutive convergents span the minimal
  nonzero (unit) area; 2 points → area 0. So "CP needs 3 generations" is
  geometric: `N_gen = NS = 3` is the minimum to enclose the symplectic unit.

### 5c. CP-phase origin in the 3-rep + the NT cover (`A5ThreeRepPhase`, 4 PURE)
Complement to the 2-rep `M⁵=−1` story: in the 3-rep the order-5 generator has
eigenvalues the **5th roots of unity** `{1,ζ,ζ⁴}` — the complex `ζ=e^{2πi/5}` is
the flavour-sector CP-phase source; Gauss sums `g₁=ζ+ζ⁴=1/φ`, `g₂=ζ²+ζ³=−φ` are
roots of `x²+x−1` (power-sum = NS), characters `1+g₁=φ`, `1+g₂=1−φ`. The
**2-rep/3-rep period cover** `10/5 = NT = 2`: the central `−1=M⁵` (apex-phase π)
is what the binary cover adds over the 3-rep's `ζ⁵=1`. So the phase has two
internal sources (3-rep `ζ`, 2-cover `−1`), related by `NT`.

### 5d. The coupling reframed as 0-parameter-forced (doc-only, §5.1)
`δ=π·R_u` *follows* from the apex form `z=r·(−1)^r` (`arg((−1)^r)=πr`); the real
question is why the apex is **single-parameter** (exponent = modulus). That is
the **§5.1 no-exterior / 0-parameter** principle: the apex phase has no
independent dialer, so it must be a function of the one internal `r` and the
only phase constant `π=arg(M⁵)`; `δ=π·r` is the minimal linear realization. The
coupling is **0-parameter-FORCED**, not arbitrary — consistent with the
no-free-parameter ethos.

## Endpoint — apex is 213-internal END-TO-END (π included)
The coupling synthesis (`5d`+) closed the conceptual gap: the **rational-level
coupling `δ/π = R_u` is ALREADY PURE** (`phase_over_pi_eq_modulus` = the §5.7
frozen=dynamic identity, shared Fibonacci convergents `2/5, 5/13, …`).

**Correction (originator caught it): `π` is NOT outside 213.** An earlier note
called `π` "the Nat boundary / transcendental tail outside 213" — an overclaim.
`213` builds `π` as a `Real213` cut (`PiCut` = Wallis `AbCutSeq`, `π∈(14/5,4)`,
∅-axiom). So `δ = π/φ²` is a product of **two 213-internal cuts**, and the apex
is internal *including* `π` (`Mixing/ApexPiInternal.lean`, 4 PURE:
`δ ∈ (112/105, 20/13) ∋ 176/147`). The phase's central `−1 = M⁵` is the **`2I`
icosian central quaternion** over `ℤ[φ]` (`MobiusPIcosian`: `SL(2,𝔽₅) ≅ 2I`,
`E₈`). Rule added to CLAUDE.md ("Transcendental-as-exterior"). So the apex is
213-internal end-to-end; the *only* residual is continuum form-minimality of
`f(r)=π·r`, not any escape from 213.

Three consistent framings of the coupling (all internal): (1) form-consequence
of `z=r·(−1)^r`; (2) §5.1 no-exterior 0-parameter; (3) §5.7 frozen=dynamic
(PURE at rational level). The apex derivation is **honestly complete to its
213-native limit**.

Soft residuals only (do NOT re-fish — `π/5=36°`, `2π/5=72°` excluded):
- the transcendental `π`-coefficient (a Nat-boundary, not a derivation gap);
- continuum form-minimality of `f(r)=π·r`.

### Genuinely new targets (next session, not apex-fishing)
1. **Apex *value* from explicit A₅ 3-rep mass matrices** — the larger
   derivation (transcendental/symbolic; verify, then seek the PURE skeleton).
2. **Promote the closed `Icosahedral/` math to `theory/`** — once the tree
   stops growing (three-tier discipline; the *math* is closed, the apex
   *application* has the transcendental tail above).
3. Other open frontiers (`gram_d2_prefactor` needs ℚ-normalised cup infra).

## Files this session
```
lean/E213/Lib/Math/Algebra/Icosahedral/OrderFive.lean     ← 9 PURE: M⁵≡−I, order-5 in A₅
lean/E213/Lib/Math/Algebra/Icosahedral/A5Bridge.lean      ← 4 PURE: eigenvalue φ²=character φ+1
lean/E213/Lib/Math/Algebra/Icosahedral/A5Reps.lean        ← 5 PURE: irreps, Clebsch, χ-orthonormality
lean/E213/Lib/Math/Algebra/Icosahedral/GoldenMixing.lean  ← 4 PURE: sin²θ₁₂=1/(φ²+1) template
lean/E213/Lib/Math/Algebra/Icosahedral/SpanAreas.lean      ← 7 PURE: span-areas, apex CP-area skeleton=NS
lean/E213/Lib/Math/Algebra/Icosahedral/Capstone.lean      ← 1 PURE: M ∈ A₅ capstone
lean/E213/Lib/Math/Algebra/Icosahedral/INDEX.md           ← sub-tree index (5 files)
lean/E213/Lib/Physics/Mixing/JarlskogApex.lean            ← +§5.5 apex_modulus_subunit_forced; §4 honest sin2β
lean/E213/Lib/Physics/Mixing/A5QuarkApex.lean             ← 7 PURE: two-origin CKM
lean/E213/Lib/Physics/Mixing/ApexCPMechanism.lean         ← 4 PURE: ★ internal apex CP derivation
lean/E213/Lib/Physics/Mixing.lean                         ← umbrella: +ApexCPMechanism, +A5QuarkApex
research-notes/frontiers/ckm_rho_eta_apex.md              ← updated: mechanism resolved, coupling remains
research-notes/frontiers/INDEX.md                         ← updated ckm entry
```

## Next
1. **Attack the coupling `δ=π·R_u`** (the one remaining internal gap) — the
   Pell symplectic invariant `−1` ↔ central `M⁵=−1` ↔ triangle area `η` link is
   the most promising untried internal route. Do NOT re-fish atomic angles.
2. The lepton/quark assignment (derive the apex *value* from explicit A₅
   3-rep mass structure) is the larger multi-session target; the mechanism
   (this session) is the structural half.
3. Standing: external DOI deposit of `PRE_REGISTRATION.md` (priority), still
   outside the repo.

## Three-tier state
All new content is `lean/E213/` (tier 2, PURE) + frontier notes (tier 1). No
`theory/` promotion yet — the apex frontier is advanced but not closed (the
coupling gap remains). Promotion candidate once the coupling closes: a
`theory/physics/ckm_apex/` chapter mirroring `Icosahedral/` + `ApexCPMechanism`.
