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

## The one remaining internal gap (NEXT TARGET)
The frozen↔dynamic **coupling** `δ = π·R_u` (phase `= π ×` modulus, i.e.
`δ/π = r = 1/φ²`). Both *ingredients* are now internal (`r` frozen, `π=M⁵`
dynamic) and the CP-existence mechanism is derived; what is **not yet forced**
is *why the two Lens readings couple as `phase = π·modulus`*.
- Tried and rejected (do NOT re-fish): the naive one-step spiral gives per-step
  rotation `π/5 = 36°` (from `M⁵=−I` over 5 steps), NOT `π/φ²=68.75°`. So the
  coupling is not a simple spiral step. The icosahedral `2π/5=72°` is also wrong.
- Next real step: find why the dynamic phase *fraction* `δ/π` equals the frozen
  contraction `r` — likely in how the 3-generation (3-rep) span maps to the
  M-iteration depth, or the Pell symplectic invariant (`pell_unit_at = −1`,
  the conserved area = the CP/area part). The Pell area invariant `−1` and the
  central `M⁵=−1` are the same `−1`; the η (triangle area) link is unprobed.

## Files this session
```
lean/E213/Lib/Math/Algebra/Icosahedral/OrderFive.lean     ← 9 PURE: M⁵≡−I, order-5 in A₅
lean/E213/Lib/Math/Algebra/Icosahedral/A5Bridge.lean      ← 4 PURE: eigenvalue φ²=character φ+1
lean/E213/Lib/Math/Algebra/Icosahedral/A5Reps.lean        ← 5 PURE: irreps, Clebsch, χ-orthonormality
lean/E213/Lib/Math/Algebra/Icosahedral/GoldenMixing.lean  ← 4 PURE: sin²θ₁₂=1/(φ²+1) template
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
