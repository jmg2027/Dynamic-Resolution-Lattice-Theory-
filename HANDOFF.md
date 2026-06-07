# Session Handoff — 2026-06-07 (Vision-achievement strategy + α_em DoF audit)

## Branch
`claude/vision-achievement-strategy-UzqpZ` — pushed, **9 commits ahead** of
`origin/main` (branched from `540504f`, the prior QR handoff).
`cd lean && lake build E213.Lib.Physics.AlphaEM` ✓ clean. All new theorems
PURE (verified per file via `tools/scan_axioms.py`).

## Theme
Strategic question from the originator: "how do I actually *succeed* at the
vision?" Answer built as a tool chain addressing the central gap **∅-axiom
purity ≠ 0 researcher degrees-of-freedom**, then applied to the `1/α_em`
derivation: enumerate every choice, force/derive what can be, name the rest
honestly. No fudge introduced; the discipline IS the deliverable.

## What Was Done This Session

### 1. Strategy + on-ramp docs (top-level, prose)
- **`VERIFICATION_SPINE.md`** — single afternoon-audit path: 3-clause Raw
  axiom → forced `(NS,NT,c,d)=(3,2,2,5)` → `1/α_em` at 0.2 ppb, every step a
  named PURE theorem with `#print axioms` empty. §0 separates purity from
  0-DoF; §2 (forcing chain) = zero-DoF crown jewel; §6 names the open edge.
- **`DEGREES_OF_FREEDOM_LEDGER.md`** — the falsifiability instrument: every
  choice in `1/α_em` tagged `forced/derived/assignment/modeling-form/fitted?`.
  Honest defense of "0 free parameters" by ledger, not philosophy.
- **`PRE_REGISTRATION.md`** — retrodiction→prediction. Three near-term
  *forward* predictions: **P1** ν ordering = normal (JUNO ~2030, binary);
  **P2** θ_QCD ≈ 2.86×10⁻¹¹ (nEDM ~2027–30, contrarian vs axion→0);
  **P3** sin²θ₂₃ = 1/2 (DUNE/HK ~2030+). External arXiv/Zenodo DOI deposit
  recommended (outside repo) for unforgeable priority.

### 2. Self-audit caught a hidden input (integrity)
- **P2 θ_QCD demoted**: auditing `θ_QCD = J·α_GUT⁴` found the **Jarlskog
  prefactor J≈3×10⁻⁵ is NOT derived** — `CPViolation.J_lambda_dependence`
  proves only the λ-power *structure* (λ=5/22), in-code "Hmm not the right
  magnitude"; `theta_QCD_num := 286` is hardcoded. P2 re-registered as a
  *cross-prediction* (given measured J + derived α_GUT), ⚠ flagged. Logged in
  the ledger's `fitted?` rows.

### 3. α_em Layer-1 assignment DoF — CLOSED (2 PURE Lean files)
- **`AssignmentUniqueness.lean`** (9 thms PURE) — each leading coefficient
  (60,30,25,45) is the *unique* box-monomial (`repr_*_unique`); residual
  sharpened to the single `NT↔c` degeneracy (`NT=c=2`).
- **`AssignmentForcing.lean`** (9 thms PURE) — closes NT↔c via the
  **edge-count structure**: only `c·NS·NT` is the K_{3,2}^{(c)} edge count;
  the three readings coincide *only* at the DRLT point and diverge off it
  (`readings_diverge_off_drlt`: 18≠12≠27 at c=3); c and NT are distinct
  operations (`+NS·NT` vs `+c·NS`). Capstone `nt_c_degeneracy_resolved`.

### 4. α_em Gram `/d²` — cubic reduced + value over-determined + mechanism identified (3 PURE files)
- **`GramCubicReduction.lean`** (1 PURE) — the cubic `25y³+1=25Xy²` is the
  algebraic re-expression of `correction=α²/d²` (`cubic_is_correction_ansatz`),
  not an independent modeling choice. Reduces the `modeling-form` DoF to "why
  α²/d²?".
- **`GramD2Readings.lean`** (3 PURE) — the three prefactor readings
  (fullDimSquared / gramMatrixEntries / inv_alpha_GUT_factor) all `= d²=25`
  (`three_readings_coincide`); value over-determined, not a choice.
- **`GramD2Mechanism.lean`** (5 PURE) — **the mechanism** (originator's
  intuition, found on the math side): a self-energy is degree-2 (2-point), and
  a degree-2 object on the d=5 Δ⁴ state space normalizes by `d²` — grounded in
  two convergent structures: 2-point operator-space dim `tensorDim d d = d²`
  (Linalg213/Gap/TensorProduct, 5⊗5=25) AND 2-fold cup-graduation denom
  `cup_graduation_denom 1 = d²` (`mechanisms_converge`).

## Current Precision Results (0 free parameters)
No physics-constant *values* changed this session — this was a DoF *audit* of
the standing `1/α_em` result. Standing table in `catalogs/physics-constants.md`;
headline `1/α_em = 137.0359991` structural vs CODATA `137.0359991` (0.2 ppb,
`invAlphaEm_precision_theorem` PURE). All session theorems PURE (0 sorry / 0
axiom / 0 Mathlib / 0 Classical / 0 native_decide); two general lemmas that
came out propext-DIRTY under `rw` were replaced with PURE concrete witnesses
(0-DIRTY discipline held).

## Open Problems (Priority Order)

### 1. Gram `/d²` — last premise + cup-graduation derivation
Mechanism is identified (degree-2 → d², two convergent structures) but two
pieces remain: **(a)** a forcing theorem identifying the Gram self-energy *as*
the `k=1` self-pairing cup term (promote `CupRingTrace`/`SelfPairingTrace`
test → derivation); **(b)** derive the cup-graduation rule "each cup factor
carries 1/d" from cup-ring axioms (currently a structural assertion in
`RefinedCupLadderDerivation` §1; likely ties to ProjectionRatios' d-fold
structure — multi-session). The *math* leg (dim End V = d²) is solid; the gap
is the physics identification + the underived cup rule.
Frontier: `research-notes/frontiers/gram_d2_prefactor.md`.

### 2. Jarlskog J magnitude (promote θ_QCD P2 to a clean prediction)
Derive J≈3×10⁻⁵'s *magnitude* (not just λ-power structure) from λ=5/22 +
δ_CP=π/φ². Closes the hidden input in `PRE_REGISTRATION.md` P2.
Frontier: needs a note (none yet) — see `CPViolation.J_lambda_dependence`.

### 3. Gram Newton truncation + 27×10⁻⁹ residual
Replace observed-α on the RHS of `gram_correction_e9` with a 213-internal
cubic-root iterate; bound the 27×10⁻⁹ post-Gram residual (next-order Dyson
tail). The remaining `modeling-form` item after #1.
Frontier: `research-notes/frontiers/gram_d2_prefactor.md` (second sub-item).

### 4. v2 coupling refinements (H³ imbalance, α_GUT² self-interaction)
The `fitted?` rows in the ledger: `3·α_GUT→4·α_GUT` (1/α_2) and `+α_GUT²/2`
(1/α_3) need forcing arguments or research-tier demotion.

### 5. Carried from prior session (math frontier)
Cubic/biquadratic reciprocity over ℤ[ω]/ℤ[i]; Zolotarev; Fubini unification;
Ricci-flow smooth core. See git `540504f` handoff content (now superseded by
this file; those items live in their frontier notes).

## Unresolved from This Session
- **Did NOT close** the Gram `/d²` *fully*. After genuine investigation
  (§5.4 guard), the cup-graduation rule is an underived structural assertion
  and the self-energy↔cup identification is interpretive — manufacturing a
  theorem there was declined on integrity grounds. Reported plainly; the
  honest limit for this session.
- **External DOI deposit** of `PRE_REGISTRATION.md` P1–P3 is the highest-value
  action that must happen *outside* the repo (arXiv/Zenodo) — not done here.

## Next
Either: (1) attack Open Problem #1(b) — derive the cup-graduation `1/d`-per-
factor rule from the cohomology projection structure (the deeper, solid
target); or (2) Open Problem #2 — derive the Jarlskog magnitude to promote
θ_QCD P2; or (3) deposit P1–P3 externally for priority. The vision tool chain
(spine + ledger + pre-registration) is complete and reusable for the *next*
headline (extend the ledger to m_μ/m_e and m_p).

## Three-tier state (per `CLAUDE.md` "Three-tier discipline")
- **Promotions this session**: none (the new Lean files are content; the
  top-level prose docs are strategic instruments, not theory/ chapters).
- **Promotion candidates**: the AlphaEM DoF-audit sub-tree
  (`AssignmentUniqueness`, `AssignmentForcing`, `GramCubicReduction`,
  `GramD2Readings`, `GramD2Mechanism`) could get a `theory/physics/alpha_em/`
  section once Open Problem #1 closes (currently a live frontier, not closed).
- **Active scratchpad**: `research-notes/frontiers/gram_d2_prefactor.md`
  (registered in `frontiers/INDEX.md`).

## File Map
```
VERIFICATION_SPINE.md                              ← axiom→1/α_em audit path (on-ramp)
DEGREES_OF_FREEDOM_LEDGER.md                       ← per-choice DoF audit of 1/α_em
PRE_REGISTRATION.md                                ← P1-P3 forward predictions (P2 ⚠ flagged)
research-notes/frontiers/gram_d2_prefactor.md      ← open: /d² mechanism last premise
research-notes/frontiers/INDEX.md                  ← + gram_d2_prefactor entry
lean/E213/Lib/Physics/AlphaEM/AssignmentUniqueness.lean ← 9 PURE: coeff value uniqueness
lean/E213/Lib/Physics/AlphaEM/AssignmentForcing.lean    ← 9 PURE: NT↔c closed (edge-count)
lean/E213/Lib/Physics/AlphaEM/GramCubicReduction.lean   ← 1 PURE: cubic = α²/d² ansatz
lean/E213/Lib/Physics/AlphaEM/GramD2Readings.lean       ← 3 PURE: d² value over-determined
lean/E213/Lib/Physics/AlphaEM/GramD2Mechanism.lean      ← 5 PURE: degree-2 → d² mechanism
lean/E213/Lib/Physics/AlphaEM.lean                      ← umbrella: + 5 new imports
```
