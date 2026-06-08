# Session Handoff — 2026-06-07 (Vision strategy + α_em DoF audit + CKM/J arc)

## Branch
`claude/vision-achievement-strategy-UzqpZ` — pushed, **~18 commits ahead** of
`origin/main` (branched from `540504f`, the prior QR handoff).
`cd lean && lake build E213.Lib.Physics.{AlphaEM,Mixing}` ✓ clean. All new
theorems PURE (verified per file via `tools/scan_axioms.py`).

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

### 5. CKM / Jarlskog arc — self-audit → apex → self-reference eigenvalue
Triggered by trying to promote θ_QCD P2 (derive `J`). Findings (all in
`lean/E213/Lib/Physics/Mixing/JarlskogApex.lean`, 12 PURE, + `CPViolation.lean`
docstring fix):
- **Self-audit caught an overclaim**: DRLT's Jarlskog `J`, computed honestly
  from its own derived factors (λ=5/22, A=φ/c=φ/2, δ=π/φ²), gives `8.18×10⁻⁵`
  vs observed `3.08×10⁻⁵` — **×2.66 over**. A `CPViolation.lean` comment had
  masked this with an arithmetic error ("≈3.5×10⁻⁵, within 10%"; its own
  factors give 7.6×10⁻⁵). Corrected to an honest missing-physics note (no Lean
  theorem asserted the wrong magnitude — comment-only).
- **Missing physics = the CKM apex `(ρ,η)`**: `s₁₃=Aλ³` omits `√(ρ²+η²)`.
- **Apex = a φ² object**: modulus `R_u = 1/φ²`, phase `δ = π/φ²` (same φ²).
  Gives `R_u=0.382` (0.17% vs obs), `J=3.12×10⁻⁵` (+1.4%), `η=0.356` (2.3%).
  `c/d=2/5=F₃/F₅` (F₃=NT,F₅=d) is the lowest Fibonacci convergent of 1/φ², not
  a competitor.
- **Single-parameter**: `δ=π·R_u`, apex `= r·e^{iπr}`, `r=1/φ²`. Determines the
  triangle and predicts `β=22.45°`, `sin2β=0.706` (inside obs `0.695±0.019`,
  the measured "golden mode"), `α=88.8°`, `R_t=0.932`.
- **`1/φ²` grounded**: it is the **contracting eigenvalue of the residue
  self-reference matrix** `[[c,1],[1,1]]` (Möbius `P`, §5.6) — `trace=NS`,
  `det=1`, `disc=NS²−4=d`, eigenvalues φ²,1/φ². So `R_u=(NS−√d)/2`, structurally
  distinguished (not a fitted golden power). PURE.
- **NOT closed** (honest §5.4): the physical identification "CKM CP-apex
  modulus = self-reference contraction rate" is the single open premise. A
  law-of-sines route (β≈π/8, 8=NS²−1) is consistent at 0.2% but β=π/8 is a 2%
  match — flagged as approximation-stacking / fishing risk; do NOT re-fish.
  Frontier: `research-notes/frontiers/ckm_rho_eta_apex.md`.

### 6. Headline audit + honest README/catalog rewrite
Applied the DoF-ledger lens to the README headline table (5 results).
`research-notes/frontiers/headline_precision_scope.md`:
- **Koide `Q = NT/NS = 2/3`** — genuinely clean, 0 param, no scale ✓.
- **α_em** — ppb precision *is* a PURE theorem (`invAlphaEm_precision_theorem`,
  137.035999111 vs CODATA, 0.2 ppb); residual = assembly DoF (ledger, mostly
  closed).
- **m_μ/m_e** — PURE proves only the leading integer bracket (205); the 0.49 ppb
  is docstring (Dyson `P` + δ's), inherits α_em.
- **m_p** — PURE proves 0.1% bracket; `Λ_QCD≈308 MeV` is docstring-only (no atomic
  derivation located) → input scale. Real content = ratio `m_p/Λ_QCD = NS·P`.
- **IE(H)** — PURE proves ~0.1% bracket; uses CODATA `m_e` (textbook `m_eα²/2`).
  Most overstated row (4.3 ppb claimed).
- **Synthesis**: DRLT genuinely predicts dimensionless *ratios*; absolutes need
  input scales (any theory does). Not fraud — atomic building blocks + honest
  in-file tags real; gap was the README table overstating docstring/scale
  precisions as PURE-proven parameter-free.
- **Fixed**: `README.md` headline table rewritten honestly (A. parameter-free
  ratios + exact combinatorics | B. absolutes needing a scale, with "what Lean
  proves" per row); `catalogs/physics-constants.md` header caveat added.

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

### 2. CKM apex — one physical identification to pin J (mostly solved)
`R_u = 1/φ²` (apex modulus) is grounded as the residue self-reference Möbius
contracting eigenvalue `(NS−√d)/2` (PURE). The single open premise: **why the
CKM CP-apex modulus = the self-reference contraction rate** — a *structural*
reason, not another % match (the law-of-sines/β=π/8 route is approximation-
stacking, do not re-fish). Closing it makes `J=A²λ⁶η` atom-pinned (currently
1.4% on J) and resolves θ_QCD P2. Frontier:
`research-notes/frontiers/ckm_rho_eta_apex.md`.

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
lean/E213/Lib/Physics/AlphaEM/GramD2Readings.lean       ← 3 PURE: d² value over-determined
lean/E213/Lib/Physics/AlphaEM/GramD2Mechanism.lean      ← 5 PURE: degree-2 → d² mechanism
lean/E213/Lib/Physics/Mixing/JarlskogApex.lean          ← 12 PURE: φ² apex = self-ref eigenvalue
lean/E213/Lib/Physics/Mixing/CPViolation.lean           ← docstring: honest J magnitude-gap note
lean/E213/Lib/Physics/Mixing.lean                       ← umbrella: + JarlskogApex
research-notes/frontiers/gram_d2_prefactor.md           ← open: /d² mechanism + "not Gram" reframe
research-notes/frontiers/ckm_rho_eta_apex.md            ← open: apex identification (do not re-fish)
research-notes/frontiers/headline_precision_scope.md    ← headline audit (PURE scope vs README precision)
README.md                                               ← headline table rewritten honestly (A ratios / B absolutes)
catalogs/physics-constants.md                           ← header caveat (precision tags = central-value)
```

## Highest-value next actions (vision)
1. **Deposit `PRE_REGISTRATION.md` P1/P3 externally** (arXiv/Zenodo DOI) — the
   one unforgeable-priority action, outside the repo. (P2/θ_QCD is candidate-
   level pending the CKM-apex identification.)
2. **Finish the headline audit** — same lens on the remaining catalog rows
   (η_B, m_t/m_c, M_Pl/v_H, magic numbers) for full README/catalog honesty.
3. **CKM apex** — the one structural identification (`ckm_rho_eta_apex.md`):
   why CP-apex modulus = the §5.6 self-reference contracting eigenvalue `1/φ²`.
   Do NOT re-fish atomic-angle % matches.
4. **Gram `/d²`** — the one premise (`gram_d2_prefactor.md`): identify the Gram
   self-energy as the `k=1` self-pairing cup term.
