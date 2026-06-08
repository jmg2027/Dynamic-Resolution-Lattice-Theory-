# Session Handoff — 2026-06-08 (CKM CP-phase: multi-disciplinary derivation marathon)

## Branch
`claude/vision-achievement-strategy-UzqpZ` — pushed, far ahead of `origin/main`.
`cd lean && lake build E213.Lib.Physics.Mixing` ✓ clean. All new theorems PURE
(114 PURE / 0 dirty across the session, `tools/scan_axioms.py`). Rust engine
binary `ckm-cp-phase` builds + runs (`cargo run --release --bin ckm-cp-phase`).

## Theme
Originator's direction, in stages: (1) "derive from 213, not literature";
(2) "go deeper — cohomology + number theory, not just group theory";
(3) "ab-initio diagonalisation via the rust engine". Result: the CKM **CP phase**
is derived/forced (not posited) and grounded across **three disciplines**, with
an exact float-free computational confirmation.

## The headline result

The posit `δ = π/φ²` (a golden phase) is **demoted** (Niven's theorem: a discrete
CP phase has rational cosine ⇒ root of unity; golden `π/φ²` is impossible). The
213-coherent CP structure is **golden modulus `R_u=1/φ²` + `90°` phase**, all from
the single prime `d = NS+NT = 5`:

```
① CP existence+uniqueness  N_gen=C(3,2)=3 ⇒ 1 phase (KM counting) ──── DERIVED
② CP phase = 90°           C₄(CD i)+CP-existence ⇒ real phases J=0 excluded ⇒ ±i ── FORCED
③ the C₄/i = d=5 complex structure, three disciplines:
     · group       CD doubling ℤ[i]^×
     · number thy  ℚ(ζ₅): Gal≅C₄ (phase) + real subfield ℚ(√5)=ℚ(φ) (modulus);
                   bridge 5=(2+i)(2−i) selects C₄/90° over C₆/60° (5 inert in ℤ[ω])
     · cohomology  signed Hodge ⋆ on the (d−1)=4-dim Δ⁴ (⋆²=−1 at grades 1,3)
                   = J=[[0,−1],[1,0]], ℤ[J]≅ℤ[i] — the SAME H*(Δ⁴) as 1/α_em ── PROVEN
④ wired to fermions  CP = C × i : C=Hodge complement (5↔5̄, ⋆²=+1, charge conj);
                     i=J localizes to down/5̄ (up-Yukawa 10·10 symmetric⇒real)
⑤ the i = apex element V_ub = −i·s₁₃ (pure imaginary at δ=90°)
⑥ ab-initio (rust, ℤ[i], float-free): unitary CKM, δ=90°, maximal Jarlskog ── EXACT
⑦ + golden modulus R_u=1/φ² (M eigenvalue = ℚ(ζ₅) real subfield)
       ⇒ cos γ = 1/φ², γ=67.54°, β=22.46° (obs 22.5°), α=90° (obs 92.4°)
```

## Honest status
- **Derived/forced** (Lean PURE): CP existence+uniqueness; phase = 90° (given
  "phase ∈ C₄" = complex structure is the NT=2 doubling); the C₄/i = signed
  Hodge ⋆ = ℤ[i] = ℚ(ζ₅) (three disciplines); golden modulus 1/φ².
- **Verified** (rust, exact ℤ[i], float-free): the i-in-apex CKM is unitary,
  δ=90°, maximal CP.
- **Fit**: `β` ≈ exact; `α,γ` ~1.5σ (decent, not perfect). The advance is
  principled-ness (Niven-allowed root-of-unity phase), not precision.
- **Open** (narrowed): the sole premise "phase ∈ C₄" (vs the explicit generation
  Yukawa carrying J from first principles); a full Δ⁴ signed-cochain Hodge lift
  (a 2-D grade-pair model is built); the ~1.5σ fit. Do NOT re-fish golden δ
  (Niven-forbidden) or atomic angles (π/5, 2π/5 excluded).

## File map (this session, all PURE unless noted)
```
lean/E213/Lib/Math/Algebra/Icosahedral/   (9 files, ~46 PURE — the d=5/A₅/self-ref math)
  OrderFive · A5Bridge · A5Reps · GoldenMixing · SpanAreas · A5ThreeRepPhase
  · A5RealityNoCP (A₅ real ⇒ no golden phase) · CyclotomicFive (ℚ(ζ₅) unify) · Capstone · INDEX
lean/E213/Lib/Math/Cohomology/Hodge/SignedStarC4.lean   (10 PURE — signed ⋆ = ℤ[i])
lean/E213/Lib/Physics/Mixing/
  JarlskogApex · ApexCPMechanism · ApexPiInternal · A5QuarkApex   (apex φ² object, π internal)
  CPPhaseCount (N_gen=3⇒1 phase) · CPPhaseC4Forcing (δ=90° forced)
  ApexRightTriangle (cos γ=1/φ²) · CPHodgeStructure (CP i = Hodge ⋆)
  CPGenerationWiring (CP=C×i, down sector) · CPMaximalPhase (i = apex V_ub)
rust-engine/crates/app/src/bin/ckm_cp_phase.rs   (ab-initio EXACT ℤ[i] CKM, δ=90°)
research-notes/cp_phase_origin_synthesis.md   (full marathon synthesis + agent reports)
research-notes/frontiers/ckm_rho_eta_apex.md  (full frontier record)
```

## Next (options)
1. **Promote to `theory/`**: the closed `Icosahedral/` math + the CP-structure
   chain (three-tier discipline; the math is closed, the apex *fit* is the soft
   part). Candidate: `theory/physics/cp_phase/` mirroring the chain.
2. **Tighten the fit / `α=90°` test**: the prediction `α=90°` (right unitarity
   triangle) is falsifiable — UTfit `α=92.4±1.4°`. Track future UT fits.
3. **Full Δ⁴ signed Hodge lift** + explicit generation Yukawa carrying J (the
   last premise).
4. Other standing: external DOI deposit of `PRE_REGISTRATION.md`.

## Earlier this session (pre-CP-marathon, same branch, also PURE)
- `1/φ²` forced over other golden powers (`JarlskogApex.apex_modulus_subunit_forced`).
- Icosahedral marathon: M is an order-5 A₅ element (M⁵≡−I), golden bridge
  `φ²=χ+1`, A₅ rep data, golden-mixing template, span-areas (apex CP-area
  skeleton=NS), 3-rep phase origin.
- Self-corrections (integrity): demoted the `δ=π·R_u` §5.7 over-claim (per-step
  rates differ); corrected "π outside 213" (π is the `PiCut` Real213 cut);
  corrected "A₅ reproduces δ from φ" (A₅ is real ⇒ CP-conserving). CLAUDE.md
  failure mode "Transcendental-as-exterior" added.
