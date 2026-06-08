# `Lib/Physics/Mixing/` — flavor mixing matrices + CP violation

CKM (quark) + PMNS (neutrino) mixing matrices, Cabibbo angle, and the
CKM CP-violating phase derived/forced across group theory, number theory,
and cohomology (the signed Hodge ⋆ on `H*(Δ⁴)`).

## Files (19)

### Mixing matrices + angles
  - `CabibboAngle.lean`     — Cabibbo angle θ_C
  - `CKMHierarchy.lean`     — CKM mixing matrix hierarchy
  - `NeutrinoMixing.lean`   — PMNS neutrino mixing matrix
  - `CPViolation.lean`      — CP-violation parameter
  - `Bridge.lean`           — bridge to other clusters

### CP phase — existence, count, and the 90° forcing
  - `CPPhaseCount.lean`        — `N_gen = C(3,2) = 3 ⇒ 1` physical phase (KM counting)
  - `CPPhaseC4Forcing.lean`    — `δ = 90°` forced: `C₄` (CD `i`) + CP-existence
  - `CPMaximalPhase.lean`      — the `i` = apex `V_ub = −i·s₁₃` (pure imaginary at 90°)
  - `CPHodgeStructure.lean`    — the CP `i` = signed Hodge ⋆ on `H*(Δ⁴)` (`⋆² = −1`, grades 1,3)
  - `CPGenerationWiring.lean`  — `CP = C × i`: `i` = `J` localized to the down/`5̄` sector

### The φ²-apex object + the fit
  - `JarlskogApex.lean`        — the apex modulus `1/φ²` forced over other golden powers
  - `ApexRightTriangle.lean`   — `cos γ = 1/φ²`; right unitarity triangle, `α = 90°` candidate
  - `ApexCPMechanism.lean`     — the apex `z = r·(−1)^r` mechanism (π internal)
  - `ApexPiInternal.lean`      — π as the `PiCut` Real213 cut (internal, not exterior)
  - `A5QuarkApex.lean`         — two distinct origins: Cabibbo magnitude vs CP-depth
  - `ApexFitConsistency.lean`  — fit ~1.5σ-consistent: `R_u` exact, `O(λ²)` Wolfenstein not RGE

### Cohomological generation Yukawa
  - `BigradedYukawa.lean`         — generations = `Λ²(ℝ³)`, `dim = C(3,2) = 3`
  - `CohomologicalYukawa.lean`    — assembly: the three Hodge hypotheses
  - `CohomologicalYukawaEval.lean`— diagonal `h = I` → phase + index (angles separate)

## Where to add new files

  - Specific mixing angle      → `<Angle>Angle.lean`
  - Hierarchy / matrix         → `<Name>Hierarchy.lean` / `<Name>Mixing.lean`
  - CP-phase structure         → `CP<...>.lean`
  - Apex / unitarity triangle  → `Apex<...>.lean`
  - Cohomological Yukawa       → `<...>Yukawa.lean`
