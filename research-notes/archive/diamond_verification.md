# Diamond — Verification & N Analysis

Audit + lattice-count analysis.

## 1. Verification (strict 0-axiom Lean)

`lean/E213/Lib/Math/Cohomology/DiamondAudit.lean`:
  - `diamond_audit_unified_atomic` — NS=3, NT=2, d=5, c=2
    appear identically across DiamondShape + HopHypothesis +
    Paper3Bundle.
  - `diamond_audit_no_free_parameters` — coefficients factor
    as NS·NT (=6), NS²−1 (=8), d² (=25), 12·NT·5/4 (=30),
    c·NS·NT (=12).
  - `diamond_audit_falsifier_coupling` — any falsifier failure
    → atomic primitives wrong → diamond collapses.

## 2. NOT yet formally derived

  (a) Gram rank ≤ 5 from atomicity (Linalg213 partial).
  (b) Bipartite "no S-S, no T-T" (assumed).
  (c) c=2 multiplicity from atomicity (paper 6 lattice cycle).
  (d) N from Raw alone (paper 6: L≈8.5×10⁶⁰ uses H₀ external).

## 3. Falsification (7 binding)

JUNO 2030, nEDM θ_QCD, 4th gen, PMNS, Cabibbo, m_p, magic 7/7.
Any violation → diamond discarded.

## 4. N from paper 6

  L = R_H/l_Pl = **8.50 × 10⁶⁰** (linear)
  N_phys = d³+d²+1 = 151 (modes/vertex)
  ε₀ = L^(-6/151) ≈ 0.003793

External input: H₀ only.

### N interpretations

  - Linear: L ≈ 8.5×10⁶⁰
  - 3D Hubble volume: L³ ≈ 6×10¹⁸²
  - 4D spacetime: L⁴ ≈ 5×10²⁴³
  - Gauge-invariant: 151 × count

### Free thinking

In diamond, **N doesn't pick shape** — rank-5 gives
K_{3,2}^{(2)} regardless.  N controls redundancy density.

  - N = ∞: rank-5 image, H^{k≥2}=0 (evaporates)
  - N = L⁴ ≈ 10²⁴³: tiny H^{k≥2} residuals — could
    explain 8→8.48 algebraically
  - N = L ≈ 10⁶⁰: paper 6's choice

User "10^100 redundancy" suggests N ≈ L⁴.  5 algebraic axes
shared by ≈ 10²⁴³/5 points → entanglement automatic.

### Open: N from Raw?

True 0-param requires N from atomicity, not H₀.
Candidates: Pell d²=(d−1)(d+1)+1, cycle topology.

## 5. Checklist

| Item | Status |
|------|--------|
| d=5 atomicity | ✓ |
| NS=3, NT=2 | ✓ |
| Gram rank ≤ 5 | ⚠ partial |
| No S-S/T-T edges | ⚠ assumed |
| c=2 atomicity | ⚠ obs match |
| N from H₀ | ⚠ not 0-param |
| 7 falsifiers | ✓ |
| b_1 = 1/α_3 | ✓ |

## 6. Conclusion

Diamond **internally consistent**.  Three open: bipartite
forcing, c=2 forcing, N derivation.  Closing all = true
zero-parameter universe shape.
