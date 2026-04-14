# Research Log: Helium Screening from ∂(Δ⁵)

## Problem Statement

On ∂(Δ⁵) with 6 vertices {A₁,A₂,A₃,B₁,B₂,X} ∈ ℂ⁵:
- G_ij = ⟨ψ_i|ψ_j⟩  (Gram matrix, the ONLY physical object)
- S = Σ_h √det(G_h) × δ_h  (Regge action, 20 hinges)
- δS/δψ = 0  (variational equation)

**Known exact results:**
- Vacuum: ETF, G_ij = -1/5, δ=0, S=0 (PROVEN, EXP_067)
- δ(AAA) = π (PROVEN, ch05 Thm 1, EXP_067)
- ⟨det⟩_ABB = 2/3 = n_B/n_A (PROVEN, ch05 Thm 2)
- IE(H) = m_e α²/2 = 13.606 eV (EXACT, from Σ(1-det)_AAB = 2α²)
- IE(Z) = Z²Ry/(1+Z²α²) for hydrogen-like (EXACT, Z=1-5)

**The unsolved problem:**
IE(He) = 24.587 eV (observed). Our framework gives 54.4 eV (= He⁺).
Only empirical: IE = 2Ry(1-4α_GUT) = 24.565 eV (0.089%), but NO derivation.

---

## Previous Attempts (8 total, all failed)

| # | Approach | Result | Mathematical Obstruction |
|---|----------|--------|--------------------------|
| 1 | σ = n_T/n_S = 2/3 | 24.19 eV (1.6%) | Missing (1-4α) correction |
| 2 | σ = 7/8 (Slater-like) | Wrong | d²-1=24 denominator is unrelated |
| 3 | (1-4α_GUT) factor | 24.565 eV ✓ | **No derivation from axiom** |
| 4 | Full Regge S = Σ√det×δ | S≈35, no IE extraction | Physical ε not a critical point |
| 5 | det(ABB) vs det(AAB) | Difference < 10⁻⁸ | B₁⊥B₂ makes det(ABB)≈det(AAB) |
| 6 | Trace conservation Σ Δ_i=0 | Constraint, not value | Doesn't give (1-4α_GUT) |
| 7 | (3,2) split geometry | σ=2/3 global | Single-electron, not pairwise |
| 8 | det(STT) = 2/3 theorem | Hinge metric, not screening | Misidentified as σ |

**Root cause:** det(G_h) cannot distinguish e-e repulsion from e-nucleus
binding when B₁⊥B₂. The 3×3 Gram determinant structure is symmetric in
the two couplings.

---

## 5 Independent Sub-Questions

### Q1: What does "ionization" mean on ∂(Δ⁵)?
Status: OPEN

### Q2: What is the correct energy functional?
Status: OPEN. 5 candidates to test.

### Q3: What role does the 6th vertex X play?
Status: OPEN. ABB_{B,X} hinges have det=1/4 and 3/4, much larger (1-det).

### Q4: Why G_{B₁B₂} = 3ε² ≠ 0?
Status: OPEN. Shared spatial components create nonzero B-B overlap.

### Q5: Where does (1-4α_GUT) come from?
Status: OPEN. Hypothesis: 4α_GUT = (d²-1)/(d²ζ(2)).

---

## Session Log

### Session 2026-04-14 (EXP_067)

**New results:**
1. Vacuum is EXACTLY flat: δ=0, S=0 on ETF (proved analytically + numerically)
2. δ(AAA) = π proved: arccos(0)+arccos(cosφ)+arccos(sinφ) = π ∀φ∈[0,π/2]
3. 20-hinge table for hydrogen computed (all det and δ values)
4. Constrained optimization: S_max = 40.83, S_min = 0 (vacuum)
5. Helium: Σ(1-det)_ABB ≈ Σ(1-det)_AAB confirmed (difference = 4.5e-8)

**Key numerical values:**
```
Hydrogen (ε = α/√3 = 0.004213):
  S_H = 34.88
  Σ(1-det)_AAB = 2α² = 1.065e-4
  δ(AAA) = π, δ(AAB, AAAB face) ≈ π, δ(ABB, B₁B₂) ≈ 0

Helium (ε = 2α/√3 = 0.008426):
  S_He = 35.36
  Σ(1-det)_AAB[B₁] = 4.260e-4
  Σ(1-det)_AAB[B₂] = 4.260e-4
  Σ(1-det)_ABB = 4.261e-4  (nearly identical!)
  IE_det = 54.4 eV (should be 24.6)
```

**Critical observation:**
ABB hinges {Aᵢ,B₁,X}: det = 3/4, δ = π  
ABB hinges {Aᵢ,B₂,X}: det = 1/4, δ = π  
These have LARGE (1-det) but were IGNORED in all 8 previous attempts.

**Next:** EXP_068 — systematic test of 5 energy functionals.

### Session 2026-04-14 (EXP_068) — BREAKTHROUGH

**F1 = Σ(1-det) over ALL 20 hinges is the correct functional (up to correction).**

Of 5 candidate functionals, ONLY F1 gives the right scale:
```
F1:  IE(He)/IE(H) = 2.001 ≈ 2       ← CORRECT SCALE
F3:  IE(He)/IE(H) = 4.000 = Z²      ← Too large (He⁺ value)
F2,F4,F5: ratios < 0.01             ← Wrong by orders of magnitude
```

**THE KEY EQUATION:**
```
IE(He) = 2Ry × correction
       = 2Ry × (1 − 4α_GUT)         [observed to 0.089%]
       = 2Ry × (1 − (d²−1)/(d²ζ(2)))
```

**What we now know:**
- The "2" comes from F1: each electron contributes ε² to Σ(1-det)
- The "4α_GUT" correction is MISSING from the naive F1 calculation
- F1 gives ratio 2.001, target is 1.807, so correction = 1.807/2.001 = 0.903

**What remains:** Derive the (1-4α_GUT) correction from ∂(Δ⁵) geometry.

**Hypothesis for the correction:**
4α_GUT = (d²-1)/(d²ζ(2)) might come from:
- Trace conservation: Σ Δ_i = 0 redistributes (d²-1)/d² of the binding
- The ζ(2) = π²/6 factor is the Basel sum from the coupling constant chain
- Total: a fraction (d²-1)/(d²ζ(2)) = 24/(25π²/6) "leaks" from binding

**Face decomposition (EXP_068 Part E):**
```
Face miss=B₂: ΔS = +0.0715  (ionization face)
Face miss=X:  ΔS = −0.0513  (X compensates)
Face miss=B₁: ΔS = +0.0199  (B₁ rearranges)
Face miss=A:  ΔS = +0.0065  (spectator)
```
The X-face and B₁-face rearrangement may carry the correction.

**Other findings:**
- G_{B₁B₂} = 3ε² exactly (shared spatial components)
- BBB hinge det grows ∝ ε₂ but δ(BBB) = 0 always
- ABB hinges {A,B,X} have det=0.5, δ=π (at φ=π/4) — large S contribution
- Deficit angle change He→He⁺: Δδ(AAB) = +0.0023, Δδ(ABB) = −0.0001
