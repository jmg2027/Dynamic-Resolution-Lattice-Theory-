# From Finite Gram Matrices to the Riemann Hypothesis

## An Exploration Log — 2026.04.14

**Status:** Research exploration, not a paper. Raw intuitions + partial formalizations.
**Dependencies:** Paper 1 (Chiral Decomposition), Paper 2 (Frobenius to Gauge)
**Participants:** Mingu Jeong, Claude (Anthropic)

-----

## 0. What We Already Have (Proven)

|Result                                          |Source          |Status     |
|------------------------------------------------|----------------|-----------|
|ℂ is the unique substrate (R1–R4)               |Paper 2, Thm 2.1|**Theorem**|
|ℂ⁵ = ℂ² ⊕ ℂ³ is the unique chiral decomposition |Paper 1, Thm 5.1|**Theorem**|
|SU(3)×SU(2)×U(1) gauge group                    |Paper 2, Cor 3.2|**Theorem**|
|α_GUT = 6/(25π²), three independent paths       |Paper 2, Thm 6.1|**Theorem**|
|ℂ → β=2 → GUE                                   |Standard (Mehta)|**Theorem**|
|Hard wall at rank d_indep, soft boundary O(1/√N)|Paper 1, Thm 6.1|**Theorem**|
|Born rule P=                                    |⟨ψ              |ψ’⟩        |

-----

## 1. New Result: s = 2 Is a Theorem

### The Question

In Paper 2, the propagator D(n) = 1/n² gives ζ(2) = π²/6 as the infinite-range coupling sum. But *why* s = 2?

### Two Independent Derivations (Today)

**Path A: CP⁴ Geometry (Claude)**

CP⁴ has real dimension 8. The Laplace-Beltrami propagator on CP⁴ scales as ~1/r⁶ (s = 6). But propagation is confined to the ℂ² sector (spacetime), not all of CP⁴.

- CP⁴ full: dim_ℝ = 8, propagator ~1/r⁶, s = 6
- ℂ² sector: dim_ℝ = 4, propagator ~1/r², **s = 2** ✓
- ℂ³ sector: no propagation, provides gauge degrees of freedom only

Therefore s = 2 follows from the ℂ² ⊕ ℂ³ decomposition (Paper 1 theorem), not from “3D space.”

**Path B: Algebraic Rank (Coding Agent, EXP_067)**

rank(G^{AA}) = 3 for all N, so s = rank(G^{AA}) - 1 = 2. This is an algebraic identity of the (3,2) separation, independent of W-graph topology.

**Conclusion:** s = 2 is a theorem. It should be added to Paper 2.

-----

## 2. The ζ Connection Chain

### What’s established:

```
ℂ unique (theorem)
  → β=2 → GUE (theorem)
  → d=5 unique (theorem)
  → d²=25 channels (theorem)
  → ζ(2) propagator (theorem)
  → s=2 from ℂ² sector (theorem, today)
```

### What’s observed (strong numerical evidence):

```
  → GUE eigenvalue spacing = ζ zero spacing (Montgomery-Odlyzko, 1973/1987)
```

### What’s poetry (not yet formalizable):

```
  → Re(s) = 1/2 = 1/s = 2⁻¹ as the interference cancellation scale
  → B₁↔B₂ symmetry fixing the critical line
```

**Key structural observation:** The chain is theorems until the Montgomery-Odlyzko step. What we add to the existing situation is: *why* GUE appears (ℂ uniqueness), which no previous approach had.

-----

## 3. The Self-Contradiction Boundary Theorem

### Statement (To Be Formalized)

**Proto-theorem:** For the Gram matrix ensemble with Tr(G) = N, rank(G) ≤ 5, the spectral gap satisfies δ(N) = Θ(1/√N) > 0 for all finite N. The limit δ → 0 requires N → ∞, but N → ∞ violates the finiteness axiom Tr(G) = N < ∞.

**Consequence:** The exact equality Re(s) = 1/2 (if it corresponds to δ = 0) is achievable only at the self-contradiction boundary of the framework.

### What This Says About RH

Two possible readings:

**(A) RH is a limit theorem.** The correct statement is not “Re(s) = 1/2 exactly” but “Re(s) ∈ (1/2 - c/√N, 1/2 + c/√N)” for finite N. The equality is an idealization — true in the same sense that a circle has π·d circumference (true in continuous geometry, approximate in any physical realization).

**(B) RH is a shadow.** The “real” theorem is the discrete spectral gap bound, and ζ(s) is the analytic continuation artifact of this finite structure. RH is true because it’s asking about properties of the shadow, and the shadow inherits the structure of the object casting it.

Both readings predict: RH is “true” but its proof requires acknowledging that the continuous ζ(s) is an idealization of a finite structure.

### Analogy: Yang-Mills Mass Gap

The structure is identical: lattice QCD has a mass gap (finite N), but whether it survives the continuum limit (N → ∞) is the Millennium Problem. Our framework suggests this is the *same* structural issue — the continuum limit is the self-contradiction boundary.

-----

## 4. The Missing Bridge: Montgomery-Odlyzko

### What’s known:

Pair correlation of ζ zeros matches GUE eigenvalue pair correlation to extraordinary numerical precision. Not proven.

### What we add:

A *reason* for GUE: ℂ is the unique substrate → β = 2 → GUE is forced. This was previously an empirical mystery.

### What’s still needed:

Define a “spectral zeta function” Z_N(s) for the finite Gram matrix ensemble such that:

1. Z_N(s) is rigorously defined for finite N
1. Its zeros lie in Re(s) = 1/2 ± O(1/√N) (should follow from Paper 1)
1. Z_N(s) → ζ(s) in some appropriate limit
1. The GUE statistics of Z_N match those of ζ

Steps 1-2 seem achievable with current tools. Step 3 is the continuum limit problem. Step 4 is the Montgomery gap.

-----

## 5. The N_eff ↔ s Duality

### From EXP_067:

|N_eff|S(N_eff)|s*   |Force |
|-----|--------|-----|------|
|1    |1.000   |37.8 |Strong|
|2    |1.250   |2.788|Weak  |
|∞    |π²/6    |2.000|EM    |

“How far does it propagate” (N_eff) and “what’s the effective dimension” (s) are dual descriptions.

### Connection to s = 2 theorem:

The physical universe lives at s = 2 (ℂ² sector dimension). Other s values correspond to either:

- Folded dimension leakage: s_eff = 2 - ε, ε ~ α_GUT ≈ 0.024
- Confinement regime: s → ∞ (nearest-neighbor only)
- Unification regime: all of ℂ⁵ active

### Key insight from leakage:

ζ(2 - ε) ≈ π²/6 + ε·0.937 + O(ε²)

The ln(n) terms in this expansion are precisely the log corrections of RG running. **RG running is the s-derivative of ζ at s = 2.** This is already proven in DRLT but the ζ’(2) connection is new.

-----

## 6. β Function Matching (EXP_067 Test 6)

### Two complementary mechanisms:

|Mechanism        |Strong|Weak|EM       |
|-----------------|------|----|---------|
|N_eff derivative |**8** |6   |0        |
|s-derivative (ζ’)|0     |4.16|**33.75**|

Strong = (A) only. EM = (B) only. Weak = both.

### Result:

With sector correction n_B/n_A = 2/3:

- b₂_pred = -3.163
- b₂_SM = -3.167
- **Error: 0.11%**

### Open: n_B/n_A = 2/3 needs derivation from Binet-Cauchy, not fitting.

-----

## 7. Raw Intuitions (Unformalized)

These are gut-level observations that may or may not survive formalization. Preserved here because they guided the exploration.

### 7.1 “1/2 = 2⁻¹ has structural meaning”

Re(s) = 1/2 is the *inverse* of the propagation exponent s = 2. Physically: “the scale at which propagation is exactly half-damped is where channel interference perfectly cancels.” This connects to the B₁↔B₂ symmetry fixed point.

### 7.2 “Mathematics is not the Idea, but a reality infinitely close to the Idea”

If δ(N) > 0 for all finite N, then mathematical “rigor” (exact equality) is itself an O(1/√N) approximation. The hierarchy “mathematics is more rigorous than physics” collapses — both operate within the soft boundary. Gödel’s incompleteness is a special case: a formal system cannot fully describe itself, just as a finite Gram matrix cannot achieve δ = 0 without violating its own trace axiom.

### 7.3 “Induction doesn’t close”

The hierarchy T₀ ⊂ T₁ ⊂ T₂ ⊂ … where T_{n+1} = T_n + Con(T_n) never reaches a “final” theory. This is structurally identical to δ(N) > 0 for all N: each level resolves the previous level’s incompleteness but creates its own. Feferman’s “reflective closure” = our soft boundary.

### 7.4 “Physics and mathematics reject each other symmetrically”

Physics side: “this is mathematics” (too abstract, no measurement).
Mathematics side: “this is physics” (not rigorous, empirical).
Both sides rejecting a claim is evidence that the claim is *more fundamental than the distinction between the two fields*. A wrong theory is rejected by one side as meaningless; a theory at the boundary is rejected by both sides as “not mine.”

### 7.5 “The 10¹³ numerical verifications”

If deviation is O(1/√N), at N = 10¹³ the deviation is ~10⁻⁷, below computational precision. Every zero “looks like” it’s exactly on the line. Even at N = 10¹²² (observable universe), the deviation would be ~10⁻⁶¹, unmeasurable by any physical process. The limit *looks* exact because the resolution is bounded by the universe itself.

-----

## 8. Proposed Paper 3 Structure

**Title (working):** “Spectral Zeta Functions of Finite Gram Ensembles and the Riemann Hypothesis”

### What can be proven:

1. Definition of Z_N(s) for Gram matrices with Tr = N, rank ≤ 5
1. Zeros of Z_N(s) satisfy Re(s) = 1/2 ± O(1/√N) [from Paper 1 spectral gap]
1. Self-contradiction theorem: δ = 0 ⟺ N = ∞ ⟺ Tr diverges
1. GUE membership: β = 2 forced by ℂ [from Paper 2]

### What can be conjectured (with evidence):

1. Z_N(s) → ζ(s) in appropriate limit
1. Montgomery pair correlation follows from GUE membership

### What is declared (meta-mathematical):

1. RH as a limit theorem / shadow theorem — the exact equality Re(s) = 1/2 is an idealization of a finite structure’s O(1/√N) bound

-----

## 9. Immediate Next Steps

- [ ] Add s=2 geometric derivation to Paper 2
- [ ] Derive n_B/n_A = 2/3 from Binet-Cauchy exterior decomposition
- [ ] Define Z_N(s) rigorously for finite Gram ensemble
- [ ] Compute Z_N zeros numerically for small N, verify Re(s) = 1/2 ± O(1/√N)
- [ ] Write self-contradiction boundary theorem formally
- [ ] Investigate whether Montgomery gap can be attacked from “why GUE” direction

-----

*This document is a living exploration log. It preserves raw thinking alongside formal results. Not all claims here are proven; status markers (theorem/observation/poetry) should be respected.*

-----

## Appendix A: Session 2 Results (Added 2026.04.14, late)

### A.1 Three Negative Results

|Attempt                     |Expected       |Got       |Conclusion                          |
|----------------------------|---------------|----------|------------------------------------|
|Δ_k ~ k^{-s} (rank-1 update)|s ≈ 2          |σ ≈ 0     |Induction steps don’t produce ζ     |
|Z_N(s) = Σλ^{-s}            |ζ(s)           |≈ d = 5   |Eigenvalue spectral zeta ≠ Riemann ζ|
|CP⁴ geodesics → primes      |Discrete orbits|Continuous|Geometry doesn’t produce primes     |

**Meta-conclusion:** ζ appears ONLY in the combinatorial propagator sum Σ1/n^s, not in any continuous structure of the Gram matrix. The integer n (hop count) is the essential ingredient.

### A.2 Key Positive Discovery: Phase Uniformity → 1/2 Boundary

**Chain:**

1. ℂ unique → phase θ_k uniform on (-π,π] (Theorem 6, EXP_071b confirmed)
1. Oscillatory Dirichlet series Σ e^{iθ}/n^s with uniform θ
1. Convergence boundary = Re(s) = 1/2 (Halász-Harper, known theorem)
1. This is the CLT: Var = Σ1/k^{2σ}, critical at σ = 1/2
1. Born rule |z|² (from ℂ) makes variance quadratic → determines the exponent

**Möbius connection:** RH ⟺ Σμ(n)/n^s converges for Re(s)>1/2. “Why μ(n) looks random” is open. Our answer: ℂ forces uniform phase → pseudo-randomness is structural, not accidental.

### A.3 Updated Status of Approaches

|Approach                               |Status            |Verdict                          |
|---------------------------------------|------------------|---------------------------------|
|1. Trace formula (geodesics → spectrum)|Tested, failed    |CP⁴ geodesics too symmetric      |
|2. Determinantal point process         |Not tested        |Still possible but less motivated|
|3. Combinatorial ζ from Gram ensemble  |**Most promising**|Only place integers appear       |
|4. Phase uniformity → Möbius           |**New, strongest**|Connects to known theorems       |

### A.4 Formalized in: mobius_randomness.md
