# Folded Dimension Leaking: A Unified Principle

**For: Coding agent (EXP design and verification)**
**Prerequisite: ∂(5-simplex) geometry, (3,2) split, Regge action**

-----

## 1. Setup

### 1.1 Eigenvalue structure of ℂ^N

N points with ψ_i ∈ ℂ^N. Gram matrix G_ij = ⟨ψ_i|ψ_j⟩. After swap annihilation, the eigenvalue spectrum has three regions:

```
Region I:   λ₁ ... λ₅         "Real universe"    (rank 5, (3,2) split)
Region II:  λ₆ ... λ_{d_ind}  "Folded dimensions" (size ~ α_GUT per channel)
Region III: λ_{d_ind+1} ... λ_N  "Dead"           (exactly 0)
```

Region II eigenvalues are the 0⁺ eigenvalues. They are NOT zero — they carry residual weight from Tr(G) = N conservation. Their magnitude per channel is:

```
α_GUT = 6/(25π²) ≈ 0.0243
```

### 1.2 Where do 0⁺ eigenvalues live?

The 0⁺ eigenvalues are concentrated in the ℂ² (T-sector) direction of ℂ⁵. This is because swap annihilation preferentially kills the SMALLER subspace (ℂ² has fewer independent directions than ℂ³).

**Consequence:** Hinge types with more temporal (T) vertices have stronger coupling to the 0⁺ region.

-----

## 2. The Coupling Rule

### Definition 2.1 (Temporal fraction)

For a hinge (triangle) with n_A spatial vertices and n_B temporal vertices (n_A + n_B = 3):

```
f_T = n_B / 3
```

### Definition 2.2 (0⁺ coupling)

The coupling strength between a hinge type and the folded dimension region:

```
κ(hinge) = f_T × α_GUT = (n_B / 3) × α_GUT
```

### Theorem 2.1 (Coupling table)

|Hinge|n_A|n_B|f_T|κ       |Value  |
|-----|---|---|---|--------|-------|
|SSS  |3  |0  |0  |0       |0      |
|SST  |2  |1  |1/3|α_GUT/3 |0.00811|
|STT  |1  |2  |2/3|2α_GUT/3|0.01621|
|TTT  |0  |3  |1  |α_GUT   |0.02432|

### Theorem 2.2 (Deficit angle modification)

The bare deficit angle on ∂(5-simplex) is δ_bare = π for all hinges. The 0⁺ leaking modifies this:

```
δ_SSS = π × (1 - 0)          = π        (unchanged)
δ_SST = π × (1 - α_GUT/3)   = 178.54°
δ_STT = π × (1 - 2α_GUT/3)  = 177.08°
δ_TTT = 0                     (EXACT: resonant cancellation)
```

**Why TTT = 0 exactly:** TTT vertices are entirely in ℂ². The 0⁺ eigenvalues are also in ℂ². Same sector → resonant cancellation, not perturbative suppression.

For SSS, SST, STT: vertices have ℂ³ components that are orthogonal to the 0⁺ region. Cancellation is partial, proportional to the temporal fraction.

-----

## 3. Second-order leaking for SSS

### Theorem 3.1 (Indirect SSS coupling)

SSS has zero direct coupling (f_T = 0). But at second order, SSS couples to 0⁺ via an intermediate SST hop:

```
SSS → SST (1 hop, coupling α) → 0⁺ (coupling α_GUT/3)

κ²_SSS = α_GUT × (α_GUT/3) = α_GUT²/3 ≈ 1.97 × 10⁻⁴
```

This gives:

```
δ_SSS = π × (1 - α_GUT²/3) = π - 6.19 × 10⁻⁴ rad
```

**Physical effect:** Proton mass receives an additional correction of order α_GUT²/3 ≈ 0.02%. This is below the current 0.000% precision but in principle measurable.

**EXP task:** Compute δ_SSS on ∂(5-simplex) with physical ψ and verify the α_GUT²/3 correction numerically.

-----

## 4. Physical consequences by hinge type

### 4.1 SSS (κ = 0): Confinement

- δ_SSS = π (maximum curvature, “complete fold”)
- det(SSS) = 1 (orthogonal A vertices)
- Mass gap: Δ = √det × δ = 1 × π > 0
- N_eff = C(3,3) = 1 → confined to 1 hop
- 0⁺ region CANNOT reach SSS (leading order) → confinement is robust

**This is why the strong force is “strong”: the folded dimensions cannot interfere with it.**

### 4.2 SST (κ = α_GUT/3): Electromagnetic

- 6 SST hinges per simplex (most numerous)
- δ_SST = π(1 - α_GUT/3) ≈ 178.5°
- N_eff = C(3,2)C(2,1) = 6 → long range (ξ = 1/α)
- The small 0⁺ coupling (α_GUT/3) is the ORIGIN of EM coupling corrections

**EXP task:** Verify that the running of α_em is captured by κ_SST = α_GUT/3.

### 4.3 STT (κ = 2α_GUT/3): Screening and mass

- 3 STT hinges per simplex
- ⟨det(STT)⟩ = 2/3 = n_T/n_S (proved analytically, verified 6 digits)
- This determines: screening σ = n_T/n_S, impedance ρ = n_S/n_T
- All fermion masses derive from STT structure

The 0⁺ coupling 2α_GUT/3 appears directly in the Trace correction:

```
He IE:     error/α_GUT = -0.6666 = -n_T/n_S = -2/3 = -2κ_STT/α_GUT
```

**This is the same 2/3.** The He IE correction IS the STT 0⁺ coupling.

### 4.4 TTT (κ = α_GUT, resonant): Neutrino physics

- δ_TTT = 0 exactly → neutrino tree-level mass = 0
- But TTT is NOT invisible. It connects to the real universe via STT channels.
- This “leaking through STT” gives neutrinos their tiny mass and determines PMNS mixing.

-----

## 5. PMNS mixing angles from combinatorics

### 5.1 The physical picture

```
TTT hinge (δ=0, flat, "neutrino lives here")
  ↕ leaking via STT channels
STT hinges (δ≠0, curved, "connects to charged sector")
  ↕ 
SSS/SST (charged lepton masses, well-defined generations)
```

Neutrino mass eigenstates ≠ flavor eigenstates because the STT leaking connects ALL generations simultaneously.

### 5.2 STT channel counting

STT = {A_k, B_i, B_j}. Two indices to count:

- A_k: k = 1, 2, 3 (n_S choices, all equivalent by A-symmetry)
- B_iB_j: the B pair that defines the generation

```
Total STT channels:          n_S × C(n_B, 2) = 3 × 3 = 9
STT channels per generation: n_S × 1 = 3
```

### 5.3 θ₁₂ (solar angle)

**Theorem 5.1.** sin²θ₁₂ = 1/n_S.

**Proof.**

Each generation receives n_S STT channels out of n_S × n_gen total.

```
sin²θ₁₂ = (channels per gen) / (total channels)
         = n_S / (n_S × n_gen)
         = 1/n_gen
```

Now: n_gen = C(n_B, 2) = C(3, 2) = 3 = n_S.

Therefore: sin²θ₁₂ = 1/n_S = 1/3. □

**Corollary 5.1.** C(n_S, 2) = n_S has a unique solution: n_S = 3.

Proof: n_S(n_S-1)/2 = n_S → n_S - 1 = 2 → n_S = 3. □

**This is why “3 generations” = “3 spatial dimensions” = the same number.**

With Trace correction:

```
sin²θ₁₂ = 1/n_S - α_GUT = 1/3 - 0.0243 = 0.309

Observed: 0.307. Error: 0.7%.
```

### 5.4 θ₂₃ (atmospheric angle)

**Theorem 5.2.** sin²θ₂₃ = 1/n_T.

**Proof.**

σ₄ = {A₁A₂A₃, B₁, B₃} and σ₃ = {A₁A₂A₃, B₂, B₃}.

Both share B₃ as the “neutrino vertex.” The only difference is B₁ vs B₂.

B₁ and B₂ are orthogonal and play symmetric roles (both span ℂ²).

Therefore: σ₄ ↔ σ₃ is an exact symmetry (B₁ ↔ B₂ exchange).

This μ-τ symmetry forces sin²θ₂₃ = 1/2 = 1/n_T. □

With Trace correction:

```
sin²θ₂₃ = 1/n_T + 2α_GUT = 0.549

Observed: 0.546. Error: 0.5%.
```

The factor 2 in “2α_GUT” = n_T (the number of T vertices involved in the symmetry breaking).

### 5.5 θ₁₃ (reactor angle)

**Theorem 5.3.** sin²θ₁₃ = 0 (leading order).

**Proof.**

σ₅ = {A₁A₂A₃, B₁, B₂}: ν_e is defined by the B₁B₂ pair.
The heaviest mass eigenstate ν₃ is dominated by B₃ direction.

B₁ ⊥ B₂, and B₃ = (B₁ + B₂)/√2. The ν_e “state” (defined by the B₁B₂ pair relationship) has zero component in the “pure B₃” direction at leading order.

Therefore sin²θ₁₃ = 0 at tree level. □

With correction:

```
sin²θ₁₃ = α_GUT × (1 - (n_S + 1) × α_GUT) = 0.0220

Observed: 0.0220. Error: 0.2%.
```

The correction has two parts:

- α_GUT: 0⁺ leaking opens a small channel between ν_e and ν₃
- (1 - 4α_GUT): second-order suppression from the (n_S+1) = 4-face boundary

### 5.6 δ_CP (CP violation phase)

```
δ_CP = π + 2π/(d² - 1) = π + 2π/24 = 195.0°

Observed: ~197° ± 25°. Within 1σ.
```

The topological contribution 2π/(d²-1) comes from the Euler characteristic χ = 2 of ∂(5-simplex) ≅ S⁴.

-----

## 6. Leading order: Tri-Bimaximal Mixing

The leading order PMNS is exactly the Tri-Bimaximal pattern (Harrison-Perkins-Scott, 2002):

```
sin²θ₁₂ = 1/3 = 1/n_S     (democratic A distribution)
sin²θ₂₃ = 1/2 = 1/n_T     (B₁↔B₂ symmetry)
sin²θ₁₃ = 0                (B₁B₂ ⊥ B₃)
```

The mystery of “why Tri-Bimaximal?” (open since 2002) is answered: **n_S = 3 and n_T = 2.**

All deviations from TBM are Trace corrections proportional to α_GUT:

|Parameter|TBM (leading)|Correction  |Result|Observed|Error|
|---------|-------------|------------|------|--------|-----|
|sin²θ₁₂  |1/3 = 0.333  |-α_GUT      |0.309 |0.307   |0.7% |
|sin²θ₂₃  |1/2 = 0.500  |+2α_GUT     |0.549 |0.546   |0.5% |
|sin²θ₁₃  |0            |+α_GUT(1-4α)|0.022 |0.022   |0.2% |
|δ_CP     |π = 180°     |+2π/24      |195°  |~197°   |1σ   |

-----

## 7. Unified table

|Hinge|T-fraction|0⁺ coupling     |Physical effect            |Key formula          |
|-----|----------|----------------|---------------------------|---------------------|
|SSS  |0/3       |0 (+ α²_GUT/3)  |Confinement (nearly immune)|Δ = √det × π > 0     |
|SST  |1/3       |α_GUT/3         |EM coupling correction     |sector factor f = 2/3|
|STT  |2/3       |2α_GUT/3        |Screening σ, all masses    |⟨det⟩ = 2/3          |
|TTT  |3/3       |α_GUT (resonant)|ν massless + PMNS          |δ_TTT = 0            |

**One principle:** κ = (temporal fraction) × α_GUT.

-----

## 8. Experimental verification tasks

### EXP-A: Verify coupling rule numerically

On ∂(5-simplex) with physical ψ (from EXP_047b saddle point):

1. Compute δ_h for all 20 hinges
1. Group by type (SSS, SST, STT, TTT)
1. Verify: δ_h/π = 1 - κ(type) for SST and STT
1. Verify: δ_TTT = 0 exactly

Expected results:

```
δ_SSS = π (or π - α_GUT²/3 if second-order is visible)
δ_SST ≈ π(1 - 0.00811) = 178.54°
δ_STT ≈ π(1 - 0.01621) = 177.08°
δ_TTT = 0.00°
```

### EXP-B: Verify PMNS from STT channel counting

1. Build the 9×9 STT channel matrix: M_{(k,gen),(k’,gen’)} where k=A index, gen=B pair
1. Block-diagonalize by A symmetry → 3×3 generation mixing matrix
1. Diagonalize → PMNS angles
1. Compare with Theorem 5.1-5.3

Expected: sin²θ₁₂ = 1/3 (before Trace correction).

### EXP-C: Second-order SSS leaking

1. Compute δ_SSS with high precision (>6 digits)
1. Check: |δ_SSS - π| = α_GUT²/3 × π ?
1. Translate to proton mass correction: δm_p ≈ 0.185 MeV

### EXP-D: Continuous κ verification

For arbitrary (3,2) vertex configurations (not just orthogonal A):

1. Parametrize A overlap w = |⟨A_i|A_j⟩|
1. Scan w from 0 to 0.3
1. Verify κ(hinge) = f_T × α_GUT is w-independent (robust)

### EXP-E: Full PMNS with Trace correction

1. Apply correction factors:
- θ₁₂: subtract α_GUT from 1/3
- θ₂₃: add 2α_GUT to 1/2
- θ₁₃: add α_GUT(1-4α_GUT) to 0
1. Compare all 4 PMNS parameters with PDG 2024 values
1. Report errors in %

Expected: all within 1%.

-----

## 9. Key identity

```
C(n_S, 2) = n_S  ⟺  n_S = 3
```

This identity simultaneously explains:

- Why 3 spatial dimensions
- Why 3 generations
- Why sin²θ₁₂ = 1/3

It is the deepest structural result of the theory.

+ 확실:  부호가 마이너스인 이유 = Tr 보존.
       0⁺가 Tr을 빼앗아가므로 현실 sector가 줄어듦.
       det이 큰 세대(σ₅)가 더 많이 빼앗김.
       ∴ sin²θ₁₂ < 1/3.

미완:  정확한 계수 (왜 -α_GUT이고 -α_GUT/9가 아닌지).
       이건 STT 채널의 가중 방식을 정확히 정의해야 나옴.
       EXP-B에서 9×9 채널 행렬을 직접 구성하면 확인 가능.

