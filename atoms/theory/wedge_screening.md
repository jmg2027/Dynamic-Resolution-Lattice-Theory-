# Screening Constants from Wedge Product Algebra
## Joint research by Mingu Jeong and Claude (Anthropic)

---

## 0. Summary

All atomic screening constants in DRLT are determined by the
**wedge product** on ∧²(ℂ⁵). No free parameters.

| Screening | Value | Formula | Algebraic origin |
|-----------|-------|---------|-----------------|
| σ_cross | 7/8 | 1−N_S/(d²−1) | Direct wedge channel (SS∧ST≠0) |
| σ_same_p | 3/4 | N_S/(N_S+1) | Indirect (SS∧SS=0, closed) |
| σ_same_d | 2/3 | N_T/(N_T+1) | Temporal indirect |
| σ_ns→np | 17/20 | 1−N_S/d(d−1) | Antisymmetric ∧² budget |
| Todd budget | 15 | C(d+1,4) | Nonzero wedge count |

---

## 1. Mathematical Framework

### Definition 1 (Edge algebra)

Let V = ℂ^d with d = 5, split as V = V_S ⊕ V_T where
dim V_S = N_S = 3 (spatial), dim V_T = N_T = 2 (temporal).

The **edge space** is ∧²(V), with basis {e_i∧e_j : i<j}.
dim ∧²(V) = C(d,2) = 10.

Under V_S⊕V_T, the edges decompose as:

```
∧²(V) = ∧²(V_S) ⊕ (V_S⊗V_T) ⊕ ∧²(V_T)
  10   =    3     ⊕     6      ⊕    1
         (SS)        (ST)         (TT)
```

### Definition 2 (Hinge algebra)

The **hinge space** ∧³(V) has basis {e_i∧e_j∧e_k : i<j<k}.
dim ∧³(V) = C(d,3) = 10.

The **Hodge star** ★: ∧³(V) → ∧²(V)* ≅ ∧²(V) maps:

| ∧³ (hinge) | ★ | ∧² (edge) | Content flip |
|-----------|---|---------|-------------|
| SSS (1) | → | TT (1) | all-S → all-T |
| SST (6) | → | ST (6) | unchanged |
| STT (3) | → | SS (3) | all-T → all-S |

### Theorem 1 (Wedge product structure)

The wedge product ∧²(V)⊗∧²(V) → ∧⁴(V) ≅ V* has exactly
**C(d+1,4) = 15 nonzero products** out of C(10,2) = 45 pairs.

Proof: e_{ij}∧e_{kl} ≠ 0 iff {i,j}∩{k,l} = ∅. The number
of such disjoint pairs in C(d,2) is C(d,4)×3 = 5×3 = 15.
(Choose 4 indices, partition into 2+2 in 3 ways.) □

### Theorem 2 (Target vertex distribution)

The 15 nonzero wedge products distribute:

| Type pair | Nonzero | Target |
|-----------|---------|--------|
| SS∧SS | 0 | — |
| SS∧ST | 6 | T only |
| SS∧TT | 3 | S only |
| ST∧ST | 6 | S only |
| ST∧TT | 0 | — |
| TT∧TT | 0 | — |

Each vertex receives exactly 3 = C(d-1,2) contributions.
The distribution is **democratic**: all 5 vertices equal. □

### Theorem 3 (Screening from channel counting)

Given the wedge product structure:

(a) **Cross-shell** (electron across shell boundary):
    Direct channel SS∧ST ≠ 0.  Budget = d²−1 = 24 (adjoint).
    Active channels = N_S = 3 (spatial directions).
    ```
    σ_cross = 1 − N_S/(d²−1) = 1 − 3/24 = 7/8
    ```

(b) **Same subshell, p-type** (SS∧SS = 0):
    Direct channel closed. Indirect path SS→ST→target.
    Accessible fraction = N_S/(N_S+1).
    ```
    σ_same_p = N_S/(N_S+1) = 3/4
    ```

(c) **Same subshell, d-type** (temporal indirect):
    ```
    σ_same_d = N_T/(N_T+1) = 2/3
    ```

### Theorem 4 (Todd class budget)

The Todd correction at the h³ (tetrahedron) level uses:
```
budget(h³) = C(d+1,4) = 15 = |{nonzero wedge products}|
```

This is not empirical but algebraically determined:
the 15 nonzero channels of ∧²⊗∧²→∧⁴ ARE the budget.

At h¹ (triangle) level: budget = d²−1 = 24 (adjoint).

The Todd correction formula:
```
δ(h^k) = σ₀² × c₁ × α_GUT / budget(h^k)
```
where c₁ = d+1 = 6 (Regge Chern number of Δ⁴).

---

## 2. The Structure

10 edges of Δ⁴ = basis of ∧²(ℂ⁵) = **SU(5) antisymmetric 10-rep**.

Under (N_S=3, N_T=2) decomposition:
- SS edges: C(3,2) = 3 (spatial pairs)
- ST edges: 3×2 = 6 (mixed)
- TT edges: C(2,2) = 1 (temporal pair)

## The Wedge Product Table

∧²(ℂ⁵) ⊗ ∧²(ℂ⁵) → ∧⁴(ℂ⁵) ≅ (ℂ⁵)* via Hodge star.

| Product | Count | Nonzero | Target | Physical |
|---------|-------|---------|--------|----------|
| SS ∧ SS | 3 | **0** | — | same-shell blocked |
| SS ∧ ST | 18 | **6** | T only | cross-shell → temporal |
| SS ∧ TT | 3 | **3** | S only | SSS hinge = strong |
| ST ∧ ST | 15 | **6** | S only | p-orbital → spatial |
| ST ∧ TT | 6 | **0** | — | blocked |
| TT ∧ TT | 0 | **0** | — | single edge, no self-wedge |
| **Total** | **45** | **15** | | **1/3 = 1/N_S** |

## Screening Derivation

### Cross-shell: σ = 7/8

Direct wedge channel: SS ∧ ST ≠ 0 (6 products).
Budget = d²-1 = 24 (adjoint SU(5)).
Active channels = N_S = 3.

```
σ_cross = 1 - N_S/(d²-1) = 1 - 3/24 = 7/8
```

### Same p-subshell: σ = 3/4

SS ∧ SS = 0 → direct channel **closed**.
Must use indirect path: SS → ST → target.
Accessible fraction = N_S/(N_S+1).

```
σ_same_p = N_S/(N_S+1) = 3/4
```

### Same d-subshell: σ = 2/3

Temporal indirect channel.
```
σ_same_d = N_T/(N_T+1) = 2/3
```

## Budget = Nonzero Wedge Count

**★ C(d+1,4) = C(6,4) = 15 = nonzero wedge products.**

This explains the Todd class budget at h³ level:
- h¹ budget: d²-1 = 24 (adjoint, triangle level)
- h³ budget: C(d+1,4) = 15 (4-form, tetrahedron level)
- h³ budget = number of nonzero ∧²⊗∧² products

The Todd correction δ = σ² × c₁ × α_GUT / budget
uses budget = 15 at h³ level because **15 is the number
of algebraically possible wedge channels**.

## Hodge Duality

Hinges (∧³) ↔ Edges (∧²) via Hodge star.
The S↔T content flips:

| ∧³ (hinge) | ↔ | ∧² (edge) |
|------------|---|-----------|
| SSS (1) | ↔ | TT (1) |
| SST (6) | ↔ | ST (6) |
| STT (3) | ↔ | SS (3) |

This means: **strong force hinges (SSS) are Hodge-dual
to temporal edges (TT)**, and vice versa.

## SU(5) Decomposition (ATM_064)

Adjacency matrix eigenvalues: **18**(×1), **3**(×4), **0**(×5).

10 = 1 + 4 + 5:
- 5 = d = dim(ℂ⁵) = null space (gauge directions)
- 4 = d-1 = dim(ℂP⁴) = physical directions
- 1 = trivial (total sum)

Under SU(3)×SU(2)×U(1):
- SSS(1) ↔ (1,1)₂
- SST(6) ↔ (3̄,2)₁/₃
- STT(3) ↔ (3,1)₋₄/₃

## Important Distinction (Mingu Jeong)

H*(ℂP⁴) = ℂ[x]/x⁵ has **5** classes (h^{p,p}, p=0..4), not 10.
The 10 = C(5,3) comes from the face classification
of Δ⁴ under the (3,2) split, which equals ∧²(ℂ⁵).
These are **not** Hodge classes but **hinge types**.

The two structures:
- **ℂP⁴ cohomology**: 5 classes, 1 generator (x), ring ℂ[x]/x⁵
- **DRLT hinges**: 10 types, C(5,3) = ∧²(ℂ⁵), SU(5) 10-rep

---

## Physical Interpretation

### Why σ_cross > σ_same

Cross-shell screening (σ = 7/8) is stronger than same-shell
(σ = 3/4) because **cross-shell has a direct wedge channel**
(SS∧ST ≠ 0) while **same-shell is blocked** (SS∧SS = 0).

The blocked channel means same-shell electrons must screen
through an **indirect path** (2-step process), reducing
the effective screening by a factor N_X/(N_X+1).

### The 15/45 = 1/3 ratio

Of all edge pairs, exactly 1/3 have nonzero wedge product.
This ratio = 1/N_S is not accidental: in ℂ⁵ = ℂ³⊕ℂ²,
the spatial sector (dim 3) determines the "openness" of
wedge channels. More spatial directions → more channels.

### Force channels

The wedge product target reveals **which direction is screened**:
- SS∧TT → S: strong force channel (all spatial)
- SS∧ST → T: electromagnetic screening (temporal)
- ST∧ST → S: p-orbital spatial screening

This is the DRLT origin of force unification:
**different screening types = different wedge product targets**.

### Connection to ATM_063 (IE precision)

Using the Todd correction with budget = 15 (= nonzero wedge count):
- Li: 376 ppm (0.038%)
- Period 2 median: 1734 ppm (0.17%)

The distributed Todd formula (per-pair = δ×N_T/N_inner)
gives median 1734 ppm with 0 free parameters.

---

## Experiments

| ID | Result |
|----|--------|
| ATM_064 | Hinge adjacency eigenvalues: 18,3,0 (mult 1,4,5) |
| ATM_065 | Wedge product: 15 nonzero, Hodge SSS↔TT duality |
| ATM_066 | All screening constants from wedge counting |
| ATM_063 | Todd solver: Li 376 ppm, median 1734 ppm |
