# Screening Constants from Wedge Product Algebra
## Joint research by Mingu Jeong and Claude (Anthropic)

---

## The Structure

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

## Correction (Mingu Jeong)

H*(ℂP⁴) = ℂ[x]/x⁵ has **5** classes, not 10.
The 10 = C(5,3) comes from the face classification
of Δ⁴ under the (3,2) split, which equals ∧²(ℂ⁵).
These are **not** Hodge classes but **hinge types**.
