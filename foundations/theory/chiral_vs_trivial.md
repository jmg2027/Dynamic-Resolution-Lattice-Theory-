# Representation-Theoretic Distinction: Chiral vs Swap-Trivial Sectors

**Status:** Established (2026-04-14)
**Depends on:** Paper 1 (chiral decomposition), Paper 2 (Frobenius to gauge), ch03 (rep uniqueness)

---

## Motivation

The Gram matrix eigenvalue spectrum after swap annihilation has three regions:

```
Region I:  λ₁ ... λ₅         (chiral)
Region II: λ₆ ... λ_{d_ind}  (swap-trivial)
Region III: λ_{d_ind+1} ... = 0  (hard wall)
```

All Region I and II eigenvalues are spectrally indistinguishable (≈ N/d_ind for generic vectors; Paper 1 Thm 6.1). This document rigorously defines the distinction.

---

## 1. Definitions

### 1.1 Gram matrix and sectoral decomposition

**Definition 1.1** (Gram matrix).
For N unit vectors ψ₁,...,ψ_N ∈ ℂ^d, the Gram matrix is G_ij = ⟨ψ_i, ψ_j⟩.
Properties: N×N, Hermitian, PSD, unit diagonal, rank ≤ d.

**Definition 1.2** (Atomic decomposition and projections).
Given ℂ^d = ⊕_{k=1}^{m} V_k with each dim V_k ∈ {2, 3}, the orthogonal projection
π_k: ℂ^d → V_k defines the **sectoral Gram matrix**:

    G^(k)_ij = ⟨π_k ψ_i, π_k ψ_j⟩

**Lemma 1.1** (Additive decomposition).

    G = Σ_{k=1}^{m} G^(k)

*Proof.* From the inner product on a direct sum: ⟨ψ_i, ψ_j⟩ = Σ_k ⟨π_k ψ_i, π_k ψ_j⟩. ∎

### 1.2 Chiral and trivial sectors

**Definition 1.3** (Chiral/trivial partition).
After τ-symmetrization of all repeated atomic blocks:

- **V_c** (chiral sector): the unique surviving atomic pair ℂ³ ⊕ ℂ² ⊂ ℂ^d. dim V_c = 5.
- **V_t** (trivial sector): the remaining τ-symmetrized paired blocks. dim V_t = d_ind − 5.

With orthogonal projections π_c and π_t:

    G_c = (⟨π_c ψ_i, π_c ψ_j⟩)_ij,    rank ≤ 5
    G_t = (⟨π_t ψ_i, π_t ψ_j⟩)_ij,    rank ≤ d_ind − 5
    G = G_c + G_t

---

## 2. Spectral Indistinguishability

**Theorem 2.1** (No spectral gap).
For N generic unit vectors in ℂ^{d_ind} (d_ind > 5, N ≥ d_ind), the eigenvalues of G satisfy:

    (λ_i − λ_j) / λ_i = O(1/√N)    for all 1 ≤ i, j ≤ d_ind

In particular, no algebraic gap exists between λ₅ and λ₆.

*Proof sketch.* G = ΨΨ† with Ψ ∈ ℂ^{N×d_ind}. The nonzero eigenvalues equal those of Ψ†Ψ ∈ ℂ^{d_ind × d_ind}. For generic Ψ with unit-norm rows, Ψ†Ψ ≈ (N/d_ind)I + O(√N) fluctuations. By GUE universality (β = 2, forced by ℂ), relative eigenvalue spacing is O(1/√N). ∎

**Corollary 2.2.** The eigenvalues of G alone cannot distinguish contributions from G_c and G_t.

---

## 3. Representation-Theoretic Distinguishability

### 3.1 Key definitions

**Definition 3.1** (Structure group).
The structure group of the decomposition ℂ^d = ⊕ V_k is S(∏_k U(n_k)).

**Definition 3.2** (Swap automorphism).
For a pair with dim V_i = dim V_j = n:

    σ_ij: SU(n)_i × SU(n)_j → SU(n)_j × SU(n)_i,  (g₁, g₂) ↦ (g₂, g₁)

This is an outer automorphism of order 2 (generating ℤ₂).

**Definition 3.3** (Complex representation).
An irreducible representation ρ of a Lie group H is *complex* if ρ ≇ ρ̄ (not isomorphic to its conjugate).

### 3.2 The theorem

**Theorem 3.1** (Representation-theoretic distinction).

**(a)** The structure group of V_c, Aut(V_c) = S(U(3) × U(2)), possesses **complex irreducible representations**.

Specifically: the fundamental representation (3, 2) satisfies (3, 2) ≇ (3̄, 2̄) = (3̄, 2).

**(b)** For any τ-symmetrized pair in V_t, the σ-invariant representations are **all self-conjugate**.

For any σ-invariant irrep ρ: ρ ≅ ρ̄.

*Proof.*

(a) The center of SU(3) is ℤ₃, acting as ω·I (ω = e^{2πi/3}) on the fundamental **3**. Its conjugate **3̄** transforms as ω̄·I. Since ω ≠ ω̄, **3** ≇ **3̄**. The fundamental of SU(2) is pseudo-real (**2** ≅ **2̄**), but the tensor product **3** ⊗ **2** has conjugate **3̄** ⊗ **2** ≇ **3** ⊗ **2** (because the SU(3) factor distinguishes them). ∎

(b) Let ρ = ρ₁ ⊗ ρ₂ ∈ Rep(SU(n)₁ × SU(n)₂). The swap acts as σ(ρ₁ ⊗ ρ₂) = ρ₂ ⊗ ρ₁. σ-invariance requires ρ₁ ≅ ρ₂. Setting ρ₁ = ρ₂ =: μ:

    ρ = μ ⊗ μ ≅ Sym²(μ) ⊕ ∧²(μ)

Both Sym²(μ) and ∧²(μ), viewed as representations of the diagonal SU(n)_diag, are self-conjugate:

    Sym²(μ̄) ≅ Sym²(μ)̄ ≅ Sym²(μ)*

since the diagonal embedding is σ-invariant by construction. ∎

---

## 4. Trace Partition and Corrections

### 4.1 Trace conservation

**Theorem 4.1** (Trace partition).

    Tr(G) = Tr(G_c) + Tr(G_t) = N

For generic unit vectors:

    Tr(G_c) = (5/d_ind) · N + O(√N)
    Tr(G_t) = ((d_ind − 5)/d_ind) · N + O(√N)

*Proof.* Tr(G_c) = Σ_i ||π_c ψ_i||². For a uniformly random unit vector in ℂ^{d_ind}, E[||π_c ψ||²] = dim(V_c)/d_ind = 5/d_ind. By CLT, the sum over N vectors has fluctuation O(√N). ∎

### 4.2 Observability

**Definition 4.1** (Chiral observable).
An observable O is *chiral* if it depends only on complex representations of Aut(V_c). Formally: O factors through the projection G ↦ G_c.

**Theorem 4.2** (Indirect correction via trace conservation).
Let O be a chiral observable with leading value O₀ computed from G_c. The correction from the existence of V_t is:

    δO/O₀ = −Tr(G_t)/Tr(G) × (sector-dependent factor)

This is an *indirect* correction: O does not couple to G_t directly (no complex representations in V_t), but Tr conservation forces G_c to carry less than the full trace N, reducing O.

The sector-dependent factor is determined by the Binet-Cauchy channel structure of ∧³(ℂ⁵) and equals f_T × α_GUT where f_T = n_B/3 (temporal fraction of the hinge) and α_GUT = 6/(25π²) (the geometric coupling constant from d² channels and ζ(2) propagator).

---

## 5. Summary

The distinction between Region I and Region II is captured by exactly one property:

> **The representation ring of the structure group of V_c contains complex irreducible representations; that of V_t does not.**

This is equivalent to the statements:
- V_c supports chirality (left ≠ right); V_t does not.
- V_c supports CP violation (ρ ≇ ρ̄); V_t does not.
- V_c supports charge quantization (π₁(U(1)) = ℤ via relative phase); V_t does not (π₁(SU(n)) = 0).

No spectral measurement can detect this distinction. It is purely algebraic.

The physical corrections arising from V_t enter only through trace conservation (Tr(G) = N), not through direct coupling to observables.

---

## Connection to other documents

- **Paper 1** (Thm 6.1): proves spectral indistinguishability (soft boundary O(1/√N))
- **Paper 2** (Thm 5.1): derives α_GUT = 6/(25π²) from geometry, not eigenvalue magnitudes
- **ch03** (§3.5): "contributions from λ₆,...,λ_{d_ind}: spectrally indistinguishable from λ₁,...,λ₅ but representation-theoretically trivial"
- **folded_dim.md** (revised 2026-04-14): corrected from "eigenvalue leaking" to "trace redistribution"
