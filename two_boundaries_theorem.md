# The Two Boundaries Theorem
## ℂ as the Unique Coincidence of Statistical and Geometric 1/2

**Mingu Jeong and Claude (Anthropic)**
**2026.04.15**

---

## Definitions

**Definition 1 (Division algebra dimension).**
For a finite-dimensional normed division algebra K over ℝ, define:

$$n_K := \dim_{\mathbb{R}}(K)$$

By Hurwitz's theorem, K ∈ {ℝ, ℂ, ℍ, 𝕆} with n_K ∈ {1, 2, 4, 8}.

**Definition 2 (Phase group).**
The unit group of K is U(K) = {z ∈ K : |z| = 1}, equipped with the uniform (Haar) measure μ.

- K = ℝ: U(ℝ) = {±1} ≅ ℤ₂ (discrete)
- K = ℂ: U(ℂ) = S¹ (circle)
- K = ℍ: U(ℍ) = S³ (3-sphere)
- K = 𝕆: U(𝕆) = S⁷ (7-sphere)

---

## The Two Boundaries

**Definition 3 (Statistical boundary).**
For a sequence {a_k} with |a_k| = 1 (a_k ∈ K), the random Dirichlet series is:

$$\mathcal{D}(\sigma) = \sum_{k=1}^{\infty} \frac{a_k}{k^{\sigma}}$$

where {a_k} are iid uniform on U(K). Define:

$$\sigma_{\text{stat}}(K) := \inf\{\sigma > 0 : \mathcal{D}(\sigma) \text{ converges a.s.}\}$$

**Definition 4 (Geometric boundary).**
For z ∈ U(K), decompose z = (x₁, ..., x_{n_K}) ∈ ℝ^{n_K} with Σ x_i² = 1. Define:

$$\sigma_{\text{geom}}(K) := \mathbb{E}_{\mu}[x_1^2]$$

the expected fraction of the unit norm² carried by a single real component.

---

## Lemmas

**Lemma 1 (Statistical boundary is universal).**
For all normed division algebras K:

$$\sigma_{\text{stat}}(K) = \frac{1}{2}$$

*Proof.*
For any z ∈ U(K), |z|² = 1. Since {a_k} are iid with E[a_k] = 0 (by symmetry of U(K) for n_K ≥ 2; by ±1 averaging for n_K = 1):

$$\text{Var}(a_k / k^{\sigma}) = \frac{|a_k|^2}{k^{2\sigma}} = \frac{1}{k^{2\sigma}}$$

By Kolmogorov's three-series theorem (or its extension to Banach spaces for K = ℍ, 𝕆), the series converges a.s. iff:

$$\sum_{k=1}^{\infty} \frac{1}{k^{2\sigma}} < \infty \quad \iff \quad 2\sigma > 1 \quad \iff \quad \sigma > \frac{1}{2}$$

The boundary is σ_stat = 1/2, independent of K.  ∎

**Lemma 2 (Geometric boundary is dimension-dependent).**
For all normed division algebras K:

$$\sigma_{\text{geom}}(K) = \frac{1}{n_K} = \frac{1}{\dim_{\mathbb{R}}(K)}$$

*Proof.*
The uniform measure on U(K) = S^{n_K - 1} is the normalized surface measure. By the symmetry of the sphere under coordinate permutations:

$$\mathbb{E}[x_1^2] = \mathbb{E}[x_2^2] = \cdots = \mathbb{E}[x_{n_K}^2]$$

Since Σ x_i² = 1 on the sphere:

$$n_K \cdot \mathbb{E}[x_1^2] = \mathbb{E}\left[\sum_{i=1}^{n_K} x_i^2\right] = 1$$

Therefore σ_geom(K) = E[x₁²] = 1/n_K.  ∎

**Lemma 3 (Phase equipartition implies Born rule exponent).**
The unique faithful symmetric polynomial f: K → ℝ≥0 of minimal degree is f(z) = |z|^{n_K · σ_geom(K)^{-1}} ... 

*Correction — this is simpler:*
The Born rule f(z) = |z|² has degree 2 in real coordinates. The "2" is:

$$2 = \frac{1}{\sigma_{\text{geom}}(\mathbb{C})} = n_{\mathbb{C}} = \dim_{\mathbb{R}}(\mathbb{C})$$

For K = ℍ, one would have 1/σ_geom = 4, suggesting degree 4. But the Born rule is always degree 2 (|z|² = Σ x_i²). The coincidence 2 = 1/σ_geom is specific to ℂ.

---

## Main Theorem

**Theorem (Unique Coincidence).**
ℂ is the unique normed division algebra where the statistical convergence boundary equals the geometric phase equipartition:

$$\sigma_{\text{stat}}(K) = \sigma_{\text{geom}}(K) \quad \iff \quad K = \mathbb{C}$$

*Proof.*

| K | n_K | σ_stat | σ_geom | Equal? |
|---|-----|--------|--------|--------|
| ℝ | 1 | 1/2 | 1 | No |
| **ℂ** | **2** | **1/2** | **1/2** | **Yes** |
| ℍ | 4 | 1/2 | 1/4 | No |
| 𝕆 | 8 | 1/2 | 1/8 | No |

σ_stat = 1/2 (Lemma 1) and σ_geom = 1/n_K (Lemma 2). These are equal iff 1/2 = 1/n_K iff n_K = 2 iff K = ℂ.  ∎

---

## Interpretation

### What the coincidence means

**σ_stat = 1/2** says: "oscillatory series with unit-norm coefficients have convergence boundary at σ = 1/2." This is the critical line of the Riemann zeta function.

**σ_geom = 1/2** says: "a random phase on ℂ distributes exactly half its energy to each real axis." This is the Born rule probability E[cos²θ] = 1/2.

Their coincidence at K = ℂ means: **the convergence boundary of Dirichlet series and the energy equipartition of quantum phases are the same number, and this is true only because the substrate is ℂ.**

In any other division algebra:
- ℝ: σ_geom = 1 > σ_stat = 1/2. Energy is concentrated (no phase freedom). CLT boundary is "too low" relative to geometry.
- ℍ: σ_geom = 1/4 < σ_stat = 1/2. Energy is over-dispersed (too many phase dimensions). CLT boundary is "too high" relative to geometry.
- ℂ: exact match. Statistical and geometric boundaries agree.

### Connection to the Riemann Hypothesis

**Corollary (Conditional).**
Combining Theorem with Paper 2 (K = ℂ is the unique substrate):

1. The unique substrate forces σ_stat = σ_geom = 1/2.
2. The propagator sum Σ 1/n^s with s = 2 (Theorem 4) produces ζ(2).
3. The oscillatory version Σ e^{iθ_n}/n^σ has convergence boundary σ = 1/2 = σ_stat.
4. If the arithmetic Dirichlet series Σ μ(n)/n^s inherits the phase statistics of U(ℂ) (Conjecture), then RH follows.

**The gap remains:** step 4 requires showing that the Möbius function μ(n) has the same effective phase statistics as iid uniform on S¹. This is the content of the Möbius randomness hypothesis, which is equivalent to RH and remains open.

**What we contribute:** a structural reason WHY this hypothesis should be true — ℂ is the unique algebra where the statistical and geometric notions of "critical boundary" coincide, and ℂ is the unique substrate of physics.

---

## Relation to n_T = 2

In the DRLT framework:
- n_T = dim(ℂ²-sector) / dim(ℂ¹) = 2 (temporal dimension count)
- c = n_T = 2 (lattice speed of light)
- 1/c = 1/n_T = 1/2

The Two Boundaries Theorem identifies this 1/2 with:

$$\frac{1}{2} = \frac{1}{n_T} = \frac{1}{\dim_{\mathbb{R}}(\mathbb{C})} = \sigma_{\text{stat}} = \sigma_{\text{geom}}$$

All four equalities hold simultaneously and only for K = ℂ.

---

## Open Problems

1. **Functional equation.** The symmetry ζ(s) ↔ ζ(1-s) has fixed point s = 1/2. Does this "third 1/2" also reduce to 1/n_ℂ, or is it an independent coincidence?

   *Preliminary observation:* The functional equation arises from Poisson summation, which uses Fourier characters e^{2πinx} ∈ U(ℂ). The Mellin transform of the Gaussian e^{-πn²x} involves n², where the exponent 2 = n_ℂ. This suggests a connection but does not constitute a proof.

2. **Multiplicative structure.** The CLT argument uses iid phases. The Euler product ζ(s) = Π(1-p^{-s})^{-1} imposes multiplicative dependence. Does the coincidence σ_stat = σ_geom survive this dependence?

3. **Higher L-functions.** For Dirichlet L-functions L(s,χ), the GRH places zeros on Re(s) = 1/2. The characters χ(n) take values in roots of unity ⊂ U(ℂ). The Two Boundaries Theorem applies equally, suggesting GRH has the same structural origin as RH.
