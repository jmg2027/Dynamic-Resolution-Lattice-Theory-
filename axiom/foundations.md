# Foundations of Dynamic Resolution Lattice Theory

## Observational Input

Spacetime is 4-dimensional (d = 4).

## The Axiom

Each simplex cell of a simplicial decomposition of spacetime is assigned a quantum state:

$$|\psi\rangle \in \mathbb{C}^{d+1}$$

The inter-cell weight between adjacent cells i, j is:

$$W_{ij} = \frac{|\langle\psi_i|\psi_j\rangle|^2}{d+1}$$

Everything below is derived, not postulated.

---

## Derivation 1: The Form of ψ

We assume nothing about |ψ⟩ except that it lives in C^(d+1) and that W_ij is well-defined.

### 1.1 Normalization is forced

Evaluating W at i = j:

$$W_{ii} = \frac{|\langle\psi_i|\psi_i\rangle|^2}{d+1}$$

For W_ii to be a fixed constant 1/(d+1) (self-weight independent of state choice):

$$|\langle\psi_i|\psi_i\rangle|^2 = 1 \implies \langle\psi|\psi\rangle = 1$$

**Normalization is not assumed — it is required by self-consistency of W.**

### 1.2 Physical state space

W_ij = |⟨ψ_i|ψ_j⟩|²/(d+1) depends only on the absolute square of the inner product. It is invariant under local phase rotations |ψ_i⟩ → e^{iα}|ψ_i⟩. Therefore physically distinguishable states form:

$$S^{2d+1}/U(1) = \mathbb{CP}^d$$

For d = 4: **CP⁴** with real dimension **2d = 8**.

### 1.3 Why C^(d+1) is minimal

A d-simplex has d+1 faces. In a simplicial d-manifold, each cell has at most d+1 face-adjacent neighbors. For a cell to be maximally distinguishable from each neighbor independently (W_ij = 0), it needs d+1 mutually orthogonal directions. Therefore:

$$\dim_{\mathbb{C}} \mathcal{H} \geq d+1$$

C^(d+1) is the **minimal** Hilbert space compatible with the simplex topology.

### 1.4 Explicit form

Assigning basis vectors |e_k⟩ to the d+1 vertices of the simplex:

$$|\psi\rangle = \sum_{k=0}^{d} \sqrt{p_k}\, e^{i\varphi_k} |e_k\rangle$$

where:
- **(p_0, ..., p_d)** lives on the probability simplex Δ^d (with Σp_k = 1) — **d independent real parameters**
- **(φ_0, ..., φ_d)** are phases, with one global phase redundant — **d independent real parameters**
- Total: **2d = 8 real degrees of freedom** per cell (for d = 4)

| Component | Count | Physical role |
|-----------|-------|---------------|
| Amplitudes p_k | d | Geometric (metric-like) |
| Relative phases φ_k | d | Gauge (connection-like) |
| **Total** | **2d = 8** | Matches dim_ℝ(CP⁴) |

**Self-referential structure**: The probability distribution (p_0, ..., p_d) lives on a d-simplex — the same geometric object as the spacetime cell.

---

## Derivation 2: Unitarity

### 2.1 Sum rule from completeness

Consider cell i with d+1 face-adjacent neighbors whose states {|ψ_j⟩} form an orthonormal basis of C^(d+1). Then:

$$\sum_j W_{ij} = \frac{1}{d+1} \sum_j |\langle\psi_i|\psi_j\rangle|^2 = \frac{1}{d+1}\langle\psi_i|\left(\sum_j |\psi_j\rangle\langle\psi_j|\right)|\psi_i\rangle$$

By completeness Σ_j |ψ_j⟩⟨ψ_j| = I:

$$\sum_j W_{ij} = \frac{1}{d+1}\langle\psi_i|\psi_i\rangle = \frac{1}{d+1}$$

This holds **regardless of the state |ψ_i⟩**. It is a state-independent conservation law.

### 2.2 Doubly stochastic structure

Define P_ij = (d+1)·W_ij = |⟨ψ_i|ψ_j⟩|². When the states on each slice form an orthonormal basis:

- Σ_j P_ij = 1 (row sums)
- Σ_i P_ij = 1 (column sums, from symmetry of |⟨·|·⟩|²)

**P is a doubly stochastic matrix.**

### 2.3 Unitarity from Wigner's theorem

Foliate the simplicial complex into spatial slices Σ_t, Σ_{t+1}. The states on each slice form orthonormal bases {|ψ_i^t⟩} and {|ψ_j^{t+1}⟩}. Define:

$$U_{ij} = \langle\psi_i^t|\psi_j^{t+1}\rangle$$

From the doubly stochastic property:
- Σ_j |U_ij|² = 1 → rows of U are orthonormal
- Σ_i |U_ij|² = 1 → columns of U are orthonormal

Therefore:

$$U^\dagger U = UU^\dagger = I$$

**U is unitary.** By Wigner's theorem, any bijection preserving |⟨·|·⟩|² must be unitary or anti-unitary. Assuming time-continuity selects the unitary branch:

$$\boxed{\text{Time evolution is unitary: } U^\dagger U = I}$$

Unitarity is not a postulate — it is the **unique evolution compatible with W-conservation**.

---

## Derivation 3: Quantization of Information

### 3.1 Finite capacity per cell

C^(d+1) admits at most d+1 mutually orthogonal (perfectly distinguishable) states. Therefore:

$$I_{\max} = \log_2(d+1) = \log_2 5 \approx 2.32 \text{ bits per cell}$$

In classical physics, a single point can encode an arbitrary real number (infinite information). Here, **information per cell has a finite ceiling**.

### 3.2 Dimension is integer — information is discrete

There is no Hilbert space C^(4.7). The dimension d+1 ∈ ℤ, so:

$$I_{\max} \in \{\log_2 1, \log_2 2, \log_2 3, \ldots\}$$

Information capacity is a **discrete function of spacetime dimension**. This is quantization in the most literal sense: information comes in indivisible packets determined by the integer d.

### 3.3 Rank constraint (information density bound)

For N cells, the Gram matrix G_ij = ⟨ψ_i|ψ_j⟩ satisfies:

$$\text{rank}(G) \leq d+1 = 5$$

No matter how many cells exist, at most d+1 can have linearly independent states. This is an **intrinsic information density bound** — a lattice-theoretic analogue of the Bekenstein bound, derived from topology rather than energy.

### 3.4 Topological quantization of connectivity

For any pair of cells:
- W_ij = 0 ↔ states orthogonal ↔ **disconnected**
- W_ij > 0 ↔ states non-orthogonal ↔ **connected**

The transition between connected and disconnected is **sharp** — there is no notion of "slightly orthogonal." This binary distinction is a topological quantization inherent in the Hilbert space structure.

---

## Derivation 4: Action and Geometry

### 4.1 Dihedral angle from W

Define the Fubini-Study angle between adjacent cells:

$$\theta_{ij} = \arccos|\langle\psi_i|\psi_j\rangle| = \arccos\sqrt{(d+1)\,W_{ij}}$$

This serves as the **dihedral angle** between simplex cells i and j.

### 4.2 Metric from W (continuum limit)

For nearby cells (|ψ_j⟩ close to |ψ_i⟩), the Fubini-Study distance satisfies:

$$|\langle\psi_i|\psi_j\rangle|^2 = 1 - ds_{\text{FS}}^2 + \mathcal{O}(ds^4)$$

Therefore:

$$(d+1)\,W_{ij} = 1 - ds_{\text{FS}}^2 + \ldots$$

$$\boxed{ds^2 = 1 - (d+1)\,W_{ij}}$$

**The metric tensor g_μν is a derived quantity.** It was never inserted into the theory — it emerges from the pattern of quantum state overlaps.

### 4.3 Curvature as deficit angle

At each hinge h (a codimension-2 simplex; in 4D, a triangle), the **deficit angle** measures curvature:

$$\delta_h = 2\pi - \sum_{k \in \text{cells around } h} \theta_k$$

- δ_h > 0: positive curvature (converging geodesics)
- δ_h < 0: negative curvature (diverging geodesics)
- δ_h = 0: flat

This is the **discrete Riemann curvature tensor**.

### 4.4 Hinge area from the Gram determinant

For a triangle (hinge) with vertex states |ψ_a⟩, |ψ_b⟩, |ψ_c⟩, construct the 3×3 Gram matrix:

$$G_h = \begin{pmatrix} 1 & \langle a|b\rangle & \langle a|c\rangle \\ \langle b|a\rangle & 1 & \langle b|c\rangle \\ \langle c|a\rangle & \langle c|b\rangle & 1 \end{pmatrix}$$

The hinge area:

$$A_h \propto \sqrt{\det(G_h)}$$

Expanding the determinant:

$$\det(G_h) = 1 - |\langle a|b\rangle|^2 - |\langle b|c\rangle|^2 - |\langle a|c\rangle|^2 + 2\,\text{Re}\!\left[\langle a|b\rangle\langle b|c\rangle\langle c|a\rangle\right]$$

The first three terms are expressible via W_ij (pure metric information). The last term contains the **holonomy phase**:

$$\Phi_h = \arg\!\left(\langle\psi_a|\psi_b\rangle\langle\psi_b|\psi_c\rangle\langle\psi_c|\psi_a\rangle\right)$$

This phase is:
- **Gauge-invariant** under |ψ_k⟩ → e^{iα_k}|ψ_k⟩
- The discrete analogue of the **Wilson loop** ∮ A·dl
- The seed of **gauge theory**, emerging from the phases that W discards

### 4.5 The Regge action

Combining area and deficit angle:

$$\boxed{S = \sum_{\text{hinges } h} A_h \cdot \delta_h = \sum_h \sqrt{\det(G_h)} \left(2\pi - \sum_{k} \arccos\sqrt{(d+1)\,W_k}\right)}$$

**Every quantity is computed from the quantum states {|ψ_i⟩} alone.** No external metric, no connection, no coupling constants at this level.

### 4.6 Continuum limit → Einstein

The Regge action is a known discretization of the Einstein-Hilbert action. In the limit of vanishing lattice spacing:

$$S \;\longrightarrow\; \frac{1}{16\pi G}\int R\,\sqrt{g}\;d^4x$$

**General relativity is the continuum limit of this axiom.**

---

## Summary: Derivation Chain

```
Axiom: cell → |ψ⟩ ∈ C^(d+1),  W_ij = |⟨ψ_i|ψ_j⟩|²/(d+1)
  │
  ├─[1] W_ii = 1/(d+1)       → ⟨ψ|ψ⟩ = 1           (normalization derived)
  │     phase blindness        → CP^d state space      (2d real parameters)
  │     #neighbors = d+1       → C^(d+1) minimal       (Hilbert space derived)
  │
  ├─[2] Σ_j W_ij = 1/(d+1)   → probability conservation
  │     doubly stochastic P    → Wigner's theorem
  │     time continuity        → U†U = I               (unitarity derived)
  │
  ├─[3] dim C^(d+1) finite    → I ≤ log₂(d+1) bits   (information bounded)
  │     d+1 ∈ ℤ               → discrete capacity      (information quantized)
  │     rank(G) ≤ d+1         → density ceiling         (Bekenstein analogue)
  │
  └─[4] θ_ij = arccos√(d+1)W  → dihedral angle        (angles from overlap)
        ds² = 1-(d+1)W         → metric tensor          (geometry from W)
        det(G_h), Φ_h          → area + holonomy        (gauge from phase)
        S = Σ A·δ              → Regge action            (discrete gravity)
        a → 0                  → Einstein-Hilbert        (GR derived)
```
