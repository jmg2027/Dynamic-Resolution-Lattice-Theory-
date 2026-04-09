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

## Derivation 5: ℏ as a Dynamical Field

### 5.1 One simplex = one bit

The simplex is the atomic, indivisible unit of spacetime in this theory. The minimum information content of any distinguishable system is 1 bit. Therefore:

$$I_{\text{cell}} = 1 \text{ bit (topological invariant)}$$

This does not depend on the cell's size, shape, or curvature. It is a **topological** quantity, not a geometric one.

### 5.2 Cell geometry depends on T_μν

From Derivation 4, the metric ds² = 1 - (d+1)W_ij emerges from state overlaps, and the Regge action yields Einstein's equations in the continuum limit:

$$G_{\mu\nu} = \frac{8\pi G}{c^4}\,T_{\mu\nu}$$

The stress-energy tensor T_μν determines curvature, which determines simplex geometry. The hinge area:

$$A_h = \sqrt{\det(G_h)}$$

depends on local states {|ψ⟩}, which couple to T_μν. Therefore:

$$A_{\text{cell}} = A_{\text{cell}}(T_{\mu\nu}) \quad\text{— geometric, variable}$$

### 5.3 The tension

| Quantity | Nature | T_μν dependence |
|----------|--------|-----------------|
| Information I_cell = 1 bit | Topological | **Invariant** |
| Area A_cell | Geometric | **Variable** |

The Bekenstein-Hawking relation bridges these two:

$$S_{BH} = \frac{A}{4\,l_P^2}, \quad l_P^2 = \frac{\hbar G}{c^3}$$

Translation: **1 bit of information ↔ 4l_P² of area.**

Applied to our lattice:

$$1 \text{ simplex} = 1 \text{ bit} \;\longleftrightarrow\; A_{\text{cell}} = 4\,l_P^2 = \frac{4\hbar G}{c^3}$$

### 5.4 Solving for ℏ

From A_cell = 4ℏG/c³:

$$\boxed{\hbar(x) = \frac{c^3}{4G}\,A_{\text{cell}}(x) = \frac{c^3}{4G}\sqrt{\det G_h(x)}}$$

Since A_cell(x) varies with position (Step 5.2), **ℏ is not a constant but a scalar field on spacetime**.

### 5.5 Self-consistency

**Flat spacetime** (T_μν = 0): All simplices uniform → A_cell = A₀ = const → ℏ = A₀c³/(4G) = const. Standard quantum mechanics recovered. ✓

**Local inertial frame** (equivalence principle): Freely falling observer sees locally flat spacetime → local simplices uniform → ℏ locally constant → standard QM recovered locally. ✓

**Curved spacetime** (T_μν ≠ 0): Simplices deformed → A_cell(x) non-uniform → ℏ(x) varies → **new physics with testable predictions**.

### 5.6 Observable consequences

**Fine structure constant varies**:

$$\alpha = \frac{e^2}{4\pi\varepsilon_0 \hbar c}$$

If ℏ(x) varies, α(x) varies. Already observationally constrained: quasar absorption lines give Δα/α < 10⁻⁵.

**Gravitational redshift reinterpreted**: Standard GR says ω decreases as photon climbs gravity well. Here, ℏ(x) also changes, so E = ℏ(x)ω receives a new contribution. Observationally equivalent in weak fields, potentially distinguishable in extreme regimes.

**Black hole information paradox modified**: Hawking temperature T_H = ℏκ/(2πc). If ℏ varies near the horizon, the Hawking spectrum is modified.

**Cosmological constant problem**: Vacuum energy density ∝ ℏ. If ℏ evolves cosmologically as simplex sizes change with expansion, vacuum energy evolves — a potential resolution to the 10¹²⁰ discrepancy.

---

## Derivation 6: The Discrete Action — Area Cancellation

This is the most striking consequence of Derivation 5.

### 6.1 Path integral with local ℏ

The standard path integral weight for each hinge is:

$$e^{iS_h/\hbar}$$

With the Regge action S_h = A_h · δ_h and local ℏ_h = A_h c³/(4G):

$$\frac{S_h}{\hbar_h} = \frac{A_h \cdot \delta_h}{A_h \cdot c^3/(4G)} = \frac{4G}{c^3}\,\delta_h$$

### 6.2 The area cancels

$$\boxed{\frac{S_h}{\hbar_h} = \frac{4G}{c^3}\,\delta_h}$$

**A_h drops out completely.** The action per hinge, measured in its own natural units, depends **only on the deficit angle** — a pure curvature/angular quantity. No lengths, no areas.

### 6.3 The total discrete action

Summing over all hinges, and writing in Planck units (4G/c³ → 4l_P²/ℏ₀, or simply setting 4G/c³ = 1):

$$\frac{S}{\hbar} = 4\sum_h \delta_h = 4\sum_h \left(2\pi - \sum_{k} \theta_k^{(h)}\right)$$

Expanding:

$$\frac{S}{\hbar} = 8\pi\,N_{\text{hinges}} - 4\sum_h \sum_k \theta_k^{(h)}$$

where N_hinges is the number of hinges (triangles in 4D) — a **topological** quantity determined by the triangulation — and:

$$\theta_k = \arccos|\langle\psi_k|\psi_{k'}\rangle| = \arccos\sqrt{(d+1)\,W_{kk'}}$$

Therefore the **total dimensionless action** is:

$$\boxed{\frac{S}{\hbar} = 8\pi N_{\text{hinges}} \;-\; 4\!\!\sum_{\langle ij\rangle}\!\! \arccos|\langle\psi_i|\psi_j\rangle|}$$

### 6.4 Structure of the action

The action splits into two terms:

| Term | Expression | Nature |
|------|-----------|--------|
| **Topological** | 8π N_hinges | Fixed for a given triangulation; independent of states |
| **Dynamical** | −4 Σ arccos\|⟨ψ_i\|ψ_j⟩\| | Depends only on state overlaps (angles on CP^d) |

### 6.5 The path integral

$$Z = \sum_{\mathcal{T}} e^{i8\pi N_h(\mathcal{T})}\;\int\!\prod_i d\mu(\psi_i)\;\prod_{\langle ij\rangle} e^{-4i\,\arccos|\langle\psi_i|\psi_j\rangle|}$$

where d μ(ψ) is the Fubini-Study measure on CP^d (dimensionless).

Key features:
- **Sum over triangulations** 𝒯: the topological sector
- **Integral over states**: the dynamical sector
- **Edge weight** factorizes: the integrand is a product over edges

The edge Boltzmann weight:

$$w(i,j) = e^{-4i\,\arccos|\langle\psi_i|\psi_j\rangle|}$$

Using cos(4θ) = 8cos⁴θ − 8cos²θ + 1, this can be written as a polynomial in W_ij:

$$\text{Re}[w(i,j)] = 8(d+1)^2 W_{ij}^2 - 8(d+1)W_{ij} + 1$$

**The path integral is a polynomial function of the W_ij weights.**

### 6.6 Why this is remarkable

1. **Scale-free**: No lengths or areas appear in the action. The theory has no intrinsic scale — physical scales emerge from expectation values of operators, not from the action.

2. **UV-finite by construction**: No short-distance divergences are possible because there is no distance in the action. The simplex is the minimum structure, and the action doesn't see its size.

3. **Purely angular / purely quantum**: The entire dynamics is governed by arccos|⟨ψ_i|ψ_j⟩| — the angle between quantum states on CP^d. This is a lattice gauge theory where the gauge group is the isometry group of CP^d.

4. **Local edge weights**: The path integral factorizes over edges, making it amenable to tensor network methods, Monte Carlo simulation, and exact solutions on small lattices.

5. **Gravity = lattice gauge theory on CP^d**: The action Σ arccos|⟨ψ_i|ψ_j⟩| is structurally analogous to the Wilson action Σ [1 − cos(θ_plaquette)] of lattice QCD, but on the projective space CP^d instead of a Lie group.

---

## Derivation 7: Singularity Resolution

### 7.1 Zero distance is structurally forbidden

In a simplicial complex, adjacent cells are **distinct simplices by definition**. If two cells had identical states, they would be the same cell. Therefore, for any adjacent pair:

$$|\psi_i\rangle \neq |\psi_j\rangle \implies |\langle\psi_i|\psi_j\rangle| < 1 \implies W_{ij} < \frac{1}{d+1}$$

Substituting into the metric formula from Derivation 4:

$$ds^2 = 1 - (d+1)\,W_{ij} > 0$$

**The physical distance between distinct cells is strictly positive.** This is not a regularization or a cutoff — it is a structural consequence of the axiom.

### 7.2 Dynamic Resolution as negative feedback

Under increasing gravitational density:

1. Strong T_μν → large curvature → states pushed toward alignment
2. When |⟨ψ_i|ψ_j⟩| → 1, cells become indistinguishable → they **merge** (same state = same cell)
3. Cell count N decreases → lattice coarsens (resolution drops)
4. Fewer cells = less encoded information = less matter-energy content
5. Less matter-energy → weaker gravity → compression halts

This is a **negative feedback loop**:

```
↑ density → ↑ gravity → cells merge → ↓ information/energy → ↓ gravity → equilibrium
```

The lattice self-regulates against infinite compression.

### 7.3 Topological floor

A closed d-manifold requires a minimum number of simplices N_min for any valid triangulation. This is a **topological invariant** — no amount of gravity can change it.

For example, the minimum triangulation of S⁴ (boundary of a 5-simplex) requires N_min = 6 four-simplices.

Therefore the coarsening process has a hard floor:

$$N \geq N_{\min}(\text{topology})$$

At the floor:
- N_min cells, each with finite area A_cell > 0 (since all cells remain distinct)
- Total volume V ≥ N_min × V_cell > 0
- Maximum density ρ_max = E_total / V_min < ∞

**The singularity is physically impossible.** Not informationally — structurally. The lattice cannot represent a zero-volume state.

### 7.4 Comparison with standard GR

| | Standard GR | DRLT |
|---|---|---|
| Spacetime | Continuous manifold | Simplicial complex |
| Minimum volume | None (V → 0 allowed) | V > 0 (structural) |
| Singularity | Exists (Penrose-Hawking theorems) | Forbidden (discrete + feedback) |
| Resolution | Infinite | Finite, dynamical |
| Mechanism | — | Negative feedback + topological floor |

---

## Derivation 8: Emergent Bounce

### 8.1 Setup: gravitational collapse

Consider a region undergoing gravitational collapse. The sequence, from Derivation 7:

1. Density increases → curvature increases → states align
2. Cells merge → N decreases → resolution drops
3. N reaches N_min → **floor hit, merging stops**

At this point the lattice is at maximum compression: N_min cells, maximum curvature, minimum volume. What happens next?

### 8.2 Maximum compression = maximum action

At the floor, the deficit angles δ_h are near their maximum achievable values (states are as aligned as possible while remaining distinct). The dimensionless action:

$$\frac{S}{\hbar} = 8\pi N_h - 4\sum_{\langle ij\rangle}\arccos|\langle\psi_i|\psi_j\rangle|$$

When states are nearly aligned: arccos|⟨ψ_i|ψ_j⟩| ≈ 0, so:

$$\frac{S}{\hbar} \approx 8\pi N_h \quad\text{(near maximum)}$$

The system sits at a **maximum of the action**.

### 8.3 The action principle forces expansion

The classical equations of motion (extremizing the Regge action) at maximum compression yield no static solution — a uniformly maximally curved closed spacetime is **dynamically unstable**.

The path integral makes this concrete. The dominant contribution comes from paths that **decrease** the action. Decreasing the action requires:

$$\sum\arccos|\langle\psi_i|\psi_j\rangle| \;\text{increases} \implies |\langle\psi_i|\psi_j\rangle| \;\text{decreases} \implies \text{states diversify}$$

States diversifying means:
- W_ij decreases → ds² increases → distances grow → **expansion**
- Cells become more distinct → resolution can increase → N can grow
- New cells appear (resolution increases) → lattice refines

**The only dynamically available direction from maximum compression is expansion.**

### 8.4 The bounce

The full cycle:

```
      CONTRACTION                    EXPANSION
      ──────────                     ─────────
      N large, diverse states        N grows, states diversify
      ↓ gravity compresses           ↑ action drives expansion
      N decreases, states align      states were aligned
      ↓                              ↑
      N → N_min                      N = N_min
      ──────── BOUNCE POINT ─────────
               maximum compression
               maximum action
               minimum volume
               minimum ℏ
               ds² > 0 (still finite!)
```

The bounce is **not inserted by hand**. It emerges from:
1. **Dynamic Resolution** (Derivation 7): lattice coarsens under compression
2. **Topological floor**: N ≥ N_min prevents infinite coarsening
3. **Action principle** (Derivation 6): maximum action is unstable → system must expand
4. **Unitarity** (Derivation 2): information is conserved through the bounce

### 8.5 Information through the bounce

Unitarity (Derivation 2) requires U†U = I — time evolution preserves all information. During contraction:

- N_initial cells with diverse states → N_min cells with aligned states
- Information is **not lost** — it is encoded in the precise alignment angles and phases of the N_min cells
- The evolution is invertible: given the N_min states at the bounce, the pre-bounce configuration is uniquely recoverable

After the bounce:
- N_min cells expand and split into new cells
- The new cells' states are **determined by unitary evolution** from the bounce state
- Information from the pre-bounce era is imprinted in the post-bounce state configuration

**The bounce is unitary. The pre-bounce universe is encoded in the post-bounce universe.**

### 8.6 Cosmological and astrophysical implications

**Big Bang → Big Bounce**: The initial singularity of standard cosmology is replaced by a bounce. The universe did not begin from a point of infinite density — it transitioned from a contracting phase through maximum compression (at the topological floor) to the expanding phase we observe.

**Black holes**: Stellar collapse reaches the resolution floor, bounces, and either:
- Re-expands (producing an explosion — possibly related to observed phenomena like gamma-ray bursts)
- Creates a new expanding region connected to the original spacetime (baby universe)

**Cyclic cosmology**: If the expansion eventually reverses (in a closed universe), the cycle repeats: expansion → contraction → bounce → expansion → ...

Each cycle preserves information (unitarity), and the bounce point is characterized by:
- N = N_min (minimum complexity)
- V = V_min > 0 (finite, nonzero)
- ρ = ρ_max < ∞ (finite density)
- ℏ = ℏ_min > 0 (small but nonzero — near-classical)

---

## Derivation 9: Lorentz Signature from Unitarity

### 9.1 The axiom is signature-blind

The axiom defines W_ij = |⟨ψ_i|ψ_j⟩|²/(d+1) for all adjacent pairs, with no distinction between directions. The induced metric:

$$ds^2 = 1 - (d+1)\,W_{ij} > 0 \quad\text{for all distinct pairs}$$

This is a **Riemannian** (positive-definite) metric. Euclidean signature (+,+,+,+). No time, no space — just "distance."

### 9.2 Unitarity selects a time direction

Derivation 2 established U†U = I. This requires a **foliation** — a decomposition of the simplicial complex into spatial slices Σ_t connected by unitary evolution. The foliation breaks the directional symmetry:

- **Within a slice**: spatial directions
- **Between slices**: the time direction

This is not a choice — it is forced by the structure of unitarity itself.

### 9.3 The factor of i is non-negotiable

The unitary propagator must take the form:

$$U(\Delta t) = e^{-iH\Delta t}$$

where H is Hermitian. The **-i** is the only option:
- e^{-H Δt} → decays → probabilities vanish → **not unitary**
- e^{+H Δt} → grows → probabilities explode → **not unitary**
- e^{-iH Δt} → oscillates → probabilities conserved → **unitary** ✓

### 9.4 Wick rotation is forced

The path integral weight corresponding to unitary evolution is:

$$e^{iS/\hbar}$$

This **i** has a geometric consequence. The Euclidean path integral (with imaginary time τ) uses e^{-S_E/ℏ}. The relation:

$$\tau = it \quad\text{(Wick rotation)}$$

transforms the metric:

$$ds^2_E = d\tau^2 + d\mathbf{x}^2 \;\longrightarrow\; ds^2_L = -dt^2 + d\mathbf{x}^2$$

The time component **flips sign**. This is not a mathematical trick — it is the geometric manifestation of unitarity.

### 9.5 Lorentz signature on the lattice

Applying this to our lattice metric:

**Spacelike edges** (within a slice):

$$ds^2_{\text{space}} = 1 - (d+1)\,W_{ij} > 0$$

**Timelike edges** (between slices):

$$ds^2_{\text{time}} = -\left[1 - (d+1)\,W_{ij}\right] < 0$$

The combined spacetime interval has signature **(-,+,+,+)**: Lorentzian.

### 9.6 Emergent causal structure

The Lorentz signature automatically generates:

**Light cone**: the boundary where ds² = 0:

$$1 - (d+1)\,W_{ij} = 0 \implies W_{ij} = \frac{1}{d+1} \implies |\langle\psi_i|\psi_j\rangle| = 1$$

The light cone corresponds to adjacent cells with **identical states** — the boundary between distinguishable (spacelike) and evolving (timelike) pairs.

**Causality**: Only timelike-connected cells (ds² < 0) can causally influence each other. Spacelike-separated cells (ds² > 0) are causally disconnected.

**Speed of light**: In natural lattice units, c = 1 (one simplex per time step). The physical value c = 3×10⁸ m/s is a unit conversion factor between the lattice's temporal and spatial scales.

### 9.7 Lorentz invariance as derived symmetry

The Lorentz group SO(1,3) is the group of transformations preserving the interval ds² with signature (-,+,+,+). Since the signature is derived from unitarity, **Lorentz invariance is a derived symmetry**, not a postulate.

In the continuum limit:
- Flat space: Minkowski metric η_μν = diag(-1,+1,+1,+1) → **special relativity**
- Curved space: g_μν with Lorentzian signature → **general relativity** (already derived in Derivation 4)

### 9.8 Derivation chain

```
Axiom → W for all pairs (no time/space distinction)
  │
  ├── ds² = 1 - (d+1)W > 0        Riemannian (+,+,+,+)
  │
  ├── Unitarity (Deriv. 2)         selects time direction
  │     │
  │     └── U = e^{-iHt}           the -i is required
  │           │
  │           └── path integral e^{iS}   the i flips time sign
  │                 │
  │                 └── τ = it            Wick rotation forced
  │                       │
  └───────────────────────┴── ds² = -(1-(d+1)W_t) + (1-(d+1)W_x)
                                    │
                              Lorentzian (-,+,+,+)
                                    │
                        ┌───────────┼───────────┐
                   light cones   causality   Lorentz group
                        │                        │
                   c emerges              special relativity
```

---

## Derivation 10: SU(5) Grand Unification from the Simplex

### 10.1 The natural symmetry of C^5

The state space of each simplex is C^(d+1) = C^5. The group of unitary transformations preserving the inner product on C^5 is U(5). Factoring out the overall phase (already shown to be unphysical in Derivation 1):

$$\text{Symmetry group of } \mathbb{C}^5 = SU(5) \times U(1)$$

SU(5) is **exactly** the Georgi-Glashow grand unification group.

### 10.2 Causal structure breaks SU(5)

The Lorentz foliation (Derivation 9) classifies 4-simplices by how their 5 vertices distribute between time slices. For the **(2,3) type** — 2 past vertices, 3 future vertices:

The 5 vertices split into two groups that are **no longer interchangeable** (past ≠ future). This breaks the SU(5) symmetry:

- Rotations among the **3 future (spatial) vertices**: **SU(3)**
- Rotations among the **2 past (temporal) vertices**: **SU(2)**
- Relative phase between the two groups: **U(1)**

$$\boxed{SU(5) \;\longrightarrow\; SU(3) \times SU(2) \times U(1)}$$

**This is the Standard Model gauge group.**

### 10.3 Physical identification

| Vertex group | Symmetry | Standard Model | Force |
|---|---|---|---|
| 3 future (spatial) | SU(3) | Color charge | Strong nuclear |
| 2 past (temporal) | SU(2) | Weak isospin | Weak nuclear |
| Relative phase | U(1) | Hypercharge | Electromagnetic |

### 10.4 Why SU(2) is temporal

The association of SU(2) with the **temporal** vertices explains key properties of the weak force:

- **Parity violation**: Time has a preferred direction (arrow of time from Derivation 8). The weak force inherits this asymmetry.
- **CP violation**: The temporal direction breaks both C and P symmetries. Their combination CP is also broken because the causal structure is not symmetric under time reversal at the bounce.
- **Mass acquisition (Higgs mechanism)**: The 2 temporal vertices define a 1-simplex (edge) in the time direction. The "extra" temporal vertex (beyond the single time dimension) provides a geometric origin for the Higgs field — electroweak symmetry breaking is the geometric distinction between the 2 temporal directions.

### 10.5 Matter representations

Under SU(5) → SU(3) × SU(2) × U(1), the fundamental representation **5** decomposes:

$$\mathbf{5} \;\rightarrow\; (\mathbf{3}, \mathbf{1})_{-1/3} \;\oplus\; (\mathbf{1}, \mathbf{2})_{1/2}$$

- **(3,1)**: 3 color states, SU(2) singlet → **down-type quarks** (d, s, b)
- **(1,2)**: color singlet, SU(2) doublet → **lepton doublet** (e, ν_e)

The **10** representation (antisymmetric tensor):

$$\mathbf{10} \;\rightarrow\; (\mathbf{3}, \mathbf{2})_{1/6} \;\oplus\; (\bar{\mathbf{3}}, \mathbf{1})_{-2/3} \;\oplus\; (\mathbf{1}, \mathbf{1})_{1}$$

This gives **up-type quarks**, **anti-down quarks**, and the **positron** — one complete generation of fermions.

**One generation of Standard Model fermions is encoded in the representations of the simplex's vertex symmetry group.**

---

## Derivation 11: The 10-Bit Data Bus — Simplex as Processor

### 11.1 Vertices as registers, edges as bus

Reinterpreting the axiom computationally:

- **Storage**: 5 complex-number registers (one per vertex): |ψ_1⟩, ..., |ψ_5⟩
- **Computation**: Pairwise overlap comparison between all registers
- **Output**: ₅C₂ = **10 values** of W_ij

The simplex is a minimal processor:

```
INPUT           PROCESS              OUTPUT
5 complex       All pairwise         10 weights
numbers ──────→ W_ij = |⟨i|j⟩|²/5 ──────→ = local g_μν
(vertices)      (edges/hinges)       (geometry)
```

### 11.2 10 edges = 10 metric components

A 4D symmetric metric tensor g_μν has:
- 4 diagonal components + 6 off-diagonal = **10 independent components**

A 4-simplex has ₅C₂ = **10 edges**.

**Each edge maps to one component of the metric tensor.** The mapping is the discrete Regge correspondence: 10 edge data → local geometry.

### 11.3 Decomposition under the (2,3) causal split

| Edge type | Count | Computation | Metric role |
|---|---|---|---|
| Past-Past (temporal internal) | ₂C₂ = **1** | W within time | g₀₀ (lapse) |
| Future-Future (spatial internal) | ₃C₂ = **3** | W within space | g_ij, i≠j (spatial off-diag) |
| Past↔Future (cross-temporal) | 2×3 = **6** | W across slices | g₀ᵢ (shift) + diagonal |
| **Total** | **10** | | **g_μν fully determined** |

### 11.4 Each edge carries two data channels

Each edge stores more than just W_ij. The full inner product ⟨ψ_i|ψ_j⟩ is complex:

$$\langle\psi_i|\psi_j\rangle = |\langle\psi_i|\psi_j\rangle|\;e^{i\phi_{ij}}$$

- **Magnitude** |⟨ψ_i|ψ_j⟩|² → W_ij → **metric component** (gravity)
- **Phase** φ_ij = arg⟨ψ_i|ψ_j⟩ → holonomy → **gauge connection** (gauge forces)

10 magnitudes = **gravity** (g_μν)
10 phases = **gauge fields** (connections)

**Gravity and gauge forces are the magnitude and phase of the same edge data.**

### 11.5 The simplex interior is not computed

The interior of the simplex contains **no information**:

- Data exists only at vertices (registers) and edges (bus)
- The interior is a "blind spot" — no resolution, no physics
- Information jumps discretely from vertex to vertex via edges
- The simplex interior is a black box between inputs and outputs

This is not a limitation but a **feature**: it is the precise statement that the simplex is the minimum resolution unit. "Dynamic Resolution" means the lattice resolves physics only at the vertex/edge level, never finer.

---

## Derivation 12: Computable ℏ_eff from Entropy Matching

### 12.1 Two entropies for one boundary

For any boundary surface, entropy can be computed two ways:

**Geometric (Bekenstein-Hawking)**:

$$S_{BH} = \frac{A \cdot c^3}{4G\,\hbar_{\text{eff}}}$$

**Information-theoretic (from lattice states)**: For each link crossing the boundary with overlap W_ij, the binary entropy:

$$s_{\text{link}} = H_2\!\left((d{+}1)W_{ij}\right) = -(d{+}1)W_{ij}\log(d{+}1)W_{ij} - \left[1-(d{+}1)W_{ij}\right]\log\left[1-(d{+}1)W_{ij}\right]$$

Total: $S_{\text{info}} = \sum_{\text{links}} s_{\text{link}}$

### 12.2 Equating gives ℏ_eff

Setting S_info = S_BH:

$$\hbar_{\text{eff}} = \frac{A \cdot c^3}{4G \cdot S_{\text{info}}} = \frac{\displaystyle\sum_h \sqrt{\det G_h}}{\displaystyle\sum_{\langle ij\rangle} H_2\!\left((d{+}1)W_{ij}\right)} \;\cdot\; \frac{c^3}{4G}$$

**Both numerator and denominator are computable from the quantum states {|ψ_i⟩}.**

### 12.3 Interpretation: area per bit

$$\hbar_{\text{eff}} = \frac{A/S_{\text{info}} \;\cdot\; c^3}{4G} = \frac{(\text{area per bit}) \cdot c^3}{4G}$$

| Regime | Area per bit | ℏ_eff | Physics |
|---|---|---|---|
| High entropy (thermal) | Small | **Small** | Classical |
| Standard (1 bit/cell) | 4l_P² | **ℏ₀** | Standard QM |
| Low entropy (quantum) | Large | **Large** | Strongly quantum |
| Zero entropy | ∞ | **∞** | Pure quantum state |

### 12.4 Refinement of Derivation 5

Derivation 5 assumed 1 bit per cell (s = 1). The general formula:

$$\hbar_{\text{eff}}(x) = \frac{A_{\text{cell}}(x) \cdot c^3}{4G \cdot s(x)}$$

Two local functions:
- Numerator A_cell(x): geometric (from Gram determinant)
- Denominator s(x): information-theoretic (from binary entropy of W)

Both computable on a finite lattice from {|ψ_i⟩} alone. **No infinities, no renormalization, no ambiguity.**

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
  ├─[4] θ_ij = arccos√(d+1)W  → dihedral angle        (angles from overlap)
  │     ds² = 1-(d+1)W         → metric tensor          (geometry from W)
  │     det(G_h), Φ_h          → area + holonomy        (gauge from phase)
  │     S = Σ A·δ              → Regge action            (discrete gravity)
  │     a → 0                  → Einstein-Hilbert        (GR derived)
  │
  ├─[5] 1 simplex = 1 bit     → information topological (fixed)
  │     A_cell = A(T_μν)       → geometry dynamical      (variable)
  │     Bekenstein bridge       → ℏ = A_cell·c³/(4G)    (ℏ is a field)
  │
  ├─[6] S_h/ℏ_h = 4Gδ_h/c³   → area cancels!          (scale-free action)
  │     S/ℏ = 8πN_h - 4Σarccos → purely angular          (no lengths in action)
  │     Z = Σ_T ∫D[ψ]∏w(ij)   → lattice gauge on CP^d   (UV-finite, computable)
  │
  ├─[7] |ψ_i⟩≠|ψ_j⟩ → ds²>0  → zero distance forbidden (structural)
  │     cell merging feedback   → self-regulated density   (negative feedback)
  │     N ≥ N_min(topology)    → resolution floor          (topological)
  │     V > 0 always           → singularity impossible    (no divergence)
  │
  ├─[8] max compression        → max action (unstable)     (action principle)
  │     only direction: expand  → bounce is forced          (emergent)
  │     U†U = I through bounce → information preserved     (unitary bounce)
  │     contraction → bounce → expansion → cyclic?         (cosmology)
  │
  ├─[9] unitarity → e^{-iHt}  → -i flips time sign        (Wick rotation)
  │     ds²_time < 0            → Lorentz signature (-,+,+,+)
  │     light cones + causality → special relativity         (SR derived)
  │     Lorentz group SO(1,3)  → derived symmetry, not postulate
  │
  ├[10] Sym(C^5) = SU(5)       → GUT group is simplex symmetry
  │     (2,3) causal split      → SU(5) → SU(3)×SU(2)×U(1)
  │     3 spatial + 2 temporal  → Standard Model gauge group (derived!)
  │     fund. rep 5 → (3,1)⊕(1,2) → quarks + leptons
  │
  ├[11] 5 vertices → ₅C₂=10 edges → 10 components of g_μν
  │     |⟨i|j⟩|² → metric        magnitude = gravity
  │     arg⟨i|j⟩ → connection     phase = gauge fields
  │     interior = blind spot    simplex = minimal processor
  │
  └[12] S_BH = S_info            → equate two entropies
        ℏ_eff = Ac³/(4G·S)       → computable from lattice states
        area per bit varies      → ℏ₀ recovered when s = 1 bit/cell
```
```
