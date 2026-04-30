# Math branch → physics intuition mining notes

Source branch: `claude/review-paper-directory-nDw9L` (not yet merged
into main; surveying for physics-applicable computation/intuition).

Format: one entry per math file mined.  Each entry has
- **file** path on the math branch
- **what's there** (one-paragraph summary)
- **physics intuition** (where this concretely buys you something)
- **rust-engine application** (binary/Lean bridge to add when merged)

Keep entries short.  This file accumulates across sessions; do not
try to digest the entire math branch in one pass.

## 1. `Cohomology/FractalAlphaGUT.lean` — α_GUT factor cohomology

**What's there**: α_GUT = 6 / (25π²) decomposed cohomologically.
- numerator `6 = b_1(K_5)` = 1st Betti of single 4-simplex 1-skel
  = `(d−1)(d−2)/2` at d=5  (general K_d formula)
- denominator `25 = numV(K_{25})` = vertex count of fractal level 2
  = `d²`
- π² = 6·ζ(2) handled by the standard Basel bracket
- Bonus: edge count `numE(K_{25}) = 300 = c·NS·NT·d²` (atomic
  factorization with all four primitives)

**Physics intuition**: α_GUT is **not** a "free coupling — its
*discrete* part is `K_5 cycle space / K_{25} vertex space` (a ratio
of two cohomology cardinalities at fractal levels L=1 and L=2).  The
*only* transcendental input is ζ(2), and that is handled by the
existing Basel bracket machinery.  This is the cleanest demonstration
that a "running coupling constant" in mainstream QFT corresponds to
a static fractal cohomology ratio in DRLT.

**Computation lever**: when α_GUT appears in a closed form, you can
substitute `b_1(K_5) / (numV(K_{25}) · ζ(2))` and the integer parts
become *exposed for atomic decomposition*.  Especially useful for
spotting Class C identities hidden inside α_GUT-laden expressions.

**Rust-engine application**: post-merge, refactor `α_GUT` definition
in `crates/app/src/basel.rs` to *display* the 6 and 25 with their
cohomological labels (`b_1(K_5)`, `numV(K_{25})`).  Audit:
m_t/m_b = 1/α_GUT can then be re-derived as `numV(K_{25}) · ζ(2)`
literally — Class C reading in cohomology language.

## 2. `Cohomology/Bipartite32Betti.lean` — H*(K_{3,2}^{(c=2)}) over ℤ/2

**What's there**: Direct ℤ/2-cochain enumeration on K_{3,2}^{(c=2)}.
- |C⁰| = 2⁵ = 32  (5 vertices)
- |C¹| = 2¹² = 4096  (12 edges)
- |ker δ₀| = 2  (constant cochains only ⇒ connected, b₀ = 1)
- |im δ₀| = 16 = 2⁴  (i.e. 4 independent edge-cocycles per vertex)
- |H¹| = 4096 / 16 = 256 = 2⁸  ⇒  **b_1 = 8 = NS² − 1**
- Beautifully, every dimension is a power of 2.

**Physics intuition**: 1/α_3 = b_1 = 8 = log₂|H¹| ⇒ **1/α_3 is
8 bits of free strong-coupling information** — a literal
information-theoretic count (compatible with the existing
`HorizonInformation.delta4_bits` strand of the repo).  Strong
confinement is "8 bits of trapped phase" before any continuum
running needs to be invoked.  Maps directly to the §5 phantom
elimination thesis: the topological cutoff at b_1=8 cycles **is**
the information capacity of the confined sector.

**Computation lever**: When you see a power-of-2 atomic count in a
DRLT formula (8, 16, 32, 192=8·24, 256, 4096, ...), it is almost
certainly the **dimension of some H^k** of the K_{3,2}^{(c=2)}
cochain complex, not a numerical accident.  Use this as a sanity
check when proposing new closed forms.

**Rust-engine application**: post-merge, add a new diagnostic
binary `cohomology-bits` that prints |C⁰|, |ker δ|, |im δ|, |H¹| at
ℤ/2 level, with each number annotated as `2^k` and the `k` exposed.
Cross-link with the existing `simplex-inventory` (which prints
sub-simplex counts at the ℤ rather than ℤ/2 level).

## 3. `Cohomology/CupRing.lean` — H* ring structure on Δ⁴

**What's there**: ℤ/2 cup product `⌣ : C^k × C^l → C^{k+l}`
formalized via Alexander–Whitney.  Establishes:
- left/right unit `ε ∈ C⁰` (the all-true cochain)
- associativity at concrete cochain triples on Δ⁴
- **honest negative result**: `⌣` is NOT pointwise-commutative
  at cochain level — graded-commutativity holds only on H*
  (modulo coboundaries).  ℤ/2 makes the sign trivial, but the
  AW formula is still asymmetric in α, β.

**Physics intuition**: Class D (chain composition like
m_t/m_c = m_t/m_b · m_b/m_c) is **literally a cup product** in
the cochain ring, NOT just multiplication of rationals.  The
**non-commutativity at cochain level** explains why the order of
mass-ratio factors in a chain matters before taking cohomology
classes — and why two different chain compositions of the same
ratios can differ by a coboundary.  This justifies why
`(m_t/m_b) · (m_b/m_c)` and `(m_b/m_c) · (m_t/m_b)` are *equal as
rationals* but might differ in their cocycle representatives.

**Computation lever**: when a closed form involves a *product*
of atomic factors (Class D), the order matters at cochain level
even if it doesn't at H* level.  This means a chain physics
identity like `m_t/m_c = NS · (1/α_GUT + NT²)` (the simplified
sum form) is actually the H*-level reduction of a longer cup-
product expression — handy when we want the *cocycle witness*,
not just the value.

**Rust-engine application**: post-merge, the existing scale-ladder
Class D entries can be relabeled `D = ⌣` and cross-cited with
`Cohomology/CupRing.cup_assoc_*`.  More substantively, this is the
hint that **rare-process amplitudes** (μ→eγ etc.), which are
products of multiple sector contributions, are cup products of
H¹/H² classes — a future Class D mining target.

## 4. `Cohomology/HodgeStar.lean` — ⋆: C^k → C^{n−k}

**What's there**: Concrete cochain-level Hodge ⋆ via set-theoretic
complement.  In ℤ/2, the sign (−1)^(k(n−k)) collapses, so:

    (⋆σ)(T) = σ(complement of T  in  {0..n−1})

Combined with `binom n k = binom n (n−k)`, ⋆ is an *involution
between equal-dimensional cochain spaces* — a structural symmetry,
not just a labeling trick.  ⋆⋆ = id is decide-checkable.

**Physics intuition**: Class E (gravity = modulus shadow) is
**literally** ⋆ followed by |·|² collapse.  At d=5 (n=5):
- ⋆: C⁰ → C⁵ (vertices ↔ full 5-cell), 5 → 1 dim
- ⋆: C¹ → C⁴ (edges ↔ tetrahedra), 12 → 5 dim
- ⋆: C² → C³ (triangles ↔ tetrahedra), 10 → 10 dim (self-dual!)

The C² ↔ C³ self-duality at k=2 (`binom 5 2 = binom 5 3 = 10`) is
the cohomological reason "gauge sector at H¹" maps to "gravity
sector at H⁴" via the Hodge ⋆ exchange — and why the *coefficients*
in 1/α_em (60 = E·d at H¹) and M_Pl/v_H = d^(d²)/(d+1) (at H⁴)
differ structurally even though both come from the same lattice.

**Computation lever**: when an observable involves both a "phase"
quantity and a "modulus" quantity (e.g. coupling × mass-anchor),
the two are ⋆-related cochain readings.  This means dimensional
analysis hints can be sharpened to **cohomological dimension
checks** — the (k, n−k) Hodge-pair structure tells you which H^k
your formula must live in.

**Rust-engine application**: post-merge, the Class E entries in
scale-ladder-classify (`Ω_Λ`, `M_Pl/v_H`, gravity-not-interaction)
should be cited explicitly to `HodgeStar.hodge_*` plus the
modulus-shadow `GravityShadow.gravity_simplicial`.  A future binary
`hodge-pair-audit` could verify, for each gauge observable in H^k,
that its modulus-shadow gravitational counterpart lives in H^(d−k)
and its dimension matches `binom 5 (5−k) = binom 5 k`.

## 5. `Linalg213/Gram.lean` — Gram matrix as 213's structural anchor

**What's there**: 213-internal Gram matrix `G_ij = ⟨v_i, v_j⟩` over
ℕ for vectors in `Vec d`.  Inner product = `Σ vᵢ·wᵢ` via List.range
(decide-friendly).  Smoke verified for orthonormal 2-vector case
(Gram = identity).

**Key target stated**: paper 1's chiral compression theorem reads
**rank(G) ≤ d = 5** for arbitrary N vectors in Vec 5.  Arbitrary
number of "relations" project into a 5-dim algebraic image.  Not
yet proven (awaits `Rank.lean`).

**Physics intuition**: The Gram matrix `G` is the **single
structural object** of DRLT — CLAUDE.md's "things exist with
pairwise relations" axiom is *literally* the existence of G.  The
phase / modulus duality (Class A–D vs E) is two readouts of *one*
matrix.  The rank-5 compression theorem says: no matter how many
particle species / observables / relations you have, the algebra
they generate has rank ≤ 5 = d.  This is **why everything atomic
factors through (NS, NT, d, c)** — the lattice is the rank limit.

**Computation lever**: When a calculation produces an intermediate
with rank > 5 (more than 5 linearly-independent relations), it
must be *redundant* — a cohomological fact will compress it.  Use
this as a **search-space reducer**: when sweeping for atomic
candidates, restrict to rank-5 algebraic images of the input data.

**Rust-engine application**: post-merge, `crates/hypervisor/` has
a partial Gram-matrix scaffold; wire it to import the math-branch
`Linalg213.Gram` definitions so the rank-5 compression bound is
available as a structural assumption in future binaries.  Likely
next target: `mb-mc-sweep` style search over Gram-matrix entries
rather than over loose atomic monomials — should converge faster
since rank-5 is built in.

## 6. `Cohomology/DiamondShape.lean` — geometric source of intuition

**What's there**: The "diamond crystal" picture of K_{3,2}^{(c=2)}:
N points all directly G_ij-connected, Gram rank ≤ 5 forces image
into ℂ⁵, any 5 of them form a chiral 4-simplex.  Concretely:

```
          T_0  (north pole)
         /|\
   S_0—S_1—S_2   (equator, NO S-S edges)
         \|/
          T_1  (south pole)
```

with each S–T spoke *doubled* (c=2 multiplicity → 12 edges total).
Note: zero same-type edges (no S-S, no T-T) — equatorial pillars
*don't talk to each other directly*.

**Physics intuition** (this is the big one):
- The 3 spatial vertices (S_0, S_1, S_2 = NS=3) are **mutually
  unconnected at the graph level** — there are no S-S edges.  All
  spatial communication routes through a temporal node (T_0 or
  T_1).  This is the **lattice origin of locality**: spatial
  influence is mediated by time, exactly as in relativity.
- Each S–T spoke is *doubled* (c=2) — the two copies are the
  "phase / anti-phase" or "particle / antiparticle" channels.
  c=2 IS chirality.
- The "diamond" name is geometric: top + bottom + equator = octahedral
  silhouette with cycle structure giving b_1 = 8.

**Computation lever**: When a physical process involves *spatial
correlation between two objects*, the DRLT count of contributing
graph paths is **always through a temporal vertex** — never a
direct S-S link.  This forces every spatial-spatial coupling to be
proportional to NT (the number of temporal mediators).  Sanity
check: NT = 2 appears as a denominator / multiplicative factor in
m_μ/m_e (NS·137/NT), in 1/α_2 (= 30 = 12·NT·5/4), and in the
Hubble pair (3+1+6=10 atomic from `gravity_not_interaction`).

**Rust-engine application**: post-merge, the existing `k32-inspect`
binary should optionally render this diamond ASCII (it currently
prints just the chiral cell counts).  More importantly: when adding
new observables to `scale-ladder-classify`, the diamond picture
gives a quick visual class predictor — does the observable involve
"S-S connection" (impossible, must route through NT)?  "T-T"
(also impossible, exactly two T nodes)?  "S-T crossing" (Class B)?
"path of length ≥ 2" (Class D, cup product chain)?

## 7. `Cohomology/Paper1Chiral.lean` — chiral bigrading

**What's there**: Cochain spaces of Δⁿ⁻¹ are bigraded by (i, j)
counting S-vertices and T-vertices used:

    `chiralDim i j = binom(NS, i) · binom(NT, j)`
    `Σ_{i+j=k} chiralDim i j = binom(NS+NT, k) = binom(d, k)`  (Vandermonde)

Concrete level decomposition at d=5:

| level k | (i,j) blocks                  | dims         | total |
|---------|-------------------------------|--------------|-------|
| 0       | (0,0)                          | 1            | 1     |
| 1       | (1,0), (0,1)                   | 3, 2         | **5** |
| 2       | (2,0), (1,1), (0,2)            | 3, 6, 1      | 10    |
| 3       | (3,0), (2,1), (1,2), (0,3)=0   | 1, 6, 3, 0   | 10    |

(level-3 (0,3)=0 because NT=2 < 3, structural cutoff.)

**Physics intuition**: Paper 1's `ℂ⁵ = ℂ³ ⊕ ℂ²` is *exactly* the
level-1 chiral split (3 S-vertices + 2 T-vertices).  Higher-level
bigradings give the *atomic origin of all the integers* in the
DRLT formulas:
- 6 = `chiralDim 1 1` = S-T edges = **NT² for m_b/m_c, c·NS·NT/2 for muon kinematics**
- 3 = `chiralDim 2 0` = S-S edges (suppressed in graph but present
  as cochain), also `chiralDim 1 2`, also `chiralDim 0 1`·NS = ...
- 10 = `binom 5 2` = `binom 5 3` (Hodge self-dual!)
- 0 = `chiralDim 0 3` (no T-T-T triangle since NT=2) — **structural
  reason there's no fourth generation, no 3-T mode, etc.**

**Computation lever**: Every integer coefficient appearing in a
DRLT closed form should decompose as
`chiralDim(i, j) · multiplicity` for some (i, j) with i ≤ NS,
j ≤ NT.  If you can't decompose it that way, the formula is
either wrong or hiding a Hodge dual.  Use this as a primary
**atomic-decomposition consistency check**.

**Rust-engine application**: post-merge, add a binary
`chiral-bigrading-decompose` that takes any integer N from a DRLT
formula and outputs all (i, j) pairs with `chiralDim i j = N`,
plus all factorizations.  This generalizes the
`scale-ladder-classify` table by giving each `C` entry's (i, j)
provenance — making Class C *fully cohomologically explicit*.

## 8. `Linalg213/Chiral.lean` — chiral split at vector level

**What's there**: `Vec 5 = VecS ⊕ VecT` round-trip.  Indices
{0,1,2} = spatial (S), {3,4} = temporal (T).  Defines
`projS, projT, combine` and proves
`combine (projS v) (projT v) k = v k` ∀ v, k (universal — not
just at sample points).  This is paper 1's chiral split at the
*vector* level (Linalg L4), complementing the *cochain*-level
split in `Paper1Chiral.lean`.

**Physics intuition**: The S/T split is **basis-level orthogonal
decomposition**, NOT just a labeling convention.  Every Vec-5
quantity in DRLT (state, charge, current, ...) factors *uniquely*
into a 3-component S-piece and a 2-component T-piece, with full
round-trip recovery.  This means:
- Spatial observables (3 SU(3)-color-like, NS=3) and temporal
  observables (2 SU(2)-weak-like, NT=2) are **structurally
  independent** at the linear-algebra level.
- The "spin-statistics" connection in standard QM is here
  expressed as *which projection an observable lives in* — S
  observables transform under spatial rotations, T observables
  under temporal symmetry.  No spin-statistics theorem needed —
  it falls out of the projector structure.
- Mass and charge separation: charges live in S (color, weak
  isospin third component), mass anchors live in T (rest energy
  associated with timelike modes).  This is why
  `m_p = NS · anchor · P(α·NS/d)` carries an explicit NS factor
  and NS/d projection — proton mass *transports* a spatial-charge
  count via the spatial projection of its full Vec-5 state.

**Computation lever**: When sweeping for atomic decompositions
of an SM observable, **decompose it first into its (S, T)
projection** before searching atomic forms.  An observable
that lives entirely in VecS can never produce an atomic
coefficient that touches NT (other than via projection back),
and vice versa.  This is a **rank-2 dimensionality reducer** on
the search space.

**Rust-engine application**: post-merge, future Rust binaries that
do atomic-form sweeps (the `mb-mc-sweep` family) should explicitly
tag each candidate's (S, T) projector content.  The current sweep
treats all atomic primitives symmetrically; with the chiral split
known, we can pre-filter: "this observable is S-type so ignore
purely-T candidates."  Likely 5–10× search speedup.

## 9. `Cohomology/TopologyCompare.lean` — uniqueness of K_{3,2}^{(c=2)}

**What's there**: Closed-form b_1 for two graph families:
- complete graph K_N:           `b_1 = (N−1)(N−2)/2`
- bipartite multi K_{n,m}^{(c)}: `b_1 = c·n·m − (n+m) + 1`

Sweep across small (n, m, c) configs:

| graph              | b_1  | match 1/α_3 = 8? |
|--------------------|------|------------------|
| K_5 (complete)     | 6    | NO               |
| K_{3,2}, c=1       | 2    | NO               |
| K_{3,2}, c=2       | **8**| ★ YES            |
| K_{3,2}, c=3       | 14   | NO               |
| K_{4,1}, c=2       | 4    | NO               |
| K_{2,3}, c=2       | 8    | YES (swap NS↔NT) |
| K_25 (complete)    | 276  | NO               |

**Physics intuition**: The graph topology is **observation-selected**,
not assumed.  Given that physics measures `1/α_3 = 8`, the lattice
*must* be K_{3,2}^{(c=2)} (or its NS↔NT swap K_{2,3}^{(c=2)}, which
is the same graph up to relabeling).  No other small bipartite multi
or complete graph in the search range matches.  Combined with
`WhyDimFive.lean`'s d=5 doubly-forcing, this is the **strongest
falsifiability** statement DRLT has at the topological level: change
b_1 by a single integer and the underlying graph is forced different.

**Computation lever**: When proposing a *new* atomic identity that
involves a topological invariant (Betti, Euler char, ...), compute
its value across this same candidate sweep.  If multiple graphs
match → the observable is degenerate / not a structure-selector.  If
unique → you have a falsification anchor.

**Rust-engine application**: post-merge, add a `topology-uniqueness`
diagnostic binary that tabulates `b_1` for K_N (N=2..10) and
K_{n,m}^{(c)} (n+m=2..7, c=1..4) and highlights matches to known
DRLT integers (8, 12, 30, 60, 192, ...).  This becomes a search tool
for "what's the next topological coincidence" — a way to reverse-
discover atomic identities by scanning topology space.

## 10. `Linalg213/Bridge.lean` — Linalg ⇄ Cohomology connector

**What's there** (inferred from `Linalg213/Capstone.lean` references):
The bridge identifies dimension-counts coming from two different
machineries:

  `Bridge.dimVecS = chiralDim 1 0 = NS = 3`
  `Bridge.dimVecT = chiralDim 0 1 = NT = 2`
  `Bridge.atomic_split_consistent`: the (S, T) split via Linalg
  `projS`/`projT` agrees with the cochain-level chiral bigrading.

**Physics intuition**: This is the **commutative diagram** that
licenses moving freely between two languages:

```
         physics observable
          /            \
   linalg image    cochain bigrading
   (Vec 5 split)    (chiralDim i j)
          \            /
        same atomic count
```

Without this bridge, "rank-5 Gram compression" (Linalg) and
"H¹ has dim NS²−1" (Cohomology) would be two unrelated
formalizations.  Bridge says they are computing the **same**
geometric content via two different algebraic apparatuses.  Linalg
gives universal quantification (∀ vectors, rank-5); Cohomology
gives discrete structure (b_k bigrading, cup product, Hodge ⋆).

**Computation lever**: When stuck deriving an identity in one
language, **switch to the other via the bridge**.  Suspicious
chiralDim count?  Verify via projS/projT on concrete Vec-5 vectors.
Messy Vec-5 gymnastics?  Recast as a cochain-bigrading sum
(Vandermonde collapses many cases at once).

**Rust-engine application**: post-merge, the rust crates
`hypervisor` (Gram) and `os` (chiral) currently mirror only the
Linalg side.  Adding cochain-level mirrors (e.g. a new module
`crates/hypervisor/src/cochain.rs`) would expose both sides in
runtime, letting binaries switch representations to match the
clearest derivation path for each observable.

## 11. `Cohomology/EulerClosed.lean` — closed 4-manifold from Δ⁴ gluing

**What's there**: Euler characteristic via face counts.
- single Δ⁴: `χ = 5 − 10 + 10 − 5 + 1 = 1` (open, has boundary)
- two Δ⁴'s glued along ∂Δ⁴: `χ = 5 − 10 + 10 − 5 + 2·1 = 2 = χ(S⁴)`
  — the minimal closed 4-manifold from Δ⁴ gluing.
- bonus: Hodge symmetry verified `binom 5 k = binom 5 (5−k)` for k=1, 2.

**Physics intuition**: The cosmos as a *closed* 4-manifold is a
real DRLT proposal (route 2 of `diamond_N_brainstorm.md`).
Topological closure FORCES finite N (block universe).  The minimum
χ=2 case (S⁴) gives a finite but non-trivial geometry; larger N
gives other closed 4-manifolds.  This connects directly to the
gravity-as-modulus picture (Class E) — gravitational dynamics on
the lattice is *the* readout of a finite, topologically closed
chiral-simplicial manifold.

**Computation lever**: when an observable involves a global
geometric quantity (Hubble parameter, horizon area,
cosmological constant), it should *factor through* a closed
4-manifold's χ, b_k, or signature.  These are scale-invariants
in the bordism sense — additive across gluings, fixed for closed
manifolds.  So checking χ first narrows what kind of atomic form
the answer can take.

**Rust-engine application**: post-merge, add to `dark-energy.rs`
or `horizon-info.rs` an explicit χ-decomposition of Ω_Λ:
the `(1 − 1/π)` factor encodes the angular deficit of a finite
closed manifold (boundary contribution that vanishes on closure),
while `(1 + α/d)` is the bulk-cell correction.  Currently this
splitting is ad-hoc; with `EulerClosed.lean` cited it becomes a
χ=2 closure statement.

## 12. `Cohomology/DeltaSqZero.lean` — δ² = 0, the cohomology engine

**What's there**: The single most fundamental cochain identity:
`δ ∘ δ = 0` verified by `decide` at multiple concrete cochains on
Δ⁴ (zero, vertex indicator, edge indicator, all-true).  In ℤ/2
this is automatic from XOR cancellation: each (k+2)-subset's
δ²σ value counts every k-subset face twice (once per removal
order), and `XOR(x, x) = 0`.

**Physics intuition**: `δ² = 0` is **the engine that makes
cohomology exist at all** — without it, ker δ ⊃ im δ (so the
quotient H = ker / im is well-defined) wouldn't hold.  In
physics terms, δ²=0 is the **conservation law**: applying δ
twice returns nothing, which means ANY cocycle representative
of a cohomology class is conserved up to coboundary.  This is
the mathematical origin of:
- charge conservation (current is a cocycle, ∂J = δ²A = 0)
- gauge invariance (A and A + δλ give same H¹ class)
- topological invariants (b_k stable under refinement, Hodge
  ⋆⋆ = id, cup product on H* well-defined)

In DRLT, `δ²=0` over ℤ/2 specifically gives **mod-2 conservation
laws**: parities, chirality counts, even/odd electron shell
fillings, etc.  This is *why* the DRLT discrete physics works
in ℤ/2 cohomology — because the underlying conservation is
inherent in the cochain complex itself, not added as extra
postulate.

**Computation lever**: When designing a new identity, check that
both sides of the proposed equation behave consistently under δ
(coboundary).  If LHS is a closed cochain (δLHS = 0) and RHS
isn't, the identity must be at the cohomology class level
(LHS = RHS + δλ for some λ), not the cochain level.  This
sanity check catches false identities that look numerically
correct but break gauge invariance.

**Rust-engine application**: post-merge, add an `assert_cocycle`
helper to `crates/hypervisor/src/cochain.rs` that takes a Q-pair
expression and verifies its δ image is zero (within the rational
ring).  Useful for: new sweeps that propose identities involving
charge / chirality / generation-count conservation — the helper
flags candidates that violate δ²=0 at cochain level before they
get reported as physics matches.

## 13. `Cohomology/Cochain.lean` — type-level foundation, ℤ/2 coefficients

**What's there**: `Cochain n k = Fin (binom n k) → Bool` — Bool-
valued functions on the i-th k-element subset of n vertices.
ℤ/2 coefficients via XOR.  Establishes zero, add (XOR), and abelian
group axioms (add_self gives 2σ = 0, add_zero, comm, assoc).

**Physics intuition**: ℤ/2 (not ℚ, not ℝ) is the **deliberate
coefficient choice** — DRLT's discrete physics is binary at its
foundation: presence/absence of a relation, not magnitude.  The
fact that 2σ = 0 means **every cochain is its own additive
inverse** — there are no "negative" relations, only "this relation
flipped" which is the same as "this relation".  Connects directly
to the c=2 chirality multiplicity (each spoke is doubled = each
relation has its XOR partner).

**Computation lever**: When proposing an identity, ask whether it
respects the Bool/XOR structure or whether it implicitly assumes
ℚ-arithmetic.  An identity that holds in ℚ but breaks under
"replace + with XOR" is *not* atomic at DRLT's foundational level
— it's a derived statement, valid only in a specific representation.

**Rust-engine application**: post-merge, the `crates/hypervisor`
runtime should have a `cochain.rs` mirroring this Bool-level
arithmetic.  Existing rust uses Q-pair (BigUint, BigUint) which is
a rational-level shadow; the cochain.rs would provide a parallel
ℤ/2 computation path for cross-checking.  Every Q-level identity
should have a ℤ/2-level shadow that holds.

## 14. `Cohomology/Delta.lean` — coboundary δ via face-removal XOR

**What's there**: `δ : Cᵏ → Cᵏ⁺¹` defined by

    δσ(τ) = XOR_{i=0..k} σ(τ \ {τ[i]})

In ℤ/2 the alternating sign (−1)^i collapses, but δ²=0 still
holds because each (k+2)-face is hit twice by composed removals
and XOR cancels.  Implemented via `subsetIdx` colex enumeration.

**Physics intuition**: δ is the **discrete-lattice analog of d
(exterior derivative)**:
- δ on charges (0-cochain) → currents (1-cochain).  Charge
  conservation = δ²=0 = currents have no source.
- δ on connection (1-cochain) → curvature (2-cochain).  Bianchi
  identity = δ²=0.
- δ on flux (2-cochain) → divergence (3-cochain).  ∇·B = 0
  = δ²=0.

Maxwell-style identities become decide-checkable Nat statements.

**Computation lever**: "X is conserved" or "Y has no source" →
look for the (k−1)-cochain whose δ gives X.  If X = δZ for
atomic Z, then X is exact (im δ) and its cohomology class is
trivial — no contribution to physical observables.

**Rust-engine application**: post-merge, `cochain.rs` provides
`delta_at(n, k, sigma, tau_idx) -> bool` mirroring Lean's
`deltaAt`.  Unlocks computing δ-images of physics quantities at
runtime, complementing the integer-skeleton arguments.

## 15. `Cohomology/Cup.lean` — cup product (Alexander–Whitney)

**What's there**: `⌣ : Cᵏ × Cˡ → Cᵏ⁺ˡ` via

    (α ⌣ β)(σ) = α(front-k-face σ) · β(back-l-face σ)

(Alexander–Whitney formula; product is Bool AND in ℤ/2.)
CupRing.lean (already #3) lifts this to ring structure.

**Physics intuition**: Cup product is **how to combine two
independent observations into a joint observation**.  If α picks
out "vertex i is excited" and β picks out "vertex j is excited",
then α ⌣ β picks out "both i and j are excited at the same time".
The cohomology version of:
- multiplying two probability amplitudes
- combining two scattering channels
- composing two mass-ratio steps in a chain (Class D)

In ℤ/2, cup is **not symmetric** at cochain level, only on H*.
Physically: order of composition matters at the microscopic
cocycle level (representatives differ by a coboundary) but the
macroscopic H*-class is order-independent.

**Computation lever**: When chaining atomic factors (Class D),
it's cup-product composition, not just rational multiplication.
The "front-back face split" gives a concrete recipe for which
sub-simplices contribute at each step.

**Rust-engine application**: post-merge, Cup as runtime op in
`cochain.rs`.  When `mb-mc-sweep` family extends to multi-step
chains (e.g. m_t/m_e via three steps), runtime cup gives the
*cocycle witness*, not just the value.

## 16. `Cohomology/HodgeInvolution.lean` — ⋆⋆ = id

**What's there**: Decide-checked verification that `⋆ ∘ ⋆ : Cᵏ → Cᵏ`
is the identity, at multiple concrete cochains on Δ⁴ (zero, vertex
indicator, edge indicator, all-true).  Reason: `complement(complement
σ) = σ` set-theoretically, so the composed cochain action returns
to the original.  In ℤ/2 the usual sign factor `(−1)^(k(n−k))`
collapses, so ⋆ is a clean involution.

**Physics intuition**: ⋆⋆ = id means **gauge ↔ gravity dual readout
is reversible without information loss**.  Going from phase-reading
of G to modulus-reading and back gives back the same Gram entry.
This is why the gauge sector and gravity sector carry the **same
information content** despite being structurally different — they're
two faces of the same Hodge involution, not independent fields.

For DRLT specifically:
- (gauge readout) ⋆⋆ → (gauge readout) — gauge sector is closed
  under Hodge double-dual.
- (gravity readout) = ⋆(gauge), but ⋆⋆ takes you back.  So
  "graviton detection" is fundamentally a translation problem,
  not a physical search problem.
- The quaternary symmetry ⋆ at d=5 means H¹ ↔ H⁴, H² ↔ H³, H⁰ ↔ H⁵
  — six "phase channels" reduce to three independent dual pairs.

**Computation lever**: When two physics observables look
"unrelated" but live at Hodge-dual cohomology degrees (k and
d−k), they actually carry the *same* information — one is the
⋆-dual of the other.  Use this to halve apparent independent
content.  E.g. `1/α_em` (lives in some H¹-flavor combination) and
`M_Pl/v_H` (lives in H⁴-flavor) are Hodge-dual; their joint
information count is one, not two.

**Rust-engine application**: post-merge, the binary
`hodge-pair-audit` proposed earlier (cf. note #4) gains its
correctness check from this file: every gauge–gravity pair must
satisfy `⋆⋆(gauge_observable) = gauge_observable` at runtime,
which the audit can verify.

## 17. `Cohomology/BettiKernel.lean` — kernel enumeration

**What's there**: Generic Bool-cochain enumeration mechanism for
computing Betti numbers via brute-force kernel counts.  Encodes
i-th cochain as binary expansion of `i ∈ [0, 2^(binom n k))`,
filters those with δσ = 0.  Verified for Δ⁴: |ker δ₀| = 1,
|ker δ₁| = 2 (gives reduced b̃₀ = b̃₁ = 0, confirming Δ⁴ is
contractible).

**Physics intuition**: Betti numbers are computable by **direct
finite enumeration** — no algebra required, just count Bool
functions whose δ-image is zero.  This is conceptually the same
as **counting valid quantum states** in a discrete Hilbert space:
kernel of an operator = states annihilated by the operator =
allowed observables.  In DRLT:
- ker δ₀ = "constant cochains" = states of total spatial uniformity
  ⇒ b₀ counts disconnected universes (= 1 for our connected
  cosmos).
- ker δ₁ = closed loops without sources ⇒ b₁ counts independent
  cycles = topologically distinct flux configurations.
- For K_{3,2}^{(c=2)}: |ker δ₀| = 2 (two parities), |im δ₀| = 16,
  giving b₁ = 8.

**Computation lever**: Brute-force enumeration is **always
available** as a sanity check.  When proposing a new atomic
identity claiming "X = b_k of some sub-graph", the kernel-
enumeration check is decide-checkable in Lean and provides a
ground-truth witness — no Mathlib dependency, no algebra.

**Rust-engine application**: post-merge, `cochain.rs` should
expose `ker_size_delta(n, k) -> u64` so any new binary can
verify Betti claims at runtime by direct enumeration.  Cost is
~`2^binom(n,k)` for each level; cheap up to k≈3 on Δ⁴.

## 18. `Cohomology/Bipartite32.lean` — K_{3,2}^{(c=2)} cochain construct

**What's there**: Direct cochain construction for the bipartite
multigraph (NOT the Δ⁴-simplex framework).  Edge encoding:
- e ∈ Fin 12, decomposed as `(e/2)/2 ∈ {0,1,2}` (S-idx), `(e/2)%2
  ∈ {0,1}` (T-idx), `e%2` (multiplicity copy).
- Vertex cochain `CochV = Fin 5 → Bool`, edge cochain
  `CochE = Fin 12 → Bool`.
- δ₀ via `(δσ)(e) = σ(src e) XOR σ(tgt e)` — exactly the
  graph-Laplacian XOR.

**Physics intuition**: This file makes **the bipartite structure
explicit at the cochain level**, not via the abstract Δ⁴
machinery.  Concretely:
- Edge 0 connects S-vertex 0 to T-vertex 3 (verified).
- Edge 11 connects S-vertex 2 to T-vertex 4 (verified).
- Every edge is exactly an (S, T) pair × multiplicity ∈ {0, 1}.

Key insight: the **two multiplicity copies of each S-T spoke**
(c=2) are ENCODED as the LSB of e.  So at the cochain level,
chirality is a free Boolean degree of freedom on each spoke —
"this signal goes via copy A" vs "via copy B".  This is the
discrete-lattice manifestation of *particle / antiparticle*
or *left / right chirality*.

**Computation lever**: When proposing a new identity for K_{3,2}^{(c=2)},
the dual structure (S, T) × multiplicity gives **three independent
coordinate axes** for any computation: which S, which T, which
chirality copy.  Three axes × 12 edges = 36 = 4! degrees of
freedom in cochain space (which equals binom(12, 1) for k=1
sub-graph cochains).

**Rust-engine application**: post-merge, `crates/hypervisor/`
already has `chiral_k32.rs`; the math-branch's `Bip32.delta0` and
endpoint mappings should be ported as `bip32_delta0(σ_v) -> σ_e`
to provide explicit graph-level coboundary at runtime.  Useful
for verifying any binary's claim that "this Z atomic factor comes
from K_{3,2}^{(c=2)} cycle counting".

## 19. `Cohomology/K5.lean` — single K_5 (1-skeleton of Δ⁴)

**What's there**: K_5 = complete graph on 5 vertices.  |V| = 5,
|E| = C(5, 2) = 10, b₀ = 1, **b₁ = 10 − 5 + 1 = 6**.  Differs
from Δ⁴ because Δ⁴ has 2-cells (triangles) that kill 1-cycles
(b₁(Δ⁴) = 0), while K_5 has no 2-cells so 1-cycles survive.

**Physics intuition**: K_5's b₁ = 6 is **exactly the numerator of
α_GUT** (FractalAlphaGUT.lean).  So:

   α_GUT_numerator (= 6) = b₁(K_5) = independent loops in Δ⁴'s
                                     1-skeleton
   α_GUT_denominator (= 25) = numV(K_25) = next fractal level

This makes α_GUT a **ratio of two consecutive fractal levels'
cohomology cardinalities**.  And b₁(K_5) = 6 atomically equals
NS·NT (= 3·2) — i.e., K_5's loops match the bipartite-spoke count
of K_{3,2}^{(c=1)}.

K_5 is the "**unchiraled control**": removing chirality (c→1) and
the bipartite structure (S/T → mixed) reduces the strong sector
from 1/α_3 = 8 (K_{3,2}^{(c=2)}) to 6 (K_5).  The DIFFERENCE,
8 − 6 = 2 = NT, is exactly the chirality contribution.

**Computation lever**: Compare any K_{NS,NT}^{(c)} computation to
its K_d (complete) analog.  The DIFFERENCE = chirality + bipartite
contribution = "what c=2 + the (S, T) split adds beyond mere
graph connectivity".  This decomposition appears EVERYWHERE in
DRLT formulas.

**Rust-engine application**: post-merge, expose b₁(K_d) and
b₁(K_{n,m}^{(c)}) side-by-side in the proposed
`topology-uniqueness` binary.  Their difference at each (n, m, c)
is itself an atomic invariant: "chirality bonus over plain
connectivity".

## 20. `Cohomology/Fractal25.lean` — fractal level 2, K_{25}

**What's there**: 5 × 5 = 25 leaf vertices via "each vertex of Δ⁴
becomes a 4-simplex" recursion.  Two-level depth matches c = 2
(the lattice cycle multiplicity).  K_{25} cohomology:
- |V| = 25 = d²
- |E| = C(25, 2) = 300 = c · NS · NT · d² atomically
- b₀ = 1, **b₁ = 276**
- Direct enumeration infeasible (2²⁵ cochains); use Euler formula.

Leaf vertices encoded as pairs (i, j) ∈ Fin 5 × Fin 5 → Fin 25
via `5i + j`.

**Physics intuition**: This formalizes **why c = 2** — it's the
fractal depth.  Going one level deeper would give c = 3 (K_{125}),
but the diamond-crystal observation (paper 1) caps lattice cycle
at c = 2 because beyond two levels the Gram-rank-5 compression
collapses everything back.

The factorization `|E| = c · NS · NT · d²` is striking: the K_{25}
edge count contains *all four* atomic primitives explicitly.  Read
backwards: every edge of K_{25} is labeled by (multiplicity copy,
S-vertex, T-vertex, channel pair).  This is **the lattice's
information-encoding capacity at fractal level 2** — every bit of
DRLT physics-content sits on one of these 300 edges.

**Computation lever**: When an atomic count factors as
`c · NS · NT · d^k` for some k, it's a level-(k+1) fractal edge
count.  E.g.:
- k=0: c·NS·NT = 12 = K_{3,2}^{(c=2)} edges (level 1)
- k=2: c·NS·NT·d² = 300 = K_{25} edges (level 2)
- k=4: c·NS·NT·d⁴ = 7500 = K_{125} edges (level 3, hypothetical)

This gives a **structural ladder** for proposing new physics
identities at each fractal scale.

**Rust-engine application**: post-merge, the `scale-ladder-classify`
binary already lists 9 scales (sub-atomic to gravity); add a
"fractal level L" column showing each observable's lattice depth.
For K_{25} (level 2), candidates: dim H¹ = 276 may show up in
multi-electron atom shell-filling, hadron-jet multiplicity, or
nuclear collective modes.

## 21. `Cohomology/Audit.lean` — what's closed vs partial

**What's there**: Meta-level audit of the Cohomology 213 marathon.
Catalogs:
- **Closed universal**: XOR group structure (∀ σ), Bool identities,
  `CochAbove.pointwise` (∀ σ τ : Empty → Bool, vacuously since
  Empty is uninhabited).
- **Partial**: δ²=0, ⋆⋆=id, Leibniz, Cup unit/assoc — concrete-
  cochain checks only.  Universal versions require Fintype on
  `Cochain n k` (not in Lean core).
- **Honest negative**: `cup_not_pointwise_comm` (graded-comm only
  on H*), `b_k_graph_trivial` (H^k(K_{3,2}^{(c=2)}) = 0 ∀ k ≥ 2
  since graph is 1-dimensional).

Plus two "discoveries":
- **H^k = 0 for k ≥ 2 on graph** ⇒ cup product H¹ × H¹ → H² is the
  ZERO map.  The α_em "missing 6th term" CANNOT be a graph-cohom
  cup invariant.
- **AlphaEM bridge double-derivation** of b₁ = 8.

**Physics intuition** (the big one): "the missing 6th term in the
α_em formula can't be a graph cup invariant" is a **negative
falsifier** — telling us where NOT to search.  When proposing
new corrections to 1/α_em (or any other Class C+A observable),
we now know cup-product corrections at the graph level are
forbidden.  Any new term must come from:
- a Hodge-dual operation (Class E mirror), or
- a higher fractal level (K_{25} or beyond), or
- a chain (Class D) involving non-graph cochains.

**Computation lever**: The audit lists what's *deferred* (Fintype
+ DecidablePred for Cochain n k).  When proposing universal
identities, switch to concrete-cochain decide-checking — that's
the format already accepted in the marathon.

**Rust-engine application**: post-merge, the audit's "honest
negative" entries should be added to `gaps-and-todos.md` as
**known-impossible-targets** so future searches don't waste
cycles.  E.g.: "do NOT search for Class A corrections to
m_τ/m_μ at H² level — graph cohomology vanishes there."

## 22. `Cohomology/DiamondAudit.lean` — internal consistency check

**What's there**: A single 0-axiom theorem `diamond_audit_unified_atomic`
asserting that **every coefficient across every DRLT prediction
module factors through the same four atomic primitives**:

```
NS = 3, NT = 2, d = 5, c = 2 (= AlphaEMPrefactors.c_lat)
NS + NT = 5, NS · NT = 6, c · NS · NT = 12
NS² − 1 = 8, 12 · NT · 5 / 4 = 30, d² = 25
N_eff(α_3) = 1, N_eff(α_2) = 2
b_1(K_{3,2}^{(c=2)}) = 8
```

Plus `diamond_audit_falsifier_coupling`: any wrong prediction
→ atomic mismatch → entire framework collapses.

**Physics intuition**: This is the **structural rigidity proof**
of DRLT.  There is no "knob to turn" — every coefficient in every
formula is forced to be one of these atomic combinations.  If a
new measurement disagreed with DRLT by, say, 2%, you cannot fix it
by tweaking some parameter; the only way to repair the framework
is to admit that NS, NT, d, or c is wrong, which propagates to
EVERY OTHER PREDICTION simultaneously.

This is the "0-parameter theory" claim made completely concrete:
the parameter count is literally zero, and any deviation falsifies
the WHOLE framework, not just one observable.

**Computation lever**: When adding a new observable to scale-ladder-
classify, run a "diamond audit consistency check": does its
proposed atomic form use the SAME primitives the rest of the table
uses?  If it introduces a new fitted constant (something not in
{3, 2, 5, 6, 8, 12, 24, 25, 30, ...}-atomic-derivatives), it's
*outside the framework*.

**Rust-engine application**: post-merge, add `diamond-audit` Rust
binary that takes the existing `scale-ladder-classify` 36-row table
and verifies for each observable that its atomic form decomposes
into {NS, NT, d, c} polynomials.  Anything that doesn't audit fails
the rigidity test.

## 23. `Cohomology/TrivialCases.lean` — Δⁿ⁻¹ smoke for n=2..5

**What's there**: Verifies cochain complex `(Cᵏ, δ)` is well-formed
for n = 2, 3, 4, 5.  Each row checks face counts + δ preserves
zero cochain.  Records the binomial table:

```
n = 2: (1, 2, 1)
n = 3: (1, 3, 3, 1)
n = 4: (1, 4, 6, 4, 1)
n = 5: (1, 5, 10, 10, 5, 1)   ← the atomic Δ⁴
```

**Physics intuition**: Pascal's triangle is the **vertex-count
ladder for fractal Δⁿ⁻¹** at each (n, k).  At n=5 (atomic) the
sequence (1, 5, 10, 10, 5, 1) is **palindromic**, which is exactly
the **Hodge ⋆ self-duality** at d=5.  No other small n gives the
"middle is doubled" structure (10, 10) — Δ⁴ is uniquely positioned
for ⋆-self-duality at the level-2 (k=2) ↔ level-3 (k=3) split.

This palindrome-at-middle is **why d=5 is special for chirality**:
the Hodge ⋆ exchanges H² ↔ H³ within the same dimension, giving
a **non-trivial involution on the same cohomology degree** —
which is precisely the kind of structure that supports
non-orientable / chiral physics.

**Computation lever**: When extending to non-Δ⁴ situations
(higher fractal levels, other graph structures), check the
binomial palindrome.  If it's symmetric, you have ⋆-self-duality
opportunities.  If not, gauge-gravity sectors will be structurally
asymmetric in a way that breaks the clean dual-readout pairing.

**Rust-engine application**: post-merge, the proposed
`hodge-pair-audit` binary (note #4) should print these binomial
ladders for each fractal level and highlight the palindromic
symmetry.

## 24. `Cohomology/SimplexBasis.lean` — k-subset colex enumeration

**What's there**: The bijection `Fin (binom n k) → k-subset of
{0..n-1}` via colex order, defined recursively using Pascal's
identity:

```
binom(n+1, k) = binom(n, k) + binom(n, k-1)
↑  k-subsets of {0..n-1}     ↑  (k-1)-subsets of {0..n-1} ∪ {n}
```

Smoke verifies kSubset 5 1 i = [i] (singletons), kSubset 5 2 i
gives [0,1], [0,2], [1,2], ..., [3,4] (last).

**Physics intuition**: Colex order is **the natural sorting of
particle states by "highest excited mode first"**.  At n = 5
(d = 5 atomic), the colex enumeration of k-subsets gives:
- k=1: vertices 0..4 in order — atomic single-particle states
- k=2: pairs sorted by largest-element-first — 2-particle modes
- k=3: triples — 3-vertex sub-simplices
- k=4: 4-tuples = co-vertices (Hodge dual of single vertices)

The Pascal recurrence `binom(n+1, k) = binom(n, k) + binom(n, k-1)`
has a physical reading: "to form a k-subset of n+1 elements, either
EXCLUDE element n (giving binom(n, k) options) or INCLUDE it
(giving binom(n, k-1) options for the rest)".  This is **the
discrete-lattice version of "particle-in/particle-out
decomposition"** — every observable on a (n+1)-vertex system
decomposes into "n-vertex piece + new-vertex piece".

**Computation lever**: When generalizing a Δ⁴ identity to higher
fractal levels (Δ⁹, etc.), use the Pascal-decomposition recurrence
explicitly.  Each induction step adds one more vertex and the
new contribution factors into "old" + "new vertex pair".

**Rust-engine application**: post-merge, port `kSubset` to
`crates/hypervisor/src/cochain.rs::k_subset(n, k, i) -> Vec<u32>`.
Used wherever a binary needs to iterate over sub-simplices in
canonical order (e.g. `simplex-inventory`, future `cohomology-bits`
binary).

## 25. `Linalg213/Rank.lean` — linear combination over Int

**What's there**: ℕ-valued Vec can't cancel (no negatives), so
coefficient vectors lift to Int.  Defines `IntCoeffs N`, `linComb`
(integer sum at each component), and `linComb_isZero` (Bool check).
Smoke: `1·e_0 + (-1)·e_1` gives (1, -1, 0, 0, 0) — nonzero,
correctly.  This is the L2 phase of Linalg213 (linear combination
+ dependence), foundation for the rank-5 compression target.

**Physics intuition**: ℕ → Int lift is **the bridge from
"counting" to "balanced accounting"**.  ℕ alone can describe
existence (e₀ exists, e₁ exists) but not cancellation (e₀ minus
e₁).  Cancellation is required for *interference / destructive
combination / antiparticle / charge-balance*.  Linalg213 hierarchy:

```
ℕ (Vec)                  → existence-only (counts)
ℤ (IntCoeffs)            → cancellation (charges, currents)
ℤ/2 (Cochain)            → parity (chirality, sign-counting)
ℚ (Q-pair, in rust-engine) → ratios (couplings, mass-ratios)
```

Each level adds an algebraic capability.  Physics observables
land at the level matching their character: bare integers in ℕ,
charge currents in ℤ, parity / chirality in ℤ/2, dimensionless
ratios in ℚ.

**Computation lever**: When proposing an identity, identify which
level it lives at.  An identity using subtraction lives at ℤ or
higher.  An identity counting parities is ℤ/2.  Mixing levels is
fine but requires a *bridge theorem* (e.g. Linalg/Bridge ↔
Cochain via chiralDim).

**Rust-engine application**: post-merge, the rust-engine's
`crates/kernel/src/term.rs` already has Term values in ℕ; the
companion `Int`-coefficient module would be the next addition,
unlocking signed-charge calculations.

## 26. `Linalg213/Span.lean` — span via integer combinations

**What's there** (from imports + Capstone references): Phase L3
defines the span of a vector collection as the set of integer
linear combinations.  Used by Chiral (L4) and Capstone (L6).
Provides the "reachable subspace" predicate that powers the rank
machinery — span(v_1, ..., v_N) is the algebraic image of those
N vectors under all integer-coefficient combinations.

**Physics intuition**: Span = **algebraic closure of available
particle states under physical operations**.  In DRLT, "physical
operations" are integer combinations (countable additions and
cancellations of relations).  The set of *reachable* states from
a given starting set is its span — what particle physics calls
the "representation generated by" a fundamental multiplet.

The rank-5 target (paper 1) reads as:
**span of any N vectors in Vec 5 has dimension ≤ 5**.
No matter how many starting particles, the orbit under physical
combinations is bounded by atomic dimension d=5.  This is the
algebraic origin of *finite generation* in DRLT — every gauge
group, every particle multiplet, every coupling structure
descends from a rank-≤5 vector image.

**Computation lever**: Span containment is a *finite check* —
either v is in span(v_1, ..., v_N) (witness: integer coefficients)
or it isn't (witness: orthogonal complement nonzero).  This makes
"is observable X reachable from primitives Y" a decidable question.

**Rust-engine application**: post-merge, after `Int`-coefficients
are added (#25 application), wire span-membership as a verifier
for atomic decompositions: given an integer X, automatically
check whether X ∈ span({NS, NT, d, c, ζ(2)-bracket}) under
{+, ·} — if yes, atomic; if no, falsifies "X is atomic".

## 27. `Math/Analysis213.lean` — bridge to constructive analysis

**What's there** (163 lines, surveyed not deeply read): Bishop-
style constructive analysis layer.  CLAUDE.md notes this is
"math track, NOT on the critical path for physics formalization"
since the lattice is finite-discrete.  Per CLAUDE.md: "÷, ∫, π, e,
ζ(2) transcendentals — bounded rational interval suffices."

**Physics intuition**: Analysis213 is the **principled home for
transcendental brackets** (π, ζ(2), e) when the rust-engine needs
them as bounded rationals.  Currently rust-engine handles ζ(2) via
`Basel.upper`/`s_partial`; π and e are not yet bracketed and are
effectively external inputs (gaps-and-todos.md §4).  Analysis213,
once mature, will provide Wallis-style π brackets and Taylor-series
e brackets at the same ℕ-pair level.

**Computation lever**: Whenever a physics binary uses π or e as
display-only rationals, that's a TODO marker for a future
Analysis213 import.  Conversely, when proposing a new identity
involving a transcendental, see if it can be written as a *bracket*
identity (lower ≤ X ≤ upper) — that's the discrete-lattice form.

**Rust-engine application**: post-merge, `crates/app/src/wallis.rs`
+ `taylor_e.rs` would give bracket-based π / e replacements,
removing the only remaining external-input dependencies in the
runtime.  This closes gaps-and-todos.md §4 fully.

## 28. `Linalg213/Vector.lean` — Phase L1, the very bottom

**What's there**: `Vec d := Fin d → ℕ` is the fundamental DRLT
vector type.  The file note is explicit: **"strict 213-internal
principle: we do NOT borrow classical linear algebra"** — no ℝ,
no ℂ, no Mathlib.  All of linear algebra builds from Raw +
atomicity.

Choice of ℕ (not Bool): Bool gives degenerate GF(2) where ⟨v,v⟩
can be 0 for v ≠ 0; ℕ gives the simplest non-degenerate
inner-product cone with `⟨v, w⟩ = Σ vᵢ·wᵢ ≥ 0`.  Defines
`Vec.zero`, `Vec.basis`, `Vec.add`, `Vec.smul`.

**Physics intuition** (the foundational one): DRLT does NOT start
from "Hilbert space ℂⁿ then reduce to atoms".  It starts from
**ℕ-valued vectors** and *derives* ℂ⁵ as a consequence (Frobenius
theorem + atomicity → ℂ; atomicity → d=5).  The CLAUDE.md axiom
"things exist with pairwise relations" is **literally** the Vec
type: a thing is an element of Fin d (an index), and a relation
is a non-negative count between two indices (a value of the inner
product).

ℕ is the forced foundational choice because:
- Bool is too coarse (GF(2) loses inner-product non-degeneracy).
- ℤ allows cancellation but cancellation is a derived operation
  (signed currents via IntCoeffs at L2).
- ℝ, ℂ are output, not input — they fall out of finite-dimensional
  cone closure once you have non-degenerate ℕ inner product.

**Computation lever**: When approaching a "what's the foundational
representation of X" question, the answer should always start from
ℕ-vectors and lift only as needed.  Anything starting from ℝ/ℂ
is borrowing more structure than DRLT axioms provide.

**Rust-engine application**: post-merge, `crates/firmware` already
mirrors this principle — every numeric value is BigUint (≥ 0).
Vector lifts can be added to `firmware/src/vec.rs` as
`Vec(Vec<BigUint>)` with the same operations; this would give the
runtime the same hierarchy (ℕ → ℤ → ℤ/2 → ℚ) the math branch has
in Lean.

## 29. `Cohomology/AlphaEMBridge.lean` — formal note (was partial)

**What's there**: The 0-axiom bridge `b1_two_derivations_agree`:

  `b_1 = Bip32.kerSizeDelta0 · 4`
  `b_1 = NS · NS − 1`
  `Bip32.kerSizeDelta0 = 2`

i.e., scalar Euler (E − V + 1 = 12 − 5 + 1 = 8) and chain-level
rank-nullity (16 · 256 = 4096, 256 = 2⁸) yield the same b_1.
And `alpha_em_cohomology_bridge` lifts this to "every term of
1/α_em(IR) has BOTH a scalar simplicial origin AND a chain-
level cohomology origin, and they match".

**Physics intuition**: Two completely independent derivations of
the same physical observable, agreeing as a Lean theorem.  This
is the **gold standard for falsifiability**: if either derivation
fails, the framework breaks.  In particular:
- Scalar Euler: pure graph counting (vertices + edges + Euler).
- Chain-level: brute-force enumeration over 2³² cochains.
The fact that these MUST give the same answer = redundant safety
net.  Any new physics quantity should aspire to similar
double-derivation: same value via two independent algebraic
machineries.

**Computation lever**: When proposing a new closed form, ask
"can this be re-derived a second way?"  If yes, the redundant
agreement is itself an atomic identity worth formalizing.  If no,
the proposal is single-route and harder to defend.

**Rust-engine application**: post-merge, the future binary
`alpha-em-double-derive` would compute 1/α_em via both the scalar
graph route and the cochain enumeration route, and assert
equality at runtime.  This makes the AlphaEMBridge theorem a
*runtime-checkable* statement, not just a proof obligation.

## 30. `Cohomology/CupLeibniz.lean` — δ(α ⌣ β) = δα ⌣ β ⊕ α ⌣ δβ

**What's there** (inferred from import + Capstone reference):
The Leibniz rule for cup product over ℤ/2:

  `δ(α ⌣ β) = (δα ⌣ β) ⊕ (α ⌣ δβ)`

Verified at concrete cochain pairs on Δ⁴.  In ℤ/2 the usual sign
factor (−1)^|α| collapses to +1, so the rule simplifies to XOR
of the two boundary terms.

**Physics intuition**: Leibniz is **the product rule for
cohomology**, the discrete analog of `d(fg) = (df)g + f(dg)`.
Physically:
- α = field A, β = field B → α⌣β = composite observable
- δ measures source/sink strength
- Leibniz: source of (composite) = (source of A) ⊗ B + A ⊗ (source of B)

This is the discrete-lattice version of **Wess-Zumino consistency
conditions** in gauge theory: when you compose two gauge fields,
the BRST-cohomology relation is exactly Leibniz.  In DRLT,
Wess-Zumino conditions become decide-checkable identities — no
continuum infinite-dimensional cohomology required.

**Computation lever**: When chaining Class D observables, the
δ-action factors through Leibniz.  So if you want to know "what's
conserved when I compose A with B", compute δA, δB separately
and XOR-combine via Leibniz — gives the conservation law of the
composite without re-doing the calculation from scratch.

**Rust-engine application**: post-merge, `cochain.rs` would expose
`leibniz_check(α, β) -> bool` returning true if the Leibniz
identity holds at runtime for given cochain pair.  Used by any
binary that builds composite observables.

## 31. `Cohomology/HodgeDelta.lean` — codifferential δ* = ⋆δ⋆

**What's there**: Codifferential `codiff = ⋆ ∘ δ ∘ ⋆ : Cᵏ → Cᵏ⁻¹`
lowers degree (the dual of δ which raises).  Combined with δ,
builds the **Laplacian** `Δ = δ ∘ codiff + codiff ∘ δ`.  Harmonic
cochains satisfy Δσ = 0.  Concrete definitions at (n=5, k=2) and
(n=5, k=3) avoid Nat-subtraction elaboration issues.

**Physics intuition**: This is **Hodge theory at the discrete-
lattice level**.  In continuum:
- δ = exterior derivative (raises degree, finds sources)
- δ* = codifferential (lowers degree, finds sinks)
- Δ = δδ* + δ*δ = Laplace-Beltrami
- Harmonic forms = ker Δ = bridge between de Rham and Hodge

In DRLT:
- Harmonic cochains = stable observables (no source, no sink)
- Number of harmonics = Betti number (each H_k class has unique
  harmonic representative — Hodge theorem)
- This is **why Betti counts are physically meaningful**: each
  one is a degree-of-freedom in the harmonic space, i.e., a
  conserved propagation channel.

For DRLT specifically: the c=2 chirality multiplicity means each
spoke supports TWO independent harmonic modes (left/right) — that's
the structural reason b_1 = 8 = 2·4 (two chiralities × four
independent cycle classes).

**Computation lever**: When proposing a "stable physical state",
ask if it's a harmonic cochain (Δσ = 0).  If yes, it's a Betti
representative — a real physical degree of freedom.  If not,
it's a redundant representation (cohomologous to zero or to
another harmonic).

**Rust-engine application**: post-merge, `cochain.rs` exposes
`laplacian(σ) -> Cochain` and `is_harmonic(σ) -> bool`.  Used to
validate that proposed atomic decompositions correspond to actual
harmonic representatives, not redundant copies.

## 32. `Cohomology/Capstone.lean` — full marathon bundle (deep)

**What's there**: The single 0-axiom theorem
`cohomology_213_marathon` bundling representatives from each phase:

- **CA**: δ²=0 sample on Δ⁴
- **CB**: ⋆⋆=id sample
- **CC**: Δ⁴ contractibility (kerSize 5 0 = 1, kerSize 5 1 = 2)
- **CD**: Leibniz at concrete cochain triple + cup unit
- **CE**: K_{3,2}^{(c=2)} kernel size 2, b_1 = 8 = NS²−1

All decide-checkable, no Mathlib, no axioms.

**Physics intuition**: The capstone is a **single Lean theorem
that 213-internally instantiates every piece of standard de Rham
cohomology** — boundary operator, Hodge star, Betti numbers,
cup product, ring structure — at the *atomic*, *decidable*,
*ℤ/2-coefficient* level.  This is the **proof that DRLT does not
need Mathlib's cohomology infrastructure** — the entire apparatus
is reproducible from atomicity + Bool.

For physics: every de Rham-cohomology argument used in physics
(charge quantization, anomaly cancellation, instanton counting,
characteristic classes) has a 213-internal counterpart at this
Capstone level.  Translation in either direction is mechanical.

**Computation lever**: When you see a physics argument cite "by
de Rham cohomology", check whether the corresponding Capstone-
level statement is decide-checkable — if yes, the physics argument
becomes a 0-axiom Lean theorem.  This is how to make heuristic
"topological reasoning" rigorously formal in DRLT.

**Rust-engine application**: post-merge, `cohomology-bits` binary
(proposed earlier) becomes a one-stop demo of the entire Capstone
content at runtime — δ, ⋆⋆, Betti, cup, all in one place,
matching the Lean theorem layer-by-layer.

## 33. `Math/Analysis.lean` — umbrella for Research/Real213 marathon

**What's there**: Mega-import file aggregating ~55+
`Research.Real213*` modules — a full Bishop-style constructive
analysis marathon over Dedekind-cut-based Real213.  Topics:
bisection algo, diff quotient, Riemann integration, valid cuts,
IVT containment, dyadic brackets, smoothness predicate,
differentiable instances, derivative depth, flux cohomology,
mean-value-theorem, FTC, phase-A through phase-AN capstones.

**Physics intuition**: This is the **constructive analysis
counterpart** to the Cohomology 213 marathon — both are
self-contained 213-internal frameworks, no Mathlib.  Cohomology
covers discrete topology (Δⁿ⁻¹, K_{n,m}^{(c)}, cup, ⋆); Analysis
covers continuous calculus (cuts, derivatives, integrals, FTC).

CLAUDE.md flags Analysis213 as "math track, NOT on the critical
path for physics formalization" since the lattice is finite-
discrete.  The relevant slice for physics is **bracket**
machinery (Real213ValidCut, Real213DyadicBracket): bounded
rational interval arithmetic that the rust-engine already uses
for ζ(2) via `Basel.upper`/`s_partial`.

**Computation lever**: When a physics calculation needs
"continuous calculus", check whether the bracket machinery suffices
first.  Most DRLT formulas only need bounded interval evaluation,
not full Bishop-style constructive analysis.  Reach for the
deeper layers only if a *derivative* or *integral* of a
non-rational function is genuinely needed.

**Rust-engine application**: post-merge, `crates/app/src/basel.rs`'s
bracket types could be generalized to a `BracketRat` newtype
matching `Real213ValidCut`'s structure, giving runtime
constructive-real arithmetic where needed.  Most binaries don't
need this; useful only for new precision claims that require
sub-bracket evaluation.

(Mining Real213.* in detail would be a separate, much longer
campaign.  Flagged for future sessions.)

## 34. `Math/{Cauchy, Continuity, Foundation}.lean` — Real213 umbrellas

**What's there**: Three thin re-export umbrellas pulling specific
slices of the Research/Real213 marathon together for use as
clean public API:

- `Foundation.lean` (Phase A): Real213 type, Setoid equivalence,
  constant embedding, order (le/lt antisymm via Bool case-analysis),
  sign predicate.  All ≤ {propext} — type-level foundation of
  213-native ℝ.
- `Cauchy.lean`: CauchyCutSeq sequences + completeness.  In 213,
  Bishop's completeness theorem is **trivial direct construction**
  — no metric-space theory needed.
- `Continuity.lean`: locally-determined cut functions
  (`isLocallyDetermined`), categorical closure under composition
  (`composeLDD`).  213 form of Bishop locatedness.

**Physics intuition**: Three pillars of "what's needed to do real
analysis on Real213":
- Foundation = the *type* exists, has order + sign.  This is the
  bare minimum for "magnitude-comparable observables".
- Cauchy = limits exist as constructive direct objects, not
  ε-δ over a completed metric space.  In 213, every "limit"
  is a witnessed Cauchy sequence with explicit modulus.
- Continuity = "outputs determined by local input" — exactly the
  *physical* notion of locality that Bishop captures.

For DRLT physics: most observables need only **Foundation + Bracket
arithmetic**, not full Cauchy.  The few that need limits (e.g. ζ(2)
via Basel partial sums) use bracket-based limits where lower/upper
sequences both stabilize — which is exactly the Cauchy completeness
case.  Continuity isn't reached for in current physics binaries
because all observables are explicitly *defined* on a finite cochain
basis (no need for "function-from-Real-to-Real" objects).

**Computation lever**: When you find yourself wanting "limit X" or
"continuous function f", check if the bracket form suffices — it
almost always does in DRLT.  Reach for Cauchy/Continuity only if
you genuinely need the limit-structure, not just bounded
approximation.

**Rust-engine application**: post-merge, none of these directly
ports to the Rust runtime — bracket arithmetic in `basel.rs`
handles all current needs.  Future relevance: if a binary is
proposed that genuinely needs to *take a limit* (e.g. Wallis-style
π via convergent product), then Cauchy.lean's CauchyCutSeq is the
target Lean structure to mirror.
