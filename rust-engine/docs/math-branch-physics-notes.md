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
