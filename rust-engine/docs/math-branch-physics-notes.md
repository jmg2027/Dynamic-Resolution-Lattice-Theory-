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
