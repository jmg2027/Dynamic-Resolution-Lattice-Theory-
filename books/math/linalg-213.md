# Linear Algebra 213

*An exposition in 213-internal vocabulary.*

The 213-native realisation of linear algebra over the canonical
K_{3,2}^{(c=2)} graph.  Subject of *Paper 1 Chiral Compression
Theorem*: arbitrary numbers of pairwise relations project into a
5-dimensional algebraic image, with the chiral split (NS, NT) =
(3, 2) emerging from the Gram-matrix rank constraint.

Companion volume to `analysis213.md`, `number-theory-213.md`,
`cohomology-213.md`.  Vocabulary: Raw, Gram matrix G_{ij},
Vec d, rank, span, chiral split, K_{3,2}^{(c=2)}.

All theorems referenced are 0-sorry, 0-Mathlib, 0-Classical,
≤ {propext, Quot.sound}, as verified in
`lean/E213/Math/Linalg213/`.

---

## Part I — Foundations

### Chapter 1.  Why linear algebra in 213

Standard linear algebra builds on a base field (ℝ, ℂ, ℚ, ...)
and a vector space defined over it.  Both are *external* — the
field structure is given, not derived.

In 213, both emerge from the Raw axiom:

  Raw → Lens → Gram pairing G_{ij} = ⟨ψ_i | ψ_j⟩
              → atomicity forces d = 5
              → rank-5 compression forces (NS, NT) = (3, 2)
              → ℂ⁵ as ambient algebraic image (NOT primitive)

Linear algebra in 213 is the study of how *pairwise relations*
between Raw entities project into a finite-rank algebraic
structure, with the rank itself (d = 5) as a *theorem*.

### Chapter 2.  Vec d and the inner product

The 213-internal vector space is `Vec d := Fin d → ℕ`
(`Math/Linalg213/Vector.lean`):

  v : Vec d  means  v : Fin d → ℕ

Vectors carry ℕ-valued coordinates.  The inner product is
componentwise sum:

  ⟨v | w⟩ := Σ_{k = 0}^{d-1} v(k) · w(k)  ∈ ℕ

This stays entirely within ℕ — no Real-valued infrastructure
needed.  The Bishop-style constructive shadow of inner-product
geometry.

### Chapter 3.  Gram matrix G_{ij}

For N vectors v₁, …, v_N in Vec d, the Gram matrix is

  G_{ij} := ⟨v_i | v_j⟩  ∈ ℕ

Hermitian (symmetric in the ℕ-valued case): G_{ij} = G_{ji} by
commutativity of multiplication.

In Paper 1's "things exist with pairwise relations" framing, G is
the *only* observable — it is the data of mutual relations in
matrix form.

See `Linalg213/Gram.lean` for the foundation lemmas.

---

## Part II — Rank-5 compression

### Chapter 4.  rank(G) and span

The rank of the Gram matrix is the dimension of the span of
{v₁, …, v_N} in Vec d:

  rank(G) := dim span(v_1, ..., v_N)  ∈ ℕ

In `Linalg213/Span.lean` and `Linalg213/Rank.lean`, span is
defined constructively as the closure under ℕ-linear
combinations, and rank as the size of the maximal independent
subset.

### Chapter 5.  Paper 1 Chiral Compression — rank ≤ 5

The central theorem of Paper 1: **for any N ≥ 1 vectors in Vec 5,
rank(G) ≤ 5**.

This is the *rank-5 compression* — an arbitrary number of pairwise
relations project into a 5-dimensional algebraic image.  Combined
with `OS.Atomicity` (which forces d = 5 as the unique
non-degenerate dimension), this is the formal statement that **5
is the unique cardinality of the algebraic shadow of any pairwise-
relation system in 213**.

Concrete witness at low N: `Linalg213/Rank5Concrete.lean` checks
the rank bound by direct enumeration for small N.

The general N case (∀ N, rank ≤ 5) requires a 213-native rank
definition — this is the load-bearing infrastructure in Linalg213.

### Chapter 6.  The chiral split (NS, NT) = (3, 2)

Within the rank-5 image, the *chiral split* selects two distinct
subspaces:

  VecS  ≃  ℕ³   (3-dim S-projection, NS = 3)
  VecT  ≃  ℕ²   (2-dim T-projection, NT = 2)

with NS + NT = 5 = d.

The split is *forced* by `OS.PairForcing`: (p, q, n) = (2, 3, 5)
is the unique unique-atomic coprime pair plus its sum.  Any 5-
dimensional atomic split must be (3, 2) up to swap.

`Linalg213/Chiral.lean` provides:

  combine_proj_eq : ∀ v ∈ Vec 5, combine (proj_S v) (proj_T v) = v

— the round-trip between the chiral projections and the original
vector is the identity.  This is closed at ≤ {propext, Quot.sound}.

---

## Part III — Bridge to Cohomology

### Chapter 7.  Bridge to chiral cohomology

The chiral split at the linear-algebra level matches the chiral
bigrading at the cohomology level (companion volume
`cohomology-213.md`):

  dim VecS  =  chiralDim 1 0  =  NS  =  3
  dim VecT  =  chiralDim 0 1  =  NT  =  2

`Linalg213/Bridge.lean` provides `atomic_split_consistent`:
the linear-algebra split (NS, NT) and the cohomology bigrading
agree.

This is a *cross-marathon coherence theorem* — the two
independently developed structures (Linalg213 and
Cohomology213/Paper1Chiral) compute the same atomic numbers (3, 2).

### Chapter 8.  Bridge to physics K_{3,2}^{(c=2)} cohomology

The Linalg213 chiral split connects to physics through the
`PhotonKernel.b_1_eq_8` bridge:

  b_1(K_{3,2}^{(c=2)})  =  NS² − 1  =  8  =  1/α_3

i.e. the strong coupling constant 1/α_3 = 8 equals the cycle-space
dimension of the chiral graph.  The bridge is established in
`Linalg213/Bridge.lean` via `K32_c2_b1` from
`Math/Cohomology/TopologyCompare.lean`.

This realises the *atomic reading* of α_3 — not a free parameter
but a Betti number.

---

## Part IV — Capstone

### Chapter 9.  Paper 1 Chiral Compression Theorem

`Linalg213/Capstone.lean` bundles six independent results into
a single 0-axiom statement of Paper 1's main claims:

  (i)   Atomic forcing: NS = 3, NT = 2, d = NS + NT = 5
        (`OS.Atomicity`)
  (ii)  Linalg213 chiral split: combine_proj_eq for ∀ v ∈ Vec 5
  (iii) Cohomology 213 chiral bigrading:
        chiralDim (1, 0) + chiralDim (0, 1) = 5
  (iv)  Bridge: dim VecS = chiralDim (1, 0) = NS;
        dim VecT = ditto NT
  (v)   Physics K_{3,2}^{(c=2)} cohomology: b_1 = 8 = NS² − 1
  (vi)  Topology uniqueness: K_{3,2}^{(c=2)} is THE small-config
        bipartite multigraph giving b_1 = 8
        (`TopologyCompare.K32_c2_b1`)

Closed at ≤ {propext, Quot.sound}.  The capstone is the formal
statement that **"ℂ⁵ chiral atomic decomposition is forced and
unique"** — at six different complementary levels, all agreeing.

### Chapter 10.  ℂ⁵ as derived, not primitive

Standard physics treats ℂ⁵ (or ℝ³, ℂ², etc.) as a *given* vector
space.  In 213, ℂ⁵ is *derived*:

  Raw  →  Frobenius constraints
       →  ℂ as the unique field admitting Hermitian inner products
       →  Atomicity forces d = 5
       →  Chiral split forces (NS, NT) = (3, 2)
       →  ℂ⁵ with chiral structure as the algebraic ambient

No assumption of complex numbers in the axiom — they emerge as
the unique inner-product-compatible field given the atomicity
constraint.

---

## Part V — Open horizons

### Chapter 11.  General N rank theorem

`Rank5Concrete.lean` verifies rank ≤ 5 for small N by direct
enumeration.  The general statement (∀ N, rank(G) ≤ 5) requires
a 213-native rank theorem — this is the load-bearing infrastructure
goal of the Linalg213 marathon.

The technical wall: defining `rank` constructively without
appealing to set-theoretic linear algebra.  Approach: maximal-
independent-subset characterisation, structural induction on N.

### Chapter 12.  Toward Real213-valued vectors

Currently `Vec d := Fin d → ℕ` — vectors carry ℕ coordinates
only.  Extending to `Vec d := Fin d → Real213` (Bishop-style
constructive reals from `Research/Real213*.lean`) would give the
full inner-product-space machinery.

The bridge file `Real213Bridge.lean` (in Math/Cohomology/) provides
the connection layer.  General Linalg213-over-Real213 is conjectural
continuation work.

### Chapter 13.  Rank stratification of cohomology classes

The five-class A/B/C/D/E classification of physical observables
(see companion `cohomology-213.md`) is conjectured to align with
*rank stratification* of the Linalg213 / cohomology coupling.  Class
A = rank-1 propagator, Class C = full-rank lattice invariant, etc.

A proof of this alignment would close the cohomology classification
theorem at the linear-algebra level.

---

## Appendix A.  Lean theorem index

Key capstones (all ≤ {propext, Quot.sound}):

- `paper1_chiral_compression_capstone` — six-conjunct bundle of
  the Paper 1 theorem
- `combine_proj_eq` — Vec 5 chiral round-trip
- `atomic_split_consistent` — Linalg/Cohomology bridge
- `K32_c2_b1` — b_1(K_{3,2}^{(c=2)}) = 8

Source files at `lean/E213/Math/Linalg213/{Vector, Gram, Span,
Rank, Rank5Concrete, Chiral, Bridge, Capstone}.lean`.

## Appendix B.  Verification standard

Every theorem closed in Lean 4 at:

  ≤ {propext, Quot.sound}    (Lean kernel floor), OR
  STRICT 0-AXIOM             (basis decomps, finite enumerations)

No `sorry`, no Mathlib, no Classical, no native_decide.

`cd lean && lake build` passes.

## Author

Mingu Jeong (Independent Researcher).

Acknowledgments: Claude (Anthropic) provided formalization
assistance under direct supervision.
