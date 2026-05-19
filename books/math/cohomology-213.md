# Cohomology 213

*An exposition in 213-internal vocabulary.*

The cohomological structure of K_{3,2}^{(c=2)} — the canonical
graph forced by Atomicity (d = 5, NS = 3, NT = 2, c = 2).  This
book covers the chain complex, Betti numbers, cup product, the
Alexander-Whitney cup, the Δ⁴ Leibniz coverage, Hodge involution,
the simplicial basis, and the universal-property capstones.

Companion volume to `analysis213.md` (calculus) and
`number-theory-213.md` (Pisano CRT + Universal Lens).  Vocabulary:
Raw, slash, Lens, Cochain, δ, Cup, AW (Alexander-Whitney), Hodge ⋆,
Bipartite32, K5.

All theorems referenced are 0-sorry, 0-Mathlib, 0-Classical,
STRICT ∅-AXIOM, as verified in `lean/E213/Lib/Math/Cohomology/`.

---

## Part I — The graph K_{3,2}^{(c=2)}

### Chapter 1.  Why K_{3,2}^{(c=2)} is forced

The Raw axiom (a, b, slash, slash_comm) plus `OS.Atomicity` —
the requirement that the simplex dimension d admits a unique
non-degenerate (p, q) split — selects:

  d = 5  (unique solution to the Bézout-shift atomicity equation)
  (NS, NT) = (3, 2)  (unique 5-vertex partition with `PairForcing`)
  c = 2  (forced by Euler b₁ = 8 on the resulting bipartite graph)

The graph is K_{NS, NT}^{(c)} — the complete bipartite graph on
3 + 2 vertices, with each S–T edge carrying multiplicity c = 2.
Total edges: NS · NT · c = 12.  This is the *only* canonical
non-degenerate K_{p,q}^{(c)} structure — see `WhyDimFive.lean`,
`TopologyCompare.lean`.

### Chapter 2.  Vertex / edge / face inventory

  Vertices V = {S₀, S₁, S₂, T₀, T₁}                   |V| = d = 5
  Edges    E = {(Sᵢ, Tⱼ) × c}                         |E| = 12
  Faces    F = chiral 2-simplices                     |F| = ...

The cochain complex C^k = (ℤ/2)^{|k-cells|}:

  C⁰ = (ℤ/2)⁵ = 32 cochains      (one per vertex)
  C¹ = (ℤ/2)¹² = 4096 cochains   (one per edge)
  C² = ...

See `Bipartite32.lean`, `Bipartite32Betti.lean`,
`BipartiteFilled.lean`.

### Chapter 3.  K5 and chiral structure

The 4-simplex K5 — complete graph on 5 vertices — is the
*ambient* simplicial structure into which K_{3,2}^{(c=2)} embeds
with the chiral split.  Number of edges: C(5, 2) = 10.  Number of
2-faces: C(5, 3) = 10.

Key identities (see `K5.lean`, `SimplexBasis.lean`):

  numV(K5) = 5 = d
  numE(K5) = 10 = NS · NT · (c+1) − 2  (alternative reading)
  b₁(K5) = (d−1)(d−2)/2 = 6  (1st Betti of single 4-simplex 1-skeleton)

The number 6 = b₁(K5) appears as the numerator of α_GUT = 6 / (25π²)
— hence the cohomological reading of α_GUT in `FractalAlphaGUT.lean`.

---

## Part II — Cochain complex

### Chapter 4.  Cochains and the coboundary δ

Cochains are functions on k-cells valued in ℤ/2.  The coboundary
operator δ : Cᵏ → Cᵏ⁺¹ is defined as the formal sum (mod 2) over
the cofaces:

  (δβ)(σ) = Σ_{τ ∈ ∂σ} β(τ)  (mod 2)

For K_{3,2}^{(c=2)}, the explicit formulas appear in
`Cochain.lean`, `Delta.lean`, `DeltaLinear.lean`.  The crucial
property:

**δ² = 0** (`DeltaSqZero.lean`)

This is closed at STRICT ∅-AXIOM via direct computation
on the finite cochain spaces.

### Chapter 5.  Universal δ²=0 prop-lift

Beyond the basic δ²=0, the full Δ⁴ stratum (spanning the (5, k)
cochains for k ∈ {0, 1, 2, 3}) is closed:

  Universal δ² = 0 prop-lift across (5, 0), (5, 1), (5, 2), (5, 3)
  Plus auxiliary strata (3, 0), (3, 1), (4, 0), (4, 1), (4, 2)

See `UniversalProp.lean`, `UniversalProp{31,41,42,51,52,53}.lean`.

The "prop-lift" terminology refers to *propositional* lifting of
the δ² = 0 fact across multiple decomposition forms (basis × basis,
two-sided lens, AND-form definitional collapse, etc).

### Chapter 6.  Betti numbers

The first Betti number b₁ of K_{3,2}^{(c=2)} is computed
constructively:

  b₁(K_{3,2}^{(c=2)}) = NS · NT · c − (NS + NT) + 1
                       = 12 − 5 + 1 = 8

(see `BettiKernel.lean`, `Bipartite32Betti.lean`).

The atomic identity 1/α_3 = NS² − 1 = 8 = b₁ is *not* a numerical
coincidence — it is the assertion that the strong coupling constant
equals the cycle-space dimension of the canonical graph.

---

## Part III — Cup product and Alexander-Whitney

### Chapter 7.  The cup product

The cup product ⌣ : Cⁿ × Cᵐ → Cⁿ⁺ᵐ on K_{3,2}^{(c=2)} cochains
is defined via Alexander-Whitney decomposition (`Cup.lean`,
`CupRing.lean`).  For α ∈ Cⁿ, β ∈ Cᵐ, σ an (n+m)-simplex:

  (α ⌣ β)(σ) = α(σ_front) · β(σ_back)

where `σ_front` is the n-face on the first n+1 vertices and
`σ_back` is the m-face on the last m+1 vertices of σ.

### Chapter 8.  CupAW (Alexander-Whitney universal cup)

CupAW is the *universal* cup product on K_{3,2}^{(c=2)} cochains —
universal in the sense that it specializes to all the AW-style
products in cohomology (see `CupAW.lean`, `CupAWBasisLeibniz.lean`).

The bilinearity infrastructure (`CupAWBilinear.lean`,
`CupAWBilinearFunc.lean`) reduces case counts exponentially:

  Naïve enumeration: 327,680 cases (32 × 4096 × 2.5)
  Bilinearity lens:  3,200 cases  (basis × basis × structural)

This 100× reduction is what makes the Δ⁴ Leibniz coverage tractable
via `decide`.

### Chapter 9.  The Δ⁴ Leibniz coverage

The **CupAW Leibniz identity** — the analogue of d(α ∧ β) =
dα ∧ β + (−1)^|α| α ∧ dβ for the simplicial cup — is closed at
all four interior strata of the (5, k) decomposition:

  (5, 1, 1) — direct decide (10,240 cases)
  (5, 1, 2) — bilinearity lens (3,200 + structural)
  (5, 2, 1) — two-sided lens (basis × basis + structural)
  (5, 2, 2) — two-sided lens (basis × basis + structural)

Bundled into `Delta4LeibnizCapstone.delta4_leibniz_capstone`.

All four STRICT ∅-AXIOM.  See the file family
`CupAWLeibniz*.lean`, `CupAWLeibnizAlgLift*.lean`,
`Delta4Capstone.lean`.

---

## Part IV — Hodge involution

### Chapter 10.  The Hodge star ⋆

The Hodge dual ⋆ : Cᵏ → Cᵈ⁻ᵏ on K_{3,2}^{(c=2)} cochains is
defined via the canonical pairing on K5 (`HodgeStar.lean`).
Under the (NS, NT) split, ⋆ swaps the role of S-vertices and
T-vertices in the dual interpretation.

### Chapter 11.  ⋆⋆ = id (Δ⁴ involution)

The Hodge involution `⋆⋆ = id` is closed at the (5, 1) and (5, 2)
strata at STRICT ∅-AXIOM (`HodgeInvolution.lean`,
`HodgeProp.lean`, `HodgeProp52.lean`).

The remaining strata (5, 0), (5, 3), (5, 4) are trivial-ish; a
bundling capstone is suggested as continuation work (see
HANDOFF Open Problem #5).

### Chapter 12.  HodgeDelta — the dual coboundary

The Hodge-dual coboundary δ⋆ = ⋆ δ ⋆⁻¹ acts on Cᵏ → Cᵏ⁻¹.
In the K_{3,2}^{(c=2)} setting, this gives the *flux* operator
that connects the cochain complex to physical observables
(see `HodgeDelta.lean`).

The combination Δ = δ⋆δ + δδ⋆ is the simplicial Laplacian — its
kernel computes the harmonic representatives of cohomology
classes.

---

## Part V — Universal property

### Chapter 13.  Universal cohomology lens

The cohomology of K_{3,2}^{(c=2)} carries a universal property:
any cochain α ∈ Cᵏ factors uniquely through its δ-class plus a
δ-image part (Hodge decomposition).

This is a *categorical* universality — the cohomology functor
satisfies the appropriate universal property in the category of
cochain complexes — formalised in `Universal.lean`,
`UniversalProp.lean`.

### Chapter 14.  Atomic readings of cohomology classes

Every closed cochain class on K_{3,2}^{(c=2)} has an atomic
reading in (NS, NT, d, c).  Examples:

  H⁰ ≃ ℤ/2          (1 connected component, b₀ = 1)
  H¹ ≃ (ℤ/2)⁸       (8 = b₁ = NS² − 1)
  H² ≃ ...

The atomic decomposition of cohomology generators (see
`SimplexBasis.lean`, `Paper1Chiral.lean`, `EulerClosed.lean`) is
what powers the cohomology classification (A/B/C/D/E) of physical
observables — see companion volumes for the application.

---

## Part VI — Fractal structure

### Chapter 15.  Fractal level L and self-similarity

The K_{3,2}^{(c=2)} graph at *fractal level L* refines each edge
into a smaller copy of K_{3,2}^{(c=2)} at level L−1.  At level L:

  numV(L) = d^L = 5^L
  numE(L) = (NS · NT · c) · 5^(L−1) = 12 · 5^(L−1)
  b₁(L) = (5^L − 1)(5^L − 2) / 2

(see `FractalLevel.lean`, `Fractal25.lean`).

The Betti scaling formula `b₁(L) = (5^L − 1)(5^L − 2)/2` is the
generating function for the cohomological depth — it appears in
the cohomology classification predictor algorithm.

### Chapter 16.  α_GUT cohomologically

The factor α_GUT = 6 / (25 π²) decomposes cohomologically
(`FractalAlphaGUT.lean`):

  numerator   6  = b₁(K5) = (d−1)(d−2)/2  (1st Betti of K5 1-skel)
  denominator 25 = numV(K_{25}) = d²       (vertex count at fractal L=2)
  π²          via Basel ζ(2) bracket (Real213)
  bonus: numE(K_{25}) = 300 = c · NS · NT · d²  (atomic factorisation)

α_GUT is therefore *not* a free coupling — its discrete part is
`K_5 cycle space / K_{25} vertex space`, a ratio of two cohomology
cardinalities at fractal levels L = 1 and L = 2.  Only ζ(2) is a
transcendental, handled by Basel.

This is the cleanest demonstration that a "running coupling
constant" in mainstream QFT corresponds to a *static fractal
cohomology ratio* in 213.

---

## Part VII — Encoding bijections

### Chapter 17.  EncodingBijection: cochain ↔ Fin

Each cochain space Cᵏ over (ℤ/2) bijects with `Fin (2^|k-cells|)`
— a Boolean enumeration.  The bijection is bit-stream-faithful:
applying δ on the cochain side commutes with the corresponding
bit-flip pattern on the Fin side.

See `EncodingBijection.lean`, `EncodingBijection52.lean`.

This encoding is what enables `decide` to verify cohomological
identities at finite strata — without the encoding, the Δ⁴
Leibniz coverage would be infeasible.

### Chapter 18.  XorPair combine (foldr induction)

The `XorPairCombine.foldr_xor_pair` is a 0-axiom List foldr
induction lemma (`XorPairCombine.lean`) that powers the
multi-cochain XOR closures.  Specialised to N-pair tuples
(`combine_5`, `combine_10`), it provides the structural backbone
for cup-product closures.

This file is the cleanest demonstration of the "List.foldr
induction = right abstraction for finite XOR facts" lesson
documented in `LESSONS_KERNEL_DECIDE.md`.

---

## Part VIII — Open horizons

### Chapter 19.  (n, a, b) generalisation of bilinearity lens

The bilinearity lens currently specialises at (5, 1, 2), (5, 2, 1),
(5, 2, 2).  A parametric lift to ∀ n via foldr-XOR + general
`decomp_n_k` is conjectural.

If closed: the Δ⁴ Leibniz capstone generalises to Δⁿ for any n,
and the cohomology framework becomes polynomial in n rather than
hand-specialised.

### Chapter 20.  Hodge ⋆⋆ = id at remaining strata

Strata (5, 0), (5, 3), (5, 4) of the Hodge involution are
trivial-ish but a bundling capstone that wraps all five strata
into a single theorem is suggested.

### Chapter 21.  Cohomology classification A/B/C/D/E

The discrete classification of physical observables into five
cohomology classes (A/B/C/D/E) is empirically validated at 100%
hit rate over a 36-observable corpus.  The *theoretical* proof
that every physically realisable observable falls into one of the
five classes — i.e., the *closure* of the classification — is
open.

Hint: each class corresponds to a specific *topological situation*
on the cochain ring (single-simplex projection, boundary leakage,
full-lattice invariant, chain product, modulus shadow).  A
classification theorem would say: any K_{3,2}^{(c=2)} cochain
operation that respects atomicity falls into one of these five
forms.

---

## Appendix A.  Lean theorem index

Key capstones (all STRICT ∅-AXIOM):

- `delta4_leibniz_capstone` — Δ⁴ Leibniz at (5, 1, 1), (5, 1, 2),
  (5, 2, 1), (5, 2, 2)
- `delta_sq_zero` — universal δ² = 0 at all strata
- `hodge_involution_52` — ⋆⋆ = id at (5, 1) and (5, 2)
- `cupAW_bilinear` — bilinearity lens
- `betti_kernel` — b₁(K_{3,2}^{(c=2)}) = 8
- `fractal_alpha_gut_decomp` — α_GUT cohomological factorisation

Source files at `lean/E213/Lib/Math/Cohomology/`.

## Appendix B.  Verification standard

Every theorem closed in Lean 4 at **STRICT ∅-AXIOM** — `#print axioms
<thm>` returns "does not depend on any axioms".

No `sorry`, no Mathlib, no Classical, no `native_decide`, no
`propext`, no `Quot.sound`.

`cd lean && lake build` passes.

## Author

Mingu Jeong (Independent Researcher).

Acknowledgments: Claude (Anthropic) provided formalization
assistance under direct supervision.
