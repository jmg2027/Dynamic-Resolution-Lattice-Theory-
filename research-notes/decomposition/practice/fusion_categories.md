# Decomposition: fusion / modular tensor categories (anyons, the S/T matrices, Verlinde, quantum dimension)

*213-decomposition per `../README.md` (model v7.1) and `../SYNTHESIS.md` (the two invariants —
the character arrow `×↦·`/`×↦+`, the `q=±1` residue tag — plus the 2-category of readings). A
**fresh** field, but one the corpus has already approached from five sides at once: the **monoidal
product** (`tqft.md` — `GRA/Monoidal.product`, `productSwapIso`), the **braiding / R-matrix** and the
deformation-`q` (`quantum_groups.md`), the **dual / antipode** (`hopf_algebras.md`), the **fusion =
tensor-decomposition of reps** (`representation.md`), and the **S-matrix = a Fourier transform**
(`fourier.md`). The new datum here is the *finiteness + the fusion-count + the modular S/T matrices*
glued onto that already-built skeleton.*

The thesis under test: **a fusion category is `tqft.md`'s monoidal product made FINITE (finitely
many simple objects) with a fusion-rule COUNT, the braiding = the `q=±1` swap + a phase
(`quantum_groups.md`), the modular S-matrix = `fourier.md`'s character transform diagonalizing the
fusion rules (Verlinde = character-orthogonality inversion), the T-matrix = the twist (the `q=±1`
self-braiding phase), and the quantum dimension = the Perron count (φ for Fibonacci anyons =
`golden_is_converge`/`golden_hyperbolic`).** No new primitive — it is `tqft.md`'s Invariant-A
monoidal product, finitized, with Invariant B (`q=±1`) carrying the braiding/twist and Invariant A
(the character arrow) carrying the S-matrix.

## The decomposition (C / Reading / Residue q=±1)

- **Construction `C` — `tqft.md`'s monoidal product, made FINITE; nothing new.** A fusion category's
  objects are built from **finitely many simple objects** `{X_0=1, X_1, …, X_{r−1}}` under the monoidal
  product `⊗` — exactly `tqft.md`'s `GRA/Monoidal.product` (`Lib/Math/Algebra/GRA/Monoidal.lean:129`)
  with a **monoidal unit** `trivial23` (`Monoidal.lean:58`, the tensor unit `1` = `Z(∅)=k`). The single
  genuinely new construction-datum is **finiteness**: the simple objects are a *finite* index set, and a
  fusion is a *finite* count. That is not a new primitive — it is the count-reading
  (`cardinality.md`/`representation.md`) restricted to a finite orbit, the same finitization
  `fourier.md`'s cyclic `⟨g⟩` already carries (a circle of finite circumference `p−1`).

- **Reading `L` — the fusion rule = the monoidal product read at the COUNT, with multiplicities
  `N^Z_{XY}`.** The fusion rules `X⊗Y = ⊕_Z N^Z_{XY} Z` are `tqft.md`'s product-preservation read at
  the **grade/count** readout: `product_NT_NT_grade` (`Monoidal.lean:182`) says
  `grade(M₁⊗M₂)=grade M₁ + grade M₂` — the `×↦+` additive character (`SYNTHESIS.md` Invariant A,
  additive twin) made a *monoidal-product-preservation* theorem. The structure constants `N^Z_{XY}`
  (how many copies of `Z` appear) are the **count reading** of that product: a non-negative integer
  *multiplicity*, exactly `representation.md`'s "decompose into irreps = the count of distinguishable
  ×-atoms in the readout". So the fusion ring is the count-reading of the finite monoidal product — the
  Aut-family's linear readings (`representation.md`) closed into a finite ring.

- **Residue `q=±1` — the braiding-phase + the twist, and the dual.** What the finite monoidal product
  *forces but the bare fusion-count does not capture*:
  - the **braiding** `c_{X,Y}: X⊗Y → Y⊗X` is the **swap with a phase**. The undeformed swap is
    `tqft.md`'s symmetric braiding `productSwapIso`/`productSwapIso_involutive`
    (`HasDistinguishing213.lean:105,122`, the `q=±1` involution) and `FoldKlein.bothSwap`
    (`Lens/Number/FoldKlein.lean:31`, `bothSwap_involutive`/`bothSwap_no_fixed`). The *phase* is
    `quantum_groups.md`'s deformation: the R-matrix is the swap deformed by `q`, and at the unimodular
    locus it meets the tag-`q=±1` (the `quantum_groups.md` **containment** finding — the
    deformation-`q` and the tag-`q` share the `±1` locus, not the same object).
  - the **T-matrix / twist** `θ_X` is the **self-braiding phase** — the `q=±1` self-application bit
    (`ResidueTag.multiplier`, ∓1, `ResidueTag.lean:81`/`:86`), the residue's own swap-on-itself.
  - the **dual** `X*` is `hopf_algebras.md`'s **antipode** — the `q=−1` unimodular involution
    (`bothSwap` "the antipode", `bothSwap_swaps_both`), the convolution-inverse the co-fold forces.
  The genuinely-ABSENT part: the **named** `FusionCategory`/`fusionRule`/`Smatrix`/`Verlinde`/`anyon`/
  `quantum_dimension` objects, and the categorical *coherence* (pentagon/hexagon, the F/R-symbols) —
  the same colimit/2-cell-coherence corner `tqft.md`'s cobordism carrier and `knots.md`'s skein move
  sit in.

## Re-seeing (⟨C | L⟩) — term by term

```
   a fusion category   =  ⟨ C (FINITE simple objects under tqft's monoidal product ⊗, unit 1)
                            | the fusion rule = ⊗ read at the count, multiplicities N^Z_{XY} ⟩
                            ⊕ braiding/twist/dual residue (q=±1, quantum_groups + hopf_algebras)

   X ⊗ Y = ⊕ N^Z_{XY} Z =  the monoidal product, grade-additive          (GRA.Monoidal.product; product_NT_NT_grade: grade(M⊗N)=grade M+grade N)
   the unit object 1     =  the monoidal unit = Z(∅)=k                      (Monoidal.trivial23; leftUnitHom/rightUnitHom = unit coherence)
   N^Z_{XY} (multiplicities) = the count reading (how many copies of Z)    (representation.md: count of distinguishable ×-atoms; cardinality.md count)
   the dual X*           =  hopf_algebras' antipode = the q=−1 involution   (FoldKlein.bothSwap; bothSwap_swaps_both/_no_fixed; ResidueTag.multiplier −1)
   the braiding c_{X,Y}  =  the q=±1 swap + a phase (R-matrix)              (productSwapIso_involutive; bothSwap_involutive; quantum_groups' qbinom deformation, q→1 = qbinom_q1)
   the T-matrix / twist θ_X = the self-braiding q=±1 phase                  (ResidueTag.multiplier_unimodular: q·q=1; residue_tag_two_poles)
   the modular S-matrix  =  the Fourier transform on the fusion ring        (fourier.md: read through ALL characters; dlog_exists/exists_primitive_root)
   S diagonalizes fusion =  characters diagonalize the multiplicative ring  (legendre_mul: the ×↦· character homomorphism)
   the Verlinde formula  =  character-orthogonality inversion (N = Σ S../S) (quadratic_orthogonality; geomSum_telescope; cyclic_orthogonality_modp)
   S-orthogonality SS†=1 =  fourier's character orthogonality Σχ=0          (root_orthogonality; cyclotomic_orthogonality; quadratic_orthogonality)
   quantum dim d_X       =  the Perron / largest fusion eigenvalue          (golden_hyperbolic: tr G=3,det=1,disc=5 — φ; golden_is_converge: the q=+1 converge pole)
   φ for Fibonacci anyons=  the converging q=+1 fixed point (Cassini)       (golden_is_converge: multiplier .converge = +1; cassini_law_one)
```

## Revelation

**Collapse + forcing + one located break — the new datum being finiteness + the fusion-count + the
modular S/T matrices glued onto `tqft.md`'s already-built monoidal product.**

**Collapse (the spine):** *a fusion category is `tqft.md`'s monoidal product (Invariant A, `⊔↦⊗` /
`×↦+` at the grade) made FINITE, with the fusion multiplicities `N^Z_{XY}` the count reading, the
braiding the `q=±1` swap + phase (Invariant B), the dual the antipode, and the modular S-matrix
`fourier.md`'s character transform.* The corpus already builds the load-bearing piece: a symmetric
monoidal product with a unit and a `q=±1` involutive swap, ∅-axiom (`GRA/Monoidal`,
`product_NT_NT_grade`, `productSwapIso_involutive`). The fusion rules add *nothing* to that — they are
that product read at the count with multiplicities, the same `representation.md` "decompose into
distinguishable atoms" move, finitized. So a fusion category does not introduce a primitive: it is
`tqft.md`'s Invariant-A monoidal product on a finite object-set, with Invariant B (`q=±1`) carrying
the braiding/twist/dual.

**Forcing — the S-matrix is forced as the Fourier transform diagonalizing the fusion ring, and
Verlinde is character-orthogonality inversion.** This is the sharpest leg, and it is `fourier.md`'s
already-closed result re-identified. The fusion ring is a finite **commutative** ring (the `N^Z_{XY}`
are symmetric in `X,Y` and the product is associative/commutative — `conv_comm`/`conv_assoc`,
`Convolution213.lean:156,257`). A commutative ring is **diagonalized by its characters** — the `×↦·`
homomorphisms `χ : (fusion ring) → ℂ` (`legendre_mul`, `LegendreMultiplicative.lean:77`, the character
homomorphism). The **S-matrix is exactly the matrix of those characters** — "read every fusion
element through every character" is `fourier.md`'s Fourier transform on a finite abelian structure
(`dlog_exists`/`exists_primitive_root`, `DiscreteLogParity.lean:123` / `PrimitiveRoot.lean:156`, the
self-dual cyclic character family `Ĉ≅C`). Therefore:
- **"S diagonalizes the fusion rules"** is *forced*: the characters are the simultaneous eigenvectors
  of the commuting fusion matrices `N_X` (the regular representation), and `S` is the change-of-basis
  to them — the same prediction `representation.md` makes (the fusion ring is the abelian rep-ring, S
  its character table).
- **The Verlinde formula** `N^Z_{XY} = Σ_a S_{Xa} S_{Ya} S*_{Za} / S_{0a}` is the **inverse Fourier
  transform** — read the diagonalized eigenvalues back into the structure constants. This is
  character-orthogonality (`SS† = 1`) inverted: the *same* `Σχ=0` orthogonality the corpus closed —
  `quadratic_orthogonality` (`CharacterOrthogonality.lean:146`, order 2), `root_orthogonality`/
  `omega_orthogonality`/`cyclotomic_orthogonality` (`RootOfUnityOrthogonality.lean:190,206,241`, orders
  3,6 in ℤ[ω]), and `cyclic_orthogonality_modp` (`CyclicCharacterOrthogonality.lean:254`, **all
  orders** mod p) — with `geomSum_telescope` (`RootOfUnityOrthogonality.lean:190`,
  `(ζ−1)·Σ_{k<n}ζᵏ=ζⁿ−1`) the forced telescoping engine. So Verlinde is not a separate miracle: it is
  the inversion `f = Σ_j f̂(j) χ_j` of the character transform, exactly `fourier.md`'s predicted
  inversion read on the fusion ring.

**Forcing — the quantum dimension is the Perron count, and φ for Fibonacci anyons is
`golden_is_converge`.** The quantum dimension `d_X` is the **largest (Perron) eigenvalue** of the
fusion matrix `N_X`, and the total `D² = Σ d_X²`. For the **Fibonacci** category (two simples `1, τ`
with `τ⊗τ = 1 ⊕ τ`) the fusion matrix is `N_τ = [[0,1],[1,1]]` — the Fibonacci/Möbius matrix — whose
dominant eigenvalue is `φ`. The repo builds this exact object: `golden_hyperbolic`
(`HyperbolicEllipticTrace.lean:71`: the golden iterator `G` has `tr G = 3`, `det G = 1`, `disc G = 5`,
the `φ²`-spectrum), and `golden_is_converge` (`ResidueTag.lean:180`) ties `φ` to the **`q=+1`
converging pole** (`multiplier .converge = +1`, the conserved Cassini determinant). So `d_τ = φ` is
the **`q=+1` converge residue** — the Perron eigenvalue of the count-reading's finite orbit,
*literally* `golden_ratio.md`'s φ as a fusion eigenvalue, certified.

**The braiding/twist as `q=±1` (Invariant B, the `quantum_groups.md` containment).** The braiding is
the `q=±1` swap (`productSwapIso_involutive`, `bothSwap_involutive`) carrying a phase; the twist
`θ_X = e^{2πi h_X}` is the self-braiding phase = the `q=±1` self-application bit
(`multiplier_unimodular`, `q·q=1`, `ResidueTag.lean:86`). Honest, per `quantum_groups.md`: the *phase*
is the deformation-`q` (a continuous dial on the count, `qbinom`, `QBinomial.lean:36`, with `q→1` the
classical limit `qbinom_q1`, `:60`), which meets the tag-`q=±1` **by containment at the `±1` locus**,
not identity. A *modular* category (S,T modular) requires the braiding be *non-degenerate* — the
escape (`q=−1`) pole of the residue, where the symmetric/undeformed (`q=+1`) braiding does not suffice.

**The located break (honest — Side B of `tqft.md`/`knots.md`/`two_cells.md`, recurring verbatim):** the
**named** `FusionCategory`/`fusionRule`/`Smatrix`/`Verlinde`/`anyon`/`quantum_dimension`/
`modular_tensor` objects are ABSENT (grep-confirmed below), and so is the categorical **coherence
data** — the **pentagon** (F-symbols / associator) and **hexagon** (R-symbols / braiding coherence),
the F/R-symbol consistency, and the **anyon model as a quotient by these coherence relations**. This
is the same missing primitive `tqft.md` hit (the cobordism category / isotopy quotient) and
`knots.md`/`two_cells.md` Shape 3 located: a coherence/colimit quotient no reading's kernel or
self-application generates, sitting in the un-built `q=−1` corner. The *algebraic* core (the finite
monoidal product + unit + swap, the fusion-count, the antipode dual, the S-matrix = character transform
with Verlinde = orthogonality inversion, the quantum dim = Perron φ) is all built or proof-shaped; the
*coherence/anyon-model carrier* (pentagon/hexagon, the modular quotient) is the genuine open primitive.

## VALIDATE verdict — **EXTEND + PREDICTION + one located BREAK**

No new primitive. A fusion category is `tqft.md`'s monoidal product (`SYNTHESIS.md` Invariant A) made
finite with a fusion-count, the braiding/twist/dual the `q=±1` residue (Invariant B, the
`quantum_groups.md`/`hopf_algebras.md` containment), the modular S-matrix `fourier.md`'s character
transform diagonalizing the fusion ring, Verlinde = character-orthogonality inversion, and the quantum
dimension = the Perron count (φ for Fibonacci = `golden_is_converge`). The verdict has four legs:

1. **fusion rules `X⊗Y=⊕N^Z_{XY}Z` = `tqft.md`'s monoidal product read at the count.** Grounded by the
   *built* monoidal product + unit + grade-additivity (`GRA.Monoidal.product`, `product_NT_NT_grade`,
   `leftUnitHom`/`rightUnitHom`, 13/0) and the involutive swap (`productSwapIso_involutive`, 23/0). The
   multiplicities `N^Z_{XY}` are `representation.md`'s count reading. **EXTEND.**
2. **the S-matrix = `fourier.md`'s character transform; Verlinde = character-orthogonality inversion.**
   PREDICTION (consolidation): the fusion ring is commutative (`conv_comm`/`conv_assoc`), diagonalized
   by its characters (`legendre_mul`), and the Verlinde inversion is the *same* `Σχ=0` orthogonality
   the corpus closed at orders 2/3/6/all-mod-p (`quadratic_orthogonality`, `root_orthogonality`,
   `cyclotomic_orthogonality`, `cyclic_orthogonality_modp`, with `geomSum_telescope` the engine). The
   abelian/1-dim slice is `fourier.md` verbatim; the full unitary `S` with quantum-dim normalization is
   the `Real213`-cut / `d>1` residue (`representation.md`'s det/tr edge). **PREDICTION + PARTIAL.**
3. **quantum dimension = the Perron count; φ for Fibonacci = `golden_is_converge`.** PREDICTION,
   certified at the Fibonacci instance: `golden_hyperbolic` (5/0) gives the `[[0,1],[1,1]]`-style
   φ-spectrum, `golden_is_converge` (in `ResidueTag` 55/0) ties φ to the `q=+1` converge pole. The
   general Perron–Frobenius eigenvalue existence for an arbitrary fusion matrix is the `Real213`-cut /
   eigenvalue-existence residue (`spectral.md`'s `disc≥0`). **PREDICTION + PARTIAL.**
4. **the named `FusionCategory`/`Smatrix`/`Verlinde`/`anyon` objects + pentagon/hexagon coherence are
   ABSENT.** Side B of `tqft.md`/`knots.md`/`two_cells.md`, recurring verbatim — the coherence/colimit
   quotient in the un-built `q=−1` corner. **PARTIAL / located break.**

So a fusion category is the character arrow's finite monoidal product (Invariant A) with the `q=±1`
braiding/twist/dual (Invariant B) and the Fourier S-matrix diagonalizing the fusion ring (Verlinde =
orthogonality inversion, quantum dim = Perron φ) — fully native and Lean-grounded on the algebraic
side **except** the categorical coherence (pentagon/hexagon, F/R-symbols) and the named anyon-model
quotient, which is the genuine open primitive shared with knots/π₁/TQFT. A clean EXTEND + PREDICTION
with one honestly-located BREAK.

## Verified Lean anchors (file:line:theorem — all grep + `tools/scan_axioms.py`-scanned this session, from repo root)

| Fusion-category datum | Theorem/def (file:line) | Purity (module tally) |
|---|---|---|
| ★ fusion `X⊗Y` = monoidal product (BUILT), w/ unit | `Lib/Math/Algebra/GRA/Monoidal.lean:129` `product` (def), `:58` `trivial23` | **13 PURE / 0 DIRTY** ✓ |
| ★ `grade(M⊗N)=grade M+grade N` (the `⊗`/count law) | `Lib/Math/Algebra/GRA/Monoidal.lean:182` `product_NT_NT_grade` | PURE (in the 13) ✓ |
| monoidal-unit coherence (`1`/`Z(∅)=k`) | `Lib/Math/Algebra/GRA/Monoidal.lean:155` `leftUnitHom`, `:167` `rightUnitHom` | PURE (in the 13) ✓ |
| ★ braiding = `q=±1` symmetric swap (involutive) | `Lib/Math/Algebra/GRA/HasDistinguishing213.lean:105` `productSwapIso`, `:122` `productSwapIso_involutive` | **23 PURE / 0 DIRTY** ✓ |
| dual `X*` = antipode = `q=−1` involution | `Lens/Number/FoldKlein.lean:31` `bothSwap` (def), `:50` `bothSwap_involutive`, `:53` `bothSwap_swaps_both`, `:58` `bothSwap_no_fixed` | **9 PURE / 0 DIRTY** ✓ |
| fusion ring commutative/assoc (S diagonalizable) | `Meta/Nat/Convolution213.lean:156` `conv_comm`, `:257` `conv_assoc`, `:87` `conv` (def) | **49 PURE / 0 DIRTY** ✓ |
| S-matrix entry = `×↦·` character (diagonalizes) | `Lib/Math/NumberTheory/ModArith/LegendreMultiplicative.lean:77` `legendre_mul` | **5 PURE / 0 DIRTY** ✓ |
| S = Fourier on self-dual cyclic char family | `Lib/Math/NumberTheory/ModArith/DiscreteLogParity.lean:123` `dlog_exists`, `:95` `qr_pow_iff_even_exp`; `…/PrimitiveRoot.lean:156` `exists_primitive_root` | **9 PURE / 0 DIRTY** (DiscreteLogParity) ✓ |
| ★ Verlinde = χ-orthogonality inversion (order 2) | `Lib/Math/NumberTheory/ModArith/CharacterOrthogonality.lean:146` `quadratic_orthogonality` | **20 PURE / 0 DIRTY** ✓ |
| ★ χ-orthogonality engine (generic telescope) | `Lib/Math/Algebra/CayleyDickson/Integer/RootOfUnityOrthogonality.lean:190` `geomSum_telescope`, `:206` `omega_orthogonality`, `:223` `root_orthogonality`, `:241` `cyclotomic_orthogonality` | **23 PURE / 0 DIRTY** ✓ |
| ★ χ-orthogonality at ALL orders mod p (Verlinde inv.) | `Lib/Math/NumberTheory/ModArith/CyclicCharacterOrthogonality.lean:254` `cyclic_orthogonality_modp` | **15 PURE / 0 DIRTY** ✓ |
| ★ quantum dim = Perron φ (Fibonacci anyons) | `Lib/Math/NumberSystems/Real213/ModularGeometry/HyperbolicEllipticTrace.lean:71` `golden_hyperbolic` (`tr G=3,det=1,disc=5`) | **5 PURE / 0 DIRTY** ✓ |
| ★ φ = the `q=+1` converge pole (Fibonacci d_τ) | `Lib/Math/Foundations/ResidueTag.lean:180` `golden_is_converge`, `:86` `multiplier_unimodular`, `:228` `residue_tag_two_poles`, `:81` `multiplier` | **55 PURE / 0 DIRTY** ✓ |
| braiding-phase = deformation-`q` (`q→1` classical) | `Lib/Math/Combinatorics/QBinomial.lean:36` `qbinom` (def), `:49` `qbinom_pascal`, `:60` `qbinom_q1`; `QBinomialSymmetry.lean` (12/0) | **11 PURE / 0 DIRTY** ✓ |
| character `×↦·` on the Aut-family (fusion = rep-ring) | `Lib/Math/NumberSystems/Real213/Markov/SternBrocotMarkov.lean:104` `det2_mul` | **130 PURE / 0 DIRTY** ✓ |

Scan tallies this session (`python3 tools/scan_axioms.py <module>` from repo root, each cited theorem
scanned `[PURE]`): `GRA.Monoidal` **13/0**, `GRA.HasDistinguishing213` **23/0**, `FoldKlein` **9/0**,
`Convolution213` **49/0**, `LegendreMultiplicative` **5/0**, `DiscreteLogParity` **9/0**,
`CharacterOrthogonality` **20/0**, `RootOfUnityOrthogonality` **23/0**, `CyclicCharacterOrthogonality`
**15/0**, `HyperbolicEllipticTrace` **5/0**, `ResidueTag` **55/0**, `QBinomial` **11/0**,
`QBinomialSymmetry` **12/0**, `SternBrocotMarkov` **130/0**.

## Dropped / flagged (honest)

- **Named `FusionCategory` / `fusionRule` / `Smatrix` / `S_matrix` / `Verlinde` / `anyon` /
  `quantum_dimension` / `modular_tensor` / `tensor_category` / `braiding` — ABSENT (grep-confirmed).**
  `grep -rniE "fusion|anyon|verlinde|s.?matrix|t.?matrix|modular.?tensor|tensor.?category|quantum.?dim|FusionCategory|fusionRule|braiding"`
  over `lean/E213/` finds **none of the fusion-category-specific objects**. The hits are false friends:
  the `braid` matches are the **Coxeter** `(ts)³=e` relation (`Lib/Physics/Symmetry/C3ChainCapstone.lean:69`,
  `OctetModule.lean:157` — a real braid relation, but the symmetric-group/Coxeter one, not a categorical
  braiding) and the "two-axis braid" *terminology* for the Möbius `P`-action
  (`MobiusProbeTwist.lean`/`ProbeTwistFixedPoint.lean` — just naming, not a braiding morphism); the
  `matrix` hits are continuant/Möbius/Markov matrices; the `fusion`/`anyon`/`verlinde`/`smatrix` greps
  return nothing. So the predicted-not-built named fusion-category bundles are **confirmed absent**; the
  **structure** (finite monoidal product, fusion-count, antipode dual, braiding swap, S = character
  transform, Verlinde = orthogonality inversion, quantum dim = Perron φ) is all built unnamed.
- **The pentagon / hexagon / associator / F-symbols / R-symbols (coherence data) — ABSENT.** The
  categorical coherence equations and the anyon model as a quotient by them sit in the same un-built
  colimit/`q=−1` coherence corner as `tqft.md`'s cobordism category and `knots.md`/`two_cells.md` Shape
  3. The genuine open primitive; flagged as the located break, not asserted.
- **The unitary S-matrix with quantum-dim normalization / a `d>1` modular S** — the corpus has the
  *abelian/1-dim* character transform and its orthogonality (closed), but the full unitary `S` over a
  general fusion ring needs the `Real213`/cyclotomic-cut `ζ` for non-`{1,2,3,4,6}` orders (`fourier.md`'s
  located transcendental-cut residue) and a `d>1` matrix-valued character (`representation.md`'s det/tr
  edge). Flagged: grounded at the abelian/Legendre level, the general `S` is the `Real213` residual.
- **General Perron–Frobenius eigenvalue existence for an arbitrary fusion matrix** — built only at the
  Fibonacci/golden instance (`golden_hyperbolic`); the general dominant-eigenvalue *existence* for a
  non-negative-integer fusion matrix with `disc<0` sits in `spectral.md`'s eigenvalue-existence
  `Real213`-cut residue. Flagged, not over-claimed.
- **The deformation-`q` = tag-`q` identity for the braiding phase — CONTAINMENT, not identity**
  (inherited verbatim from `quantum_groups.md`). The braiding phase is the continuous deformation-`q`
  (`qbinom`); the tag-`q=±1` (`ResidueTag.multiplier`) is the discrete swap bit. They share the `±1`
  *locus* by containment, aligned at `q=+1`. Flagged as the inherited honest break, not asserted as one
  object.
- **The bialgebra/Frobenius/Hopf compatibility (`Δ_+⇄Δ_×`, frontier F1)** — inherited from
  `hopf_algebras.md`/`tqft.md` (the one law fusing `m` and `Δ`); the antipode/dual leg is PURE but the
  single fusing law is unwritten. Flagged.

### Buildable witness (named)

The natural ∅-axiom closure of this note, beyond `tqft.md`'s `IsMonoidalGradeFunctor`: a
**`fibonacci_fusion_perron`** statement exhibiting the Fibonacci fusion matrix `N_τ = [[0,1],[1,1]]` (=
the golden iterator `G` shifted) and proving its dominant fusion eigenvalue is the φ-spectrum of
`golden_hyperbolic` (`tr=3,det=1,disc=5` for `G`, or `tr=1,det=−1,disc=5` for `N_τ` directly) — packaging
"the quantum dimension `d_τ = φ` is the `q=+1` converge-pole Perron count" (`golden_is_converge`) into one
bundled theorem. A second buildable witness: **`verlinde_is_character_inversion`** — bundle
`quadratic_orthogonality` / `cyclic_orthogonality_modp` (`SS†=1`) with `legendre_mul` (S diagonalizes the
commutative fusion ring `conv_comm`/`conv_assoc`) into a single statement "the Verlinde inversion
`N = S·(diag)·S†` is the inverse character transform", at the abelian/cyclic slice where it is fully
∅-axiom. Both promote PREDICTION rows to packaged EXTENDs; the pentagon/hexagon coherence + the named
anyon-model quotient stay the located break (a coherence/colimit-grade boundary, not a missing 213
primitive, per `tqft.md`/`two_cells.md` Shape 3).

## Cross-frame

`tqft.md` (KEY — the monoidal product `⊔↦⊗`, `GRA.Monoidal.product`/`product_NT_NT_grade`/`trivial23`/
`productSwapIso`; the cobordism-carrier/coherence break a fusion category inherits); `quantum_groups.md`
(KEY — the braiding = the `q=±1` swap + deformation phase, `qbinom`/`qbinom_q1`, the deformation-`q` vs
tag-`q` CONTAINMENT finding, R-matrix/Yang–Baxter the braid leg); `hopf_algebras.md` (KEY — the dual =
the antipode = `bothSwap`, the `m`/`Δ` convolution, the inherited F1 bialgebra compatibility);
`representation.md` (the fusion ring = the abelian rep-ring, `N^Z_{XY}` = the count of distinguishable
×-atoms, the det/tr `d>1` edge); `fourier.md` (KEY — the S-matrix = the character transform, S-orthogonality
= `Σχ=0`, Verlinde = the predicted inversion, the cyclotomic-cut residue for non-`{1,2,3,4,6}` orders);
`golden_ratio.md`/`spectral.md` (the quantum dim = the Perron φ eigenvalue, `golden_hyperbolic`/
`golden_is_converge`, the `disc<0` eigenvalue-existence residue); `knots.md`/`two_cells.md` (the
coherence/colimit quotient = the anyon-model's missing primitive, Shape 3 verbatim); `SYNTHESIS.md`
(Invariant A the character/monoidal-product arrow, Invariant B the `q=±1` tag — a fusion category =
Invariant A finitized + Invariant B on the braiding/twist/dual + the Fourier S-matrix).
```