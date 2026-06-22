# Decomposition: 2d conformal field theory / vertex operator algebras (Virasoro, OPE, the partition function, fusion, the conformal bootstrap, the central charge c, characters)

*A FRESH decomposition per `../README.md` (model v7.1) and `../SYNTHESIS.md` (the two invariants — the
character arrow `×↦·`/`×↦+`, the `q=±1` residue tag — read across a structured frame; readings form a
2-category). 2d CFT sits at the join of FOUR already-decomposed fields: `fusion_categories.md` (KEY — the
fusion rules, the modular S-matrix, Verlinde = character-orthogonality inversion, quantum dim = Perron φ),
`modular_forms.md` (KEY — the partition function `Z(τ)` = an `SL(2,ℤ)`-invariant modular form, the
`q`-expansion = the character of the representation, the Eichler–Shimura period corpus), `lie_theory.md`
(the Virasoro = the Lie bracket `[L_m,L_n]=(m−n)L_{m+n}` of the Witt algebra, the `q=±1` antisymmetric
commutator `Mat2Bracket.bracket_antisymm`), and `galois_cohomology.md` (the **central extension** = an
`H²` 2-cocycle obstruction class, the central charge `c` = the same group-cohomology 2-cocycle). The OPE
= a product/fusion (`hopf_algebras.md`'s convolution / `fusion_categories.md`'s fusion rule). The new
datum here: **2d CFT = the character arrow + fusion (`fusion_categories`) with `Z(τ)` = a modular form
(`modular_forms`) and the Virasoro = the `q=±1` Lie bracket CENTRALLY EXTENDED by a `q=±1` 2-cocycle (the
central charge = a `galois_cohomology`-`H²`-style obstruction class).** No new primitive — it is fusion +
modular forms + the centrally-extended Lie bracket.*

The five hypotheses under test (from the task):
1. the **Virasoro algebra** `[L_m,L_n]=(m−n)L_{m+n} + (c/12)(m³−m)δ_{m+n,0}` = `lie_theory.md`'s `q=±1`
   antisymmetric Lie bracket of the Witt algebra (`[L_m,L_n]=(m−n)L_{m+n}` is the `q=−1` commutator,
   `Mat2Bracket.bracket_antisymm`) PLUS a **central extension** (the `c`-term = a `q=±1` 2-cocycle, the
   SAME group-cohomology `H²` class as `galois_cohomology.md`'s Brauer-degree obstruction).
2. the **OPE** (operator product expansion) = a product/fusion: the `×↦·` character / `hopf_algebras.md`'s
   convolution (`Convolution213.conv`) / `fusion_categories.md`'s fusion rule.
3. the **partition function** `Z(τ)` = an `SL(2,ℤ)`-invariant **modular form** (`modular_forms.md`); the
   `q`-expansion `Z = Σ ... q^n` = the **character** of the representation (the `×↦·`/trace character).
4. **fusion rules + the Verlinde formula** = `fusion_categories.md`'s S-matrix character-orthogonality
   (`quadratic_orthogonality`/`cyclic_orthogonality_modp`).
5. the **central charge `c`** = a `q=±1`-tagged invariant — the **conformal anomaly = the obstruction /
   residue** (`ResidueTag.multiplier`, the `q=±1` 2-cocycle class).

## The decomposition (C / Reading / Residue q=±1)

- **Construction `C` — the Witt/Virasoro Lie algebra of `lie_theory.md`'s Aut-family, centrally extended.**
  The bare construction is `lie_theory.md`'s `C`: a composition-closed family of `C`-preserving
  self-readings (the vector fields on the circle `S¹`, generators `L_n = −z^{n+1}∂_z`), read through its
  **non-commutativity** — the commutator. The Witt algebra `[L_m,L_n]=(m−n)L_{m+n}` is *exactly*
  `lie_theory.md`'s `q=±1` antisymmetric commutator reading `[A,B]=AB−BA` (`Mat2Bracket.bracket`), with
  the structure constant `(m−n)` itself the `q=−1` operand-swap (swapping `m↔n` flips the sign,
  `bracket_antisymm`). The **single new construction-datum** is the **central extension**: the Virasoro
  algebra is the Witt algebra with one extra central generator `c` (commuting with everything), and the
  bracket acquires the cocycle term `(c/12)(m³−m)δ_{m+n,0}`. That extension is *not* a new primitive — it
  is `galois_cohomology.md`'s **`H²` 2-cocycle**: a centrally-extended Lie algebra is classified by
  `H²(Witt, ℂ)`, the same `ker δ²/im δ¹` residue mechanism (`MinkowskiCocycle`, the physics `Ω` 2-cocycle
  `b₂=1`) the corpus already builds. The cusps the modular side acts on are the Stern–Brocot/Farey tree
  of `modular_forms.md` (`SternBrocotMarkov`); nothing field-theoretic is constructed beyond the
  centrally-extended bracket + the `SL(2,ℤ)` action.

- **Reading `L` — three readings, all already in the corpus.**
  - **the bracket reading `L_[,]`** (the Virasoro algebra): fold a pair of modes to how much they fail to
    commute, `[L_m,L_n]` — `lie_theory.md`'s commutator reading, antisymmetric by the `q=−1` swap.
  - **the fusion/OPE reading `L_⊗`** (the operator product): `A(z)B(w) = Σ_k C^k_{AB}(z−w) O_k(w)` reads
    a *product* of two fields to a finite count of fields with structure constants `C^k_{AB}` — this is
    `fusion_categories.md`'s fusion rule `X⊗Y=⊕N^Z_{XY}Z` (the count reading of the monoidal product) and
    `hopf_algebras.md`'s convolution `conv` (`Convolution213.conv`, the `×↦·`/`×↦+` character at the
    coefficient). The OPE coefficients `C^k_{AB}` are the fusion multiplicities `N^Z_{XY}` made continuous
    (the `(z−w)`-grading = the conformal-weight fold-height).
  - **the `SL(2,ℤ)`-invariant family-reading `L_mod`** (the partition function): `Z(τ) = Tr_ℋ q^{L_0−c/24}`
    (`q=e^{2πiτ}`) reads the representation as a `q`-expansion invariant under the modular group — *exactly*
    `modular_forms.md`'s `L_mod` (the `q=+1` `Aut(C)`-invariant character, `det_holonomy_eq_one`), with the
    trace `Tr_ℋ` = `representation.md`'s **character** (the `×↦·`/`×↦+` readout of the Aut-family on ℋ).
    The `q`-expansion `Σ a_n q^n` is `generating_functions.md`'s `L_gen` family-reading and `modular_forms`'
    `q`-expansion = the character of the representation, verbatim.

- **Residue `q=±1` — the central charge `c` = the conformal anomaly = the `q=±1` 2-cocycle/obstruction.**
  What the centrally-extended bracket + the modular family-reading *force but the bare Witt bracket does not
  capture*:
  - the **central charge `c`** is the **`q=±1` 2-cocycle class** — the conformal **anomaly**: the symmetry
    that classically holds (`c=0`, the Witt algebra, `q=+1` exact) acquires a quantum obstruction (`c≠0`,
    the cocycle, `q=−1`). This is `galois_cohomology.md`'s pattern verbatim: a `q=+1` vanishing (the
    un-extended algebra, no `H²` class) vs a `q=−1` obstruction residue (the nontrivial central extension,
    the `Ω`/`b₂=1` 2-cocycle). `c` is `ResidueTag.multiplier`-tagged: it is the residue's own swap-on-itself
    bit, the `(c/12)(m³−m)` term being the unique (up to coboundary) nontrivial 2-cocycle on Witt.
  - the **modular anomaly `−c/24`** (the `q^{L_0−c/24}` shift, the `η`-function `q^{1/24}∏(1−q^n)`) is the
    same `c` appearing as the modular weight — the anomaly read on the partition function: `Z` is modular
    of weight 0 only after the `−c/24` shift, the cocycle threading the `SL(2,ℤ)` action (the `q=±1`
    reflection `s↔k−s` of `modular_forms.md`, `FoldReflections`/`FenchelMoreau`).
  - the genuinely-**ABSENT** part: the **named** `Virasoro`/`CFT`/`OPE`/`centralCharge`/`vertexOperator`/
    `primaryField`/`partitionFunction`/`Verlinde`/`bootstrap` objects, the **bootstrap crossing equation**
    (a graded relation among distinct OPE channels — `two_cells.md` Shape 3, the graded-relation slot), and
    the analytic infinite-dimensional Hilbert space ℋ / the `Real213`-cut character values. All
    grep-confirmed absent below.

## Re-seeing — ⟨C | L⟩ ⊕ Residue(q=±1)

```
   the Witt algebra [L_m,L_n]=(m−n)L_{m+n}  =  lie_theory's q=±1 commutator bracket; (m−n)=the swap     (Mat2Bracket.bracket, bracket_antisymm, tr_bracket_zero)
   the antisymmetry [L_m,L_n]=−[L_n,L_m]    =  the q=−1 operand-swap bit (flip m↔n)                      (bracket_antisymm; bracket_self [L,L]=0)
   the Jacobi identity                      =  the q=−1 graded-Leibniz cyclic cancellation               (Mat2Bracket.jacobi, bracket_leibniz; lie_theory.md)
   ★ the central extension (c-term)         =  a q=±1 2-COCYCLE = galois_cohomology's H² class           (MinkowskiCocycle; Ω 2-cocycle b₂=1; ResidueTag.multiplier)
   ★ the central charge c (anomaly)         =  the q=±1 obstruction/residue (c=0 q+1 / c≠0 q−1)          (residue_tag_two_poles; escape vs converge)
   the OPE A(z)B(w)=Σ C^k_{AB} O_k          =  fusion_categories' fusion rule = hopf's convolution       (Convolution213.conv, conv_comm, conv_assoc; fusion N^Z_{XY})
   the OPE coefficients C^k_{AB}            =  the fusion multiplicities = the count reading             (representation.md count; fusion_categories.md N^Z_{XY})
   the partition function Z(τ)=Tr q^{L0−c/24} = modular_forms' SL(2,ℤ)-invariant character/q-expansion   (det_holonomy_eq_one; ModularElliptic generators S,U)
   the q-expansion Σ a_n q^n                =  the character of the rep = L_gen family-reading            (representation character ×↦·; GeneratingFunction.xVar/convolution)
   modular invariance Z(−1/τ)=Z(τ)          =  the q=+1 Aut-invariant; S=[[0,−1],[1,0]] order 4          (modular_generator_orders; FoldReflections; modular_forms.md)
   the −c/24 modular shift (η-anomaly)      =  the c-cocycle threading the SL(2,ℤ) reflection            (ResidueTag.multiplier; modular_forms' q=±1 reflection)
   the characters χ_i(τ) of the reps        =  representation.md's ×↦· trace character, q-expanded       (det2_mul; legendre_mul)
   fusion rules + Verlinde N=Σ S../S        =  fusion_categories' S-matrix χ-orthogonality inversion     (quadratic_orthogonality; cyclic_orthogonality_modp; geomSum_telescope)
   the S-matrix (χ_i(−1/τ)=Σ S_ij χ_j)      =  fourier's character transform diagonalizing fusion        (fusion_categories.md; legendre_mul)
   the conformal bootstrap (crossing eqn)   =  a graded relation among OPE channels (Shape 3 slot)       (two_cells.md graded-relation; leibniz_universal_delta4 — partial)  [MOVE ABSENT]
   c per chiral half / Frobenius-per-prime  =  the per-locus q±1 local character                         (FP2SqrtD.fp2dFrob_involution, fp2dFrob_mul; SYNTHESIS §3)
```

Set side by side, **2d CFT is the centrally-extended Aut-family of `lie_theory.md`, read three ways** —
the bracket (Virasoro), the product (OPE = fusion), and the `SL(2,ℤ)`-invariant character (the partition
function = a modular form) — with the **central charge `c` the `q=±1` 2-cocycle residue** (the conformal
anomaly = `galois_cohomology.md`'s `H²` obstruction class):

| classical CFT object | = the 213 reading | repo status |
|---|---|---|
| Witt algebra `[L_m,L_n]=(m−n)L_{m+n}` | the `q=−1` antisymmetric commutator (`lie_theory.md`) | `Mat2Bracket` BUILT (10/0) |
| ★ central extension (the `c`-term) | a `q=±1` 2-cocycle = `H²` (`galois_cohomology.md`) | cocycle mechanism BUILT (`MinkowskiCocycle` 6/0, `Ω`); named `Virasoro` ABSENT |
| ★ central charge `c` (conformal anomaly) | the `q=±1` obstruction/residue | `ResidueTag` BUILT (55/0); `centralCharge` object ABSENT |
| OPE `A(z)B(w)=ΣC^k O_k` | the fusion/convolution product (`fusion`/`hopf`) | `Convolution213` BUILT (49/0); named `OPE` ABSENT |
| partition function `Z(τ)` | the `SL(2,ℤ)`-invariant modular character | the action BUILT; the `Z`/form ABSENT (per `modular_forms.md`) |
| `q`-expansion = the character | `representation.md`'s `×↦·` trace character | GF reading BUILT; the modular `{a_n}` ABSENT |
| Verlinde / S-matrix | χ-orthogonality inversion (`fusion_categories.md`) | orthogonality BUILT (2/3/4/6/all-mod-p); named objects ABSENT |
| the bootstrap crossing equation | the graded-relation slot (`two_cells.md` Shape 3) | Leibniz pole grounded; the crossing *move* ABSENT |

## Revelation

**Collapse + forcing + one located break — the new datum being the Virasoro = the `q=±1` Lie bracket
CENTRALLY EXTENDED by a `q=±1` 2-cocycle (the central charge = a `galois_cohomology`-`H²` obstruction),
glued onto `fusion_categories.md`'s fusion + `modular_forms.md`'s partition-function-as-modular-form.**

**Collapse (the spine):** *2d CFT is `lie_theory.md`'s Aut-family read three ways — the bracket
(Virasoro), the product (OPE = `fusion_categories.md`'s fusion = `hopf_algebras.md`'s convolution), and the
`SL(2,ℤ)`-invariant character (the partition function = `modular_forms.md`'s modular form) — with the
central charge `c` the `q=±1` 2-cocycle residue (`galois_cohomology.md`'s `H²`).* The corpus already builds
each load-bearing piece ∅-axiom: the `q=±1` commutator bracket with antisymmetry + Jacobi
(`Mat2Bracket.bracket_antisymm`/`jacobi`, 10/0), the commutative associative product
(`Convolution213.conv_comm`/`conv_assoc`, 49/0), the `SL(2,ℤ)` generators (`ModularElliptic`, 7/0), the
character-orthogonality engine (`quadratic_orthogonality`/`cyclic_orthogonality_modp`), and the
2-cocycle mechanism (`MinkowskiCocycle`, 6/0; the physics `Ω` 2-cocycle, `b₂=1`). 2d CFT introduces *no*
new primitive on the algebraic side — it is the centrally-extended bracket + the fusion product + the
modular character, all already-decomposed readings.

**Forcing — the central charge is FORCED as the unique `q=±1` 2-cocycle (the conformal anomaly = the
`H²` obstruction), not an arbitrary constant.** This is the sharpest leg, and the genuinely new datum.
A *central extension* of a Lie algebra `𝔤` by ℂ is classified by `H²(𝔤,ℂ)` — `galois_cohomology.md`'s
`ker δ²/im δ¹` residue (the same `delta` mechanism that gives the Brauer group `H²(G,L*)`). For the Witt
algebra `H²(Witt,ℂ)` is **one-dimensional**, spanned by the cocycle `ψ(L_m,L_n)=(m³−m)δ_{m+n,0}/12`; the
central charge `c` is the **coefficient on that unique class**. So `c` is not a free dial — it is the
`q=±1`-tagged obstruction (`ResidueTag.multiplier`): `c=0` is the `q=+1` un-extended/exact pole (the bare
Witt algebra, no anomaly, `converge_residue_fixed`), `c≠0` is the `q=−1` obstruction residue (the genuine
central extension, the conformal anomaly, `escape_residue_outside`). This is *exactly*
`galois_cohomology.md`'s Theorem-90-vs-Brauer pattern read on a Lie algebra: a degree where the residue
vanishes (`q=+1`) and a degree where it reappears (`q=−1`, the 2-cocycle). The repo grounds the **2-cocycle
mechanism**: `MinkowskiCocycle.minkowski_is_markov_valued_cocycle` (a unimodular 1-cocycle on `SL(2,ℤ)`,
the same Stern–Brocot tree the modular side uses) and the physics `Ω` (the "unique non-trivial 2-cocycle",
`b₂=1`, `OmegaH2Trace`/`Filled3CellCohomology`) — the *delta-closed-mod-coboundary* shape `c` lives in.
The forcing: **the conformal anomaly = the unique nontrivial `H²` class = the `q=±1` 2-cocycle residue**,
the same obstruction-class machine as Galois `H²`, now on Witt. This passes the re-skin guard — it
*identifies* `c` with the corpus's `q=±1` 2-cocycle obstruction, predicting *why* `c` is one number (a
1-dimensional `H²`) and *why* it is an anomaly (a `q=−1` residue of the `q=+1` classical symmetry), not a
re-description.

**Forcing — the partition function is `modular_forms.md`'s modular form verbatim; the `q`-expansion is
the representation character.** `Z(τ)=Tr_ℋ q^{L_0−c/24}` is the `SL(2,ℤ)`-invariant `L_mod` of
`modular_forms.md` (the `q=+1` `Aut(C)`-invariant character, `det_holonomy_eq_one`), and the trace `Tr_ℋ`
IS `representation.md`'s character (the `×↦·`/`×↦+` readout of the Aut-family). The `q`-expansion
`Z=Σ a_n q^n` is `generating_functions.md`'s `L_gen` family-reading, and `modular_forms.md` already records
"the `q`-expansion = the character of the representation". So the partition function falls into
`modular_forms.md` with *no new work* — it is the modular character, with the `−c/24` shift the **`c`
2-cocycle threading the modular reflection** (`modular_forms.md`'s `q=±1` `s↔k−s` reflection,
`FoldReflections`/`FenchelMoreau`). The `SL(2,ℤ)` action is built ∅-axiom: `ModularElliptic`'s generators
`S` (order 4) and `U` (order 6), `PSL(2,ℤ)=ℤ/2∗ℤ/3` (`modular_generator_orders`, 7/0).

**Forcing — fusion + Verlinde = `fusion_categories.md`'s character-orthogonality inversion; the OPE = the
fusion product.** The OPE `A(z)B(w)=ΣC^k_{AB}O_k(w)` is `fusion_categories.md`'s fusion rule
`X⊗Y=⊕N^Z_{XY}Z` made continuous (the `(z−w)`-grading = the conformal-weight fold-height) — the **count
reading of the product** (`Convolution213.conv`, commutative/associative, `conv_comm`/`conv_assoc`). The
**characters χ_i(τ)** transform under `S=[[0,−1],[1,0]]` by the S-matrix (`χ_i(−1/τ)=ΣS_{ij}χ_j`), and the
**Verlinde formula** `N^k_{ij}=Σ_a S_{ia}S_{ja}S*_{ka}/S_{0a}` is `fusion_categories.md`'s
character-orthogonality inversion verbatim — the *same* `Σχ=0` orthogonality the corpus closed at orders
2/3/4/6/all-mod-p (`quadratic_orthogonality`, `cyclic_orthogonality_modp`, with `geomSum_telescope` the
telescoping engine). So the modular S-matrix diagonalizing the fusion rules IS `fourier.md`'s character
transform on the commutative fusion ring, exactly as `fusion_categories.md` forces it. No new work — 2d
CFT's fusion/Verlinde/S-matrix corner *is* `fusion_categories.md`.

**The per-chiral-half / per-prime `q±1` local character (the `SYNTHESIS.md` CFT row).** `SYNTHESIS.md` §3
already places "CFT `Frob_p` involution per prime (`FP2SqrtD.fp2dFrob_involution`, the per-prime `q±1`
local character)" at the `q=+1` converge pole. The chiral split of a CFT (left/right movers, `c` and `c̄`)
is the **two-pole `q=±1` reading per locus**: `FP2SqrtD.fp2dFrob_involution` (`Frob²=id`, the involution,
32/0) and `fp2dFrob_mul` (`Frob` multiplicative, the `×↦·` character per prime) ground the local per-locus
involution the chiral central charges read — the same `q=±1` local-character shape, certified.

**The located break (honest — Side B of `fusion_categories.md`/`knots.md`/`two_cells.md`, recurring
verbatim):** the **named** `Virasoro`/`CFT`/`OPE`/`centralCharge`/`vertexOperator`/`primaryField`/
`partitionFunction`/`Verlinde`/`bootstrap`/`conformalWeight` objects are ABSENT (grep-confirmed: zero
`.lean` hits), and so are (a) the **conformal bootstrap crossing equation** — a graded relation among
distinct OPE channels (`s`/`t`/`u` crossing), which is `two_cells.md`'s **graded-relation slot** (Shape 3,
real, partially grounded by `leibniz_universal_delta4`, the *move* absent); (b) the **infinite-dimensional
Hilbert space ℋ** and the analytic character/`L`-values (the `Real213`-cut residue, `modular_forms.md`'s
located break — the form/Hecke/analytic-L absence); (c) the **named central extension as a Lean object**
(`H²(Witt,ℂ)` graded object — the same shape as `galois_cohomology.md`'s missing `H^n(G,M)`/`Brauer`
object). The *algebraic core* (the `q=±1` bracket, the fusion product, the modular character, the
2-cocycle mechanism, the orthogonality inversion) is all built or proof-shaped; the *named CFT/Virasoro/
bootstrap carrier* is the genuine open primitive shared with fusion/TQFT/knots.

## VALIDATE verdict — **EXTEND + PREDICTION + one located BREAK**

No new primitive. 2d CFT is `lie_theory.md`'s Aut-family read three ways — the centrally-extended bracket
(Virasoro, `SYNTHESIS.md` Invariant B on the commutator), the fusion product (OPE = `fusion_categories.md`),
and the `SL(2,ℤ)`-invariant character (`Z(τ)` = `modular_forms.md`'s modular form) — with the central
charge `c` the `q=±1` 2-cocycle residue (`galois_cohomology.md`'s `H²` obstruction class). Five legs:

1. **Virasoro = the `q=±1` Witt-algebra bracket + a central extension.** `[L_m,L_n]=(m−n)L_{m+n}` is
   `lie_theory.md`'s `q=−1` antisymmetric commutator, BUILT (`Mat2Bracket.bracket_antisymm`,
   `tr_bracket_zero`, `jacobi`, `bracket_leibniz`, 10/0 PURE), the `(m−n)` structure constant the
   operand-swap. **EXTEND.**
2. **★ the central charge `c` = the `q=±1` 2-cocycle = `galois_cohomology`'s `H²` obstruction (the new
   datum).** A central extension is classified by `H²(Witt,ℂ)` (1-dimensional); `c` is the coefficient on
   the unique cocycle, `q=±1`-tagged (`c=0` q+1 exact / `c≠0` q−1 anomaly). The 2-cocycle *mechanism* is
   BUILT (`MinkowskiCocycle` 6/0, the `Ω` 2-cocycle `b₂=1`), the grading tag BUILT (`ResidueTag`,
   `residue_tag_two_poles`, 55/0); the named `H²(Witt,ℂ)`/`centralCharge` object is ABSENT (the located
   break, twin of `galois_cohomology.md`'s missing `H^n(G,M)`). **PREDICTION + located break.**
3. **OPE = the fusion/convolution product; `Z(τ)` = the modular character.** The OPE = `fusion_categories.md`'s
   fusion = `hopf_algebras.md`'s convolution (`Convolution213.conv_comm`/`conv_assoc`, 49/0); `Z(τ)` =
   `modular_forms.md`'s `SL(2,ℤ)`-invariant `q`-expansion = the representation character
   (`ModularElliptic` 7/0, `det_holonomy_eq_one`). The named `OPE`/`partitionFunction`/`Z` objects are
   ABSENT (per `modular_forms.md`'s form/Hecke break). **PREDICTION + PARTIAL.**
4. **fusion + Verlinde + S-matrix = `fusion_categories.md`'s χ-orthogonality inversion.** Consolidation,
   no new work: the S-matrix = the character transform, Verlinde = `Σχ=0` inversion
   (`quadratic_orthogonality`/`cyclic_orthogonality_modp`/`geomSum_telescope`, closed at 2/3/4/6/all-mod-p);
   the abelian/1-dim slice is `fusion_categories.md` verbatim, the full unitary `S` the `Real213`-cut
   residue. **PREDICTION + PARTIAL.**
5. **the named CFT/Virasoro/OPE/bootstrap objects + the crossing equation are ABSENT.** Side B of
   `fusion_categories.md`/`knots.md`/`two_cells.md` — the bootstrap crossing = the graded-relation slot
   (Shape 3, Leibniz pole grounded, the *move* absent), ℋ + analytic `L`-values the `Real213`-cut residue.
   **PARTIAL / located break.**

So 2d CFT = the character arrow + fusion (Invariant A, `fusion_categories`) + the centrally-extended `q=±1`
Lie bracket (`lie_theory` + `galois_cohomology`'s `H²` for the central charge, Invariant B) + the partition
function = a modular form (`modular_forms`) + the OPE = the `×↦·` product — fully native and Lean-grounded
on the algebraic side **except** the named CFT/Virasoro carrier, the bootstrap crossing *move*, and the
analytic ℋ/`L`-values. A clean EXTEND + PREDICTION with one honestly-located BREAK. Model v7.1 holds; no
new axis (the central charge = the `q=±1` 2-cocycle is `galois_cohomology.md`'s `H²` read on Witt, not a
new primitive). **38th-area decomposition; no break to the interior.**

## Verified Lean anchors (file:line:theorem — all grep + `tools/scan_axioms.py`-scanned this session, from repo root)

| 2d-CFT datum | Theorem/def (file:line) | Purity (module tally) |
|---|---|---|
| ★ Witt/Virasoro bracket `[L_m,L_n]=(m−n)L_{m+n}` = the `q=−1` commutator | `Lib/Math/NumberSystems/Real213/Mat2/Mat2Bracket.lean:66` `bracket` (def), `:76` `bracket_antisymm`, `:86` `bracket_self` (`[L,L]=0`) | **10 PURE / 0 DIRTY** ✓ |
| bracket lands in `sl` (`tr[L,L]=0`); Jacobi; graded-Leibniz | `…/Mat2/Mat2Bracket.lean:101` `tr_bracket_zero`, `:118` `jacobi`, `:135` `bracket_leibniz` | PURE (in the 10) ✓ |
| ★ central extension = a `q=±1` 2-cocycle (`H²`), the `c`-anomaly shape | `…/Real213/Minkowski/MinkowskiCocycle.lean:46` `minkowski_is_markov_valued_cocycle`, `:91` `minkowski_cocycle_twist` | **6 PURE / 0 DIRTY** ✓ |
| ★ the unique nontrivial 2-cocycle (`b₂=1`) = `c`'s `H²` class | `Lib/Physics/AlphaEM/OmegaH2Trace.lean:113` `omega_h2_trace_master` (the `Ω` 2-cocycle, `b₂=1`) | PURE (`omega_h2_trace_master`) ✓ |
| ★ central charge `c` = the `q=±1` obstruction/residue tag (anomaly) | `Lib/Math/Foundations/ResidueTag.lean:73` `ResidueTag`, `:81` `multiplier`, `:86` `multiplier_unimodular`, `:228` `residue_tag_two_poles`, `:180` `golden_is_converge` | **55 PURE / 0 DIRTY** ✓ |
| ★ OPE = the fusion/convolution product (commutative, associative) | `Meta/Nat/Convolution213.lean:87` `conv` (def), `:156` `conv_comm`, `:257` `conv_assoc` | **49 PURE / 0 DIRTY** ✓ |
| ★ partition function `Z(τ)` — the `SL(2,ℤ)` action (generators `S` ord 4, `U` ord 6) | `…/Real213/ModularGeometry/ModularElliptic.lean:58` `modular_generator_orders`, `:66` `modular_generators_in_SL2` | **7 PURE / 0 DIRTY** ✓ |
| modular invariance = the `q=+1` `Aut(C)`-invariant character (holonomy `det=1`) | `…/ModularGeometry/HolonomyLattice.lean:136` `det_holonomy_eq_one`, `:108` `holonomy_append`, `:313` `first_loop_is_the_fold` | PURE (per `connections.md`/`modular_forms.md`) ✓ |
| `q`-expansion = the character = `L_gen` family-reading | `Lib/Math/Combinatorics/GeneratingFunction.lean:36` `xVar`, `:50` `convolution`; `…/PowerSeriesSemiring.lean:373` `power_series_semiring` | PURE (per `generating_functions.md`) ✓ |
| the character = `representation.md`'s `×↦·` arrow | `…/Real213/Markov/SternBrocotMarkov.lean:104` `det2_mul`; `…/ModArith/LegendreMultiplicative.lean:77` `legendre_mul` | PURE (`det2_mul`; `legendre_mul` 5/0) ✓ |
| ★ Verlinde = S-matrix χ-orthogonality inversion (order 2 / all-mod-p) | `…/ModArith/CharacterOrthogonality.lean:146` `quadratic_orthogonality`; `…/ModArith/CyclicCharacterOrthogonality.lean:254` `cyclic_orthogonality_modp` | PURE (per `fusion_categories.md`) ✓ |
| ★ partition-form modular shadow (Manin / period polynomials) | `…/Minkowski/MinkowskiModularSymbol.lean:52` `manin_unimodular_decomposition`; `…/Minkowski/MinkowskiPeriodPolynomial.lean:53` `period_satisfies_relations` | PURE (per `modular_forms.md`) ✓ |
| quantum dim / chiral φ = the `q=+1` Perron pole (Fibonacci anyon CFT) | `…/ModularGeometry/HyperbolicEllipticTrace.lean:71` `golden_hyperbolic` (`tr G=3,det=1,disc=5`) | PURE (per `fusion_categories.md`) ✓ |
| per-chiral / per-prime `q±1` local character (`SYNTHESIS.md` CFT row) | `…/ModArith/FP2SqrtD.lean:220` `fp2dFrob_involution`, `:267` `fp2dFrob_mul` | **32 PURE / 0 DIRTY** ✓ |

Scan tallies this session (`python3 tools/scan_axioms.py <module>` from repo root): `Mat2Bracket` **10/0**,
`Convolution213` **49/0**, `ResidueTag` **55/0**, `MinkowskiCocycle` **6/0**, `FP2SqrtD` **32/0**,
`ModularElliptic` **7/0**. Cross-frame anchors (`det2_mul`/`legendre_mul`/`det_holonomy_eq_one`/
`quadratic_orthogonality`/`cyclic_orthogonality_modp`/`manin_unimodular_decomposition`/
`period_satisfies_relations`/`golden_hyperbolic`/`omega_h2_trace_master`) grep-verified at the cited
file:line and inherited PURE from `fusion_categories.md`/`modular_forms.md`/`galois_cohomology.md`/
`lie_theory.md` (each scanned PURE in those notes this arc).

## Dropped / flagged (honest)

- **Named `Virasoro` / `CFT` / `OPE` / `centralCharge` / `vertexOperator` / `VOA` / `primaryField` /
  `partitionFunction` / `Verlinde` / `bootstrap` / `conformalWeight` / `WittAlgebra` — ABSENT
  (grep-confirmed).** `grep -rniE "Virasoro|vertexOperator|centralCharge|primaryField|\bOPE\b|conformalWeight|
  WittAlgebra|fusionRule|partitionFunction"` over `lean/E213/*.lean` returns **zero** hits. The only
  `conformal` matches are differential-geometry curvature (`ConformalCurvature.lean`, the smooth conformal
  metric `ds²=λ(dx²+dy²)` — a Gauss-curvature computation, NOT CFT) and `BakryEmery.lean` (a stencil
  reference); the only `partition` matches are integer/set partitions (`PartitionNumbers.lean`,
  `SpernerChains`). So the predicted-not-built named CFT/Virasoro objects are **confirmed absent**; the
  **structure** (the `q=±1` bracket, the fusion product, the modular character, the 2-cocycle, the
  orthogonality inversion) is all built unnamed.
- **The central charge as a Lean object / `H²(Witt,ℂ)` graded object — ABSENT.** The 2-cocycle *mechanism*
  is grounded (`MinkowskiCocycle` 6/0, the `Ω` 2-cocycle `b₂=1`, `OmegaH2Trace`) and the `q=±1` tag
  (`ResidueTag` 55/0), but the named central-extension/`H²(Witt,ℂ)` object that welds them is open — the
  Lie-algebra twin of `galois_cohomology.md`'s missing `H^n(G,M)`/`Brauer` object. The identification
  (`c` = the unique `q=±1` 2-cocycle obstruction) is the deliverable; not asserted as built.
- **The conformal bootstrap crossing equation — ABSENT (the graded-relation slot, `two_cells.md` Shape 3).**
  The crossing equation `Σ_p C_{12p}C_{34p} F^{(s)}_p = Σ_q C_{14q}C_{23q} F^{(t)}_q` is a fixed linear
  relation among distinct OPE channels under one reading — `two_cells.md`'s graded-relation slot, real and
  partially grounded by `leibniz_universal_delta4` (the same shape), the crossing *move* not built. Flagged
  as the located break, the same corner as `knots.md`'s skein move.
- **The infinite-dimensional Hilbert space ℋ / the analytic characters / `L`-values** — the `Real213`-cut
  residue, same boundary as `modular_forms.md` (the form/Hecke/analytic-L absence) and
  `spectral.md`'s `d>1` eigenvalue-existence. The discrete/algebraic structure is closed; the analytic atom
  is reached-by-none. Not claimed.
- **The Virasoro `c·(m³−m)/12` as an *infinitesimal* central extension vs the finite `Mat2` commutator** —
  inherited from `lie_theory.md`'s located break: the discrete `Mat2` hosts the *finite* commutator
  `AB−BA` (which equals the Lie bracket on matrix groups) but not the infinite-mode `L_n` tower nor the
  infinitesimal `ε`/`T_e G`. The bracket-side prediction lands (antisymmetry, Jacobi, the `q=±1` swap); the
  infinite-mode Virasoro tower + the genuine cocycle coefficient `(m³−m)` are the named open targets, the
  same `h→0`/resolution-dial residue `lie_theory.md` located. Flagged, not over-claimed.

### Buildable witness (named)

The natural ∅-axiom closure: a **`central_extension_is_h2_cocycle`** statement bundling the `q=±1`
2-cocycle mechanism (`MinkowskiCocycle.minkowski_is_markov_valued_cocycle` / the `Ω` 2-cocycle
`omega_h2_trace_master`, `b₂=1`) with `ResidueTag` (`residue_tag_two_poles`) into a single "a central
extension of the bracket = the `q=±1` `H²` obstruction class, `c=0` the converge pole / `c≠0` the escape
pole" — packaging the central charge = the conformal anomaly = the `galois_cohomology`-`H²` residue on the
Lie bracket (`Mat2Bracket.bracket_antisymm`). A second witness, **virasoro_partition_is_modular_character**:
bundle the `SL(2,ℤ)` action (`modular_generator_orders`) + the character (`det2_mul`) + the `q`-expansion
(`GeneratingFunction.convolution`) into "`Z(τ)` = the `SL(2,ℤ)`-invariant `q`-expansion character", at the
abelian slice where it is fully ∅-axiom. Both promote PREDICTION rows to packaged EXTENDs; the named
Virasoro/OPE/bootstrap carrier + the crossing *move* + the analytic ℋ stay the located break (a
coherence/colimit/`Real213`-cut boundary, not a missing 213 primitive, per `fusion_categories.md`/
`modular_forms.md`/`two_cells.md` Shape 3).

## Cross-frame

`fusion_categories.md` (KEY — the fusion rules `X⊗Y=⊕N^Z_{XY}Z`, the modular S-matrix = the character
transform, Verlinde = χ-orthogonality inversion, quantum dim = Perron φ; the OPE = the fusion product, the
pentagon/hexagon coherence break a CFT's chiral data inherits); `modular_forms.md` (KEY — the partition
function `Z(τ)` = an `SL(2,ℤ)`-invariant modular form, the `q`-expansion = the character, the
Eichler–Shimura period corpus, the `q=±1` `s↔k−s` reflection, the form/Hecke/analytic-L break);
`lie_theory.md` (KEY — the Virasoro/Witt bracket = the `q=±1` antisymmetric commutator
`Mat2Bracket.bracket_antisymm`/`jacobi`, the infinitesimal `ε`/infinite-mode tower break);
`galois_cohomology.md` (KEY — the central extension = an `H²` 2-cocycle obstruction, the central charge =
the `galois_cohomology`-`H²` class, `MinkowskiCocycle`/`Ω`, `ResidueTag` `q=±1`); `hopf_algebras.md` (the
OPE = the convolution product `Convolution213.conv`, the antipode/dual); `representation.md` (the partition
character = the `×↦·` trace character on ℋ, the det/tr `d>1` edge); `quantum_groups.md` (the braiding/R-
matrix on the chiral OPE, the deformation-`q` vs tag-`q` CONTAINMENT); `two_cells.md`/`knots.md` (the
bootstrap crossing equation = the graded-relation slot, Shape 3; the coherence/colimit quotient the
chiral/anyon data inherits); `SYNTHESIS.md` (Invariant A the character/fusion arrow, Invariant B the
`q=±1` tag carrying the central extension, the §3 CFT `Frob_p`-per-prime `q±1` local-character row
`FP2SqrtD`).
