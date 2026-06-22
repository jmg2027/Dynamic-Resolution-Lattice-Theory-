# Decomposition: characteristic classes / Chern–Weil theory

*213-decomposition of "the Chern classes `c_i(E)` of a complex vector bundle, the Chern–Weil
homomorphism (curvature → cohomology via invariant polynomials), the total Chern class
`c(E)=det(I+Ω/2πi)`, the Chern character `ch(E)=tr exp(Ω)`, Euler/Pontryagin/Stiefel–Whitney
classes, the splitting principle, naturality under pullback, and Gauss–Bonnet–Chern `∫e(TM)=χ`",
per `../README.md` (model v7.1) and `../SYNTHESIS.md` (the two invariants + the `q=±1` spine + the
`×↦·` det-character read four ways + the det/tr = e₁/e₂ Vieta resolution). A **fresh** field,
LEVERAGE phase — the bar is PREDICTION/REVELATION. Sits directly atop `curvature.md` (the
loop-reading's `q=±1` residue = curvature, the `det` Noether-invariant holonomy), `de_rham.md`
(`H*_dR = ker d/im d`, the residue landed in cohomology, the telescope), `determinant.md`/
`representation.md`/`spectral.md` (the det/tr character, dissolved as `e₁`/`e₂` Vieta), and
`hyperbolic_geometry.md` (Gauss–Bonnet built discretely as `DiscreteGaussBonnet`).*

The thesis under test: **a characteristic class is the calculus's `×↦·` determinant-character OF the
curvature, landed in cohomology.** Chern–Weil takes an invariant polynomial of the curvature 2-form
`Ω` and produces a cohomology class; the total Chern class `c(E)=det(I+Ω)` is the
characteristic-polynomial / Cayley–Hamilton reading of `Ω`, so the individual Chern classes `c_i` are
the **elementary symmetric functions of the curvature eigenvalues** — exactly the `tr=e₁=c₁`,
`det=e₂=c₂` of `Mat2Spectrum.det_tr_split_is_e1_e2`, the SYNTHESIS det/tr = e₁/e₂ finding generalized
from a single matrix to a bundle's curvature. The Chern character `ch(E)=tr exp(Ω)` is the `×↦+`
additive character (exp/log, additive on `⊕`). The splitting principle = diagonalize = the spectral
reading. Naturality under pullback = the Lens-morphism 2-cell (`view_factors_through_morphism`).
Euler class + Gauss–Bonnet–Chern = `curvature.md`/`hyperbolic_geometry.md`'s built
`DiscreteGaussBonnet` (curvature integral = Euler characteristic). **No new primitive** — it is the
det/tr = e_i character read on curvature, landed in de Rham cohomology.

## The decomposition (C / Reading / Residue)

- **Construction `C` — the curvature 2-form `Ω`, which is `curvature.md`'s holonomy-loop residue;
  nothing new.** A characteristic class introduces no construction of its own. Its operand is the
  **curvature** of a connection — and `curvature.md` already decomposed curvature as the `q=±1`
  residue of the loop-composition reading `L_loop` on the `Mat2` ×-construction
  (`HolonomyLattice.holonomy`, the `List Mat2` of transitions folded by `holonomy_append`; curvature
  = the deficit by which `holonomy w ≠ I`, born with the sign-fold `S`, `first_loop_is_the_fold`). On
  the abstract-index side the curvature is the Riemann tensor `riemUp` of `TensorCalculus.lean`
  (`R^l_{ijk}`, with both first-Bianchi identities `riem_bianchi1`, the `q=−1` cyclic cancellation).
  So the operand of Chern–Weil is the **same curvature `C`** the geometry cluster already carries —
  a `Mat2`/`riemUp` curvature, not a new bundle object. (The classical packaging — a complex vector
  bundle `E`, its connection `∇`, the smooth `Ω∈Ω²(M;End E)` — is the `Real213`-cut residue; see
  Residue.)

- **Reading `L_char` — an `Aut`-invariant polynomial of the curvature, i.e. the character of `Ω`.**
  Chern–Weil's defining move: read the curvature through an **invariant polynomial** — a readout that
  is unchanged under the gauge/conjugation action (`P(gΩg⁻¹)=P(Ω)`), i.e. an `Aut`-invariant readout
  = `noether.md`/`curvature.md`'s `q=+1` conserved character. The two canonical invariant polynomials
  are precisely the calculus's two characters:
  - **`det(I+Ω)` — the multiplicative `×↦·` character** (`determinant.md`'s `det2_mul` arrow). Its
    coefficients in the formal parameter are the **elementary symmetric functions `e_i` of the
    curvature eigenvalues** = the **Chern classes `c_i`**. This is *literally* the Vieta reading of
    the characteristic polynomial (`Mat2CayleyHamilton.cayley_hamilton`, `Mat2Spectrum.det_eq_e2`/
    `tr_eq_e1`): `c₁ = tr Ω = e₁`, `c₂ = det Ω = e₂`, in general `c_i = e_i(spectrum Ω)`.
  - **`tr exp(Ω)` — the additive `×↦+` character** (`exponential.md`'s exp, the `vp_mul`/`+↦×`
    twin). This is the **Chern character `ch(E)`**, additive on Whitney sums
    `ch(E⊕F)=ch(E)+ch(F)` (the `×↦+` direction) and multiplicative on tensor products — the additive
    twin of the multiplicative `c`.

  So `L_char` is the README's character mode, *bidirectional*: `det` (multiplicative, → `c_i`) and
  `tr exp` (additive, → `ch`) are the two directions of one character arrow read on `Ω`. The
  **splitting principle** ("pretend `Ω` is diagonal, `Ω = diag(x₁,…,x_d)`, so `c(E)=Π(1+x_i)`,
  `ch(E)=Σ exp(x_i)`") is exactly the **spectral reading** (`spectral.md`): work with the eigenvalues
  `x_i`, then re-symmetrize — the `e_i`/power-sum bookkeeping the Vieta theorems certify.

- **Residue — two strata, tagged `q=±1`, exactly the `curvature.md`/`de_rham.md` pattern.**
  1. *The cohomology landing*: the character of `Ω` is not a number — it lands in **de Rham
     cohomology** `H*_dR = ker d/im d` (`de_rham.md`'s `Residue(L↑,C)`). The Chern–Weil theorem's
     two halves — (a) the class is *closed* (`dP(Ω)=0`, by the Bianchi identity `riem_bianchi1`/
     `dΩ+[A,Ω]=0`) and (b) *independent of the connection* (the difference of two is *exact*) — are
     exactly "forced (closed) but determined only up to one degree down (exact)", the `q=±1` residue
     read in cohomology. So a characteristic class = the character of `Ω` MODULO the de Rham residue.
  2. *The smooth `Real213`-cut residue*: the named complex vector bundle `E`, the smooth connection
     `∇`, the curvature 2-form `Ω∈Ω²(M;End E)`, the `2πi` normalization, and the de Rham comparison
     iso `H*_dR ≅ H*_sing(·;ℂ)` are the `Real213`-cut / smooth-tensor residue — reached by no finite
     resolution, the SAME boundary `curvature.md` (no smooth metric/transported field) and
     `de_rham.md` (no smooth form bundle, no de Rham iso) already located. The named
     `Chern`/`ChernWeil`/`VectorBundle`/`Pontryagin`/`StiefelWhitney`/`eulerClass` objects are
     **ABSENT** (grep-confirmed below) — predicted-not-built.

## Re-seeing — ⟨C | L_char⟩ ⊕ Residue

```
   the curvature 2-form Ω         =  curvature.md's holonomy-loop q=±1 residue       (first_loop_is_the_fold; riemUp)
   an invariant polynomial of Ω   =  L_char = the Aut-invariant character of Ω        (noether's q=+1, det_holonomy_eq_one)
   the Chern–Weil homomorphism    =  read Ω through L_char, land in H*_dR             (de_rham.md's Residue(L↑,C))
   total Chern class c(E)=det(I+Ω) =  the ×↦· det-character / char-poly of Ω          (det2_mul; cayley_hamilton)
   the Chern classes c_i           =  e_i(spectrum Ω), elementary symmetric functions  (det_tr_split_is_e1_e2 GENERALIZED)
       c₁ = tr Ω = e₁              =  the additive coefficient of the char poly         (Mat2Spectrum.tr_eq_e1)
       c₂ = det Ω = e₂            =  the multiplicative coefficient                     (Mat2Spectrum.det_eq_e2)
   the Chern character ch(E)=tr exp(Ω) = the ×↦+ additive character (additive on ⊕)     (exponential.md exp; vp_mul twin)
   the splitting principle        =  diagonalize Ω = the spectral reading              (spectral.md; the x_i eigenvalues)
   "c is closed, dP(Ω)=0"         =  Bianchi identity = the q=−1 cyclic cancellation    (riem_bianchi1; dsq_zero)
   "c is connection-independent"  =  the difference is exact = the q=±1 residue mod im d (de_rham residue)
   naturality  c(f*E)=f* c(E)     =  the Lens-morphism 2-cell  M.view = h∘L.view        (view_factors_through_morphism)
   the Euler class e(TM)          =  the loop/orientation residue of the curvature        (curvature.md, the q=−1 deficit)
   Gauss–Bonnet–Chern ∫e(TM)=χ    =  the curvature–Euler telescope Σκ = 2χ              (gauss_bonnet_Kmn, totalCurv_eq)
```

The single move: **characteristic classes are not a new edifice** — they are the `×↦·`/`×↦+`
character arrow (`determinant.md`/`exponential.md`/`spectral.md`) read on `curvature.md`'s curvature,
landed in `de_rham.md`'s cohomology residue. The Chern classes are the elementary symmetric functions
of the curvature spectrum — the SAME `e_i` the corpus proved are `tr`/`det`, now read off `Ω` instead
of a single `Mat2`.

## Re-seeing table (the unification)

| classical characteristic-class object | the calculus's reading | repo status |
|---|---|---|
| the curvature 2-form `Ω` (Chern–Weil's input) | `curvature.md`'s holonomy-loop `q=±1` residue / `riemUp` | **BUILT** (`first_loop_is_the_fold`, `riemUp`, `riem_bianchi1`) |
| invariant polynomial of `Ω` (gauge-invariant) | `L_char` = the `Aut`-invariant `q=+1` character | **BUILT** as the character (`det_holonomy_eq_one`, `det2_mul`) |
| total Chern class `c(E)=det(I+Ω)` | the `×↦·` det / char-poly reading of `Ω` | **BUILT at the matrix level** (`cayley_hamilton`, `det2_mul`) |
| ★ the Chern classes `c_i = e_i(spectrum Ω)` | elementary symmetric functions of the spectrum = the det/tr = e₁/e₂ Vieta, generalized | **BUILT for `e₁,e₂`** (`tr_eq_e1`, `det_eq_e2`, `det_tr_split_is_e1_e2`); `d>2`/`e_{>2}` structural |
| the Chern character `ch(E)=tr exp(Ω)`, additive on `⊕` | the `×↦+` additive character (exp/log) | exp character **BUILT** (`vp_mul`); `tr exp(Ω)` on a bundle structural |
| the splitting principle (diagonalize `Ω`) | the spectral reading, the `x_i` eigenvalues | **BUILT** (`disc_eq_gap_squared`, `spectrum_roots`) |
| `c` closed (`dP(Ω)=0`) | Bianchi = `q=−1` cyclic cancellation | **BUILT** (`riem_bianchi1`, `dsq_zero_universal_delta4`) |
| `c` connection-independent (difference exact) | the `q=±1` residue mod `im d` in `H*_dR` | **BUILT** (de Rham residue, `reduced_betti_d4_contractible`) |
| naturality `c(f*E)=f*c(E)` (pullback) | the Lens-morphism 2-cell `M.view=h∘L.view` | **BUILT** (`view_factors_through_morphism`, 3/0) |
| Euler class `e(TM)` | the loop/orientation residue of the curvature | **BUILT discretely** (the `q=−1` deficit, `first_loop_is_the_fold`) |
| Gauss–Bonnet–Chern `∫e(TM)=χ` | the curvature–Euler telescope `Σκ=2χ=2(1−b₁)` | **BUILT discretely** (`gauss_bonnet_Kmn`, `totalCurv_eq`, `simplex_face_euler_zero`) |
| Pontryagin `p_i` (real), Stiefel–Whitney `w_i` (mod 2) | `e_i` of `Ω∧Ω` (real char) / the order-2 parity char of `Ω` (`{±1}`) | structural: `e_i` reading + `parity.md`'s `L₂`; no named object |
| the smooth bundle `E`/`∇`/`Ω∈Ω²(M;End E)`/`2πi`/de Rham iso | the `Real213`-cut smooth residue | **ABSENT** (the located break) |

## Revelation (collapse + forcing + the q=±1 spine)

**Collapse — the Chern classes ARE the e_i Vieta coefficients of the curvature spectrum; this is the
NEW datum.** `spectral.md`/`representation.md` proved (via `det_tr_split_is_e1_e2`) that for a single
`Mat2`, `tr=e₁` (additive `×↦+`) and `det=e₂` (multiplicative `×↦·`) are the two elementary symmetric
functions of one spectrum — the det/tr "split" dissolved into Vieta. **Characteristic classes are
that theorem read on the curvature instead of on a single matrix**: the total Chern class
`c(E)=det(I+Ω)` is the characteristic polynomial of `Ω`, so its coefficients `c_i = e_i(spectrum Ω)`
are *exactly the same elementary symmetric functions*, with `c₁=tr Ω=e₁` and `c₂=det Ω=e₂` being the
literal `tr_eq_e1`/`det_eq_e2`. The Chern character `ch(E)=tr exp(Ω)` is the **additive `×↦+` twin**
(the power sums of the spectrum, additive on `⊕` exactly as `exp` is additive under the `×↦+` arrow,
`vp_mul`). So `determinant.md` (the det character), `representation.md`/`spectral.md` (det/tr=e₁/e₂),
`exponential.md` (the exp/`×↦+` twin), `curvature.md` (the curvature `Ω`), and `de_rham.md` (the
cohomology landing) **are all characteristic-class theory the whole time** — the `c_i` are the
det/tr=e₁/e₂ finding generalized from a matrix to a bundle's curvature, landed in cohomology. This is
the new contribution beyond re-skinning `curvature.md`/`determinant.md`.

**Forcing — multiplicativity, additivity, and naturality are FORCED, not chosen.**
- `c(E⊕F)=c(E)·c(F)` (Whitney) is *forced* by `det` being the `×↦·` character: `det(I+Ω_E⊕Ω_F) =
  det(I+Ω_E)·det(I+Ω_F)` is `det2_mul` on the block-diagonal curvature — the same bare-`ring`
  multiplicativity the corpus proves, not an added axiom.
- `ch(E⊕F)=ch(E)+ch(F)` is *forced* by `tr exp` being the `×↦+` character: trace of `exp` of a
  block-diagonal sum splits additively, the `exponential.md` `+↦×`/`×↦+` arrow.
- `c(f*E)=f*c(E)` (naturality under pullback) is *forced* by the Lens-morphism 2-cell: a pullback is
  a reading-of-a-reading, and `view_factors_through_morphism` (`M.view = h∘L.view`, ∅-axiom) is the
  naturality triangle term-for-term — the characteristic class commutes with pullback because the
  character commutes with the morphism (`two_cells.md`: readings form a 2-category).
- closedness `dP(Ω)=0` is *forced* by the Bianchi identity `riem_bianchi1` — the `q=−1` cyclic
  cancellation, the same mechanism as `dsq_zero`/`jacobi`.

**The q=±1 spine (`SYNTHESIS.md` §3) on the curvature.** The Euler class / Gauss–Bonnet–Chern is the
spine's geometric pole made an integral identity:
- `c(E)=det(I+Ω)` is the `q=±1` det-character of the loop-residue: flat (curvature 0, `q=+1`
  conserved `det_holonomy_eq_one`) ⟹ trivial classes; curved (`q=−1` deficit
  `first_loop_is_the_fold`) ⟹ nontrivial classes — the characteristic class detects exactly the
  `q=−1` holonomy deficit `curvature.md` named.
- **Gauss–Bonnet–Chern `∫e(TM)=χ` = the curvature–Euler telescope** `Σκ=2χ=2(1−b₁)`
  (`gauss_bonnet_Kmn`, `totalCurv_eq`) already built discretely in `curvature.md`/
  `hyperbolic_geometry.md`: the Euler class integrated against the fundamental cycle = the Euler
  characteristic, the curvature (`q=−1` loop residue) integrated = the topology (`b₁`, the homology
  residue) — *one* `q=±1` residue read as curvature on one side and as `χ` on the other. The repo
  also has `simplex_face_euler_zero` (`FaceTerms.lean`), the alternating face-count vanishing = the
  `L(id)=χ` Euler cancellation underneath.

So characteristic classes = (the `×↦·` det-character OF the curvature = the `e_i` Vieta coefficients =
`c_i`, generalizing det/tr=e₁/e₂) + (the Chern character = the `×↦+` additive character) +
(Gauss–Bonnet–Chern = the built curvature–Euler telescope) — **no new primitive**.

## VALIDATE verdict — **EXTEND** (decisive consolidation: c_i = the e_i Vieta of curvature; one PREDICTION leg; one located break)

No new primitive, no break in the interior. Characteristic classes slot entirely into the v7.1 model:
`C` = the curvature `Ω` (`curvature.md`'s loop-residue / `riemUp`, carrying direction/`q=±1` +
fold-height), `L_char` = the bidirectional character (det → `c_i`, `tr exp` → `ch`) read as an
`Aut`-invariant of `Ω`, `Residue` = the de Rham cohomology landing tagged `q=±1` plus the smooth
`Real213`-cut bundle. It is a **decisive consolidation**: the det/tr = e₁/e₂ Vieta resolution
(`spectral.md`/`representation.md`) is now seen as the *defining mechanism* of an entire field — the
Chern classes ARE the elementary symmetric functions of the curvature spectrum, and the Chern
character is their additive `×↦+` twin.

- **PREDICTION leg (honest):** the calculus *predicts* the form of the full Chern–Weil machine —
  `c_i = e_i(spectrum Ω)` (forced by Vieta), `c(E⊕F)=c(E)c(F)` (forced by `det2_mul`),
  `ch(E⊕F)=ch(E)+ch(F)` (forced by `tr exp` = `×↦+`), naturality (forced by
  `view_factors_through_morphism`), closedness (forced by `riem_bianchi1`), Gauss–Bonnet–Chern
  (= the built telescope). The matrix-level e₁/e₂ Vieta is **closed**; `e_{>2}` for `d>2` and the
  power-sum bookkeeping of `ch` are grounded by analogy to the closed `Mat2` case (`Mat2` is 2×2, so
  only `e₁,e₂` are directly built), not independently closed at general `d`.

- **Located break (the `de_rham.md`/`curvature.md` spirit):** the **smooth characteristic-class
  object** — a complex `VectorBundle E`, a `Connection ∇`, the curvature `Ω∈Ω²(M;End E)`, the `2πi`
  normalization, `ChernClass`/`ChernWeil`/`ChernCharacter`/`Pontryagin`/`StiefelWhitney`/`eulerClass`
  as named objects, and the de Rham comparison iso `H*_dR ≅ H*_sing(·;ℂ)` that makes the class an
  *integer/topological* invariant — is ABSENT (grep-confirmed). The discrete parallel theory is the
  worked instance; the smooth bundle + its curvature 2-form + the de Rham iso is the `Real213`-cut /
  smooth-tensor residue, exactly the boundary `curvature.md` (no smooth metric / transported field)
  and `de_rham.md` (no smooth form bundle, no de Rham iso) already located. This is the same located
  break, not a new one.

## Verified Lean anchors (file:line:theorem) — all grep-confirmed, scans from repo root

**★ The Chern classes = the e_i Vieta coefficients of the curvature spectrum (the central NEW
collapse — generalizing det/tr = e₁/e₂):**
- `lean/E213/Lib/Math/NumberSystems/Real213/Mat2/Mat2Spectrum.lean:103` `det_eq_e2`
  (`det M = μ·ν = e₂`, the multiplicative `×↦·` coefficient = `c₂`); `:115` `tr_eq_e1`
  (`tr M = μ+ν = e₁`, the additive `×↦+` coefficient = `c₁`); `:204` `det_tr_split_is_e1_e2`
  (both + `disc=(μ−ν)²` + `spectrum_roots`, the det/tr split dissolved as Vieta); `:167`
  `disc_eq_gap_squared`; `:186` `spectrum_roots`. **PURE (9/0).**
- `lean/E213/Lib/Math/NumberSystems/Real213/Mat2/Mat2CayleyHamilton.lean:37` `cayley_hamilton`
  (`M²=tr·M−det·I` = the characteristic-polynomial reading `c(E)=det(I+Ω)` specializes); `:50`
  `char_poly_discriminant`; `:57` `dial_is_char_discriminant`. **PURE (4/0).**

**The curvature `Ω` = Chern–Weil's input (per `curvature.md`):**
- `lean/E213/Lib/Math/Geometry/TensorCalculus.lean:135` `riemUp` (the abstract-index Riemann
  curvature `R^l_{ijk}`); `:163` `ricciFromRiem`; `:186` `riem_bianchi1` (the Bianchi identity = the
  `q=−1` cyclic cancellation = "`dP(Ω)=0` closed"); `:281` `scalar_einstein`. **PURE (23/0).**
- `lean/E213/Lib/Math/NumberSystems/Real213/ModularGeometry/HolonomyLattice.lean:108`
  `holonomy_append` (the loop-fold = functorial transport); `:123` `det_mul`; `:136`
  `det_holonomy_eq_one` (flat = `q=+1` conserved character `det=1` = the invariant-polynomial pole);
  `:313` `first_loop_is_the_fold` (`holonomy[S,S]=−I≠I`, the `q=−1` curvature deficit the Euler class
  detects); `:292` `positive_loop_trivial`. **PURE (26/0).**

**The det / `×↦·` character (per `determinant.md`) and the `×↦+` exp twin (per `exponential.md`):**
- `lean/E213/Lib/Math/NumberSystems/Real213/Markov/SternBrocotMarkov.lean:104` `det2_mul`
  (`det(MN)=det M·det N`, the `×↦·` arrow = `c(E⊕F)=c(E)c(F)` Whitney). (per `determinant.md`)
- `lean/E213/Lib/Math/NumberTheory/PrimeValuation.lean:96` `vp_mul`
  (`vp(ab)=vp a+vp b`, the `×↦+` additive character = `ch(E⊕F)=ch(E)+ch(F)` the Chern character's
  additivity). **PURE (7/0).** (also `Meta/Nat/VpMul.lean:165`)

**Naturality under pullback = the Lens-morphism 2-cell (per `two_cells.md`):**
- `lean/E213/Lens/Compose/Morphism.lean:37` `view_factors_through_morphism`
  (`M.view r = h(L.view r)`, the naturality triangle term-for-term = `c(f*E)=f*c(E)`). **PURE (3/0).**

**Euler class + Gauss–Bonnet–Chern = the built curvature–Euler telescope (per `curvature.md`/
`hyperbolic_geometry.md`):**
- `lean/E213/Lib/Math/Geometry/DiscreteCurvature/DiscreteGaussBonnet.lean:42` `gauss_bonnet_Kmn`
  (`totalVertexCurv = 2·eulerChar`, the discrete `Σκ=2χ` = `∫e(TM)=χ`); `:53` `totalCurv_eq`
  (`= 2−2·cyclomatic = 2−2b₁`, curvature residue = homology residue). **PURE (12/0).**
- `lean/E213/Lib/Physics/Simplex/FaceTerms.lean:125` `simplex_face_euler_zero` (the alternating
  face-count vanishing = the `L(id)=χ` Euler cancellation under Gauss–Bonnet). (grep-confirmed)

**The `q=±1` residue tag (the spine, per `SYNTHESIS.md` §3):**
- `lean/E213/Lib/Math/Foundations/ResidueTag.lean:228` `residue_tag_two_poles`; `:86`
  `multiplier_unimodular`; `:180` `golden_is_converge`. **PURE (55/0).**

**The cohomology landing = the de Rham residue (per `de_rham.md`):**
- `lean/E213/Lib/Math/Cohomology/Examples/BettiKernel.lean` `reduced_betti_d4_contractible`,
  `kerSizeDelta` (`H* = ker δ/im δ`, the residue the characteristic class lands in). (per `de_rham.md`)
- `lean/E213/Lib/Math/Cohomology/Delta/V4Capstone.lean` `dsq_zero_universal_delta4` (the `q=±1`
  cancellation = closedness). (per `de_rham.md`)

**Scan tallies (`python3 tools/scan_axioms.py E213.<module>`, from repo root, this session):**
`Mat2Spectrum` 9/0 · `Mat2CayleyHamilton` 4/0 · `TensorCalculus` 23/0 · `HolonomyLattice` 26/0 ·
`DiscreteGaussBonnet` 12/0 · `Morphism` 3/0 · `PrimeValuation` 7/0 · `ResidueTag` 55/0. All PURE,
0 DIRTY.

## Dropped / flagged (honest)

- **The named characteristic-class / vector-bundle objects — ABSENT, predicted-not-built.** grep over
  `lean/E213` (case-insensitive) for `Chern`/`characteristic_class`/`ChernWeil`/`Chern_Weil`/
  `ChernClass`/`ChernCharacter`/`Pontryagin`/`StiefelWhitney`/`Euler_class`/`eulerClass`/
  `VectorBundle`/`vectorBundle`/`connection.*bundle`/`principal.bundle`/`line.bundle`/
  `tangent.bundle`/`pullback.bundle`/`splitting.principle`/`Todd.class` returns **no Lean object**.
  The only superficial hits are `Probability/.../Chernoff*` (a probability inequality, not Chern
  classes) and `FreeReduction.lean:248` "Headline bundle" (a theorem-bundle doc comment, not a fiber
  bundle). The named `ChernClass`/`ChernWeil`/`VectorBundle`/`Pontryagin`/`StiefelWhitney`/
  `eulerClass` objects are confirmed absent — the located break, the `Real213`-cut smooth-bundle
  residue (the same boundary `curvature.md`/`de_rham.md` locate).
- **`c_i = e_i` is grounded for `e₁, e₂` only (the `Mat2` 2×2 ceiling).** `det_tr_split_is_e1_e2`
  closes `c₁=tr=e₁` and `c₂=det=e₂` because `Mat2` is 2×2 (only two eigenvalues, two symmetric
  functions). The general `c_i = e_i` for `d>2` (a `d×d` curvature with `d` Chern classes) is grounded
  by analogy to the closed `Mat2` case — the same elementary-symmetric-function reading, not
  independently closed at general `d`. Stated as the open leg, not asserted.
- **The Chern character `ch(E)=tr exp(Ω)` is grounded only via its two component characters.** The
  exp `×↦+` arrow is built (`vp_mul`) and the trace is built (`Mat2Spectrum.tr_eq_e1`), and their
  additivity-on-`⊕` is the `×↦+` character; but `tr exp(Ω)` as a single object on a bundle (the power
  series `Σ tr Ω^k/k!`) is structural, not a named theorem. Cited scope-honest.
- **Pontryagin / Stiefel–Whitney have no named object.** `p_i = e_i` of `Ω∧Ω` (the real char) and
  `w_i` = the order-2 parity character (`parity.md`'s `L₂` into `{±1}` / mod-2 reduction) are
  structural readings of the same `e_i`/`L₂` machinery; no `Pontryagin`/`StiefelWhitney` Lean object
  exists. Not cited as anchors; flagged as the `e_i`/parity-character reading, predicted-not-built.
- **The smooth Gauss–Bonnet–Chern `∫e(TM)=χ` with the `2πi` normalization** — the `2πi` is a
  `Real213`-cut; only the discrete `Σκ=2χ` (integer-valued, `gauss_bonnet_Kmn`) is built. Cited
  scope-honest, exactly as `hyperbolic_geometry.md` flags the smooth `∫K=2πχ`.
- **Verified buildable witness (no new claim asserted):** the load-bearing collapse is already a set
  of `decide`/`ring_intZ` theorems (`det_tr_split_is_e1_e2`, `cayley_hamilton`, scanned PURE this
  session). A clean additional witness would be a `Mat2`-level "total Chern class of a block sum
  factors" — `det(I+Ω_E⊕Ω_F) = det(I+Ω_E)·det(I+Ω_F)` — which is `det2_mul` on the block-diagonal
  curvature (already PURE); no new count-inequality is proposed beyond the grep-confirmed,
  scanned-PURE anchors above.
```
