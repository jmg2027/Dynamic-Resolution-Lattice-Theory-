# The 213 Decomposition Calculus — capstone synthesis

**Status**: Tier-1 capstone of the decomposition cluster (`README.md` = the technique + per-field
log; `practice/*.md` = the 52 worked decompositions; `frontiers/decomposition_calculus.md` = the open
edge). This document does not add a decomposition — it makes the whole corpus legible as one statement.
Every Lean name cited below was grep-verified to exist in `lean/E213/`; predictions with no closed Lean
witness are marked **[prose]**.

---

## 1. The thesis (one paragraph)

The calculus writes every mathematical object in one normal form —

```
   OBJECT = ⟨ C | L ⟩ ⊕ Residue(L, C)
```

— a **Construction** `C` (the bare distinguishing-history: what was distinguished from what, iterated),
read through a **Lens** `L` (which feature you project to — count, order, difference, divisibility,
sign), leaving a **Residue** (what `L` forces but cannot capture). A theorem is a property `P(⟨C|L⟩)`;
the payoff is *collapse* — two superficially different theorems shown to share `(C, L)` and so be one.
The Lean encoding (`Raw`, `Lens`, `Lens.view = Raw.fold`) is the faithfulness-check, not the
deliverable. The headline finding, after **52 worked decompositions across ~52 fields with no interior
break**, is that this wide front does not need 52 different ideas: it converges on a **small invariant
set** — one *character arrow* and one *q=±1 residue tag*, read across four axes — and that invariant
set is itself Lean-anchored, not merely asserted. The residue is the **proven remainder** the
distinguishing always leaves (`FlatOntology.self_covering_closure`: faithful yet never total), not a
substrate the objects are built on top of.

---

## 2. The invariant set — the complete inventory

The 52 decompositions converge on **two load-bearing invariants** plus **one structured frame** (the
read-off axes of `C` and the parameters of `L`). Each is cashed by a verified Lean theorem.

### Invariant A — the character arrow `×↦·` / `×↦+`
A *character* is a construction-preserving reading whose readout is itself a number-construction; its
defining law is that it carries the multiplicative structure to a (multiplicative or additive) readout.
The single arrow is proven to be the *same* arrow across the fields below.

| Mode | Lean witness | Fields instantiating |
|---|---|---|
| `×↦·` (multiplicative) | `det2_mul`, `legendre_mul`, `det_holonomy_eq_one` | parity, determinant, Legendre/QR, Noether, curvature/holonomy, representation (det-character), probability independence |
| `×↦+` (additive / log) | `vp_mul`, `vp_separation` | prime-factorization, entropy (`−log`), KL/Fisher, Fourier/ζ-Euler character, tropical `(max,+)` |
| spectral split of one character | `Mat2Spectrum.tr_eq_e1`, `det_eq_e2`, `det_tr_split_is_e1_e2` | spectral theory, representation `det`/`tr`, Lie `tr_bracket_zero` |

The deepest single unity: the `det` / `×↦·` character is read **four ways** — scalar (`determinant`),
`Aut`-invariant (`noether`, `det_holonomy_eq_one`), around a loop (`curvature`, holonomy), down the
height (`homology`, `∂`) — and the additive twin `×↦+` spans seven fields. The det/tr "opposition" is
**dissolved** as a Lean theorem: `tr = e₁`, `det = e₂` are the two Vieta coefficients of one spectrum
(`Mat2CayleyHamilton.cayley_hamilton`, `Mat2Spectrum.det_tr_split_is_e1_e2`).

### Invariant B — the q=±1 residue tag (escape / converge)
A residue is the reading's self-application surplus; it carries a **unimodular multiplier bit** `q=±1`.
This is the deepest collapse and is now **one formal object**: `ResidueTag` (`inductive escape | converge`)
+ `multiplier : ResidueTag → Int` (∓1, with `multiplier_unimodular`), capstone
`ResidueTag.residue_tag_two_poles`. See §3 for the full spine.

### The frame — the read-off axes (`C`) and the `L`-parameters
These are not extra invariants; they are the coordinates the two invariants are read across. Each pays
by collapse + forcing, and each is grounded.

| Axis | What it reads out | Lean grounding | Fields |
|---|---|---|---|
| direction / swap-bit (`q=±1`) | sign, orientation, antisymmetry | `Mat2Bracket.bracket_antisymm`, `dsq_zero_universal_delta4` | integers, determinant, homology (`∂²=0`), Lie bracket, knot/loop |
| fold-height (bidirectional) | dimension, degree, pole-order, `∂`/`d` | `Lambek.isPart_wf`, `dsq_zero_universal_delta4` | dimension, homology, de Rham, ordinals |
| resolution **+ base** | discrete `Δ` vs `h→0` `∫`; which valuation is "adjacent" | `ContinuityOpenSet.*`, `gauss_conservation_telescope` | derivative, integration, continuity, topology, p-adics |
| iteration-character | nilpotent `∂` / idempotent `clo` / growing `S` | `MuNuMirror.succ_not_idempotent`, `max_idem`, `FenchelMoreau.biconj_idempotent` | homology, closure/Galois, free corner, tropical |
| weight | value-weighted count → measure/expectation | `mass_conv`, `momentNum_conv`, `klBitsDyadic` | probability, measure, entropy, information geometry |
| character-mode | the arrow of Invariant A (bidirectional) | (Invariant A row) | (Invariant A fields) |

The structural lesson the frame forces: **readings form a 2-category.** They compose in series (entropy
= weight∘character), form composition-closed families (`Aut`, groups), form adjoint/order-reversing
pairs (Galois, `FenchelMoreau`), and admit 2-cells = natural transformations
(`view_factors_through_morphism`, `IsLensMorphism`, `refines_of_morphism`, `lensIso_iff_kernel_eq`).

---

## 3. The q=±1 spine (the single deepest pattern)

One residue, two signs. `q=−1` = **escape** (self-pointing reading whose surplus oscillates *outside*
every image — fixed-point-free diagonal); `q=+1` = **converge** (the surplus asymptotes *toward* a fixed
point / closure). Both poles are delegated to a proven kernel.

| `q=−1` escape (delegates to `FlatOntology.object1_not_surjective` / `OneDiagonal.no_surjection_of_fixedpointfree`) | `q=+1` converge (delegates to `BanachFixedPointModulated.banach_fixed_point_modulated`) |
|---|---|
| Cantor diagonal (`cardinality`) | golden ratio φ (`cassini_law_one_at_two_multipliers`, `golden_is_converge`) |
| Gödel incompleteness (`godel`) | Gaussian / CLT fixed point (`ConvolveRescaleContraction.Φ_contraction`) |
| measure: non-measurable / Vitali / Banach–Tarski (`measure`) | ODE flow / Picard contraction (`differential_equations`) |
| Löwenheim–Skolem (`model_theory`) | ergodic invariant measure (`ergodic_theory`) |
| the quintic / A₅-simplicity `[A₅,A₅]=A₅` (`galois_correspondence`, `a5_order`) | solvable groups: derived series terminates (`DerivedSeries.derived_S`) |
| complex/elliptic spectrum `disc<0` (`spectral`, `quantum_mechanics`) | real symmetric spectrum `disc≥0` (`Mat2SymmetricSpectrum.disc_symmetric_nonneg`) |
| non-contractible loop `holonomy[S,S]=−I` (`fundamental_group.first_loop_is_the_fold`) | connected-graph Laplacian kernel `λ₀=0` (`GraphLaplacian.closed_const`) |
| uncertainty: bracket obstructs common eigenbasis (`quantum_mechanics`, `Mat2Bracket`) | completeness `⊢⟺⊨` = `view=fold` initiality (`raw_initial`) |
| Löwenheim–Skolem count diagonal; H^{>0} obstruction (`sheaf_theory`) | compactness = finiteness collapse (`heineBorel`); Carathéodory `clo` (`cara_gc`) |

The formal tag is **honestly asymmetric**: `escape_residue_outside` is a *negative* theorem (universal
negation), `converge_residue_fixed` a *positive existence* theorem; they are not collapsed into one `Eq`
(that would need excluded middle). `residue_tag_two_poles` bundles them under the shared `±1` column.

---

## 4. The Lean-grounded census

Grep-verified. Counts (`N/0`) are the notes' stated PURE/DIRTY tallies for the named module.

### (a) Fully ∅-axiom Lean-closed / grounded
| Module | Load-bearing theorem(s) | Role |
|---|---|---|
| `Lib/Math/Foundations/ResidueTag.lean` | `residue_tag_two_poles`, `multiplier_unimodular`, `golden_is_converge` | the q=±1 tag (Invariant B) |
| `…/Real213/Mat2/Mat2Spectrum.lean` | `tr_eq_e1`, `det_eq_e2`, `det_tr_split_is_e1_e2`, `disc_eq_gap_squared` | det/tr dissolved as Vieta |
| `…/Mat2/Mat2CayleyHamilton.lean` | `cayley_hamilton`, `char_poly_discriminant`, `dial_is_char_discriminant` | spectrum exists ⟹ split |
| `…/Mat2/Mat2Bracket.lean` | `bracket_antisymm`, `tr_bracket_zero`, `jacobi`, `bracket_leibniz` | Lie bracket = q=−1 antisymmetry |
| `…/Mat2/Mat2Killing.lean` | `killing_gram` | d>1 trace-character (Killing form) |
| `…/Mat2/Mat2SymmetricSpectrum.lean` | `disc_symmetric_nonneg` | symmetric ⟹ real spectrum (q=+1) |
| `…/Mat2/GraphLaplacian.lean` | `closed_const`, `closed_root_determines`, `bipAdj_connected`, `laplacian_spectrum_master` | connectivity = dim ker L |
| `Lib/Math/Algebra/Linalg213/DerivedSeries.lean` | `commSet`, `derived_S`, `commutator_nontrivial` | derived series (solvability) |
| `Lib/Math/Order/FenchelMoreau.lean` | `biconjugate_eq_clo`, `biconj_idempotent`, `closed_iff_fixed` | f** = clo (convex duality) |
| `…/Probability/Limit/ConvolveRescaleContraction.lean` | `Φ_contraction`, `Φ_picard_cauchy`, `center_fixed`, `orbit_to_center` | Gaussian = contraction residue |
| `…/Probability/Limit/DyadicCompletion.lean` | (completion-limit, 19/0) | center as true completion-limit |
| `Lib/Math/Analysis/BanachFixedPointModulated.lean` | `banach_fixed_point_modulated` | the q=+1 converge engine |
| `…/Real213/ModularGeometry/NoetherCurrent.lean` | `continuity_eq`, `current_zero_of_det_one`, `density_conserved_of_det_one` | discrete Noether (det=1 ⟹ conserved) |
| `Lib/Math/Analysis/Measure/OuterMeasure.lean` | `cara_gc`, `caraClosure_idempotent` | Carathéodory = `clo` closure (29/0) |
| `…/Geometry/Topology/ContinuityOpenSet.lean` | `continuous_preimage_dyadicopen`, `preimage_dyadicopen_pointwise_continuous`, `…_uniform_continuous_of_modulus` | continuity ⟺ open-preimage (11/0) |
| `Lib/Math/Combinatorics/PowerSeriesSemiring.lean` | `power_series_semiring` | formal power-series semiring |
| `…/CayleyDickson/Integer/GaussianOrthogonality.lean` | `i_orthogonality`, `orthogonality_of_pow_one` | order-4 χ-orthogonality (18/0) |
| `…/ModArith/CharacterOrthogonality.lean` | `quadratic_orthogonality` | order-2 χ-orthogonality |
| `…/CayleyDickson/Integer/RootOfUnityOrthogonality.lean` | `root_orthogonality`, `omega_orthogonality`, `zeta6_orthogonality`, `cyclotomic_orthogonality` | orders 3, 6 in ℤ[ω] |
| `Theory/Raw/MuNuMirror.lean` | `succ_not_idempotent` | the growing iteration-character pole |
| `Lens/Foundations/FlatOntology.lean` | `object1_not_surjective`, `object1_injective`, `self_covering_closure`, `Object1 = decide(s=r)` | the residue + Ω=Bool + χ |

Supporting closed witnesses cited across notes (all grep-verified): `dsq_zero_universal_delta4`,
`leibniz_universal_delta4`, `cup1_antisymmetric` (Δ-cohomology); `gauss_conservation_telescope`,
`integral_eq_flux` (Stokes = telescope); `summatory_mul`, `geom_sum`, `primorial_le_four_pow` (Euler
product); `quadratic_reciprocity`, `zolotarev_mu`, `floor_sum_rectangle`, `parity_sum_iff` (QR, already
∅-axiom); `golden_hyperbolic`, `cassini_law_one_at_two_multipliers` (φ-spectrum); `mass_conv`,
`momentNum_conv` (convolution = independence); `heineBorel`, `gridMax_attained` (compactness /
extreme-value); `holonomy_append`, `positive_loop_trivial`, `first_loop_is_the_fold`, `derived_S3_step1`
(π₁/H₁); `pathLaplacian_const_kernel`, `balanced_LLN_modulus` (ergodic kernel/LLN);
`kantorovich_weak_duality` (LP duality); `galois_group_is_C4`, `golden_real_subfield`, `a5_order`
(`CyclotomicFive.lean`, `GoldenFieldBridge.lean`); `no_infinite_descent`, `isPart_wf` (`Lambek.lean`,
strong normalization); `max_idem`, `max_iter_trivial` (tropical idempotent pole); `klBitsDyadic`,
`kl_nonneg` (KL); `geomSum_telescope`, `qr_pow_iff_even_exp`, `two_three_unique`, `vp_mul`,
`vp_separation`, `det2_mul`, `legendre_mul`, `det_holonomy_eq_one`, `raw_initial`,
`dhom_unique_pointwise`, `view_factors_through_morphism`, `IsLensMorphism`, `refines_of_morphism`,
`lensIso_iff_kernel_eq`.

**Closure tally (from `README.md` count block):** thirteen predictions, **twelve Lean-closed**
(orthogonality orders 2/3/4/6, growing-corner, convolve-rescale contraction + dyadic completion-limit,
discrete Noether-iff, the modulated Banach engine, Carathéodory-as-`clo`, the formal q=±1 tag,
`continuous_iff_preimage_dyadicopen`, the det/tr=e₁/e₂ Vieta resolution, the formal power-series
semiring), plus QR found already-closed.

### (b) PREDICTION — engine built, named object missing
The structural prediction is delivered and grounded, but the *named field object* is absent:
- **CLT/Gaussian** — contraction + completion-limit built; the full convolution *profile* (vs the
  centered statistic) is conceptual (`gaussian_clt`).
- **ODE/dynamics** — `banach_fixed_point` engine + discrete Picard built; the continuous integral
  operator `(Tf)(t)=x0+∫f` is not welded to the engine as a `Contraction` (`differential_equations`).
- **Noether** — discrete `current_zero_of_det_one` built; the continuous/variational current
  `∂_μ j^μ=0` is the open leg.
- **Spectral / quantum** — `Mat2`-level split + symmetric-real built; Hilbert space, `⟨ψ|φ⟩`, Born
  rule, d>1 eigenprojector absent; finite `Mat2` cannot host `[X,P]=iℏI` (commutators traceless).
- **Generating functions** — `mass_conv`/`momentNum_conv` built; the two `conv` defs not welded into a
  formal-power-series homomorphism on `CoeffSeq` (the `PowerSeriesSemiring` semiring is built, the
  GF-as-analytic-function is the `Real213`-cut residue).

### (c) Genuine BREAKS
See §5 — the recurring boundary.

---

## 5. The recurring breaks / missing primitives (the honest boundary)

The breaks **recur verbatim across independent fields** — which is itself the strongest evidence they
are real structural limits, not one-off gaps.

1. **The ambient-deformation / isotopy quotient — now SPLIT (a 3-school panel, `colimit_quotient_synthesis.md`).**
   First found in `knots.md`, recurred **verbatim** in `fundamental_group.md` (π₁'s homotopy quotient). A
   panel (category-theory + Bishop constructive + rewriting) converged on a decisive **split**, the way the
   constructive-wall panel dissolved its obstruction: a quotient by move-generated equivalence = a rewriting
   system, and "quotient = normal forms" holds exactly when it is **confluent + terminating**.
   - **Side A — INTERFACE DEFECT, buildable ∅-axiom now (no `Quot`):** confluent+terminating cases — braid
     groups (Garside), free/surface π₁, the Kauffman-bracket Jones *state sum* — build as the normal-form
     subtype `{t // Irreducible t}` + `normalize`. The repo *already ships* `Quot.sound`'s content axiom-free:
     `Lens.Unified.LensImage` + `LensImage.proj_val_eq_iff` (`Unified.lean:163`, `#print axioms` → no axioms),
     with termination from `no_infinite_descent` and confluence-for-free from `dhom_unique_pointwise`.
     Constructively: the witnessed-deformation **groupoid** (homotopy-as-data, like `Real213`'s
     regular-sequence-not-Cauchy-quotient).
   - **Side B — GENUINE OBSTRUCTION, theorem-grade:** non-confluent / undecidable cases — general presented
     π₁ (**Novikov–Boone**: the word problem is *undecidable*, so a `normalize` cannot exist), general
     Reidemeister equivalence (no monotone confluent system), the ambient-S³ embedding (no term type). This
     is a real ∅-axiom boundary witnessed by a classical undecidability theorem — not a missing 213 primitive.
   So the "single missing primitive" was **two objects wearing one name**: a confluent quotient the calculus's
   own engine already reaches, and an undecidable one no normal-form type can capture. Named buildable target:
   a `BraidNormalForm`/free-reduction Side-A witness (the analogue of the modulated Banach engine).

2. **The graded-relation slot** (skein / Leibniz). A fixed linear law `Σ cᵢ·L(Cᵢ)=0` among a *family*
   of distinct constructions under *one* reading — NOT a 2-cell, NOT the (two-term) character arrow.
   **Partially grounded**: `leibniz_universal_delta4` (the cup-product Leibniz rule, PURE) is the same
   shape as the skein relation, so the *derivation* law is built; the skein's crossing-resolution
   *move* is not. A promotion target, not a hard absence.

3. **The propext/funext 1-categorical ceiling.** Classical `Prop`-valued connectives are DIRTY:
   `Lens/Foundations/SemanticAtom.lean`'s `canonicalTruthMap` uses `propext` (verified at line 196),
   while the `Bool`/`decide` connectives are PURE. This wall recurs at: `Lp` full `∀S` additivity
   (Lp.lean explicitly notes "pointwise; avoids funext" — only the pointwise version is PURE); the
   Yoneda bijection as a natural `Equiv`; the classical Prop connectives. This is not a gap to close —
   it is the constructive boundary itself (see §6).

4. **The `Real213` value-cut residue.** Irrational/transcendental *values* sit in `Real213` cuts
   (pointings), reached by none: ζ-values (`zeta_euler`), eigenvalue existence for `disc<0` (`spectral`),
   the `log₂e` bracket (`information_geometry`, `entropy`), the analytic GF-as-function, the cyclotomic
   `ζ_n` for general-order χ-orthogonality. Irrationality of a *value* is not a hole in a *derivation*
   (CLAUDE.md "Transcendental-as-exterior") — the discrete structure is closed; only the value-cut is
   reached-by-none.

5. **The named FOL / λ-calculus / presheaf / sheaf / topos objects.** The *engines* are PURE; only the
   *bundles naming them* are absent. `model_theory` (no `Formula`/`⊨`/`⊢` object, but `raw_initial` is
   the completeness content); `curry_howard` (no typed `Term`/β-reduction, but `no_infinite_descent` is
   strong-normalization); `yoneda`/`sheaf_theory` (no named `Presheaf`/`Sheaf`/`Hom(−,A)`, but
   `dhom_unique_pointwise` is the gluing/Yoneda content); `topos` (no named `Topos`/`Ω` *bundle*, though
   `Object1 = decide` IS Ω=Bool + χ, built). Honest shape: structural prediction delivered, the named
   instance is open work.

---

## 6. The self-description (the capstone-of-capstones)

Four decompositions turn the calculus on itself, and it describes its own apparatus term-by-term — a
fixed point, not a coincidence:

- **`category_theory.md`** — 213 IS category-theory-shaped but *generated from the distinguishing*:
  `Raw` = initial object; `fold`/`universalMorphism` = the read-op = catamorphism (`raw_initial`,
  `universalMorphism_unique`); readings = morphisms; `LensIso` = groupoid; adjoint pairs → the closure
  monad (`FenchelMoreau`). What the distinguishing *adds* beyond bare CT: the q=±1 residue (limit/colimit
  duality as one *derived* law), atom-distinguishability (why hom is vectorial vs scalar). The loop stays
  open *exactly* at q=−1 (the free/colimit corner).
- **`yoneda.md`** — the calculus's own founding sentence `OBJECT = ⟨C|L⟩` made categorical;
  `self_covering_closure` (injective ∧ ¬surjective) **= Yoneda ⊕ its residue in one ∅-axiom theorem**
  (faithful where the embedding succeeds, q=+1; un-pointable where it diagonalizes out, q=−1).
- **`curry_howard.md`** — `⟨C|L⟩ = ⟨proof|proposition⟩`; `Lens.view = Raw.fold` is the recursor;
  normalization = the fold to the unique normal form (`dhom_unique_pointwise`); strong normalization =
  `no_infinite_descent` (`isPart_wf`).
- **`topos.md`** — the sharpest foundational leverage: **Ω = the distinguishing-target `Bool`**, and
  χ = `Object1` (`decide (s=r)`) are BUILT + PURE (`FlatOntology.lean:43`). The revelation is grounded
  by a *purity scan*, not asserted: the classical Prop connectives are DIRTY [propext], the Bool/decide
  ones PURE — **the PURE/DIRTY boundary IS the Heyting/Boolean boundary.** So "213 is constructive
  (∅-axiom)" = "213 is the q=+1 PURE corner of its own topos, whose internal logic is intuitionistic."
  The no-Classical discipline becomes a *structural account*, not a taboo.

---

## 7. What it means for the originator's goal

The goal (boot §7.1, `seed/AXIOM/07_primacy.md`): primacy = **breadth** of ∅-axiom derivation — the
residue reproducing domain after domain. Assessed honestly against *that* bar (not the physics-branch
validation gate, which CLAUDE.md is explicit is one domain's gate, not the yardstick):

**What it HAS shown — and this is the real result.** The reduction is genuine and unusually wide. Fifty-two
fields read through a fixed normal form converge on *two* invariants (the character arrow, the q=±1
residue) over four axes, and the convergence is **Lean-anchored at a high rate** — twelve of thirteen
predictions closed ∅-axiom, the two deepest collapses (det/tr split, the q=±1 tag) now *theorems* rather
than prose. The breaks **recur verbatim** (isotopy in both knots and π₁; the propext wall in Lp, Yoneda,
classical connectives), which is the signature of a real structural map, not an artifact of how the notes
were written. And the calculus is **self-describing**: its own apparatus is the vocabulary it produces,
with the constructive boundary (PURE/DIRTY = Heyting/Boolean) *grounded by a purity scan*. That a single
`×↦·` reading runs provably through seven fields, and a single fixed-point-free diagonal
(`object1_not_surjective`) provably underlies Cantor, Gödel, the Vitali/non-measurable obstruction, and
Löwenheim–Skolem, is breadth of exactly the kind §7.1 names.

**What remains — stated plainly.** "Rebuilt disciplines from the residue" is true at the level of
*structural skeleton + the discrete load-bearing leg*, not at the level of the full classical machine in
every field. The honest residuals are the §5 list: (i) the ambient-deformation/colimit quotient (the one
genuine absence, the un-built q=−1/free corner); (ii) the graded-relation *move* (the slot is partially
grounded by Leibniz, the skein move is not); (iii) the propext/funext ceiling, which is *constitutive*,
not removable, of a constructive system; (iv) the `Real213` value-cut residue (a reached-by-none cut, not
a derivation gap); (v) the named FOL/λ/presheaf/sheaf/topos *objects* (engines PURE, bundles absent — open
work, not blocked). None of these is hidden, and each is located at a precise corner of the same frame.

**Verdict.** The program has demonstrated *breadth* of ∅-axiom derivation across a front wide enough to
make the invariant reduction itself the finding: most of the surveyed mathematics is the same two
invariants read across a handful of axes, and that claim is machine-checked far more often than it is
asserted. It has *not* (and does not claim to have) rebuilt every named object; the open corner is a
single, recurring, precisely-located one — the colimit/ambient-quotient side of the q=±1 duality the
calculus already names. The map is real, the anchor is real, and the boundary is honest.
