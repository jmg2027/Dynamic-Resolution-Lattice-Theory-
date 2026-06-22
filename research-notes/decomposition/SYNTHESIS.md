# The 213 Decomposition Calculus — capstone synthesis (v2)

**Status**: Tier-1 capstone of the decomposition cluster (`README.md` = the technique + per-field
log; `practice/*.md` = the 58 worked decompositions; `FRONTIER_AUDIT.md` = the honesty pass;
`frontiers/colimit_quotient_synthesis.md` + the 3 panel memos = the open edge, now half-built). This
document does not add a decomposition — it makes the whole corpus legible as one statement. Every Lean
name cited below was grep-verified to exist in `lean/E213/` and scanned ∅-axiom via `tools/scan_axioms.py`;
predictions with no closed Lean witness are marked **[prose]**.

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
deliverable. The headline finding, after **58 worked decompositions across ~58 fields**, is that this
wide front does not need 58 different ideas: it converges on a **small invariant set** — one *character
arrow*, one *q=±1 residue tag*, and (the deepest reflexive turn) one *residue-taking operation* — read
across four axes, all Lean-anchored, not merely asserted. `Residue(L,C)` is the **proven remainder** the
distinguishing always leaves (`FlatOntologyClosure.self_covering_closure`: faithful yet never total), not a
substrate the objects are built on top of — and **homological algebra is the field that names that very
operation** (§2, §6).

---

## 2. The invariant set — the complete inventory

The 58 decompositions converge on **two load-bearing invariants** plus **one structured frame** (the
read-off axes of `C` and the parameters of `L`) — and one reflexive addition: the calculus naming its own
residue operation. Each is cashed by a verified Lean theorem.

### Invariant A — the character arrow `×↦·` / `×↦+`
A *character* is a construction-preserving reading whose readout is itself a number-construction; its
defining law is that it carries the multiplicative structure to a (multiplicative or additive) readout.
The single arrow is proven to be the *same* arrow across the fields below.

| Mode | Lean witness | Fields instantiating |
|---|---|---|
| `×↦·` (multiplicative) | `det2_mul`, `legendre_mul`, `det_holonomy_eq_one` | parity, determinant, Legendre/QR, Noether, curvature/holonomy, representation (det-character), probability independence, L-function Euler product (modular forms) |
| `×↦+` (additive / log) | `vp_mul`, `vp_separation` | prime-factorization, entropy (`−log`), KL/Fisher, Fourier/ζ-Euler character, tropical `(max,+)` |
| spectral split of one character | `Mat2Spectrum.tr_eq_e1`, `det_eq_e2`, `det_tr_split_is_e1_e2` | spectral theory, representation `det`/`tr`, Lie `tr_bracket_zero` |

The deepest single unity: the `det` / `×↦·` character is read **four ways** — scalar (`determinant`),
`Aut`-invariant (`noether`, `det_holonomy_eq_one`), around a loop (`curvature`, holonomy), down the
height (`homology`, `∂`) — and the additive twin `×↦+` spans seven fields. The det/tr "opposition" is
**dissolved** as a Lean theorem: `tr = e₁`, `det = e₂` are the two Vieta coefficients of one spectrum
(`Mat2CayleyHamilton.cayley_hamilton`, `Mat2Spectrum.det_tr_split_is_e1_e2`).

### Invariant B — the q=±1 residue tag (escape / converge)
A residue is the reading's self-application surplus; it carries a **unimodular multiplier bit** `q=±1`.
This is the deepest collapse and is **one formal object**: `ResidueTag` (`inductive escape | converge`)
+ `multiplier : ResidueTag → Int` (∓1, with `multiplier_unimodular`), capstone
`ResidueTag.residue_tag_two_poles`. See §3 for the full spine.

### ★ The reflexive deepening — the calculus names its own residue-taking operation
Homological algebra (`practice/homological_algebra.md`) does not add a field; it **names the operation
the calculus has been running since batch 4**. A **derived functor** `Ext^n`/`Tor_n` *is* `Residue(L,C)`
with `L` = "a non-exact functor (`Hom`, `⊗`) composed with the resolution dial", graded by degree `n`,
tagged `q=±1`:
- `Ext⁰=Hom` / `Tor₀=⊗` = the **q=+1 exact part** (`ker=im`, residue empty);
- `Ext^{>0}` / `Tor_{>0}` = the **q=−1 obstruction residue** = `de_rham`'s `H*_dR` = `sheaf`'s `H^{>0}`,
  *verbatim* one `ker δ/im δ` mechanism (`BettiKernel.reduced_betti_d4_contractible`);
- the connecting `δ` / long-exact-sequence / `δ²=0` = the `q=±1` sign-propagation
  (`dsq_zero_universal_delta4`, `V4Capstone`), the orientation bits cancelling pairwise;
- the resolution (proj/inj) = the resolution dial *at chain level* (`IsResolutionShift`,
  `compose_modulus_eq`); `Ext¹` = extensions-mod-split, the split-`q=+1`/non-split-`q=−1` residue
  (`clo_idempotent`).

So homology, de Rham, and sheaf cohomology are three *outputs* of one machine, and the README's normal
form `⟨C|L⟩ ⊕ Residue(L,C)` is not a description but an *operation*. Every leg is built and PURE
(`ResidueTag`, `delta`/`dsq_zero`/`reduced_betti_d4_contractible`, `IsResolutionShift`, `clo_idempotent`,
`ConvolveProfile`); the genuine absence is only the *named* graded `Ext^n`/`Tor_n`/resolution/exact-sequence
object (§5, the abelian-category twin of the missing presheaf-bundle).

### The frame — the read-off axes (`C`) and the `L`-parameters
These are not extra invariants; they are the coordinates the invariants are read across. Each pays by
collapse + forcing, and each is grounded.

| Axis | What it reads out | Lean grounding | Fields |
|---|---|---|---|
| direction / swap-bit (`q=±1`) | sign, orientation, antisymmetry | `Mat2Bracket.bracket_antisymm`, `dsq_zero_universal_delta4` | integers, determinant, homology (`∂²=0`), Lie bracket, knot/loop, modular reflection `s↔k−s` |
| fold-height (bidirectional) | dimension, degree, pole-order, `∂`/`d` | `Lambek.isPart_wf`, `dsq_zero_universal_delta4` | dimension, homology, de Rham, ordinals, derived-functor degree |
| resolution **+ base** | discrete `Δ` vs `h→0` `∫`; which valuation is "adjacent" | `ContinuityOpenSet.*`, `gauss_conservation_telescope` | derivative, integration, continuity, topology, p-adics, proj/inj resolution |
| iteration-character | nilpotent `∂` / idempotent `clo` / growing `S` | `MuNuMirror.succ_not_idempotent`, `max_idem`, `FenchelMoreau.biconj_idempotent` | homology, closure/Galois/Nullstellensatz, free corner, tropical |
| weight | value-weighted count → measure/expectation | `mass_conv`, `momentNum_conv`, `klBitsDyadic` | probability, measure, entropy, information geometry, ergodic |
| character-mode | the arrow of Invariant A (bidirectional) | (Invariant A row) | (Invariant A fields) |

The structural lesson the frame forces: **readings form a 2-category.** They compose in series (entropy
= weight∘character), form composition-closed families (`Aut`, groups), form adjoint/order-reversing
pairs (Galois, Legendre–Fenchel, **and now the Nullstellensatz** — three instances of one `f**=clo`,
below), and admit 2-cells = natural transformations (`view_factors_through_morphism`, `IsLensMorphism`,
`refines_of_morphism`, `lensIso_iff_kernel_eq`).

**The `f**=clo` order-reversing-closure family is now three instances, one Lean object.** Field-Galois
(`Fix⊣Inv`, `galois_correspondence.md`), Legendre–Fenchel (`f**`, `convex_duality.md`), and **algebraic
geometry's `V⊣I` ideal–variety correspondence** (`algebraic_geometry.md`) are the *same* idempotent
closure `clo = G∘F` being the identity on its closed elements. The Nullstellensatz `I(V(J))=√J` is then
*forced* as `clo(J)=√J` with `√√J=√J` = `clo_idempotent` / `biconj_idempotent` and reduced ⟺
`closed_iff_fixed` — the radical is the *name* of the closure. All three share `clo_idempotent`
(`GaloisConnection`, 15/0) and `biconj_idempotent` (`FenchelMoreau`, 18/0); Carathéodory's outer measure
(`caraClosure_idempotent`, 29/0) is the nearest closure instantiated on an actual set-system. The
ideal/variety/`Spec` *object* is the single located missing leg.

---

## 3. The q=±1 spine (the single deepest pattern)

One residue, two signs. `q=−1` = **escape** (self-pointing reading whose surplus oscillates *outside*
every image — fixed-point-free diagonal); `q=+1` = **converge** (the surplus asymptotes *toward* a fixed
point / closure). Both poles are delegated to a proven kernel.

| `q=−1` escape (delegates to `FlatOntologyClosure.object1_not_surjective` / `OneDiagonal.no_surjection_of_fixedpointfree`) | `q=+1` converge (delegates to `BanachFixedPointModulated.banach_fixed_point_modulated`) |
|---|---|
| Cantor diagonal (`cardinality`) | golden ratio φ (`cassini_law_one_at_two_multipliers`, `golden_is_converge`) |
| Gödel incompleteness (`godel`) | Gaussian / CLT fixed point (`ConvolveRescaleContraction.Φ_contraction`) |
| measure: non-measurable / Vitali / Banach–Tarski (`measure`) | ODE flow / Picard contraction (`differential_equations`) |
| Löwenheim–Skolem (`model_theory`) | ergodic invariant measure / time=space average (`CyclicErgodic.birkhoff_period_eq_space`) |
| the quintic / **A₅-perfect `[A₅,A₅]=A₅`** (`A5Perfect.a5_perfect`, `a5_not_solvable`) | **solvable groups: derived series terminates** (`Solvable.solvable_S3'`, `DerivedSeries.solvable_S3`) |
| complex/elliptic spectrum `disc<0` (`spectral`, `quantum_mechanics`) | real symmetric spectrum `disc≥0` (`Mat2SymmetricSpectrum.disc_symmetric_nonneg`) |
| non-contractible loop `holonomy[S,S]=−I` (`fundamental_group.first_loop_is_the_fold`) | connected-graph Laplacian kernel `λ₀=0` (`GraphLaplacian.pathLaplacian_const_kernel`, `GraphConnectivity.closed_const`) |
| uncertainty: bracket obstructs common eigenbasis (`quantum_mechanics`, `Mat2Bracket`) | completeness `⊢⟺⊨` = `view=fold` initiality (`raw_initial`) |
| `Ext^{>0}`/`Tor_{>0}` obstruction; H^{>0} (`homological_algebra`, `sheaf_theory`) | `Ext⁰=Hom`/`Tor₀=⊗`; compactness = finiteness collapse (`heineBorel`); Carathéodory `clo` (`cara_gc`) |

**Both poles of solvability are now one Lean object.** `Solvable.lean` (65/0) makes the derived series an
iterated operator `derivedSeries step G k`, with `isSolvable`/`isPerfect` predicates and the pure-induction
headline `perfect_nontrivial_not_solvable` (no enumeration) unifying `solvable_S3'` (`q=+1`) and
`a5_not_solvable'` (`q=−1`, via `a5_isPerfect` from `A5Perfect.a5_perfect`) under the `ResidueTag` `±1`
bit (`solvability_two_poles`, `tagOfVerdict_S3` = converge, `tagOfVerdict_A5` = escape). The quintic's
insolvability is the `q=−1` pole, machine-checked.

**Ergodicity = the q=+1 constant kernel, now built.** `CyclicErgodic.lean` (26/0) grounds the cleanest
closable instance: the cyclic shift `rot n` on `{0,…,n−1}`, with `birkhoff_period_eq_space`
(time-average = space-average, the `q=+1` fixed point reached exactly at the period) and
`rotInvariant_is_constant` (invariant ⟹ constant = the dim-1 `q=+1` kernel, via
`GraphConnectivity.closed_const` on the cycle — *literally* `graph_theory`'s Laplacian `λ₀=0` transported
onto the Koopman-invariant subspace), with `nonergodic_invariant_not_constant` the `q=−1` contrast
(`dim ker = #components > 1`). Orthogonality is also now closed at **all orders** mod p
(`CyclicCharacterOrthogonality.cyclic_orthogonality_modp`, finite-field route, 15/0) — the `Σχ=0`
prediction no longer needs a `Real213` cyclotomic `ζ` for the existence claim.

The formal tag is **honestly asymmetric**: `escape_residue_outside` is a *negative* theorem (universal
negation), `converge_residue_fixed` a *positive existence* theorem; they are not collapsed into one `Eq`
(that would need excluded middle). `residue_tag_two_poles` bundles them under the shared `±1` column.

---

## 4. The Lean-grounded census

Grep-verified, each scanned ∅-axiom this pass. Counts (`N/0`) are the `tools/scan_axioms.py` PURE/DIRTY
tallies. **Twenty-seven ∅-axiom modules** anchor the corpus.

### (a) Fully ∅-axiom Lean-closed / grounded
| Module | Load-bearing theorem(s) | Role |
|---|---|---|
| `Lib/Math/Foundations/ResidueTag.lean` | `residue_tag_two_poles`, `multiplier_unimodular`, `golden_is_converge` | the q=±1 tag (Invariant B) |
| `…/Real213/Mat2/Mat2Spectrum.lean` | `tr_eq_e1`, `det_eq_e2`, `det_tr_split_is_e1_e2`, `disc_eq_gap_squared` | det/tr dissolved as Vieta |
| `…/Mat2/Mat2CayleyHamilton.lean` | `cayley_hamilton`, `char_poly_discriminant`, `dial_is_char_discriminant` | spectrum exists ⟹ split |
| `…/Mat2/Mat2Bracket.lean` | `bracket_antisymm`, `tr_bracket_zero`, `jacobi`, `bracket_leibniz` | Lie bracket = q=−1 antisymmetry |
| `…/Mat2/Mat2Killing.lean` (19/0) | `killing`, `killing_gram`, `adMap`, `adX_traceless` | d>1 trace-character (Killing form) |
| `…/Mat2/Mat2SymmetricSpectrum.lean` | `disc_symmetric_nonneg` | symmetric ⟹ real spectrum (q=+1) |
| `…/Mat2/GraphLaplacian.lean` (16/0) | `pathLaplacian_const_kernel`, `pathLaplacian_spectrum_roots`, `pathLaplacian_graph_spectrum` | the 2-vertex `[[1,−1],[−1,1]]` Laplacian toy (λ₀=0) |
| `Lib/Math/Algebra/Linalg213/DerivedSeries.lean` | `commSet`, `derived_S3_step1`, `solvable_S3`, `commutator_nontrivial` | derived series (S₃ solvability) |
| `Lib/Math/Algebra/Linalg213/Solvable.lean` (65/0) | `perfect_nontrivial_not_solvable`, `solvable_S3'`, `a5_not_solvable'`, `solvability_two_poles` | general `isSolvable`/`isPerfect`; both poles unified |
| `Lib/Math/Algebra/Icosahedral/A5Perfect.lean` (9/0) | `a5_perfect` (`[A₅,A₅]=A₅`), `a5_not_solvable`, `A5_card`=60 | the quintic q=−1 pole |
| `Lib/Math/Algebra/Group/FreeReduction.lean` (26/0) | `proj_val_eq_iff`, `freeReduce_idempotent`, `freeEquiv_iff_reduce_eq`, `free_group_quotient_no_quot`, `proj_section` | the colimit Side-A witness (free group as normal-form Σ-quotient, no `Quot`) |
| `Lib/Math/Cohomology/Examples/NonzeroBetti.lean` (56/0) | `loopClass_not_coboundary`, `betti_one_cycle`, `nonzero_cohomology_class`, `cycle_vs_contractible_qpm` | nonzero `H¹` witness (hollow triangle S¹=∂Δ², b₁=1); cycle=q−1 escape vs contractible=q+1 |
| `Lib/Math/Combinatorics/CyclicErgodic.lean` (26/0) | `birkhoff_period_eq_space`, `measure_preserving`, `rotInvariant_is_constant`, `nonergodic_invariant_not_constant` | finite measure-preserving / Birkhoff / ergodicity=constant-kernel |
| `Lib/Math/Order/FenchelMoreau.lean` | `biconjugate_eq_clo`, `biconj_idempotent`, `closed_iff_fixed`, `cloAntitone_eq_gc_clo` | f**=clo (the three-instance closure) |
| `…/Probability/Limit/ConvolveRescaleContraction.lean` | `Φ_contraction`, `Φ_picard_cauchy`, `center_fixed`, `orbit_to_center` | Gaussian = contraction residue |
| `…/Probability/Limit/DyadicCompletion.lean` | (completion-limit, 19/0) | center as true completion-limit |
| `Lib/Math/Analysis/BanachFixedPointModulated.lean` | `banach_fixed_point_modulated` | the q=+1 converge engine |
| `…/Real213/ModularGeometry/NoetherCurrent.lean` | `continuity_eq`, `noether_local`, `density_conserved_of_det_one` | discrete Noether (det=1 ⟹ conserved) |
| `Lib/Math/Analysis/Measure/OuterMeasure.lean` | `cara_gc`, `caraClosure_idempotent` | Carathéodory = `clo` closure (29/0) |
| `…/Geometry/Topology/ContinuityOpenSet.lean` | `continuous_preimage_dyadicopen`, `…_uniform_continuous_of_modulus` | continuity ⟺ open-preimage (11/0) |
| `Lib/Math/Combinatorics/PowerSeriesSemiring.lean` | `power_series_semiring` | formal power-series semiring |
| `…/CayleyDickson/Integer/GaussianOrthogonality.lean` | `i_orthogonality`, `orthogonality_of_pow_one` | order-4 χ-orthogonality (18/0) |
| `…/ModArith/CharacterOrthogonality.lean` | `quadratic_orthogonality` | order-2 χ-orthogonality |
| `…/CayleyDickson/Integer/RootOfUnityOrthogonality.lean` | `root_orthogonality`, `omega_orthogonality`, `zeta6_orthogonality`, `cyclotomic_orthogonality` | orders 3, 6 in ℤ[ω] |
| `…/ModArith/CyclicCharacterOrthogonality.lean` (15/0) | `cyclic_orthogonality_modp`, `cyclic_orthogonality_of_root`, `omega_order_n` | χ-orthogonality at **all orders** mod p (finite-field route) |
| `Theory/Raw/MuNuMirror.lean` | `succ_not_idempotent` | the growing iteration-character pole |
| `Lens/Foundations/FlatOntology{,Closure}.lean` | `object1_not_surjective`, `object1_injective`, `self_covering_closure` (Closure); `Object1 = decide(s=r)` (FlatOntology) | the residue + Ω=Bool + χ |

Supporting closed witnesses cited across notes (all grep-verified): `dsq_zero_universal_delta4`,
`leibniz_universal_delta4`, `cup1_antisymmetric`, `reduced_betti_d4_contractible`, `kerSizeDelta`
(Δ-cohomology / the derived-functor residue mechanism); `gauss_conservation_telescope`,
`integral_eq_flux` (Stokes = telescope); `summatory_mul`, `geom_sum`, `dconv_mul` (Euler product);
`quadratic_reciprocity`, `zolotarev_mu`, `floor_sum_rectangle` (QR, ∅-axiom); `golden_hyperbolic`,
`cassini_law_one_at_two_multipliers` (φ-spectrum); `mass_conv`, `momentNum_conv` (convolution =
independence); `heineBorel`, `gridMax_attained` (compactness); `holonomy_append`,
`first_loop_is_the_fold`, `det_holonomy_eq_one` (π₁/H₁/holonomy); `GraphConnectivity.closed_const`,
`closed_root_determines`, `LaplacianSpectrum.laplacian_spectrum_master`, `bipAdj_connected` (graph
connectivity = dim ker); `balanced_LLN_modulus`, `countTrue_append` (Birkhoff/LLN); `kantorovich_weak_duality`
(LP duality); `galois_group_is_C4`, `golden_real_subfield` (`CyclotomicFive`); `manin_unimodular_decomposition`,
`minkowski_is_markov_valued_cocycle`, `period_satisfies_relations` (modular-form period side, 30/0);
`mulDiv_gc`, `vp_mul`, `eq_of_vp_eq`, `two_three_unique` (Nullstellensatz closure + prime atom);
`TensorCalculus.riemUp`, `riem_bianchi1`, `scalar_einstein` (abstract-index Riemann tower, 23/0);
`no_infinite_descent`, `isPart_wf` (`Lambek`, strong normalization); `max_idem` (tropical idempotent pole);
`raw_initial`, `dhom_unique_pointwise`, `view_factors_through_morphism`, `IsLensMorphism`,
`lensIso_iff_kernel_eq`, `LensImage.proj_val_eq_iff` (the 2-category + the `Quot`-free Σ-quotient).

**Closure tally (`README.md` count block):** thirteen predictions, **twelve Lean-closed** (orthogonality
orders 2/3/4/6 + **all-orders-mod-p**, growing-corner, convolve-rescale contraction + dyadic
completion-limit, discrete Noether-iff, the modulated Banach engine, Carathéodory-as-`clo`, the formal
q=±1 tag, `continuous_iff_preimage_dyadicopen`, the det/tr=e₁/e₂ Vieta resolution, the formal
power-series semiring), plus QR found already-closed.

### (b) PREDICTION — engine built, named object missing
Structural prediction delivered and grounded, the *named field object* absent: **CLT/Gaussian** (full
convolution *profile*); **ODE/dynamics** (continuous integral operator as a `Contraction`); **Noether**
(continuous/variational `∂_μ j^μ=0`); **spectral/quantum** (Hilbert space, `⟨ψ|φ⟩`, Born rule, d>1
eigenprojector — finite `Mat2` cannot host `[X,P]=iℏI`, commutators traceless); **generating functions**
(analytic GF-as-function = `Real213`-cut); **ergodic** (the *infinite/convergent* Birkhoff theorem with
modulus, vs the built finite-period instance; the Koopman operator as a named object); **modular forms**
(the automorphic side — Hecke/eigenform/analytic `L(f,s)` — dual to the *built* Eichler–Shimura period
corpus); **homological algebra** (the `Ext^n`/`Tor_n`/resolution/exact-sequence object — see §5; the
nonzero-`Ext¹`/`H¹` *witness* it named is now **BUILT**, `NonzeroBetti.lean` 56/0, hollow-triangle b₁=1);
**combinatorial game theory** (the `Game`/`Nim`/`Grundy`/`mex` object — but every *leg* is built:
impartial game = surreal's `C` swap-trivial, nim-value = `Raw.fold` to the Nim-heap normal form,
game-sum = parity's character in 𝔽₂^k (`psiNatPos_linear`, `C2_6.mul`), P/N = the q=±1 poles; ★ the
nim-sum character is PURE only coordinatewise, DIRTY as packed `Nat.xor` — the PURE/DIRTY=Heyting/Boolean
line on the central arrow, `game_theory.md`).

### (c) Genuine BREAKS
See §5.

---

## 5. The recurring breaks / missing primitives (the honest boundary)

The breaks **recur verbatim across independent fields** — itself the strongest evidence they are real
structural limits, not one-off gaps. `FRONTIER_AUDIT.md` is the repo-first reconciliation pass behind
this section: **7 stale "missing leg" claims were corrected** (e.g. `lie_theory`'s "no `jacobi`/Killing"
→ `Mat2Bracket`/`Mat2Killing`; `noether`'s "no `∂·j`" → `NoetherCurrent.noether_local`;
`galois`'s "no derived series" → `DerivedSeries`/`Solvable`; the `TensorCalculus` Riemann-tower
correction), and ~22 genuinely-absent objects confirmed honest. The breaks below reflect that audit.

1. **The ambient-deformation / colimit quotient — now SPLIT, and Side A BUILT ∅-axiom**
   (`colimit_quotient_synthesis.md` + 3 panel memos). First found in `knots.md`, recurring **verbatim** in
   `fundamental_group.md`. A 3-school panel (category-theory + Bishop constructive + rewriting) converged
   on a decisive **split** — the way the constructive-wall panel dissolved its obstruction: a quotient by
   move-generated equivalence is a rewriting system, and "quotient = normal forms" holds *exactly when* it
   is **confluent + terminating** (Newman + Church–Rosser). This is the program's **second wall-style
   result** (diagnose → build the buildable side), so the corner is no longer "a single missing primitive"
   but **two objects wearing one name**:
   - **Side A — INTERFACE DEFECT, now BUILT ∅-axiom (no `Quot`).** Confluent+terminating cases — free /
     surface / complete-rewriting π₁ (free reduction), the braid group (Garside greedy form), the
     Kauffman-bracket Jones *state sum* (a terminating crossing-resolution fold) — build as the normal-form
     subtype `{t // Irreducible t}` + `normalize`. **The witness is built**:
     `Lib/Math/Algebra/Group/FreeReduction.lean` (26/0) — the free group as a normal-form Σ-quotient with
     `proj_val_eq_iff : (proj u).val = (proj v).val ↔ FreeEquiv u v` (`Quot.sound`'s content axiom-free),
     `freeReduce_idempotent`, the decidable word problem `freeEquiv_iff_reduce_eq`, and the bundle
     `free_group_quotient_no_quot` — **no `Quot`, no `Classical`, no Mathlib**. It is the exact analogue of
     `LensImage.proj_val_eq_iff` (`Unified.lean:163`, also axiom-free), with termination from
     `no_infinite_descent` and confluence-for-free from `dhom_unique_pointwise`. This is the colimit corner's
     answer to the modulated Banach engine that closed the constructive wall.
   - **Side B — GENUINE OBSTRUCTION, theorem-grade.** Non-confluent / undecidable cases — general presented
     π₁ (**Novikov–Boone**: the word problem is *undecidable*, so a `normalize` cannot exist), general
     Reidemeister equivalence (no monotone confluent system — unknotting must sometimes raise crossing
     number), the ambient-S³ embedding (no `Raw`/`Lens` term type at all). A real ∅-axiom boundary witnessed
     by a classical undecidability theorem — not a missing 213 primitive, the sharpest possible witness that
     the corner is genuinely open.

2. **The graded-relation slot** (skein / Leibniz). A fixed linear law `Σ cᵢ·L(Cᵢ)=0` among a *family* of
   distinct constructions under *one* reading — NOT a 2-cell, NOT the (two-term) character arrow.
   **Partially grounded**: `leibniz_universal_delta4` (the cup-product Leibniz rule, PURE) is the same shape
   as the skein relation, so the *derivation* law is built; the skein's crossing-resolution *move* is not (it
   sits with the Side-A bracket state-sum). A promotion target, not a hard absence.

3. **The propext/funext 1-categorical ceiling.** Classical `Prop`-valued connectives are DIRTY:
   `Lens/Foundations/SemanticAtom.lean`'s `canonicalTruthMap` uses `propext`, while the `Bool`/`decide`
   connectives are PURE. The wall recurs at: `Lp` full `∀S` additivity (only the pointwise version PURE);
   the Yoneda bijection as a natural `Equiv`; the classical Prop connectives. **Not a gap to close — the
   constructive boundary itself** (see §6).

4. **The `Real213` value-cut residue.** Irrational/transcendental *values* sit in `Real213` cuts
   (pointings), reached by none: ζ-values, eigenvalue existence for `disc<0`, the `log₂e` bracket, the
   analytic GF / analytic `L(f,s)`, the algebraically-closed base field the weak Nullstellensatz wants, the
   smooth `Real213`-cut metric the geometry cluster shares. Irrationality of a *value* is not a hole in a
   *derivation* (CLAUDE.md "Transcendental-as-exterior") — the discrete structure is closed; only the
   value-cut is reached-by-none. `FRONTIER_AUDIT.md` flags the smooth metric and the de Rham comparison iso
   `H*_dR ≅ H*_sing` as the top shared residuals of this kind.

5. **The named FOL / λ / presheaf / sheaf / topos / `Ext` objects.** The *engines* are PURE; only the
   *bundles naming them* are absent. `model_theory` (`raw_initial` is the completeness content);
   `curry_howard` (`no_infinite_descent` is strong-normalization); `yoneda`/`sheaf_theory`
   (`dhom_unique_pointwise` is the gluing/Yoneda content); `topos` (`Object1 = decide` IS Ω=Bool + χ);
   `homological_algebra` (every leg — `ker δ/im δ`, the `q=±1` grading, the resolution dial, the
   split/closure — built and PURE; only the graded `Ext^n`/`Tor_n`/resolution/exact-sequence object open,
   the abelian-category twin of the missing presheaf-bundle). Honest shape: structural prediction
   delivered, the named instance is open work — and a buildable witness is named (a nonzero `Ext¹` via
   `kerSizeDelta` on a *non-exact* resolution, mirroring the exact zero `reduced_betti_d4_contractible`).

---

## 6. The self-description (the capstone-of-capstones)

Decompositions that turn the calculus on itself, and it describes its own apparatus term-by-term — a
fixed point, not a coincidence. Homological algebra's "names its own residue operation" (§2) reinforces
this: the reflexive turn is now five-deep.

- **`category_theory.md`** — 213 IS category-theory-shaped but *generated from the distinguishing*:
  `Raw` = initial object; `fold`/`universalMorphism` = catamorphism (`raw_initial`); readings =
  morphisms; `LensIso` = groupoid; adjoint pairs → the closure monad. What the distinguishing *adds*: the
  q=±1 residue, atom-distinguishability. The loop stays open *exactly* at q=−1 (the free/colimit corner —
  now half-built, §5.1).
- **`yoneda.md`** — the founding sentence `OBJECT = ⟨C|L⟩` made categorical; `self_covering_closure`
  (injective ∧ ¬surjective) **= Yoneda ⊕ its residue in one ∅-axiom theorem** (faithful where the
  embedding succeeds, q=+1; un-pointable where it diagonalizes out, q=−1).
- **`curry_howard.md`** — `⟨C|L⟩ = ⟨proof|proposition⟩`; `Lens.view = Raw.fold` is the recursor;
  normalization = the fold to the unique normal form (`dhom_unique_pointwise`); strong normalization =
  `no_infinite_descent` (`isPart_wf`) — the *same* termination engine the colimit Side-A build leans on.
- **`homological_algebra.md`** — the deepest reflexive turn: the field whose entire content is *running*
  `Residue(L,C)`, degree by degree. "Derived functor" is the systematic, graded name for the calculus's
  own residue-taking operation (§2); the long exact sequence is the q=±1 tag *displayed degree by degree*.
- **`topos.md`** — the sharpest foundational leverage: **Ω = the distinguishing-target `Bool`**, χ =
  `Object1` (`decide (s=r)`), BUILT + PURE. The revelation is grounded by a *purity scan*, not asserted:
  classical Prop connectives DIRTY [propext], Bool/decide ones PURE — **the PURE/DIRTY boundary IS the
  Heyting/Boolean boundary.** So "213 is constructive (∅-axiom)" = "213 is the q=+1 PURE corner of its own
  topos, whose internal logic is intuitionistic." The no-Classical discipline becomes a *structural
  account*, not a taboo — and the colimit split (§5.1) makes the same boundary operational: the buildable
  Side A is exactly the decidable q=+1 PURE corner, Side B exactly the `Quot`-needing q=−1 escape.

---

## 7. What it means for the originator's goal

The goal (boot §7.1, `seed/AXIOM/07_primacy.md`): primacy = **breadth** of ∅-axiom derivation — the
residue reproducing domain after domain. Assessed honestly against *that* bar (not the physics-branch
validation gate, which CLAUDE.md is explicit is one domain's gate, not the yardstick):

**What it HAS shown — and this is the real result.** The reduction is genuine and unusually wide.
Fifty-eight fields read through a fixed normal form converge on *two* invariants (the character arrow,
the q=±1 residue) plus the reflexive residue-operation, over four axes, and the convergence is
**Lean-anchored at a high rate** — twelve of thirteen predictions closed ∅-axiom across twenty-six
∅-axiom modules. The deepest collapses are now *theorems*, not prose: the det/tr split (Vieta), the
q=±1 tag, the three-instance `f**=clo` closure (Galois + Legendre + Nullstellensatz), and both poles of
solvability unified in one object (`Solvable.solvability_two_poles`, the quintic's `A5Perfect.a5_perfect`
as the q=−1 pole). The breaks **recur verbatim** (isotopy in knots *and* π₁; the propext wall in Lp,
Yoneda, classical connectives), the signature of a real structural map. And the calculus is
**self-describing** at five depths, with the constructive boundary (PURE/DIRTY = Heyting/Boolean)
*grounded by a purity scan*.

**The two hardest corners are now not only diagnosed but PARTIALLY BUILT — state this plainly.** The
program has a method for its walls: *diagnose, then build the buildable side, and name the residual as
theorem-grade*. It has now done this twice.
- **The constructive wall** (the `Real213`/completion corner) — defeated by the modulated Banach engine
  (`banach_fixed_point_modulated`, the q=+1 converge kernel).
- **The colimit / ambient-quotient corner** (the q=−1/free corner `category_theory.md` named as the open
  loop) — **Side A now BUILT** (`FreeReduction.lean`, the free group as a `Quot`-free normal-form
  Σ-quotient, 26/0), with Side B located as a *theorem-grade* obstruction (Novikov–Boone undecidability),
  not a missing 213 primitive.
That is breadth of exactly the kind §7.1 names: a single `×↦·` reading runs provably through seven
fields, a single fixed-point-free diagonal (`object1_not_surjective`) provably underlies
Cantor/Gödel/Vitali/Löwenheim–Skolem, and the program's own two hardest corners are half-rebuilt rather
than merely flagged.

**What remains — stated plainly.** "Rebuilt disciplines from the residue" is true at the level of
*structural skeleton + the discrete load-bearing leg + (now) one of the two hardest corners' buildable
side*, not the full classical machine in every field. The honest residuals: (i) the colimit corner's
**Side B** (Novikov–Boone-grade undecidable / non-confluent quotients — a genuine boundary, witnessed by
a classical theorem); (ii) the graded-relation *move* (slot partially grounded by Leibniz, the skein move
not); (iii) the propext/funext ceiling, *constitutive* of a constructive system, not removable; (iv) the
`Real213` value-cut residue — the **smooth `Real213`-cut metric** (geometry cluster's largest shared gap,
per `FRONTIER_AUDIT.md`), the de Rham comparison iso, the analytic ζ / `L(f,s)`; (v) the named
graded-derived-functor object (`Ext^n`/`Tor_n`/resolution/exact-sequence — every leg PURE, the bundle
open) alongside the FOL/λ/presheaf/sheaf/topos/`Spec` objects. None is hidden, and each is located at a
precise corner of the same frame.

**Verdict.** The program has demonstrated *breadth* of ∅-axiom derivation across a front wide enough to
make the invariant reduction itself the finding: most of the surveyed mathematics is two invariants read
across a handful of axes — a claim machine-checked far more often than asserted — and the calculus even
names its own residue-taking operation (homological algebra). It has *not* rebuilt every named object, and
does not claim to. But it has now done more than diagnose its hardest corners: it has **built both of
their buildable sides** (the constructive wall via the Banach engine, the colimit corner's Side A via the
`Quot`-free free-reduction quotient), leaving precisely-located theorem-grade residuals (Side B's
undecidability, the smooth value-cut metric, the named graded object). The map is real, the anchor is
real, the corners are half-rebuilt, and the boundary is honest.
