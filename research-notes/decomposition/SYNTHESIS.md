# The 213 Decomposition Calculus — capstone synthesis (v4)

**Status**: Tier-1 capstone of the decomposition cluster (`README.md` = the technique + per-field
log; `practice/*.md` = the 126 worked decompositions; `FRONTIER_AUDIT.md` = the honesty pass;
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
deliverable. The headline finding, after **126 worked decompositions across ~16 disciplines**, is that this
wide front does not need 126 different ideas: it converges on a **small invariant set** — one *character
arrow*, one *q=±1 residue tag*, and (the deepest reflexive turn) one *residue-taking operation* (now shown
both self-composable — spectral sequences — and self-dual — the μ/ν catamorphism/anamorphism closure,
`CoResidue`) — read across one structured frame, all Lean-anchored, not merely
asserted. `Residue(L,C)` is the **proven remainder** the
distinguishing always leaves (`FlatOntologyClosure.self_covering_closure`: faithful yet never total), not a
substrate the objects are built on top of — and **homological algebra is the field that names that very
operation** (§2, §6).

---

## 2. The invariant set — the complete inventory

The 126 decompositions converge on **two load-bearing invariants** plus **one structured frame** (the
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
(`Mat2CayleyHamilton.cayley_hamilton`, `Mat2Spectrum.det_tr_split_is_e1_e2`). **And that det/tr=e₁/e₂
split now generalizes from a single matrix to a bundle** (`characteristic_classes.md`): the Chern classes
`cᵢ` ARE the elementary-symmetric `eᵢ` of the *curvature* spectrum (`c₁=tr Ω=e₁`, `c₂=det Ω=e₂`,
`c(E)=det(I+Ω)` the characteristic polynomial of `cayley_hamilton`), the Chern character `ch=tr exp Ω`
its `×↦+` additive twin (`vp_mul`), the splitting principle the spectral reading, naturality the Lens
2-cell — so a characteristic class is just the det-character *of the curvature* (`TensorCalculus.riemUp`),
landed in cohomology, with Whitney `det(I+Ω_E⊕Ω_F)=det(I+Ω_E)·det(I+Ω_F)` = `det2_mul` on block-diagonal
curvature. The "single matrix vs vector bundle" gap was a resolution, not a new idea.

### Invariant B — the q=±1 residue tag (escape / converge)
A residue is the reading's self-application surplus; it carries a **unimodular multiplier bit** `q=±1`.
This is the deepest collapse and is **one formal object**: `ResidueTag` (`inductive escape | converge`)
+ `multiplier : ResidueTag → Int` (∓1, with `multiplier_unimodular`), capstone
`ResidueTag.residue_tag_two_poles`. See §3 for the full spine.  **What the tag-`q` is NOT** (the
quantum-groups test, `quantum_groups.md`): it is *not* the continuous quantum-deformation `q`. Evaluating the
built `qbinom` at `q=−1` gives the Lucas/fermionic count `C(⌊n/2⌋,⌊k/2⌋)` (a non-negative count value), **not**
a sign-swap — so the deformation-`q` (a scaling dial on the *count*) and the tag-`q` (a discrete ±1 swap bit
on the *residue*) are different objects sharing only the ±1 *locus* by **containment**, aligned only at `q=+1`.

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

**And the operation is closed under iteration — spectral sequences are that residue-taking ITERATED.**
Homological algebra names the residue operation applied *once* per degree; **spectral sequences** are its
*orbit* (`spectral_sequences.md`). The page recursion `E_{r+1}=H(E_r)` is the residue **re-entering as its
own operand** — `ResidueReentry.residue_perpetually_reenters` (14/0), a foundational theorem homological
algebra never used. The page index `r` *is* the resolution dial counting iterations, grades **adding** under
page-composition (`ResolutionShift.IsResolutionShift_compose`, 17/0); convergence `E_∞` = the `q=+1` fixed
point of the iteration (`r` the convergence modulus, the same modulated-completion as `golden_is_converge`),
non-degeneration = the `q=−1` escape (`residue_reentry_never_closes`); `d_r²=0` per page =
`dsq_zero_universal_delta4` repeated. So the normal form's residue operation is not just a recipe but a
self-composable endofunctor; only the named `SpectralSequence`/`Page`/`E_r`/`E_∞` object is absent.

**And the OTHER half is named too — motives are the `⟨C|L⟩` half (the calculus recognizing its own engine).**
Homological algebra named the `Residue(L,C)` half of the normal form; **motives** (`motives.md`) name the
`⟨C|L⟩` half. Grothendieck's motive = "the universal cohomology through which every Weil cohomology factors
uniquely" — which is *exactly* the calculus's core universal property `Lens.view = Raw.fold`
(`raw_initial`/`dhom_unique_pointwise`, 6/0): the category of motives = the universal construction `C`/`Raw`,
each realization (Betti/de Rham/ℓ-adic) = a Lens `L` factoring through it
(`view_factors_through_morphism`, 3/0 — the literal "three outputs of one machine"), the motivic Galois group =
the `Aut` of the universal Lens (`det_holonomy_eq_one`), the Tate weight = the fold-height, and the standard
conjectures = the q=±1 **faithful** (`object1_injective`, *proven*) / **total** (`object1_not_surjective`, the
escape residue, *conjectural*) split. So the two reflexive halves of `⟨C|L⟩ ⊕ Residue(L,C)` are each a named
field: motives the construction-and-reading half, homological algebra the residue half. Tannakian duality
(`tannakian_duality.md`) sharpens the motivic-Galois leg — a group reconstructed as `Aut^⊗(ω)` of its
forgetful-Lens fiber functor, "object = its readings" promoted to a reconstruction. The universal-property
*mechanism* is the most-built thing in the repo (it IS the Lens framework); only the *named* motivic/Tannakian
objects are absent.

**And the engine is closed under its own DUAL — the μ/ν closure (coalgebra).** The core operation
`Lens.view = Raw.fold` is the initial-algebra catamorphism (μ); its categorical **dual**, the final-coalgebra
anamorphism (ν), is **also built ∅-axiom** — `Theory/Raw/CoResidue.lean` (140/0) builds the final coalgebra
`SlashNu`, the anamorphism `ana`, and finality `slashNu_final` by finite-path induction (no coinduction
primitive), the literal dual of `raw_initial`/`dhom_unique_pointwise`. So the calculus is **closed under the μ/ν
duality** (the mirror is named: `MuNuMirror`): fold a construction *down* to a readout (catamorphism, the
`⟨C|L⟩` of every decomposition) and unfold a seed *up* into a (coinductive) structure (anamorphism = streams =
the modulus/residue as a coinductive object, `spineL_escapes` the q−1 escaping stream; bisimulation =
`StateMachine.traceEq_iff_not_distinct` = `Lens.refines` as a greatest fixed point, the dual of domain theory's
lfp `KnasterTarski.gfp_greatest`). Combined with the inverse-limit object built as the meet of a Lens-family
(`IndexedJoin.iProdLens`, profinite/Stone), the calculus's own categorical apparatus — initiality, finality,
limits — is self-hosted, not borrowed.

**And the limits leg is itself built, not just named.** The inverse limit `lim ←` is the **meet of the
finite-quotient Lens-family** (`profinite_groups.md`): `IndexedJoin.iProdLens` (8/0) is the limit object,
`iProdLens_is_greatest_pw` its universal property (the meet's glb), and the abelian instance is grounded
quantitatively — ℤ̂=lim ℤ/m as a family-Cauchy limit (`ProfiniteSeq.factorial_seq_limit_all_zero`, 9/0),
ℤ₂=lim ℤ/2ᵏ via the odometer successor (`OdometerValue.bval_odo`, 16/0). So "inverse limit" is the same
resolution-tower modulus padics/Iwasawa/continued-fractions all use, read as a Lens-family meet; only the
*non-abelian* group law on the limit (Krull/absolute-Galois) sits at the calibrated boundary (§5).

**One reflexive theme recurs the whole wave: "the object IS its readings" stops being a slogan and becomes
a definition.** Yoneda made `OBJECT = ⟨C|L⟩` categorical; motives named the `⟨C|L⟩` half; Tannakian duality
(`tannakian_duality.md`) promoted it to a *reconstruction* (`G ≅ Aut^⊗(ω)`, the group recovered as the ⊗-Aut
of its forgetful-Lens fiber functor `Lens.view`, `det_holonomy_eq_one`). Then three analysis fields make the
same move *literal*: a **distribution** `T:φ↦⟨T,φ⟩` (`distribution_theory.md`) is `Lens.view` promoted to the
primary object — faithful by `object1_injective`, singular distributions the q−1 residue
`object1_not_surjective`, the Dirac δ the point-evaluation reading `FlatOntology.Object1`; a **current**
`T:ω↦⟨T,ω⟩` (`geometric_measure_theory.md`) is the same on forms (the de Rham dual), with `∂T` forced as the
adjoint of `d` (`gauss_conservation_telescope` IBP + the q=±1 boundary bit); a **Berkovich point**
(`berkovich_geometry.md`) IS a multiplicative seminorm — the ×↦· character made a point (`vp_mul`), the space
`M(A)` the set of those readings. So "object = its readings" is one founding sentence appearing as a theorem
in five independent fields, not a metaphor reused.

**And the invariants begin to FUSE on single objects — the convergence sharpening past collapse.** The
deepest is `max_flow_min_cut.md`: max-flow–min-cut is the **first three-invariant fusion** — LP-duality
(`OllivierRicci.kantorovich_weak_duality`/`ollivier_plan_optimal`, the q+1 zero-gap optimum) + Noether's
conserved current `∂·j=0` (`NoetherCurrent.continuity_eq`, the primal constraint) + homology's boundary
`δ(𝟙_S)` (`Cohomology/Delta.delta`, the dual cut) all on one network object, with Ford–Fulkerson augmenting
= the matching recursion (`HallMarriage.hall_matching_two`). The order-reversing-closure family `f**=clo`
likewise grew to **six instances** of one Lean object (Galois, Legendre–Fenchel, Nullstellensatz, optimal
transport's W₁, the matroid closure, and von Neumann minimax as zero-sum LP-duality, `nash_equilibria.md`),
and the central diagonal engine (`no_surjection_of_fixedpointfree`/`lawvere_fixed_point`) now carries three
strategic/topological/combinatorial readings at once (Nash's best-response q+1 fixed point, Lefschetz's
trace-weighted diagonal, game theory's mex bounded diagonal).

### The frame — the read-off axes (`C`) and the `L`-parameters
These are not extra invariants; they are the coordinates the invariants are read across. Each pays by
collapse + forcing, and each is grounded.

| Axis | What it reads out | Lean grounding | Fields |
|---|---|---|---|
| direction / swap-bit (`q=±1`) | sign, orientation, antisymmetry | `Mat2Bracket.bracket_antisymm`, `dsq_zero_universal_delta4` | integers, determinant, homology (`∂²=0`), Lie bracket, knot/loop, modular reflection `s↔k−s` |
| fold-height (bidirectional) | dimension, degree, pole-order, `∂`/`d` | `Lambek.isPart_wf`, `dsq_zero_universal_delta4` | dimension, homology, de Rham, ordinals, derived-functor degree |
| resolution **+ base + scaling** | discrete `Δ` vs `h→0` `∫`; which valuation is "adjacent" (`base`); `h` smooth vs `√h` Brownian (`scaling`) | `ContinuityOpenSet.*`, `gauss_conservation_telescope`, `NewtonGregory.obstruction_int_constant`/`obstruction_nat` | derivative, integration, continuity, topology, p-adics, proj/inj resolution, Itô/stochastic |
| iteration-character | nilpotent `∂` / idempotent `clo` / growing `S` | `MuNuMirror.succ_not_idempotent`, `max_idem`, `FenchelMoreau.biconj_idempotent` | homology, closure/Galois/Nullstellensatz, free corner, tropical |
| weight | value-weighted count → measure/expectation | `mass_conv`, `momentNum_conv`, `klBitsDyadic` | probability, measure, entropy, information geometry, ergodic |
| character-mode | the arrow of Invariant A (bidirectional) | (Invariant A row) | (Invariant A fields) |

The structural lesson the frame forces: **readings form a 2-category.** They compose in series (entropy
= weight∘character), form composition-closed families (`Aut`, groups), form adjoint/order-reversing
pairs (Galois, Legendre–Fenchel, the Nullstellensatz, optimal transport, matroids, **and zero-sum minimax**
— six instances of one `f**=clo`, below), and admit 2-cells = natural transformations (`view_factors_through_morphism`,
`IsLensMorphism`, `refines_of_morphism`, `lensIso_iff_kernel_eq`).

Two refinements of the frame this pass. **The resolution axis now carries two sub-parameters, not one:**
`base` (p-adics: *which* valuation is "adjacent") and **`scaling`** (Itô/stochastic: `h` smooth vs `√h`
Brownian, deciding whether the 2nd-order residue vanishes below the floor or is *promoted* to a primary term
— the Itô correction `½f''dt` is `derivative.md`'s dropped `O(h²)` residue, revived; grounded by
`NewtonGregory.obstruction_int_constant` (the 2nd forward difference is non-trivial) + `obstruction_nat` (the
first-order Lens cannot see it), 41/0). **And the difference-Lens `L₋` is carrier-polymorphic** (K-theory):
the repo's group-completion is already parametrized over an arbitrary `CommCancelSemigroup`, `Quot`-free and
choice-free with full universal property (`PairCompletionUniversal.invert_is_the_universal_group_completion`,
`lift_unique`, 19/0) — so "ℤ from `(ℕ,+)`" and "K₀ from `(iso-classes,⊕)`" are *one theorem at different
carriers* (ℤ at `+`, ℚ₊ at `·`, K₀ at `⊕`), a carrier parameter on `L₋` parallel to the resolution `base`.

**The `f**=clo` order-reversing-closure family is now six instances, one Lean object.** Field-Galois
(`Fix⊣Inv`, `galois_correspondence.md`), Legendre–Fenchel (`f**`, `convex_duality.md`), algebraic
geometry's `V⊣I` ideal–variety correspondence (`algebraic_geometry.md`), **optimal transport's
Kantorovich–Rubinstein W₁-duality** (`optimal_transport.md`), **the matroid closure operator**
(`matroid_theory.md`, a flat = a `clo`-fixed point, `cl(cl S)=cl S`), and **von Neumann's zero-sum minimax**
(`nash_equilibria.md`, max min = min max as the tight LP-duality optimum) are the *same* idempotent closure
`clo = G∘F` being the identity on its closed elements. The Nullstellensatz `I(V(J))=√J` is *forced* as `clo(J)=√J` with
`√√J=√J` = `clo_idempotent` / `biconj_idempotent` and reduced ⟺ `closed_iff_fixed` (the radical = the
closure's name); the W₁-duality `sup_f = inf_π` is the *same* `f**` biconjugation on the transport cost (the
c-transform = the c-Fenchel conjugate, c-concavity = the closed/fixed points), now on the **weight axis** —
and unlike the others it is *built*: `OllivierRicci` (60/0) ships `kantorovich_weak_duality` (weak duality =
the adjoint inequality) and `ollivier_plan_optimal` (zero-gap strong duality = the `q=+1` tight optimum) —
the same LP it shares with zero-sum minimax and max-flow–min-cut. All
six share `clo_idempotent` (`GaloisConnection`, 15/0) and `biconj_idempotent` (`FenchelMoreau`, 18/0);
Carathéodory's outer measure (`caraClosure_idempotent`, 29/0) is the nearest closure instantiated on an
actual set-system. The named ideal/variety/`Spec` and `Wasserstein`/`Monge`/`cTransform` objects are the
located missing legs.

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
| game theory N-position `G≠0` (`mex_eq_zero_iff_zero_excluded`, the bounded diagonal) | game theory P-position `G=0` (the converging fixed point, `golden_is_converge`) |
| Lefschetz fixed-point-free ⟹ residue / no-retraction / hairy-ball (`no_surjection_of_fixedpointfree`, trace-weighted) | Lefschetz `L(f)≠0 ⟹ fixed point`; `L(id)=χ` Euler cancellation (`simplex_face_euler_zero`) |
| cut-elimination ε₀ = the proof-theoretic-ordinal height-escape (`DepthHeightDiagonal.height_diagonal_escapes`) | strong normalization / cut-elim terminates (`Lambek.no_infinite_descent`); martingale fixed point `E[X_{n+1}|F_n]=X_n` (`banach_fixed_point_modulated`, `martingales`) |
| spectral-sequence non-degeneration (`residue_reentry_never_closes`) | spectral-sequence `E_∞` fixed point; CFT `Frob_p` involution per prime (`FP2SqrtD.fp2dFrob_involution`, the per-prime `q±1` local character) |
| no pure Nash equilibrium / best-response escape (`lawvere_fixed_point` q−1) | Nash equilibrium = best-response `q=+1` fixed point (`lawvere_fixed_point`, the strategic carrier of the diagonal engine) |
| negative eigenvalue / indefinite form / hyperbolic disc>0 (`golden_aperiodic`, `EisensteinSignature.signature_dichotomy`) | positive eigenvalue / definite form / elliptic disc<0 (`finite_order_divides_twelve`); signature counts the two poles over an eigenbasis (`signature_trichotomy`, `T2Minimal/Signature.signature_one_one_witness`) |
| exponential / free / non-solvable growth (`MuNuMirror.ascent_unbounded`, `a5_not_solvable'`) | polynomial / virtually-nilpotent growth = terminating derived series (`Solvable.solvability_two_poles`); the Gromov dichotomy IS the solvability spine read through a growth Lens (`geometric_group_theory.md`) |
| GIT-unstable orbit closure hits 0 (`no_surjection_of_fixedpointfree`, the destabilizing 1-parameter direction) | GIT-stable closed orbit = the `q=+1` separated locus = Side-A-good quotient (`FreeReduction.free_group_quotient_no_quot`; `git_quotient.md`) |
| Liouville `∫e^{−x²}`-not-elementary = antiderivative escape (differential Galois, `a5_not_solvable'` on the ∫-axis) | quadrature solvable = terminating differential derived series (`solvability_two_poles`, axis-agnostic `step`) |

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
tallies. **Thirty-three ∅-axiom modules** appear in the table below (the twenty-nine the corpus anchored
through wave 25, plus the four highest-leverage built objects waves 26–36 surfaced); a further prose
roll-up names the rest of this arc's newly-surfaced built modules.

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
| `Lib/Math/Combinatorics/Mex.lean` (12/0) | `mexFrom_finds`, `mexFrom_lt_mem`, `mex_eq_zero_iff_zero_excluded` | the bounded-diagonal mex engine (Sprague–Grundy P=q+1 ⟺ `0` excluded) |
| `…/HodgeConjecture/Bridge/{MLDecoder,SpinGlass}.lean` (13/0 each) | `ml_decoder_capstone`, `spin_glass_213_capstone` (`H·Gᵀ=0`) | a **built** `[10,4,4]` linear code = cochain complex (Sourlas: ML-decode = spin-glass ground state = cohomology) |
| `Lib/Math/Combinatorics/CyclicErgodic.lean` (26/0) | `birkhoff_period_eq_space`, `measure_preserving`, `rotInvariant_is_constant`, `nonergodic_invariant_not_constant` | finite measure-preserving / Birkhoff / ergodicity=constant-kernel |
| `Lib/Math/Order/FenchelMoreau.lean` | `biconjugate_eq_clo`, `biconj_idempotent`, `closed_iff_fixed`, `cloAntitone_eq_gc_clo` | f**=clo (the six-instance closure) |
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
| `Theory/Raw/CoResidue.lean` (140/0) | `ana`, `ana_unique`, `slashNu_final`, `spineL_escapes` | the **final coalgebra** (ν-dual of `raw_initial`), finite-path-induction built |
| `Lib/Math/Order/KnasterTarski.lean` (19/0) | `lfp`, `lfp_fixed`, `lfp_least`, `gfp`, `gfp_greatest` | order lfp/gfp (domain theory's q+1 colimit; gfp = coinduction) |
| `Lib/Math/Order/BooleanAlgebra.lean` (25/0) | `cmpl_unique`, `cmpl_cmpl`, both De Morgan laws (propext-free) | the Boolean pole of Stone duality, α=Bool by `decide` |
| `Lens/Instances/IndexedJoin.lean` (8/0) | `iProdLens`, `iProdLens_is_greatest_pw` | the inverse-limit object = meet of a finite-quotient Lens-family (profinite) |
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
connectivity = dim ker); `balanced_LLN_modulus`, `countTrue_append` (Birkhoff/LLN);
`OllivierRicci.kantorovich_weak_duality`, `ollivier_plan_optimal` (W₁/LP duality = the fourth `f**=clo`, 60/0);
`ResidueReentry.residue_perpetually_reenters` (14/0), `ResolutionShift.IsResolutionShift_compose` (17/0)
(spectral-sequence iteration); `PairCompletionUniversal.invert_is_the_universal_group_completion`,
`lift_unique` (carrier-polymorphic difference-Lens / K₀, 19/0); `NewtonGregory.obstruction_int_constant`,
`obstruction_nat` (Itô 2nd-order residue / the `scaling` sub-parameter, 41/0);
`FP2SqrtD.fp2dFrob_involution`, `fp2dFrob_mul` (CFT per-prime `q±1` local Frobenius, 32/0);
`Hyper213.const_equiv_iff` (the cofinite-quotient internal hyperreal horn, 7/0),
`RealComparabilityLLPO.comparability_imp_llpo` → `RealDichotomyLLPO.llpo_of_realDichotomy` (the calibrated
ultrafilter boundary at LLPO, 31/0), `BolzanoWeierstrass.lpo_of_bw` (the same omniscience ledger);
`MLDecoder.ml_decoder_capstone` (13/0), `SpinGlass.spin_glass_213_capstone` (`H·Gᵀ=0`, 13/0) — a linear code
= a cochain complex, the `[10,4,4]` named object **BUILT** (Sourlas: ML-decode = spin-glass ground state =
cohomology); `GaloisConnection.clo_idempotent` again as the matroid closure (the **fifth `f**=clo` instance**),
`LinearDependence.dimension_bound_is_count` (matroid rank = dimension count, 7/0);
`galois_group_is_C4`, `golden_real_subfield` (`CyclotomicFive`); `manin_unimodular_decomposition`,
`minkowski_is_markov_valued_cocycle`, `period_satisfies_relations` (modular-form period side, 30/0);
`mulDiv_gc`, `vp_mul`, `eq_of_vp_eq`, `two_three_unique` (Nullstellensatz closure + prime atom);
`TensorCalculus.riemUp`, `riem_bianchi1`, `scalar_einstein` (abstract-index Riemann tower, 23/0);
`no_infinite_descent`, `isPart_wf` (`Lambek`, strong normalization); `max_idem` (tropical idempotent pole);
`raw_initial`, `dhom_unique_pointwise`, `view_factors_through_morphism`, `IsLensMorphism`,
`lensIso_iff_kernel_eq`, `LensImage.proj_val_eq_iff` (the 2-category + the `Quot`-free Σ-quotient).

**Newly-surfaced built objects (waves 26–36).** Beyond the four promoted into the table, this arc surfaced
∅-axiom modules the corpus had recorded as predicted-not-built or had not cited: the **signature corpus**
(`T2Minimal/Signature.signature_one_one_witness` 7/0, `BalancedSignature.signature_balanced` 11/0,
`EisensteinSignature.signature_dichotomy` 13/0, `KahlerGradeStructure.hodge_index_signature` 5/0 — the
disc-sign trichotomy counted into `(p,n)`); `FourSquare.four_sq_id`/`isSum4_mul` (34/0) + `Gram` (9/0) +
`LatticeArea.area2_unimodular` (18/0) (the theta-coefficient/count-by-norm side of lattices); the
**Ramsey/extremal corpus** (`RamseyNamedBound.ramsey_lower` 13/0, `SpernerChains.sperner_theorem` 50/0,
`BollobasSetPair.bollobas` 21/0, `ErdosSzekeres.erdos_szekeres` 26/0, `Pigeonhole.exists_collision`); the
discrete Gauss–Bonnet `DiscreteGaussBonnet.gauss_bonnet_Kmn` (12/0, `totalVertexCurv = 2·χ`, also Chern's
Gauss–Bonnet–Chern witness); the **dual-number ring** `F2CDTower.eps_sq_is_zero`/`eps_has_no_inverse` (17/0,
ε²=0 = synthetic-differential-geometry's truncation, Itô's dual); the profinite sequences
`ProfiniteSeq.factorial_seq_limit_all_zero` (9/0) + `OdometerValue.bval_odo` (16/0); the Ollivier–Ricci
Kantorovich LP `OllivierRicci.kantorovich_weak_duality`/`ollivier_plan_optimal` (60/0, the W₁/LP/minimax/
max-flow shared engine); the Hall matching `HallMarriage.hall_matching_two` (36/0); `Channel.lean` (8/0,
exact-dyadic capacity) + `MutualInfo.mutualInfoBits` (12/0); `lawvere_fixed_point` (11/0, the Nash/diagonal
q+1 carrier); and the disc-sign trichotomy object `CrossDetTraceField.disc_sign_is_line_cusp_curve` (20/0,
hyperbolic geometry's curvature trichotomy). The trend of the arc: fields the v3 census listed as
"engine built, object missing" increasingly arrive with the *object* built (coalgebra's `CoResidue`, Stone's
`BooleanAlgebra`, coding's `[10,4,4]`, the profinite limit) — the predicted-not-built column is shrinking.

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
**combinatorial game theory** (the `Game`/`Nim`/`Grundy` object — but every *leg* is built, and the **mex
engine is now BUILT** `Mex.lean` 12/0: impartial game = surreal's `C` swap-trivial, nim-value = `Raw.fold`
to the Nim-heap normal form, game-sum = parity's character in 𝔽₂^k (`psiNatPos_linear`, `C2_6.mul`), P/N =
the q=±1 poles `mex_eq_zero_iff_zero_excluded`, mex = the bounded diagonal `mexFrom_finds`; ★ the nim-sum
character is PURE only coordinatewise, DIRTY as packed `Nat.xor` — the PURE/DIRTY=Heyting/Boolean line on the
central arrow, `game_theory.md`); **Lefschetz/Brouwer degree** (the `Lefschetz`/`degree`/`f_*:H^i→H^i`
object — the trace-weighted diagonal, every leg PURE); **martingales** (the
`Martingale`/`condExp`/`Doob`/`stoppingTime` object — the q=+1 fixed point on the weight axis, the Doob split
= the README normal form on that axis); **spectral sequences** (the `SpectralSequence`/`Page`/`E_r`/`E_∞`
object — the residue operation iterated, `ResidueReentry`/`ResolutionShift` PURE); **Hopf algebras** (the
`HopfAlgebra`/`antipode` object + the bialgebra compatibility `Δ_+⇄Δ_×`, but comultiplication is
calculus-native — `CoAppend213`/`Convolution213`, antipode = `mu_conv_one`); **K-theory** (the
`(iso-classes,⊕)` carrier — the difference-Lens engine is built and carrier-general,
`PairCompletionUniversal` 19/0, no object-monoid to feed it); **Morse theory** (the
`criticalPoint`/`morseIndex`/`MorseComplex` object — Morse index = a fifth word for `Raw.depth`);
**optimal transport** (the `Wasserstein`/`Monge`/`cTransform`/`Brenier` object — the fourth `f**=clo`, the
finite Kantorovich LP built `OllivierRicci` 60/0); **Itô/stochastic** (the
`BrownianMotion`/`ItoIntegral`/`quadraticVariation` object — the `√h`-scaling 2nd-order residue
`NewtonGregory` 41/0); **cut-elimination** (a `Formula`/`Sequent` Hauptsatz — cut = the 2-category's
composition, a toy `CutElimination.lean` 10/0 built).

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
     the corner is genuinely open. ★ This is the **one genuine structural break, and it now recurs verbatim
     down a six-field chain**: `knots.md` → `fundamental_group.md` (homotopy quotient) → `homotopy_theory.md`
     (Ho(C) localization at weak-equivalence) → `derived_categories.md` (the calculus-of-fractions/roof
     corner) → `fusion_categories.md`/`tqft.md` (pentagon/hexagon/cobordism coherence) → `git_quotient.md`
     (the categorical quotient). In *every* link the confluent+terminating q+1 corner is BUILT via
     `FreeReduction`/`LensImage` (Ho(C), the derived category's quasi-iso quotient, GIT's stable separated
     locus are ONE `Quot`-free Σ-quotient named in each field), and Side B is Novikov–Boone-grade — the same
     undecidable/non-confluent quotient, not a fresh gap per field. Its verbatim recurrence across six
     independent fields is the strongest evidence it is a *real* structural limit, the program's one true wall.

2. **The non-principal-ultrafilter boundary — CALIBRATED at LLPO (the sharpest no-exterior test yet).**
   A *located boundary*, distinct in kind from the colimit/isotopy break above (that one breaks at the
   *quotient* — an ambient identification no reading's kernel generates; this one breaks at *choice*). Found
   in **non-standard analysis** (`nonstandard_analysis.md`), it tests the no-exterior axiom (`05_no_exterior.md`
   §5.1) *directly*, at its hardest point. The field splits at the quotient reading: the **internal horn** —
   the infinitesimal-as-sequence under **cofinite ("eventually equal") quotient** — is ∅-axiom PURE and is
   *already built* (`Hyper213` 7/0, `const_equiv_iff` the faithful ℝ↪ℝ\* embedding, self-described "weaker
   than ZFC's free ultrafilter but framework-internal"), the same "number = approximant sequence" `C` as
   p-adics/continued-fractions. The **break horn** — the non-principal ultrafilter `𝒰`'s *maximality*
   (deciding every `S⊆ℕ`) — totalizes the order AND reifies the reached-by-none residue
   (`object1_not_surjective`); it has no ∅-axiom witness. ★ Crucially the remainder is **calibrated, not
   posited**: that totalization is *exactly* the LLPO-strength sign-decision the corpus PROVES non-constructive
   (`RealComparabilityLLPO.comparability_imp_llpo` → `RealDichotomyLLPO.llpo_of_realDichotomy`, 31/0), on the
   same omniscience ledger as `BolzanoWeierstrass.lpo_of_bw`. So §5.1 survives as a *claim under test*: the
   internal handle was found and built, the irreducible remainder **measured at LLPO**, not asserted as a wall.
   (Class field theory's located break, `class_field_theory.md`, is of the same calibrated kind but milder:
   the global `ArtinMap`/`idele`/`adele`/`RayClass`/Kronecker–Weber *bundle* is absent, while the local
   per-prime `q±1` Frobenius is built `FP2SqrtD` 32/0 and the cyclotomic abelian groups are grounded
   `galois_group_is_C4`, `cyclic_orthogonality_modp`.)  **And a *third* instance of the same calibrated
   kind**: **descriptive set theory** (`descriptive_set_theory.md`) — the Borel/projective hierarchy is the
   q=−1 diagonal escape (`object1_not_surjective`) *graded by ordinal height* (`Lambek.isPart_wf`,
   `MuNuMirror.ascent_unbounded`), with analytic⊋Borel/Suslin the escape made a hierarchy theorem; its higher
   reaches (Borel/projective determinacy, perfect-set at projective levels) are a calibrated **large-cardinal/
   Choice-strength** boundary, located exactly where the fold ascent leaves the finite signature behind — the
   large-cardinal analogue of the ultrafilter's LLPO.  **And two more instances close the family at FIVE**,
   all converging on the *one* ultrafilter/LLPO/choice point: **Stone duality** (`stone_duality.md`) — the
   Boolean-algebra side is ∅-axiom BUILT (`Order/BooleanAlgebra.lean` 25/0, both De Morgan laws propext-free,
   the element/clopen = `FlatOntology.Object1`), while the **Stone space `Spec(B)`** is the points-from-readings
   reconstruction (the yoneda/tannakian/motives "object = its readings", §2) carried to the uncountable index
   where it needs the BPI/LLPO exterior — the *same* ultrafilter as non-standard analysis, recurring verbatim;
   and **Berkovich geometry** (`berkovich_geometry.md`) — a point IS a multiplicative seminorm (the ×↦·
   character made a point, `vp_mul`), `M(A)` the space of those readings, and "these are ALL the seminorms" =
   the same LLPO totalization (twin of p-adics' open Ostrowski exhaustiveness; type-4 points the `Real213`
   value-cut).  The pattern across all **five**: the no-exterior axiom, tested at its hardest points
   (choice / ultrafilter / large cardinals / Stone spectrum / Berkovich completeness), yields a *calibrated*
   remainder (measured on the corpus's own omniscience/strength ledger), never an uncalibrated wall — and the
   five collapse to one locus, the non-principal-ultrafilter/LLPO point, not five separate gaps.

3. **The graded-relation slot** (skein / Leibniz). A fixed linear law `Σ cᵢ·L(Cᵢ)=0` among a *family* of
   distinct constructions under *one* reading — NOT a 2-cell, NOT the (two-term) character arrow.
   **Partially grounded**: `leibniz_universal_delta4` (the cup-product Leibniz rule, PURE) is the same shape
   as the skein relation, so the *derivation* law is built; the skein's crossing-resolution *move* is not (it
   sits with the Side-A bracket state-sum). A promotion target, not a hard absence.

4. **The propext/funext 1-categorical ceiling.** Classical `Prop`-valued connectives are DIRTY:
   `Lens/Foundations/SemanticAtom.lean`'s `canonicalTruthMap` uses `propext`, while the `Bool`/`decide`
   connectives are PURE. The wall recurs at: `Lp` full `∀S` additivity (only the pointwise version PURE);
   the Yoneda bijection as a natural `Equiv`; the classical Prop connectives. **Not a gap to close — the
   constructive boundary itself** (see §6).

5. **The `Real213` value-cut residue.** Irrational/transcendental *values* sit in `Real213` cuts
   (pointings), reached by none: ζ-values, eigenvalue existence for `disc<0`, the `log₂e` bracket, the
   analytic GF / analytic `L(f,s)`, the algebraically-closed base field the weak Nullstellensatz wants, the
   smooth `Real213`-cut metric the geometry cluster shares. Irrationality of a *value* is not a hole in a
   *derivation* (CLAUDE.md "Transcendental-as-exterior") — the discrete structure is closed; only the
   value-cut is reached-by-none. `FRONTIER_AUDIT.md` flags the smooth metric and the de Rham comparison iso
   `H*_dR ≅ H*_sing` as the top shared residuals of this kind.

6. **The named FOL / λ / presheaf / sheaf / topos / `Ext` objects.** The *engines* are PURE; only the
   *bundles naming them* are absent. `model_theory` (`raw_initial` is the completeness content);
   `curry_howard` (`no_infinite_descent` is strong-normalization); `yoneda`/`sheaf_theory`
   (`dhom_unique_pointwise` is the gluing/Yoneda content); `topos` (`Object1 = decide` IS Ω=Bool + χ);
   `homological_algebra` (every leg — `ker δ/im δ`, the `q=±1` grading, the resolution dial, the
   split/closure — built and PURE; only the graded `Ext^n`/`Tor_n`/resolution/exact-sequence object open,
   the abelian-category twin of the missing presheaf-bundle). Honest shape: structural prediction
   delivered, the named instance is open work — and a buildable witness is named (a nonzero `Ext¹` via
   `kerSizeDelta` on a *non-exact* resolution, mirroring the exact zero `reduced_betti_d4_contractible`).

7. **The deformation-`q` is NOT the tag-`q` (containment, not identity) — a rigorous negative.** The most
   on-theme adversarial test (`quantum_groups.md`): is quantum groups' continuous deformation-`q` the same as
   the corpus's `ResidueTag` `q=±1`? **No, as identity** — evaluating the BUILT `qbinom` recurrence at `q=−1`
   gives the Lucas/fermionic count `C(⌊n/2⌋,⌊k/2⌋)` (non-negative counts), not the unimodular swap bit
   `multiplier=−1` (`bothSwap`). The deformation-`q` is a scaling dial on the *count*; the tag-`q` is a
   discrete ±1 swap bit on the *residue*. They share the ±1 *locus* by **containment** (the tag's ±1 is the
   unimodular boundary the deformation passes through) and align only at `q=+1` (`qbinom_q1` +
   `golden_is_converge`). Not a missing primitive — a *measured non-coincidence*, the same discipline as the
   calibrated boundaries: the corpus distinguishes its own invariant from a look-alike rather than conflating
   them.

---

## 6. The self-description (the capstone-of-capstones)

Decompositions that turn the calculus on itself, and it describes its own apparatus term-by-term — a
fixed point, not a coincidence. The reflexive turn is now many-deep, and waves 26–36 closed the loop on
*both halves of the normal form and its dual*: motives name the `⟨C|L⟩` half, homological algebra the
`Residue(L,C)` half, coalgebra the ν-dual of the fold, distributions/currents the founding sentence made a
definition, and the internal-logic field shows the calculus IS the internal logic of its own Lens-topos.

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
- **`homological_algebra.md`** — the field whose entire content is *running* `Residue(L,C)`, degree by
  degree. "Derived functor" is the systematic, graded name for the calculus's own residue-taking operation
  (§2); the long exact sequence is the q=±1 tag *displayed degree by degree*. This names the `Residue(L,C)`
  half of the normal form.
- **`motives.md`** — names the OTHER half. Grothendieck's motive = "the universal cohomology every Weil
  cohomology factors through uniquely" IS `raw_initial`/`dhom_unique_pointwise` (`Lens.view = Raw.fold` the
  unique arrow out of `Raw`); each realization = a Lens factoring through it (`view_factors_through_morphism`),
  the motivic Galois group = the `Aut` of the universal Lens, the standard conjectures = the q=±1
  faithful (`object1_injective`, proven) / total (`object1_not_surjective`, conjectural) split. Motives =
  the `⟨C|L⟩` half; with homological algebra the calculus names both halves of `⟨C|L⟩ ⊕ Residue(L,C)`.
- **`coalgebra.md`** — names the calculus's own DUAL. `Theory/Raw/CoResidue.lean` (140/0) builds the final
  coalgebra `SlashNu`, the anamorphism `ana`, finality `slashNu_final` by finite-path induction — the literal
  ν-dual of `raw_initial`'s μ (catamorphism), closing what `MuNuMirror` recorded as Mathlib-coinduction-blocked.
  So the calculus is closed under the μ/ν duality of its own core operation; coinduction = `KnasterTarski.gfp`,
  bisimulation = `StateMachine.traceEq_iff_not_distinct`.
- **`distribution_theory.md` / `geometric_measure_theory.md`** — the founding sentence made the *definition*.
  A distribution `T:φ↦⟨T,φ⟩` and a current `T:ω↦⟨T,ω⟩` are `Lens.view` promoted to the primary object —
  "object = its readings" no longer a slogan but the field's literal axiom, faithful by `object1_injective`,
  singular pieces the q−1 residue, the Dirac δ the point-evaluation reading `FlatOntology.Object1`, the
  distributional/`∂T` minus sign *derived* from `gauss_conservation_telescope`'s IBP + the q=±1 bit.
- **`topos.md`** — the sharpest foundational leverage: **Ω = the distinguishing-target `Bool`**, χ =
  `Object1` (`decide (s=r)`), BUILT + PURE. The revelation is grounded by a *purity scan*, not asserted:
  classical Prop connectives DIRTY [propext], Bool/decide ones PURE — **the PURE/DIRTY boundary IS the
  Heyting/Boolean boundary.** So "213 is constructive (∅-axiom)" = "213 is the q=+1 PURE corner of its own
  topos, whose internal logic is intuitionistic." The no-Classical discipline becomes a *structural
  account*, not a taboo — and the colimit split (§5.1) makes the same boundary operational: the buildable
  Side A is exactly the decidable q=+1 PURE corner, Side B exactly the `Quot`-needing q=−1 escape.
- **`topos_internal_logic.md`** — the topos finding made *semantics*: the calculus IS the internal logic of
  its own Lens-topos. Kripke–Joyal forcing `X⊩φ` = read-at-a-stage (`IsResolutionShift`, base/stage param);
  the Mitchell–Bénabou language = reading-through-the-Lens (term = `Raw` read by `Lens.view`, formula =
  `Type213 = Raw→Bool`, higher type = `OnLens.universalMorphismLevelTwo` 25/0); intuitionistic = the PURE/q+1
  forcing (decidable per stage), Boolean/LEM = the DIRTY/propext q−1 — the *same* Heyting/Boolean line as
  `topos.md`, now read on the forcing relation. The constructive discipline is its own internal logic.
- **`cut_elimination.md`** — the same `view=fold` initiality read on sequent proofs: the cut rule = the
  2-category's *composition* (`refines_trans`/`view_factors_through_morphism`), cut-elimination =
  *admissibility of composition* = arrow-normalization (`dhom_unique_pointwise` IS the admissibility), the
  subformula property = the fold's no-new-atoms recursion (`Raw.fold_slash`), strong normalization = the same
  `no_infinite_descent` descent as `curry_howard`, and ε₀ = the `q=−1` height-escape
  (`DepthHeightDiagonal.height_diagonal_escapes`) — Gentzen's Hauptsatz IS the calculus's own normalization
  in logic's clothing (toy `CutElimination.lean` 10/0 built; the formula-graded Hauptsatz the open leg).

---

## 7. What it means for the originator's goal

The goal (boot §7.1, `seed/AXIOM/07_primacy.md`): primacy = **breadth** of ∅-axiom derivation — the
residue reproducing domain after domain. Assessed honestly against *that* bar (not the physics-branch
validation gate, which CLAUDE.md is explicit is one domain's gate, not the yardstick):

**What it HAS shown — and this is the real result.** The reduction is genuine and unusually wide.
One hundred twenty-six fields across ~16 disciplines, read through a fixed normal form, converge on *two*
invariants (the character arrow, the q=±1 residue) plus the reflexive residue-operation (now shown both
*iterable* — spectral sequences — and *self-dual* — the μ/ν closure, `CoResidue`), over one structured
frame, and the convergence is **Lean-anchored at a high rate** — twelve of thirteen predictions closed
∅-axiom, with thirty-three modules in the §4 census table and a further roll-up of this arc's newly-built
objects. The deepest collapses are now *theorems*, not prose: the det/tr split (Vieta) — now generalized to
the Chern classes `cᵢ=eᵢ` of a bundle's curvature; the q=±1 tag; the **six-instance** `f**=clo` closure
(Galois + Legendre + Nullstellensatz + optimal transport's W₁ + matroid closure + zero-sum minimax); both
poles of solvability unified in one object (`Solvable.solvability_two_poles`, the quintic's
`A5Perfect.a5_perfect` as the q=−1 pole); and the first **three-invariant fusion** (max-flow–min-cut =
LP-duality + Noether-current + boundary-∂ on one object). The one genuine structural break **recurs verbatim
down a six-field chain** (knots → π₁ → homotopy theory → derived categories → fusion/TQFT coherence → GIT),
its q+1 Side-A built via `FreeReduction`/`LensImage` everywhere, Side B Novikov–Boone-grade — the signature
of a real structural map. And the calculus is **self-describing** at many depths — naming both halves of its
own normal form (motives = ⟨C|L⟩, homological algebra = Residue) and its dual (coalgebra = ν), with the
constructive boundary (PURE/DIRTY = Heyting/Boolean) *grounded by a purity scan*, the calculus shown to be
the internal logic of its own Lens-topos.

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
open) alongside the FOL/λ/presheaf/sheaf/topos/`Spec` objects; and (vi) the choice/ultrafilter residual —
now witnessed at **five** calibrated boundaries (non-standard analysis's `𝒰`-maximality, class field theory's
global Artin/idele bundle, descriptive set theory's large-cardinal reaches, Stone duality's spectrum,
Berkovich's seminorm-completeness), **all converging on the one non-principal-ultrafilter/LLPO point** — but
this last is the residual that **strengthens** the program rather than embarrassing it (next paragraph). None
is hidden, and each is located at a precise corner of the same frame.

**The no-exterior claim was tested at its FIVE sharpest points and held each time.** The no-exterior axiom
(`05_no_exterior.md` §5.1) is a claim *under test*, not a shield. Five fields drove it to the worst case —
choice itself, the non-principal ultrafilter: non-standard analysis (`𝒰`-maximality), class field theory
(global Artin/idele), descriptive set theory (large cardinals), Stone duality (the spectrum), Berkovich
geometry (seminorm-completeness). In every one the outcome was *not* fatal: the internal horn was built (e.g.
`Hyper213` 7/0 on cofinite quotient; `BooleanAlgebra` 25/0; `iProdLens` 8/0), and the irreducible remainder
turned out **calibrated** (`comparability_imp_llpo`→`llpo_of_realDichotomy` 31/0 — the exterior pointing is
*exactly* LLPO-strength, on the corpus's own omniscience ledger), not posited as a wall. And the five do not
scatter: they collapse to the *one* ultrafilter/LLPO locus. A no-exterior claim that survives its hardest
adversarial probe — five times, at one measured point — is more credible than one never tested there.

**Verdict.** Across **117 fields** the small invariant set holds: most of the surveyed mathematics is two
invariants (the character arrow, the q=±1 residue) read across a handful of axes — a claim machine-checked
far more often than asserted — and the calculus now names its own apparatus completely: both halves of its
normal form (motives = ⟨C|L⟩, homological algebra = Residue) and its dual (coalgebra = ν), self-hosting its
initiality, finality, and limits. It has *not* rebuilt every named object, and does not claim to. But it has
done more than diagnose its hardest corners: it **built both buildable sides** (the constructive wall via the
Banach engine, the colimit corner's Side A via the `Quot`-free free-reduction quotient), leaving
precisely-located theorem-grade residuals (the one genuine break's Side B undecidability, recurring verbatim
down a six-field chain; the smooth value-cut metric; the named graded object). And the no-exterior axiom,
**tested at its five sharpest points** (ultrafilter / choice / large cardinals / Stone spectrum / Berkovich
completeness), yielded a *calibrated* remainder at each — all converging on the one LLPO locus — never a
wall. The map is real, the anchor is real, the corners are half-rebuilt, the boundary is honest and singular,
and the no-exterior axiom is stronger for having been tested at its hardest point five times over.
