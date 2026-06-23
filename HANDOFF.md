# Session Handoff — 2026-06-22 (multi-agent marathon: 진의 + decomposition calculus v7)

## Branch
`claude/multi-agent-math-research-3lv3gj` — pushed. `lake build E213` clean, all new modules ∅-axiom PURE.

## ★★ CURRENT STATE (2026-06-22, 42-wave multi-agent marathon) — read `research-notes/decomposition/SYNTHESIS.md` FIRST
The decomposition-calculus program (the originator's recalibrated central direction — see RECALIBRATION below)
now spans **141 worked decompositions** (past the century mark) of mathematical fields, all reading through `OBJECT = ⟨C|L⟩ ⊕ Residue`,
converging on **two invariants** (the character arrow `×↦·`/`×↦+`; the `q=±1` residue tag, now formal in
`ResidueTag.lean`) + the reflexive deepening (homological algebra names the calculus's own residue-taking
operation; spectral sequences = that operation ITERATED). Canonical indices: **`SYNTHESIS.md`** (the capstone
map — invariants, q=±1 spine, Lean census, recurring breaks, the self-description: PURE/DIRTY =
Heyting/Boolean = why 213 is constructive), `README.md` (the technique + per-field entries),
`FRONTIER_AUDIT.md` (honesty pass). **~28 ∅-axiom Lean modules** ground the invariants (full list:
SYNTHESIS.md §4 census). **★ Two wall-style results:** (1) the constructive wall DEFEATED (modulated Banach
engine); (2) the colimit/ambient-quotient corner SPLIT — Side A BUILT ∅-axiom (`FreeReduction`, free group
as normal-form Σ-quotient, NO `Quot`) vs Side B theorem-grade (Novikov–Boone).

**Waves 16–19 (this session), 58→67 decompositions:** game theory (Sprague–Grundy = XOR character + q=±1
P/N split; `mex` engine BUILT ∅-axiom `Mex.lean` 12/0 — the bounded diagonal); Lefschetz/degree (L(f)≠0 ⟹
fixed point = the trace-weighted diagonal); martingales (q=+1 conditional-expectation fixed point, Doob =
⟨C|L⟩⊕Residue); spectral sequences (the residue operation iterated, `residue_perpetually_reenters`);
Hopf algebras (the slash read co-, comultiplication calculus-native, antipode = q−1; located break = bialgebra
compatibility F1); K-theory (= integers' group-completion difference-Lens one carrier up; the completion is
carrier-polymorphic, `PairCompletionUniversal` 19/0); Morse theory (read-a-space-by-height; Morse index = a
5th word for `Raw.depth`); continued fractions (the PUREST residue-doctrine instance — convergents = modulus,
irrational = reached-by-none); optimal transport (the FOURTH f**=clo instance, `OllivierRicci` 60/0 Kantorovich
LP built); cut-elimination (= the fold-to-normal-form on proofs; subformula property = the fold's
no-new-atoms law; ε₀ = q−1 height-escape; repo toy `CutElimination` 10/0). NonzeroBetti (56/0) closed
homological_algebra's nonzero-H¹ witness.

**Waves 20–25 (this session), 67→84 decompositions:** Itô (the resolution axis carries a `scaling`
sub-param √h, the 2nd-order residue revived); class field theory (the ×↦· character at maximal abelian
extent; located break = global idele bundle); **non-standard analysis (a CALIBRATED located boundary** —
`Hyper213` uses cofinite not ultrafilter; the ultrafilter's maximality = a non-constructive primitive
calibrated at LLPO, `comparability_imp_llpo`→`llpo_of_realDichotomy`); coding theory (named object BUILT — a
`[10,4,4]` code, the Sourlas identity ML-decode=spin-glass=cohomology, MLDecoder/SpinGlass 13/0); matroid
(5th f**=clo instance); differential Galois (galois's q±1 solvability on the ∫-axis, Liouville = q−1
antiderivative escape); operator algebras (the C*-axiom promotes spectral's disc≥0 to an axiom; Gelfand = the
character's 8th field); toric geometry (Newton polytope = the multi-var ×↦+ valuation image); symplectic
(lie q−1 + noether q+1 fused on Sp(2); ω named in `SignedCup`); random walks (harmonic = Laplacian-kernel =
martingale; found `WeightedGreen` 11/0, a stale-gap fix); **descriptive set theory (a 2nd calibrated boundary**
— the diagonal escape graded by ordinal height; projective determinacy = large-cardinal boundary); Hodge
theory (the (p,q) bigrading + signed q±1 star; the `HodgeConjecture/` tree substantially built); free
probability (R-transform = the ×↦+ free-log, semicircle = free CLT, free cumulants = non-crossing = Catalan);
percolation (thin/honest — p_c the q±1 transition, mostly analogy); renormalization group (the resolution dial
made a FLOW; DRLT tie: `1/α_3(N)=(NS²−1)·S(N)` AsymptoticFreedom 6/0); operads (Raw.fold made arity-graded;
`CombinatorialArity` proves binary-generated); TQFT (character arrow as monoidal functor ⊔↦⊗; `GRA/Monoidal`
13/0 ships `product_NT_NT_grade`).  **Wave 26 (84→87):** quantum groups (★ a precise **BREAK** — the
deformation-`q` vs tag-`q` is **CONTAINMENT not identity**: `qbinom` at q=−1 is the Lucas/fermionic table
`C(⌊n/2⌋,⌊k/2⌋)`, a non-negative count, NOT the tag's ±1 swap bit; they meet only at the ±1 locus,
`QBinomial` 11/0); information theory (mutual info = the ×↦+ character's additivity-defect = the channel
residue; `Channel.lean` BUILT 8/0); Nash equilibria (the q=+1 fixed point of best-response, a 3rd carrier of
the diagonal engine; minimax = LP duality = a 6th duality instance; Brouwer existence = a calibrated LLPO
gap).  **Wave 42 (132→135):** symmetric functions (Λ = the universal home of the elementary `eᵢ` the corpus
keeps rediscovering — det/tr=e₁/e₂, Chern, Newton; consolidating capstone), optimal control (value fn = the q+1
Bellman-contraction fixed point, Pontryagin = Noether), quantum information (no-cloning = q−1 no-surjection,
⊗ = monoidal grade, vN entropy = ×↦+ character). **Two ∅-axiom actions this turn:** (1) BUILT Newton's
identities `newton_id_p2`/`newton_id_p3`/`newton_id_p4` (3-variable `p₂=e₁p₁−2e₂`, `p₃=e₁p₂−e₂p₁+3e₃`,
`p₄=e₁p₃−e₂p₂+e₃p₁`) in `NewtonInequalities` (5/0→8/0) + `trace_sq` (`tr(M²)=tr²−2det`, the matrix-level
degree-2 power sum from Cayley–Hamilton) in `Mat2TraceRecurrence` (5/0→6/0) — and found the all-degrees
Newton–Girard recurrence for the 2-element spectrum ALREADY built (`Mat2TraceRecurrence.trace_recurrence`,
`p_{n+2}=e₁p_{n+1}−e₂p_n`).  So the power-sum↔elementary `×↦+↔×↦·` bridge is now closed at degrees 2,3,4 (3-var)
and all degrees (2-element matrix spectrum); (2) CORRECTED a
false-friend: the proposed `no_universal_qubit_copier` witness is Cantor (a no-universal-realizer fact at
`Qubit:=Bool`), NOT no-cloning — basis states ARE clonable (CNOT `U(b,0)=(b,b)`); genuine no-cloning needs the
amplitude residue, stays predicted-not-built.  Prediction tally now **13/14 Lean-closed**.  SYNTHESIS at
**v4 (count 141)**.

**Bertrand / prime-distribution arc (2026-06-23, course-corrected):** built the entire *structural* content
of Erdős's Bertrand proof ∅-axiom — `PrimePowFactorization.lean` (10/0: `prod_prime_pow_eq`, the explicit
FTA product form `m=∏p^{vₚ}`, the crux gap) + `CentralBinomFactorization.lean` (8/0: `central_binom_factorization`,
`central_binom_upper_bound` `C(2n,n)≤4^{2n/3}·(2n)^{√2n}`, `exists_prime_in_window` reducing large-n Bertrand
to two pure-`Nat` facts).  **Originator course-correction**: this was *formalization*, not the `⟨C|L⟩⊕Residue`
decomposition — the actual 213 move.  Re-read as **decomposition #136 `prime_distribution.md`**: object = the
*basis* `L_vp` presupposes (the ×-atoms as +-line positions); residue = the prime-gap structure (NOT none, the
dual of `prime_factorization.md`); Bertrand = the `q=+1` bound on that residue; Erdős's proof = the `×↦+`
character arrow forced via `C(2n,n)`'s ×-reading vs +-size.  Remaining Bertrand (pure-`Nat`, ABSENT): crossover
asymptotic + finite chain (frontier `bertrand_postulate.md`).  Lesson: "larger target" = deeper *decomposition*,
not harder formalization.

**Decomposition #137 `modular_arithmetic.md` (2026-06-23):** the residue Lens `n↦n%m` IS 213's count-Lens (§6)
— the model self-portrait.  `div_add_mod` (`n = m·(n/m) + n%m`) = `⟨C|L⟩ ⊕ Residue` as arithmetic.  **Name
disambiguation**: classical "residue" (remainder) = Lens *image*; 213 Residue = the dropped quotient — opposite
halves of one division.  CRT = coprime residue-Lens family jointly faithful (`crt_unique`).  **The `q=±1` tag's
origin**: the Legendre symbol `(a/p)∈{±1}` IS the tag on `(ℤ/p)*` (quadratic *residue* = q=+1 square) —
`euler_dichotomy`/`legendre_mul` = the tag + its multiplicativity; whence the word "residue."

**Decomposition #138 `gcd_euclidean.md` (2026-06-23):** gcd = the residue Lens ITERATED to its `q=+1`
terminating fixed point (`gcdFuel n (b%(a+1)) (a+1)`, well-founded modulus `M=max a b + a`).  Dynamic
(algorithm) = static (divisibility-lattice meet, `gcd213_greatest`), and that lattice = the count-Lens
refinement lattice (`leavesModNat_lcm`: refines=∣, meet=lcm, CRT=coprime case).  Completes the **residue-Lens
triptych**: `modular_arithmetic` (the Lens) → `gcd_euclidean` (terminating iteration, q=+1) →
`prime_distribution` (non-terminating iteration, q=−1) — the two faces of iterating `%`.

**Decomposition #139 `computability_halting.md` (2026-06-23):** the meeting of the two spines.  L_halt = the
termination reading (a↦(x↦halts?(a,x))) = a self-cover `f:A→(A→Bool)` (Gödel-coded, `Raw.toNat_injective`);
Residue = the diagonal (no total halt-decider, `no_surjection_of_fixedpointfree` OneDiagonal 11/0, the q=−1
pole).  **Decidability of the q=±1 termination tag is GRADED by the well-founded modulus**: gcd (modulus exists
→ decidable +1, `gcdFuel` total) → Collatz (open) → halting (no modulus → undecidable = the diagonal).  The
modulus is the boundary between a readable q and the diagonal q.  Cantor/Gödel/Turing = count/provability/
termination-Lens of ONE residue (`one_diagonal_generates`).  Unifies the residue-tag spine and the one-diagonal
spine: the dynamic q=±1 tag and the diagonal are one object.

**Decomposition #140 `cayley_dickson.md` (2026-06-23):** the CD tower ℝ→ℂ→ℍ→𝕆 = iterated doubling (`CDDouble`),
the cleanest place BOTH invariants are load-bearing.  L = `conj` (the q=±1 involution; anti-fixed imaginaries
double each step).  Residue = the law LOST per doubling (order→comm→assoc→alternativity).  Survivors proved
∅-axiom = the q=+1 kept laws: alternativity/flexibility (`cd_alt_left`/`cd_alt_right`/`cd_flexible`,
CDDoubleAlternative 3/0) + the **multiplicative norm character N(xy)=N(x)N(y)** (`diag_collapse`/`hurwitz_cross`,
CDDoubleMoufang 23/0 = Invariant A ×↦· on norms).  Hurwitz (dim 1,2,4,8) = q-tagged termination: the ×↦· norm
character survives 4 doublings (q=+1) then breaks at 𝕊 (q=−1, zero divisors).  ABSENT: named terminus + packaged
Hurwitz.  Tested-refinement also added to SYNTHESIS §2 (iii): the Euclidean engine (finite-reach fixed point)
vs the Banach engine (reached-by-none limit) are TWO engines, not conflated — the tag is on descent-termination,
not value-convergence.

**Decomposition #141 `frobenius_endomorphism.md` (2026-06-23):** the COLLAPSE point of Invariant A.  In char p,
x↦xᵖ is a ring endomorphism — multiplicative `(xy)ᵖ=xᵖyᵖ` AND additive `(x+y)ᵖ≡xᵖ+yᵖ` (freshman's dream,
`freshman_binom` LucasTheorem 18/0, every middle binomial ≡0 mod p).  So ×↦· and +↦+ are the SAME self-map
`(·)ᵖ` — sharper than `prime_factorization`'s "× read as +" (two resolutions); here the separating resolution
vanishes.  Residue = the fixed set: Fermat (`fermat` MulOrder 13/0, a^(p−1)%p=1, equiv aᵖ≡a) fixes 𝔽_p (q=+1
core); moved part = 𝔽_{pⁿ}∖𝔽_p (q=−1), Frobenius generating Gal (order n).  Sharpens finding (iv): where A is a
full endomorphism, B's fixed pole = the fixed field.  FALSE-FRIEND flagged: `Frobenius.lean` = the Frobenius
*number* (coin problem), not this endomorphism.

**SYNTHESIS §2 deepened (2026-06-23):** SEVEN invariant-level findings folded into the canonical inventory
(finding (v): the **modulus is NOT a third invariant** — it is the finite signature of B's `q=+1`-reached-by-none
pole, absent for faithful Lenses + discrete escapes; one tag B with two specialisations A/modulus.  Open
directions recorded in `research-notes/frontiers/invariant_structure.md`) —
(i) the `q=±1` tag's ORIGIN = the Legendre symbol on `(ℤ/p)*` (quadratic residue; whence the name; q^k=1
extension = cyclic power-residue); (ii) the **residue-location law**: a faithful coordinate Lens relocates its
residue to the basis it presupposes (L_vp faithful → residue = prime distribution); specific to
many-distinguishable-atom bases (×-atoms); (iii) the **iterated residue-Lens engine**: `q=±1` = whether the
Euclidean descent terminates — gcd (+1, modulus) / continued fractions (rational +1 / irrational −1) / prime
distribution (−1) are one engine; its meta-undecidability (halting) = the one diagonal (#139);
(iv) **how A and B relate**: `B` (q=±1) = `A`'s unimodular shadow / 2-torsion where a character exists
(modular: Legendre = the character into {±1}), the bare diagonal escape where none does (foundations) — `B`
is more primitive (survives where `A` doesn't); Frobenius (#141) is the sharpest case (A = full ring endo,
B's fixed pole = the fixed field 𝔽_p).

**Five calibrated boundaries** now located
(nonstandard/LLPO, CFT/bundle, descriptive-set/large-cardinals, Stone/ultrafilter, Berkovich/seminorm-completeness) — all converging on the one ultrafilter/LLPO/choice point: the no-exterior axiom, tested at its hardest
points, yields a *calibrated* remainder on the corpus's own strength ledger, never an uncalibrated wall.

Process notes (this session): `scan_axioms` can read a freshly-registered module's stale `.olean` as
false-DIRTY — `#print axioms` on a clean rebuild is authoritative. Core `List.length_range`/`length_filter_le`
leak `propext` — use `E213.Tactic.List213.*` (pure) instead; a pure `length_range` is NOT yet in the repo
(blocked one Morse-bound build — reverted rather than ship DIRTY). Agent-proposed buildable witnesses must be
re-checked: one (`kerSizeDelta 5 k ≤ binom 5 k`) was FALSE (count vs dimension category error) and was caught.
The 12 per-wave sections below are superseded by SYNTHESIS.md (kept for provenance; a `/handoff`
regeneration would prune them).

## ★ LATEST (batch-8 wave, model v7) — read this before the dense block below
**30 worked decompositions, model v7, four predictions Lean-closed.** Batch-8 six-agent wave:
- **Gödel** (PREDICTION) = same `q=−1` escaping diagonal as Cantor/`object1_not_surjective`; predicts
  *where* incompleteness vanishes.
- **surreals** (EXTEND) = Conway's `{L|R}` IS the directed iterated distinguishing, term-for-term.
- **knots** (★ FIRST partial-break) = braid *group* EXTENDS, knot *invariant* BREAKS at two located
  missing primitives: skein = relation-among-distinct-constructions; knot = ambient-isotopy quotient.
  This **locates the calculus's boundary** — the normal form covers neither.
- **p-adics** (PREDICTION) = new reading slot: resolution carries a **`base`** (which valuation is
  "adjacent"); predicts the family of completions; Ostrowski exhaustiveness = open leg.
- Two leverage closures: **orthogonality orders 3/6** (`RootOfUnityOrthogonality`, 23 PURE) extends
  `fourier.md` order-2; **`Φ_contraction`** (`ConvolveRescaleContraction`, 20 PURE) closes
  `gaussian_clt.md`'s keystone leg (honest residual: no `CompleteMetricModulus Dy`, profile open).
**Model v7** = v6 + {resolution carries a `base` (padic); the boundary is located (knots break:
skein + isotopy-quotient are named missing primitives)}.

## ★ SECOND WAVE (model v7.1) — four more agents, three new Lean closures
- **v7.1 (`two_cells.md`)** — META-decomposition of natural transformations re-partitions the knots
  break: naturality DISSOLVES (readings form an explicit **2-category** — `view_factors_through_morphism`
  etc., ∅-axiom); skein/Leibniz = a real **graded-relation slot** (grounded by `leibniz_universal_delta4`);
  isotopy-quotient = genuinely absent (colimit/`q=−1` corner + ambient space). Missing-primitive list
  shrinks from two coarse items to those two precise ones.
- **Noether closed (discrete)** — `NoetherCurrent.lean` (14/0) + `TelescopingConservation.lean` (8/0):
  continuity equation `∂_t ρ = j` + Noether-as-iff `noether_local : (∀w, current g w = 0) ↔ det g = 1`.
  Residual: full variational `∂_μ j^μ=0` needs analytic Real213 (no Lagrangian/flow) — named frontier.
- **Representation theory (`representation.md`)** — the character arrow's home field; Schur orthogonality
  = the already-closed `Σχ=0`; `×↦·` arrow now spans **seven** fields. New located edge: the **`det`/`tr`
  split** (`det` is the built multiplicative character; `Mat2.tr` exists only as an additive order/growth
  readout — `GoldenAperiodic`/`traceDisc` — no `tr`-multiplicativity, no `Rep(G)`/Maschke).
- **Gaussian completion-limit** — `DyadicCompletion.lean` (19/0): a genuine **quotient-free** dyadic
  Cauchy-completion `DyC L`, the lifted `Φhat_contraction`, and `orbit_to_center_completion` (center as a
  true completion-limit). **Principled wall**: `banach_fixed_point`'s wrapper needs a total choice-free
  `lim` (universal `climconv`) — constructively impossible; the *content* is delivered, the wrapper isn't.

## ★ THIRD WAVE — the constructive wall DEFEATED + measure theory

- **★ THE BANACH-ENGINE WALL IS DEFEATED ∅-axiom** (`research-notes/frontiers/wall_synthesis.md` =
  CLOSED). A three-school "genius mathematician" panel (Bishop constructive, computable-analysis/
  domain-theory, reverse-math) converged: the wall is an **interface defect** — the bare `lim` +
  universal `climconv` smuggles countable choice `AC₀,₀`; the fixed-point theorem is ∅-axiom once the
  modulus is *data*. Implemented Route A: `BanachFixedPointModulated.lean` (new reusable engine —
  `CompleteMetricModulusMod` with modulus-as-data `limMod`, `picard_cauchy_mod`,
  `banach_fixed_point_modulated`, all axiom-free) + `DyadicCompletion.lean §8-10`
  (`climconv_regDiag` the crux, `completeDyMod` first non-trivial instance,
  **`gaussian_center_fixed_via_engine`** — the Gaussian center as a fixed point of `Φhat` THROUGH the
  engine, not by-hand). All `#print axioms` → "does not depend on any axioms"; `lake build E213` clean.
  (Three wall memos: `wall_constructive.md`/`wall_computable.md`/`wall_reverse_math.md`. Caught & fixed
  a docstring over-claim + propext-leaking Nat lemmas during verification.)
- **Measure theory (`measure.md`)** — the sharpest leverage: measure theory is already built Choice-free
  in `Analysis/Measure/` (35/0); the calculus PREDICTS that classical Choice-dependence (Vitali,
  Banach–Tarski) is *exactly* the `q=−1` escape residue (same diagonal as Cantor/Gödel), so the repo's
  "no Choice" stance is **derived** (= "stay at `q=+1`"), not a taboo. Located break: `Lp` full additivity
  leaks `Quot.sound` via `funext` (only pointwise PURE).
- **ODE / dynamical systems (`differential_equations.md`)** — the `q=+1` contraction residue spans a third
  field (φ/Gaussian/ODE); real discrete ODE corpus surfaced (`Analysis/ODE/`).

## ★ FOURTH WAVE — q=±1 tag formalized, QR already-closed, Carathéodory, Gaussian profile

- **★ The `q=±1` residue tag is now ONE formal ∅-axiom object** (`Lib/Math/Foundations/ResidueTag.lean`,
  55/0) — the notebook's deepest open collapse, CLOSED. `ResidueTag (escape | converge)` + `multiplier`
  (∓1, unimodular) + `TaggedResidue`, capstone `residue_tag_two_poles`. q=−1 ⟹ `escape_residue_outside`
  (⟵ `no_surjection_of_fixedpointfree`: Cantor/Gödel/measure); q=+1 ⟹ `converge_residue_fixed`
  (⟵ `banach_fixed_point_modulated`: φ/Gaussian/ODE), `golden_is_converge` ties +1 to the φ Cassini
  multiplier. HONEST: one tag + one consequence *per pole*, NOT one biconditional (poles asymmetric:
  universal-negation vs existence; a single `Eq` needs excluded middle).
- **Quadratic reciprocity (`quadratic_reciprocity.md`)** — fresh decomposition found QR is **already
  fully proved ∅-axiom** (`quadratic_reciprocity`, 11/0, Eisenstein lattice double-count). σ_a carries
  FIVE readouts (psign/det/Legendre via `zolotarev_mu`/Gauss-sign/Eisenstein-floor) all one number —
  parity.md's collapse on the Legendre symbol; reciprocity sign = the q=±1 parity residue. No open leg.
- **Carathéodory outer-measure (`Analysis/Measure/OuterMeasure.lean`, 29/0)** — closed measure.md's
  named target: instantiated AS the predicted `clo` closure (genuine Galois connection,
  `caraClosure_idempotent`, conservative). The degenerate form = the predicted q=+1-corner content.
- **Gaussian profile (`Probability/Limit/ConvolveProfile.lean`, 20/0)** — a genuine discrete convolution
  `⋆` + moment-preservation (`mass_conv`, `momentNum_conv` = mean is the additive +-character). HONEST
  partial: the full *density* profile as Φ's fixed point needs a continuous L¹ metric the repo lacks (a
  List-Nat lattice can't rescale by 1/√2 and stay integral) — this is the complementary profile-side half
  of `gaussian_center_fixed_via_engine`.

## ★ FIFTH WAVE — continuity open-set cert, topology, order-4 orthogonality, generating functions
- **`continuous_iff_preimage_dyadicopen` CLOSED** (`Geometry/Topology/ContinuityOpenSet.lean`, 11/0):
  forward + pointwise-backward unconditional; uniform backward via modulus-as-data (the `AC₀,₀` wall,
  located). Certifies continuity.md's prose leg.
- **Topology (`topology.md`)** — PREDICTION: compactness = the `q=+1` finiteness-residue, contrapositive
  of cardinality's `q=−1` escape; consolidates onto `ResidueTag`. `ExtremeValue.ModContOnGrid.gridMax_attained`
  (finite-resolution attainment) vs `Msup` (reached-by-none limit). (Caught + fixed the agent's citation
  slips: `ModContOnGrid.` namespace; `max_reached_by_none` is a prose §5 header, not a theorem.)
- **Orthogonality order 4 (`GaussianOrthogonality.lean`, 18/0)** — `i_orthogonality` in ℤ[i] +
  `orthogonality_of_pow_one` (order-agnostic conditional: ζⁿ=1 ∧ (ζ−1) cancellable ⟹ Σ=0). Orders closed:
  2/3/4/6. Residual: arbitrary-n needs ℤ[ζ_n].
- **Generating functions (`generating_functions.md`)** — PREDICTION: GF-product = the Cauchy convolution
  `⋆` (`ConvolveProfile.mass_conv`/`momentNum_conv`), unifying zeta_euler + ConvolveProfile + recurrences.
  Missing: the two conv defs not welded into a formal-power-series semiring.

## ★ SIXTH WAVE — det/tr split DISSOLVED (spectrum) + Lie bracket + formal power-series semiring
- **det/tr split dissolved as a Lean theorem** (`Mat2/Mat2Spectrum.lean`, 9/0): `tr_eq_e1` (tr=μ+ν=e₁,
  additive `×↦+`), `det_eq_e2` (det=μν=e₂, multiplicative `×↦·`), `disc_eq_gap_squared`,
  `det_tr_split_is_e1_e2` — det and tr are the two elementary symmetric functions of one spectrum (on the
  committed `cayley_hamilton`). Conditional on root existence (= `Real213`/ℂ residue). `spectral.md`
  decomposition: eigenvalue = q=+1 scale-residue, φ = the Fibonacci matrix's dominant eigenvalue.
- **Lie theory (`lie_theory.md`)** — bracket = the q=−1 antisymmetry residue (forced traceless = the `sl`
  kernel = det/tr split from the algebra side); exp:𝔤→G = the `×↦+` character; Jacobi = the graded-Leibniz
  pole (`leibniz_universal_delta4`), NOT naive ∂²=0. Missing: the infinitesimal/tangent `ε` (T_eG), BCH.
- **Formal power-series semiring** (`Combinatorics/PowerSeriesSemiring.lean`, 33/0) — closes
  generating_functions.md's leg: the WELD (both Cauchy products = the same partial sum), the transported
  pointwise semiring laws, and `massN_toCoeffSeq_conv` (the multiplicative `×↦·` character). Residual:
  pointwise (extensional needs funext = forbidden).

## ★ SEVENTH WAVE — symmetric spectral theorem, Lie bracket grounded, de Rham, information geometry
- **2×2 symmetric spectral theorem** (`Mat2/Mat2SymmetricSpectrum.lean`, 9/0): `disc_symmetric_nonneg`
  (symmetric `disc=(a−d)²+(2b)²≥0` ⟹ real spectrum, the `q=+1` corner; elliptic escape unavailable),
  `disc_zero_iff_scalar`, `disc_symmetric_pos_of_nonscalar`. Closes spectral.md's eigenvalue-existence
  residue for the symmetric case at the `disc≥0` level (the √disc *value* stays a Real213 cut).
- **Lie bracket grounded** (`Mat2/Mat2Bracket.lean`, 10/0): `bracket_antisymm` (q=−1), `tr_bracket_zero`
  (traceless/sl₂), `jacobi`, `bracket_leibniz` (derivation) — resolves lie_theory.md's "no named bracket".
- **de Rham (`de_rham.md`)** — strongest consolidation: d²=0=∂²=0, **Stokes = `gauss_conservation_telescope`
  (already ∅-axiom)**, wedge-Leibniz = `leibniz_universal_delta4`, H*_dR = homology's residue upward.
- **Information geometry (`information_geometry.md`)** — KL = entropy-character's asymmetry residue (q=+1
  at p=q), Fisher = its Hessian/curvature; PARTIAL (dyadic atom built, full functional+metric absent).

## ★ EIGHTH WAVE — Killing form (d>1 trace grounded), graph theory, convex duality, model theory
- **d>1 trace character grounded** (`Mat2/Mat2Killing.lean`, 19/0): via the adjoint rep on sl₂ — `killing
  X Y := tr(ad_X∘ad_Y)`, `killing_symmetric`, `adX_traceless`, **`killing_eq_trace_form` (K=4·tr(XY))**,
  `killing_gram` (nondegeneracy=semisimplicity). The additive trace lands as the Lie algebra's invariant
  form (not a multiplicative character). Closes representation.md's main residue.
- **Graph theory (`graph_theory.md`)** — Laplacian spectrum = q=+1 diffusion-residue; connectivity = dim
  ker L is BUILT (`GraphConnectivity.closed_const`). Promotable: 2-vertex Laplacian as a Mat2, spectrum {0,2}.
- **Convex duality (`convex_duality.md`)** — Legendre–Fenchel f**=clo(f) = galois closure; weak/strong LP
  duality BUILT (`kantorovich_weak_duality`/`ollivier_plan_optimal`). Missing: the Legendre transform object.
- **Model theory (`model_theory.md`)** — completeness ⊢φ⟺⊨φ = view=fold initiality; logical compactness =
  topology's q=+1 finiteness corner (same `heineBorel`). The q=+1 companion of godel.md.

## ★ NINTH WAVE — K₂ Laplacian welded, quantum mechanics, Yoneda (self-capstone), Galois correspondence
- **K₂ Laplacian as a Mat2** (`Mat2/GraphLaplacian.lean`, 16/0): `pathLaplacian=⟨1,−1,−1,1⟩`, spectrum {0,2},
  ker=span(1,1) (q=+1 constant), `pathLaplacian_connected` (λ₁=2>0) — welds `Mat2SymmetricSpectrum`+`Mat2Spectrum`
  to a concrete graph (grounds graph_theory.md).
- **Quantum mechanics (`quantum_mechanics.md`)** — measurement = q=+1 symmetric real eigenvalue; uncertainty =
  the q=−1 commutator bracket-residue; unitary = det_holonomy=1. Honest ceiling: finite Mat2 can't host
  [X,P]=iℏI (commutators traceless) — trace-free antisymmetry residue, not iℏ.
- **Yoneda (`yoneda.md`)** — the self-describing capstone: Yoneda = the calculus's own OBJECT=⟨C|L⟩; ★
  `self_covering_closure` (injective ∧ ¬surjective) = Yoneda ⊕ its residue in ONE ∅-axiom theorem (q=+1 faithful
  / q=−1 un-pointable).
- **Galois correspondence (`galois_correspondence.md`)** — subfield↔subgroup anti-iso = the order-reversing
  closure (f**=clo(f)); field content partially grounded (`CyclotomicFive.galois_group_is_C4`, golden subfield,
  A₅ built); solvability = the commutator tower q=+1 (terminating) vs quintic's A₅-escape q=−1 (iteration = open leg).

## ★ ELEVENTH WAVE — Fenchel–Moreau (clo), topos (why-constructive), π₁, ergodic
- **Fenchel–Moreau f**=clo(f)** (`Order/FenchelMoreau.lean`, 18/0): the antitone self-adjoint closure
  (`biconj_idempotent`, `closed_iff_fixed` = strong duality, `cloAntitone_eq_gc_clo` = the monotone-clo
  reduction) — grounds convex_duality's weld. (Caught a Fin-3 propext leak → Bool.)
- **★ Topos (`topos.md`)** — the sharpest foundational leverage, VERIFIED by purity scan: Ω = the
  distinguishing-target Bool, χ = `Object1` (BUILT+PURE); the classical Prop connectives in SemanticAtom are
  DIRTY [propext] while Bool/decide are PURE — **the PURE/DIRTY boundary IS the Heyting/Boolean boundary**, so
  "213 is ∅-axiom-constructive" = "213 is the q=+1 PURE corner of its own topos (internal logic Heyting)".
- **π₁ (`fundamental_group.md`)** — loop algebra EXTENDS (H₁ = π₁ abelianized = the commutator quotient
  `DerivedSeries.commSet`); the homotopy quotient BREAKS at EXACTLY knots.md's break, recurring verbatim →
  promotes it to a principled topological-quotient limit (one ambient-deformation primitive serves both).
- **Ergodic (`ergodic_theory.md`)** — the most consolidating: invariant measure = q=+1 fixed point;
  ergodic theorem = the q=+1 Birkhoff/LLN residue; ergodicity = the dim-1 constant kernel = Laplacian λ₀=0.

## ★ TENTH WAVE — S₃ solvability tower, Curry–Howard, sheaf theory, tropical
- **S₃ solvable, the q=+1 commutator-tower** (`Linalg213/DerivedSeries.lean`, 21/0): group commutator
  `gcomm=a⁻¹b⁻¹ab`, `gcomm_id_iff_commute`, `derived_S3_step1` ([S₃,S₃]=A₃), `derived_A3_step2` ([A₃,A₃]={e}),
  `solvable_S3` (2-step termination); A₅-escape probed. Grounds galois's solvability leg for S₃.
- **Curry–Howard (`curry_howard.md`)** — the calculus is a type theory describing itself: ⟨C|L⟩=⟨proof|prop⟩,
  normalization = fold-to-normal-form, strong normalization = `no_infinite_descent`'s q=+1 well-founded floor.
- **Sheaf theory (`sheaf_theory.md`)** — gluing = q=+1 unique-amalgamation (= `dhom_unique_pointwise`), H^{>0} =
  the q=−1 local-global obstruction (= de_rham's coboundary residue).
- **Tropical (`tropical.md`)** — (max,+) = the ×↦+ character's idempotent T→0 limit; the repo's own docstrings
  pre-classify `max` as the idempotent pole (`max_idem`, mirror of `succ_not_idempotent`).

## ★ TWELFTH WAVE — SYNTHESIS capstone + Fenchel–Moreau, Birkhoff/ergodic, random matrix, connections
- **★ `SYNTHESIS.md`** — the capstone map of the whole 54-decomposition corpus (two invariants, the q=±1
  spine, the ~21-module Lean census, the recurring breaks, the self-description: PURE/DIRTY = Heyting/Boolean
  = why 213 is constructive; honest verdict vs §7.1 breadth). Linked from the README intro.
- **Fenchel–Moreau** (`Order/FenchelMoreau.lean`, 18/0): f**=clo(f) via the antitone self-adjoint closure.
- **Cyclic Birkhoff/ergodic** (`Combinatorics/CyclicErgodic.lean`, 26/0): time=space at the period;
  ergodicity = the constant kernel, reusing `closed_const` (= graph_theory's Laplacian λ₀ machinery).
- **connections.md** — curvature = holonomy loop AND bracket commutator (both built); ★ STALE-GAP CORRECTION:
  `TensorCalculus.lean` (23/0) already has the Riemann tensor/Christoffel/Levi-Civita/Bianchi — three notes
  declared a false gap; fixed curvature.md + de_rham.md.
- **random_matrix.md** — Wigner semicircle = the q=+1 free-convolve fixed point (Catalan moments grounded).

**Tally:** 54 decompositions + the `two_cells` meta + the formal `q=±1` tag + `SYNTHESIS.md`; **thirteen
predictions, twelve Lean-closed** + Lean **groundings**: spectral (`Mat2SymmetricSpectrum`), Lie (`Mat2Bracket`),
representation (`Mat2Killing`), graph (`GraphLaplacian`), galois/solvability (`DerivedSeries`), convex
(`FenchelMoreau`), ergodic (`CyclicErgodic`). `lake build E213` clean. Open frontier: full A₅-simplicity + general isSolvable, the Legendre transform object (weld `clo` at
`Fix=Inv=(·)*`), continuous Noether current, arbitrary-n orthogonality (`ℤ[ζ_n]`), the symmetric eigenvalue
√-cut value, the full Gaussian density profile, KL functional + Fisher metric, the smooth-manifold form complex,
FOL/λ-calculus objects, Hilbert/Born, presheaf/sheaf object, tropical semiring, the νF/free-monad carrier.

NOTE (housekeeping): HANDOFF has accumulated many per-wave sections; a `/handoff` or `/doc-sync` consolidation
pass would tidy it. The decomposition README + frontier `decomposition_calculus.md` are the canonical running index. Open frontier
(`decomposition_calculus.md` + `wall_synthesis.md` residual): variational Noether current, general-χ
orthogonality at arbitrary n (needs `ℤ[ζ_n]`), the `tr`-character / `Rep(G)`-Maschke at `d>1`, the full
Gaussian *density* profile (continuous L¹ metric), a formal-power-series semiring (weld the two `conv`
defs), the arbitrary-cover quantifier (compactness/measure q=−1 half), the native free-monad/νF carrier,
isotopy/colimit quotient, Ostrowski exhaustiveness.

## ★ DIRECTION RECALIBRATION (2026-06-22, from the originator directly — READ FIRST)
The originator course-corrected the whole approach: **the Lean files are scaffolding, not the body —
he never wrote them, delegated all to AI.** The body is **the idea in the opening axiom docs: to *see
mathematics cleanly* through the single act of distinguishing.** Raw/Lens are the *Lean encoding*
(machine verifier); 0-axiom is just the discipline the purpose forces. His stated direction (verbatim
intent): *first **create a way of doing/describing mathematics** — like category theory / type theory /
topos created theirs — then **decompose & rewrite existing mathematics** into it.* Re-deriving
classical theorems in Lean (e.g. the FTA marathon below) is **scaffolding-exercise, not research of
his idea** — honestly acknowledged. New central program started:

**`research-notes/decomposition/` — the 213 Decomposition Calculus** (human-facing technique;
README.md = the spec: `OBJECT = ⟨Construction | Reading⟩`, Residue, the 4-step procedure, and the
**revelation rule** = every decomposition must *reveal* (collapse / forcing / residue-surfaced), never
just re-skin — the design constraint that kept CT from being "abstract nonsense"). Key grounding: the
calculus is the **positive form of CLAUDE.md's failure-mode catalog** (each failure = a missed
decomposition). Frontier registered: `research-notes/frontiers/decomposition_calculus.md`.
**Twenty-three worked decompositions** in `practice/` (all Lean-certified citations). +batch-6 (both
PREDICTION, EXTEND): `integration` (∫ = Σ at residue resolution; FTC = "telescoping is
resolution-invariant", Σ⊣Δ and ∫⊣d = same adjoint at two resolutions — ties resolution to the
adjoint-pair structure; gauss_conservation_telescope PURE), `zeta_euler` (Euler product falls out of
the UFD character: Σ_n=Π_p = distributive law of the faithful valuation coordinate; summatory_mul/
geom_sum/primorial_le_four_pow ∅-axiom; ζ-value = Real213-cut residue; "generating function = read C
weighted" is the dual of Fourier's "read Ĉ", one per character-arrow direction). Four predictions
total, two Lean-closed (succ_not_idempotent, quadratic_orthogonality). +batch-7: `category_theory`
(★ the originator's FOUNDING QUESTION answered: 213 IS category-theory-shaped but GENERATED FROM the
distinguishing — verdict (c) literal, term-by-term Raw=initial/fold=read-op/readings=morphisms/adjoint→
closure-monad; HoTT absent+forbidden; the distinguishing ADDS q=±1 residue + atom-distinguishability +
forced (3,2,5); the calculus is self-describing), `curvature` (flat=det1=Noether-invariant; curvature=
loop-reading's q=±1 residue; Gauss-Bonnet ties it to homology's residue). **★ Capstone unity**: the one
`det`/`×↦·` character is read FOUR ways — scalar (determinant) / Aut-invariant (Noether) / around a loop
(curvature) / down the height (homology) — residues tied by Gauss-Bonnet. The calculus reduces a wide
swath of math to **two invariants** (the character arrow + the q=±1 residue) read across {direction,
fold-height, resolution, iteration-character}. **25 decompositions, no break.** Model v6 stable. **+batch-5 = the
LEVERAGE phase** (bar raised from collapse to *predict/derive*): `noether` (PREDICTION, structural —
conserved = Aut-invariant character, q=+1; variational current open), `gaussian_clt` (PREDICTION —
Gaussian = convolve-rescale fixed point, generalizes φ; contraction lemma the open target), `fourier`
(PARTIAL — self-duality Ĉ≅C + character-existence predicted; orthogonality Σχ=0 open), `adjunction`
(the repo proved the closure MONAD before naming it: Galois clo=G∘F, η/μ/triangle identities; the
free/growing corner is the un-built edge). **Two load-bearing finds**: (1) ONE `×↦·` character arrow
runs through parity/valuation/det/entropy/Noether/Fourier — six theorems, one reading; (2) the calculus
is a *category of readings* living in the two q=±1 poles, and only the **q=+1 closure corner** is built
(free/growing corner open). **Model v6** named in README. Honest leverage verdict: the calculus
PREDICTS at the structural level (form + why); **TWO predictions are now CLOSED in ∅-axiom Lean** (the
technique paying off, verifiably): (1) the **growing/iteration-character axis** — `MuNuMirror.`
`succ_not_idempotent` (PURE), the distinguishing's successor reading is non-idempotent (mirror of
`clo_idempotent`), so the calculus is NOT confined to the q=+1 closure corner; new axis
iteration-character {∂ nilpotent / clo idempotent / S growing}, orthogonal to q=±1; (2) **character
orthogonality** — `ModArith/CharacterOrthogonality.quadratic_orthogonality` (20 PURE), Legendre-level
Σχ=0 + altSign=Legendre. Remaining leverage targets (frontier): convolution-contraction→Gaussian,
continuous Noether current, general-χ orthogonality (needs ζ), the free monad multiplication. +batch-4 (all EXTEND): `homology` (∂ = fold-height run DOWNWARD → height is bidirectional; ∂²=0 forced by q=±1
sign-cancellation; nilpotent vs involutive = the two q=±1 poles), `ordinals` (ω = height-residue, q=+1,
3rd instance; model caps HONESTLY at ω — finite-signature boundary), `galois` (first NON-INVERTIBLE
reading-pair = adjoint/order-reversing connection; fundamental thm = residue-collapse-to-closure;
LensIso = the closed special case), `entropy` (★ L-parameters COMPOSE IN SERIES: H=E[−log p]=weight∘
character; FIRST LEVERAGE — the calculus PREDICTS entropy's form, −log forced by independence→additivity
= the ×↦+ character, not re-skin). **Model v4**: L's form a category (compose in series, Aut-families,
adjoint pairs); fold-height + character both bidirectional; Residue q=±1 (escape/nilpotent vs
converge/involutive/closure). No break across 17 targets; first genuine prediction achieved (entropy).
Earlier-batch detail: +batch-3 `groups`
(a group = `⟨C | Aut C closed under composition⟩`, axioms forced; EXTEND) + `probability`
(`P = ratio∘count`, first *composite reading*; `L` gains a `weight` parameter; independence = ×-character,
expectation = its additive twin; EXTEND). **Model v3 lesson: readings form a category — they compose and
have automorphism families.** No model-break yet across 13 targets. Model refined three times by
the practice (README "Refinements"): `C` = distinguishing + {direction→sign, fold-height→dim/degree,
atom-distinguishability→×/+}; `L` = a reading + {resolution (→ a whole discipline = topology when made a
condition), bidirectional character-mode (×↦+ valuation/log and +↦× exp, one arrow)}; **Residue is
first-class and tagged `q=±1`** — the escaping residue (Cantor diagonal, `q=−1`) and the converging
residue (φ, `q=+1`) are ONE residue at the two unimodular poles (`cassini_law_one_at_two_multipliers`),
the calculus's deepest collapse. Batch-2 fresh: `determinant` (det = character `×↦·`),
`golden_ratio` (φ = self-application residue; the q=±1 find), `exponential` (exp = inverse character;
e = residue), `continuity` (topology = the resolution dial's three questions). **Six worked
decompositions** in `practice/` — superseded; see eleven above. Earlier list:
crystallized-from-repo — `parity.md` (parity/congruence/perm-sign/det=±1 = one construction-preserving
finite reading, Zolotarev), `integers.md` (ℤ = difference-reading of a directed count-pair),
`equivalence.md` (동치/동형/준동형 = one Lens-arrow); and **four FRESH** (4-agent parallel panel) —
`prime_factorization.md` (×↦+ collapse, `vp_mul`; exp/log wall = ×-atom distinguishability),
`cardinality.md` (finite + uncountable = count-reading + its forced residue, `object1_not_surjective`),
`dimension.md` (dimension/degree/pole-order = one height-reading, forced), `derivative.md` (derivative
= the ℤ difference-Lens at residue resolution; Δ/d, Σ/∫ one reading across resolution).

**The technique was refined BY the practice** (README "Refinements from the first practice batch"):
`C` carries optional read-off sub-structures {direction→sign, fold-height→dimension/degree,
atom-distinguishability→×/+ split}; `L` carries {resolution, character/logarithmic mode}; Residue is
first-class and stratifies (`⟨C|L⟩ ⊕ Residue(L,C)`). **Next: more FRESH decompositions** to break/extend
this map (candidates: matrices/det, continued fractions/φ, the exponential, topology/continuity,
probability); Lean stays a faithfulness-check. Minor tooling: `scan_axioms.py` has a probe-path write
bug when run from a non-root cwd (one agent hit it) — fix when convenient.

## The directive (진의) — re-inferred this session (4-agent panel) + the originator's question
The originator asked, via `/goal`: infer the repository's ultimate purpose by multi-agent debate and
*conduct* deep multi-session autonomous research toward it — and "is the goal to make the axiom into
category theory / HoTT?" (he says he can't precisely name his own goal).

**Inference (panels: CT/HoTT positioning · purpose · skeptic · strategist), recorded in
`research-notes/frontiers/the_purpose_and_the_marathon.md`:**
- **CT/HoTT answer: no.** 213's formal core *already is* standard category theory — `Raw` = initial
  F-algebra, `Raw.fold` = catamorphism, residue = Lawvere fixed-point non-surjectivity (Lambek proved
  in `Theory/Raw/Lambek`). It reaches this from a *different primitive* (the distinguishing), not by
  recasting the axiom as CT. **HoTT: absent** (no univalence/identity-type/HIT; `propext`/`Quot.sound`/
  `funext` are *forbidden* — structurally opposite to univalence). Verdict: "same content, different
  primitive" (c), not "reducible to CT" (a).
- **Ultimate purpose:** a *sustained discipline of non-self-deception* about one intuition — "the act
  of distinguishing is the self-grounding primitive, and mathematics/∞/residue are its *forced*
  unfolding" — with ∅-axiom as the lie-detector. The unnamed driver: *to encounter a result the
  primitive forces that he did not import*, machine-checked so it can't be talked away.
- **Survival path (CT/type-theory/topos history → "Line B template"):** none won the foundations
  contest by argument; each was accepted as a *tool a real community found useful* (CT→Grothendieck;
  type theory→Curry–Howard + proof assistants/Scholze; topos→étale cohomology). 213's move: ship the
  strict-∅-axiom Mathlib-free corpus as an *engineering* artifact (trusted-axiom-base minimization),
  judged on utility — not "a new foundation."

## What was done this session (all ∅-axiom PURE, verified, pushed)

### The descent leg — FTA *generated* over the Raw-derived ℕ₊ (the marathon spine)
The substance gap (substance_test): the disciplines run on Lean `Nat`, "act and unfolding two adjacent
codebases." Closed for arithmetic, over `Nat213` (Peano's Raw-generated ℕ₊), M0→M4:
- **M0** — de-laundered the divisibility cone: `Order.mul_left_cancel` re-proved natively (trichotomy
  + distributivity), so `Divisibility`'s whole cone is `toNat`-free (the substance bet, won).
- **M1** — `Irreducible.lean` (18 PURE): `Irreducible` over `Nat213`; `2,3,5` irreducible, `4` not;
  `five_irreducible` via native `lt_succ_iff` enumeration + cofactor bound.
- **M2** — `Factorization.lean` (18 PURE): `exists_factorization` (every `n` = product of
  irreducibles). Native `acc_lt`/`wf_lt` (no `Nat` measure); constructive `decBoundedExists` →
  decidable `lt`/`Dvd` + decided dichotomy `irreducible_or_properDiv` (no `Classical.em`); native
  `mem_append_pure`/`not_mem_nil` (avoid propext-carrying core `List` lemmas).
- **M3** — `EuclidUnique.lean` (7 PURE): `euclid` (irreducible ⇒ prime) + `prime_dvd_prod`. The
  no-zero/no-subtraction wall dissolved by an internal handle (§5.4): a *subtractive* gcd (differences
  = `lt`-witnesses, fits ℕ₊), gcd existence + multiplicative law `gcd(c·a,c·b)=c·gcd(a,b)` in one
  well-founded induction (`gcd_exists_mul`, spec ∀-quantified over the scaling `c`).
- **M4 — CAPSTONE** — `FTA.lean` (11 PURE): `fta` = existence + uniqueness-up-to-permutation, over
  `Nat213`. Native propext-free `Perm`/`erase`/`prod_erase`/`cons_erase_perm`; uniqueness by structural
  induction (`prime_dvd_prod` + `mul_left_cancel`). **Arithmetic-generation half achieved: the FTA is
  computed on the Raw-generated carrier — instantiation, not assertion.**
- **M5 — forcing** — `Forcing.lean` (3 PURE): `peano_succ_is_distinguishing` (Peano `succ` = the
  distinguishing `slashOrSelf · Raw.b` under `Bridge.toRaw`) + `factorization_forced_by_distinguishing`
  (the distinguishing-blind `degLens` conflates `four`/`five`; the count reading separates them). The
  FTA's prime/composite distinction is carried *iff* the reading distinguishes. Honest wall stated:
  `Nat213` is a parallel inductive, link is the *injective* bridge → "recognition, not genesis."
- **M6 — forcing dichotomy (negative arm)** — `Forcing.lean` extended (6 PURE): `forcing_dichotomy`
  lifts M5 to the `DStr` schema level — `Raw` is the free `DStr` + `Nat213` embeds injectively
  (positive); a distinguishing-blind (subsingleton) carrier can't host the FTA carrier nor is a `DStr`
  (negative, fails named clause D1). **Open arm (honest)**: *every* `Generated DStr ≅ Raw` (transport
  the FTA) is the open `DStr` existence leg, not claimed. This marathon re-confirmed Route A's
  commutativity + junk-injectivity costs → Route B (mutual WF recursion) is the honest target.
- **Applied — Euclid's theorem** — `Infinitude.lean` (3 PURE): `infinitude_of_irreducibles` (no finite
  list of irreducibles is complete), generated over `Nat213` from the FTA. A *second*
  discipline-defining theorem after the FTA — primacy as breadth.
- **Applied — irreducible ⟺ prime** — `Prime.lean` (4 PURE): `irreducible_iff_prime`, the UFD-defining
  coincidence over `Nat213` (Euclid `→` + cancellation `←`). The structural reason FTA uniqueness holds.

### Line B (external exposure)
- `research-notes/drafts/strict_zero_axiom_formalization_paper.md` rewritten as an
  engineering/empirical contribution (trusted-axiom-base; CompCert/seL4 framing), metaphysics
  stripped. In-file "Notes for revision" flag numbers to confirm before submission.

## Open Problems (priority order)
1. **The `DStr` existence leg** — the one honestly-open piece of the descent leg (M6 positive arm):
   construct the injective catamorphism `rawDStr → N` for a `Generated DStr N` (uniqueness half
   `dhom_unique_pointwise` done), giving `≅ Raw` and FTA-by-transport for *every* rival. Routes (all
   axiom-free): (a) reuse proven total-target `raw_initial`; (b) apartness-preserving morphisms;
   (c) well-founded mutual recursion. Frontiers: `the_distinguishing_schema.md`, `the_descent_leg.md`.
2. **Line B exposure** — the §5.1 verdict-wall: a clean capstone proves coherence + forcing, **not**
   "not a re-skin." Only an exterior settles it. Finish the paper's flagged numbers; consider a
   pre-registered, time-boxed open-problem attack. Frontier: `the_substance_test.md` (Line B).
3. **Census tooling fix (NEW — audited this session)** — a whole-corpus audit found the
   `scan_all_axioms.py --csv` batch mode **resolves only ~4177 of ~20,429 top-level decls** (~80%
   silently dropped to per-module probe timeouts / name-resolution); its aggregate total is
   untrustworthy. Per-module `scan_axioms.py` is authoritative. Fixed this session: a false "1 real
   DIRTY" (command-elaborator `elab{Verify,Derive}Conjugation` cross-attributed to a `Cauchy.*`
   module) is now sealed by decl name (`SEALED_DIRTY_DECLS`); the stale "18,845"/"three CommandElab"/
   "Classical.choice in NativeGuard" claims are corrected in `STRICT_ZERO_AXIOM.md` + the Line B paper.
   **Remaining**: fix the batch probe (name-qualification + per-decl timeout) so the whole-corpus
   census is reproducible — a real gate-integrity task. 0 real DIRTY holds (per-module + resolved set).

## File Map
```
lean/E213/Lens/Number/Nat213/Irreducible.lean    ← M1 irreducibility
lean/E213/Lens/Number/Nat213/Factorization.lean  ← M2 existence + native WF + decidable Dvd
lean/E213/Lens/Number/Nat213/EuclidUnique.lean   ← M3 Euclid / subtractive gcd
lean/E213/Lens/Number/Nat213/FTA.lean            ← M4 FTA capstone (existence + uniqueness)
lean/E213/Lens/Number/Nat213/Forcing.lean        ← M5/M6 forcing: FTA tied to the distinguishing
lean/E213/Lens/Number/Nat213/Infinitude.lean     ← Euclid's theorem (infinitude) over Nat213
lean/E213/Lens/Number/Nat213/Prime.lean          ← irreducible ⟺ prime (UFD coincidence)
lean/E213/Lens/Number/Nat213.lean                ← aggregate (registers all seven)
research-notes/frontiers/the_purpose_and_the_marathon.md  ← the inference + marathon spine + Line B template
research-notes/frontiers/the_descent_leg.md               ← M0–M4 record + M5/M6 + honest walls
research-notes/drafts/strict_zero_axiom_formalization_paper.md ← Line B(a), reframed as engineering
```

## Next
The descent leg's **generative half (M0–M4: FTA over `Nat213`)** and **forcing half (M5–M6 negative
arm)** are closed. Two honest items remain: (1) the **`DStr` existence leg** (M6 positive arm — the
one open construction, routes (a)/(b)/(c) above); (2) **Line B exposure** (confirm the paper's flagged
numbers, then submit / time-boxed open-problem attack — the only test of "not a re-skin," §5.1).
Most actionable next: the existence leg via route (b) apartness-preserving morphisms (`Raw.cmp` is a
decidable apartness), or finalize the Line B paper.
