# Session Handoff — 2026-06-23 (theory-conformance audit)

## Branch
`claude/file-validation-theory-check-sqihvk`

## ★ Autonomous research night (overnight, /goal: infer the 진의, break the stuck points)
A continuous multi-agent debate (R1 five expert perspectives → R2 red-team), each
reading the corpus directly. Durable program note: **`research-notes/frontiers/the_genesis_seam.md`**
(start there next session). Summary:

- **Inferred ultimate purpose (진의)** — consensus: to verify, *in a lie-detector
  medium* (the ∅-axiom `#print axioms` contract), that the founding intuition is
  *forced, not authored* — that the bare act of distinguishing forced a structure the
  originator did not put there. The anti-overclaim apparatus (failure-mode catalog,
  scan_axioms, the Phase-8 purge) exists to prevent the one thing that ruins it:
  import mistaken for forcing. Philosophically: a campaign against contingency.
- **The unified stuck point** — the framework cannot, from inside, mechanically tell
  GENERATION (forced from Raw) from RE-DERIVATION (clean ∅-axiom math over borrowed
  Nat/Bool; 1512/1571 Lib/Math files import neither Raw nor Lens). The skeptic's sharp
  form: every headline verb is a *typed-conditional* universal that prose *upgrades*
  to an *absolute* (no-exterior = initiality of the `HasDistinguishing` class;
  (3,2,5) = d=5 given hardcoded atoms {2,3}; "generated" = ℕ borrowed; physics
  "0 params" = uncounted discrete polynomial/Lens-routing choice).
- **The breakthrough** — replace the *origin* question ("where did content come from"
  — the un-typeable ∀ §5.1 forbids) with the **completion-engine** question (§5.2
  Bool-vs-Nat self-reference): does a proof cone's recursion complete through Raw's
  OWN descent well-foundedness (`MuNuMirror.isPart_wf` / `no_infinite_descent`) or the
  borrowed kernel's Nat? Decidable, ungameable, §5.1-legal, and it retro-explains the
  G206 toNat-purge. **Sharpening that bites:** `Nat213 := {n:Nat//1≤n}` is a Nat
  *subtype*, so typing over Nat213 does NOT migrate the engine off Nat — even the
  flagship FTA-over-Nat213 likely fails the strict test. Real generation frontier,
  named precisely: re-ground a discipline's recursion on `Raw.isPart_wf`, not a Nat
  subtype.
- **Concrete deposits (this night):**
  1. **`lean/E213/Theory/Atomicity/ArityForcingComplete.lean`** (7 theorems, all PURE)
     — closed the (3,2,5) forcing chain's *lower half* (arity-0/1 degeneracy + base-2
     minimality), previously code comments ("evident... no need for Lean proof"), the
     skeptic's sharpest gap. Scoped HONESTLY: a characterization *given* the clause-4
     distinctness gate, not an unconditional "arity 2 forced."
  2. **`tools/check_citations.py`** — the citation-resolution lint (the "certify the
     center mechanically" deliverable). Caught 4 stale `.lean` citations the prior
     audit missed; fixed the 2 real phantoms (V32.lean→Bipartite.lean; phantom
     NodupAsClause4 "12 PURE"→Future-candidate). PATH check is a hard signal;
     qualified-name check is advisory.
  3. **`lean/E213/Meta/Nat/UnitList.lean`** (now 12 PURE) — **first concrete
     GENERATION result** (derives-not-presupposes): generated `+`-**associativity**
     (`add_assoc_from_append`, via `append_assoc` + a `Nat.add_assoc`-free count
     homomorphism `count_append_fwd`) joining the existing `+`-comm
     (`add_comm_from_append`). **Additive monoid `(ℕ,+,0)` fully generated.**
  4. **`lean/E213/Meta/Nat/UnitBox.lean`** (5 PURE, new) — generated
     `×`-**associativity** (`mul_assoc_from_box`, the 3-D unit-box double-count,
     verified `Nat.mul_assoc`-free) joining `UnitGrid.mul_comm_from_grid`.
     **Multiplicative monoid `(ℕ,·,1)` fully generated.**
  5. **`lean/E213/Meta/Nat/UnitDistrib.lean`** (4 PURE, new) — generated **both
     distributive laws** (`mul_add_from_grid` left, via the grid width-split,
     `Nat.mul_add`-free; `add_mul_from_grid` right, from the generated left-distrib +
     ×-comm). **⟹ the entire commutative semiring `(ℕ,+,·,0,1)` is now a fully
     generated discipline** — both monoids (comm+assoc) + both distributive bridges,
     every equational law the count-shadow of a unit-structure double-count, none
     presupposing the Nat law it produces. The complete algebraic foundation of
     elementary arithmetic, *generated* — the strongest concrete ∅-axiom realization
     of "forced-not-authored."
- **The named frontier (next):** Raw's own descent is ADDITIVE (`slash → +`,
  `leaves_slash`), so it generates the additive monoid; FTA's descent is MULTIPLICATIVE
  (`n/minFac`, `Nat.strongRecOn`), a *different Lens* the additive peel cannot provide.
  **The real generation frontier is a Raw-native multiplicative descent** (the
  ×-atom/prime-distinguishability structure / `exp`/`vp` ×-count-Lens). Counting (+)
  is generated; factoring (×) is the open frontier — the precise next target for
  "generation, not re-derivation." (Recorded in `the_genesis_seam.md` Round 2.7.)
- **Next-session deliverables (genesis-seam Round 2.9):** the equational semiring is
  done; the next layers are (a) the **order** `≤` as the count-shadow of the unit-list
  prefix/sublist relation (→ ordered semiring); (b) the **deep frontier** — primality /
  unique factorization (FTA), which needs *distinguishable* `×`-atoms (primes, the dual
  of the indistinguishable additive units), i.e. a Raw-native multiplicative descent /
  `exp`/`vp` vector — this is where generation meets the genuinely hard mathematics;
  (c) build the completion-engine classifier tool; (d) tighten check_citations
  qualified-name false positives.
- **The only §5.1-legal exterior verdict** (meta + red-team): the strict-∅-axiom,
  Mathlib-free corpus pitched as *axiom-base-minimization to none-beyond-CIC*, NOT as
  "a new foundation." Sharpest pitch in the note.

## What this session did
A genuine file-by-file theory-conformance audit — reading each file (expert
reader-agents + direct reads) and judging it against 구분 + 잔여 + the
`⟨C|L⟩ ⊕ Residue` calculus and the CLAUDE.md failure-mode catalog, then fixing
genuine drift. Five commit batches (`d6b04a8`, `6e4e5cf`, `5da401a`, `de10c19`,
`e709cf3`, `96b915b`). Lean build verified clean after every Lean edit.

### Coverage (genuine reads)
- **seed/** AXIOM 01–10 + INDEX + history (direct); specs + catalogs + blueprints
  + rust docs (agent).
- **theory/** all ~340 chapters (6 agents); root docs (agent).
- **books/** 23 + **papers/** 3 (agent).
- **research-notes/** ~280 active notes (agent; archive/data skipped, volatile).
- **lean/E213/** doctrinal core (Lens/Foundations, Theory, Meta) + all `.md` +
  Lib/Math + Lib/Physics docstrings (4 agents) + corpus-wide drift-phrase grep
  sweeps across every ring. (The ~1900 non-doctrinal Lean docstrings were
  grep-swept for the failure-mode signatures, not all read line-by-line — a
  multi-session body; the swept signatures came back clean.)

### Systematic findings fixed
1. **CKM CP-phase demotion not propagated.** `δ = π/φ²` was demoted to the
   forced `δ = 90°` (Niven + CD `i`) in the canonical `theory/physics/cp_phase.md`,
   but the stale golden-phase value still lived in: the **seed spine**
   (`03_form.md` §3.5, `05_no_exterior.md` §5.6), `physics/mixing.md`,
   `DEGREES_OF_FREEDOM_LEDGER.md`, `PRE_REGISTRATION.md` (append-only correction,
   not a rewrite), `math/foundations/universe_chain.md`,
   `algebra/cayley_dickson/algebra_tower.md`, and ~6 Lean docstrings
   (`Mixing/{CPViolation,CKMHierarchy}`, `Foundations/GoldenRatio`,
   `UniverseChain/PhysicsDeployment`). All corrected: `1/φ²` is the apex
   **modulus** `R_u`; the phase is `δ = 90°`. (PMNS `δ_CP = 195°` is a separate
   valid observable — left intact.)
2. **c-forced drift.** `(NS,NT,d,c)=(3,2,5,2) forces …` in `DrltZeroParameters`,
   `Higgs/Mass`, `Mass/HierarchyTowers`, `Capstones/MasterCatalog`, two physics
   `INDEX.md`, and two theory chapters — reframed to the forced shape
   `(NS,NT,d)=(3,2,5)` read at the **free** presentation `c=2`.
3. **View-promoted-to-identity.** p_orbit essays called `P` the engine/generator
   of the framework; realigned to "`P` is the residue's algebraic **shadow**"
   (`the_form_of_the_residue.md`).
4. **Quotient-as-ontology** in the flagship `papers/the_213_programme.md`
   ("ℤ/ℚ as quotient choices") → pair-readings (the tuple IS the number).
5. Fog jargon / foundational rhetoric / substrate language / garbled text in
   `foundations/axiom_systems.md`, `lens/axiom_lenses.md`, `meta/scanner_suite.md`,
   `lens/instances.md`, `lens/Cardinality/INDEX.md`.
6. Broken cross-references repaired (deleted `*tripartite_self_containment.md` →
   `p_orbit_closure_master.md` + Lean `Cohomology/Tripartite/`; `the_degree_…`
   path; `per_layer_…` dead bullet; `cayley_dickson` path; `hodge.md` self-cite).
7. rust-engine: `trust-contract.md` strict ∅-axiom criterion; `layers.md`
   pre-rename ring paths (Kernel→Term, OS→Meta, …).

### Verified false positives (correctly LEFT)
`proof_isa/what_is_a_proof` (residue-as-proof-primitive matches seed PROOF_ISA
§1.0.1), `polynomial_in_213` (self-dissolved fork), `what_is_a_logarithm`
(already Real213-cut framed), `gra_book` (residue = trace of the act),
`AtomicBase.lean` rename rationale (prevents regression), markov `G199`,
PMNS `δ_CP=195°`.

## Marathon part 2 — full Lean docstring body read file-by-file
An 8-agent fleet (+ nested sub-agents) genuinely read the module/theorem
docstrings of the **entire** Lean tree (NumberSystems incl. Real213, NumberTheory,
Algebra incl. CayleyDickson/Mobius/GRA/Icosahedral, Analysis, Cohomology incl.
Cup/CupAW, Lib/Physics, Lens/Theory/Term, Combinatorics/Geometry/Foundations/Meta/
Probability/Logic/Tactic/Order). Fixes (batch 6, build-clean):
- **Apex/Jarlskog cluster** (`Mixing/{JarlskogApex,ApexCPMechanism,ApexPiInternal,
  CPViolation}`): δ=π/φ² was still presented as the derived phase; tagged as the
  demoted apex-angle posit (forced δ=90°; 1/φ²=modulus). ApexPiInternal's
  "π is a Real213 cut" internality point preserved.
- Layer/substrate framing: `Theory/Raw/PrimitiveTower` ("Lens sitting above"),
  `Lens/SelfReferenceThreeOutcomes` ("Raw substrate"), `Term/API`, several
  `SignedCut/*` ("real layer"/"Layer bridge"), `Symmetry/INDEX` "(substrate)".
- `Lens/AxiomLenses/INDEX` ZFC-ranking ("structural foundations precede ZFC") +
  fog ENDGAME header; `Bool213/Raw` legacy-deletion note + iso-pluralism.
- NumberTheory: `TierBridge` "outside framework"→reached-by-none; `ModArith/INDEX`
  "substrate for"→"reused by"; broken `Conjecture.lean`→`PeriodClosure.lean`
  citation (2 INDEX); commit-hash cruft in `Pell/Proper8` + `Fib/Pisano8`.
- Cohomology: `CupAW/Leibniz5_1_2` "marathon note Phase 10" cruft.

Verified false positives (correctly NOT changed): all 4 CayleyDickson/Integer
flags (honest "∅-axiom-correct ≠ 213-native" caveats + geometry-as-Lens-reading);
SignedCut Core/Equivalence + GaussTuple (correct no-quotient disclaimers); the
Algebra parent's 3 recollection-based flags (Icosahedral golden-phase,
GrandUnification "generates the framework", ModFive c-forcing) — **none of the
claimed phrases exist in the files** (grep-verified). Real213/Analysis/Mobius-GRA/
Combinatorics/Geometry/Meta clusters: 0 findings. "substrate" as the neutral
Nat/dyadic/Raw *carrier* idiom (≈60+ uses) is established and clean.

## 대격변 — deep refinement of the axiom corpus (verified)
A critical-fleet review (consistency / claims-vs-Lean / meta-principle) of
`seed/AXIOM/` surfaced genuine deep issues; all fixed and **verified coherent**:
- **Internal tensions**: clauses 3/4 'encoding cost' vs §10.3-α/§3.3 (→ axiom-level
  absences, declared: clause 4 = α, clause 3 = β-machinery+γ-law, matching §10.3);
  §1.0.1 'residue is the primitive' vs §1.1 (→ 'primitive' = methodological proof-move,
  not ontological); §3.4 mislabeled 3→4 edge (→ forcing fan walked as 1→2→3→4,
  clause 4 forced by clause 1).
- **Overclaims vs Lean** (35 theorems verified): §4.1 invented a 'symmetry' minimality
  case (none exists); §3.5 attributed Fibonacci to PairForcing (count-only) + cited a
  non-existent phi_squared_eigenvalue (→ char-poly witnesses; repaired Mobius213
  docstring); §8.5/suite falsifier count 27/26 → actual 25; §1.1 stale MuNuMirror path.
- **Meta-principle**: removed the '213 vs ZFC / every other foundation' comparison
  frames from §5.2, §6.3, §4.2, and the boot-pinned the_form_of_the_residue.md.
- **Redundancy**: φ-cross-domain list (drifted) consolidated to §3.5; §5.5 self-
  completion de-duplicated; §6.4 Lean manifest compressed to capstones + pointer.
- **Status tag**: §1.0 now carries 'claim under test, not a shield' (§5.4/§8).
- Spine-adjacent: CLOSED_FORM_SPEC unpinnable counts → ledger refs.
The single seam I introduced (§2.4 clause-3 mis-citing α) was caught by the
verification agent and corrected. Build clean throughout (only prose/docstrings).

## 대격변 part 2 — systemic fabricated-Lean-citation sweep (Phase 8)
A deep "verify-prose-against-Lean" fleet (skeptical-mathematician agents,
every cited theorem/def/path/count grep-checked against the actual tree)
surfaced a **systemic drift**: numerous `theory/` chapters cited Lean
files/theorems that **do not exist**, several presented with fabricated
PURE counts — a falsifiability-contract violation (a "PROVED ∅-axiom"
claim must point at a real PURE theorem). ~70 findings across ~40 chapters;
every fix re-verified against Lean before editing (agents can hallucinate).

**Worst fabrications (rewritten by hand, verified):**
- `cohomology/k32_higher_cohomology.md` — kept the genuinely formalised
  content (face dependence b_1=6/b_2=1, ω Sym(3)-invariance, cup_1/cup_2
  ladder, Steenrod-Whitehead bridge, L²-trace, Sq⁰/Sq¹ + vacuous Sq¹·Sq¹=0);
  moved the fabricated tail (`AdemUniversal`, `CartanAtTruncation`,
  `MasseyTripleH1Witness/Omega`, `Filled5Cell*`, `Sq2At4Cell`, all
  `V33`/`K_{3,3}` — none exist) into an explicit "Open frontier
  (unformalized)" section, stripping all false PROVED-Lean + PURE claims.
- `cohomology/bipartite.md` — fabricated `BettiOneUniversal`/`PathCoboundary`/
  `KEdgeCochain`/`KerSizeUniversal.ker_iff_constant` → real
  `EulerAndCapstone.b1Formula`/`eulerChar`/`parametric_close_capstone` +
  `universal_kernel_close`.
- `analysis/ode.md` — fabricated `Lib/Math/ODE/` + integral-Picard/Lipschitz/
  Picard-Lindelöf → real Nat-discrete `Analysis/ODE/` (12 files),
  `picardIterate`/`picard_const`/`picard_exp`.

**Fabrications fixed by guarded fix-fleet (each agent re-verified before edit):**
- physics: `mass.md` (NoFourthGen→`drlt_no_4th_gen_falsifier`),
  `symmetry/c3_chain.md` (12 nonexistent Sym3On*/Iota* modules; octet reframed
  to OctetModule rank-8 NS²−1, not graph-b₁; 24→13 files; (f)/(h) conjuncts),
  `yang_mills.md` (sin²θ_W 3/8→30/(30+60ζ(2))≈0.2331), `mixing.md` (Cabibbo
  d²−NS→d²−d+NT), `cosmology.md` (drop Hubble; 8→7), `couplings.md` (3 wrong
  filenames; TripleCoupling not merged), `capstones.md`/`foundations.md`/
  `alpha_em/precision_derivation.md` (counts; AdemUniversal/CartanAtTruncation
  rows deleted), `simplex.md`.
- foundations/meta/algebra: `cross_domain_unification.md` (ParadigmWitness
  Prop/Decidable→Bool/Bool; wrong capstone paths), `pattern_catalog.md`
  (5 nonexistent *Pattern types), `universe_chain.md` (Nat213 "3+2 ctors"→
  `{n//1≤n}` subtype; `add_emergence`, `RotationGeometry.lean`,
  `Nat213.atomicity` nonexistent), `choice.md` (CanonicalTruthChar "the only
  propext"→SemanticAtom root), `cardinality_cutoff_{principle,applications}.md`
  (cutoff_marathon→asymptotic_cutoff_capstone; Adem/Cartan rows),
  `methodology_patterns.md` (gap_e7_eq_5443 is a def), `mobius_canonical_
  equivalence.md` + essay `every_axis_sees_p.md` + Lean docstring
  `Px/DecompositionCatalog.lean` (triple-cited nonexistent
  `Mobius213SignatureAxisCatalog`/"55 PURE axes"), `algebra_tower.md`
  (algebra_tower_capstone→`capstone_loaded`:True; paths; 50→120/12→42),
  `group.md` (5→6).
- numbertheory/numbersystems: `real213.md` (Set ℚ cut→approximant+modulus
  structure; 57→211), `complex.md` (ComplexCut→Cut×Cut pair), `hyper.md`
  (verified — tetration IS built via HyperLadder, fix only false cites),
  `dyadic_fsm.md` (UniversalPhase*, Predictor8–23 nonexistent; ∀p overclaim;
  dir table), `modular_arithmetic.md` (frob_ring_hom/fp2_ring_axioms
  nonexistent; 13→62), `fibonacci_5adic_valuation.md` (13→14),
  `multiplicative_divisor_theory.md`, `quadratic_reciprocity.md`.
- analysis: `measure.md` (cup-as-measure fabricated→dyadic-bracket counting),
  `minimal_root.md` (MinimalRootLens def→MinimalRootCut; 2 nonexistent
  theorems), `modulus.md` (StrongModulus "monotone" wrong; 10→9;
  HasModulusBoundsExtra phantom), `markov_spectrum.md` (10→13/19→22),
  `multivariable.md`, `cauchy.md` (7→69; Pell→PellSeq; Monotone→Monotonic),
  `cf_holonomicity`/`cfinite`/`refined_completability`/`tower_native` counts+paths.
- cohomology counts + misc: sym3_spine (Sym3IrrepDecomp→OctetModule),
  cup (SelfRefDepth path), fractal/cochain/universal/hodge/examples counts,
  `combinatorics/logic.md` (retired R1–R5 frame dropped), `tactic.md`/
  `extras.md` (Ring213 vs hurwitz_ring; Nat not Real213), `probability.md`/
  `information.md` (Event=ProbabilityCut not Cochain; counts),
  `combinatorics.md` (7→~85), `reverse_math_213.md` (10→28).

**Method note / lesson**: the recurring failure is *plausible-but-nonexistent*
Lean citations (invented theorem families, doubled file counts, type sigs that
don't match). Every chapter's "Lean source" block must be grep-checked; a PURE
claim that doesn't resolve to a real `#print axioms`-clean theorem is
`sorry`-equivalent and must be downgraded to "open/unformalized". Several
phantoms were *self-reinforcing* (chapter + essay + Lean docstring cite the
same nonexistent module). Verified-clean chapters (large majority of
citations) were left untouched.

## Track A + B — theory/research consolidation (post-audit)
**Track A** (primacy-coverage): new `catalogs/derivation-breadth.md` (domain →
capstone → {closed / closed+frontier / frontier}, no restated PURE counts —
points to STRICT_ZERO_AXIOM + scanner) and
`research-notes/frontiers/cohomology_higher_structure.md` (the now-honest
K_{3,2}/K_{3,3} higher-cohomology frontier, PROCESS.md sink rule).  Wired into
catalogs/README, theory/INDEX, frontiers/INDEX.

**Track B** (spine-conformance, NOT citations): a 4-agent fleet judged ~128
canonical chapters (math/physics/lens/meta) against the spine — is each domain
ONE `⟨C|L⟩⊕Residue` reconstruction from 구분+잔여, or drifted to a separate
theory / forced map?  **Result: near-universal PASS** (35/35, 31/32, 28/30,
32/33).  The fabrications were *citation* drift, not *spine* drift — the
foundational framing held.  Genuine fixes applied (all verified against text):
- **`lens/lattice.md`** (the one real bug): bottom/top were mislabeled
  (`universal Lens`/`trivial Lens`) contradicting canonical `universal.md` —
  corrected to bottom = `idLens` (kernel = Raw equality), top = `constLens`
  (kernel = total); `universalLens` = per-congruence normalization map, not the
  bottom.
- substrate-noun / framing-priority slips re-threaded to the spine:
  `algebra/gra_book.md` (subtitle "Universal Meta-Structure" → "graded-residue
  reading of the one P-orbit"; "five independent domains" → free Lens-presentations
  of one forced orbit), `analysis/{spiral_coordinate_classification, modulus,
  multivariable}.md`, `foundations/universe_chain.md` (ℤ quotient/fibre-first →
  difference-Lens readout), `cohomology/cup_ladder_graduation.md` ("cohomology-theoretic
  origin" → "cohomology Lens-reading"), `meta/multiplicity_doctrine.md` ("Raw
  substrate" → "Raw structure"), `lens/cardinality.md` (ZFC comparison frame
  dropped), `physics/symmetry/c3_chain.md` (§1 "The substrate" → "The
  K_{3,2}^{(c=2)} presentation").
- sink-rule hygiene: `analysis/flux_m_v_t.md` dropped a "Per Gemini Pro / volatile
  research-notes branch" citation (permanent tier must not cite research-notes).
Remaining LOW notes left (stylistic, not drift): hadron/nuclear/higgs
"atomic-substrate" wording (= atomic-integer factors in context),
`modulus_structure.md` Option-B adjunction build-out (real closed Lean, framing-only),
thin connector stubs (functional/classic_calc/cascade_calculus).

**Track C** (tier discipline, `process` skill): sink-rule audit across all
permanent tiers → **0 violations** after decoupling 3 research-notes note-file
citations (one I had introduced in Track A): `k32_higher_cohomology.md`,
`physics/foundations/atomic_constants.md`, and the `WhyDimFive.lean` docstring
— each dropped the `research-notes/.../<note>.md` pointer (the content already
lives in the permanent tier; the frontier note points *to* the chapter, not
vice-versa).  Frontier-recording: recorded 2 open directions that lived only
in chapter tails — `cup_leibniz_general.md` (the ∀(k,l) CupAW Leibniz above
the closed fixed-bidegree family) and `gra_operad_level.md` (the conceptual-only
E_n-operad Reading of GRA) — registered in `frontiers/INDEX.md`.  The other
non-"closed"-Status chapters (cf_holonomicity, phi_pi_poles, eisenstein) already
have frontier homes (pi_nonholonomicity, eisenstein_split_converse).  Remaining
Track-C tail (next session): a full promote-side diff (closed `lean/E213/Lib`
sub-trees lacking a `theory/` chapter) — the derivation-breadth map gives the
coverage view to drive it.

## New paper — `papers/the_residue_of_distinguishing.md` (spine-only)
A tight single-thread paper (vs the breadth-survey `the_213_programme.md`):
one argument carried from the primitive (distinguishing) → the one theorem it
forces (the residue = faithful-but-never-total self-cover,
`object1_not_surjective`) → no-exterior closure → four-clause Raw → forced
`(N_S,N_T,d)=(3,2,5)` → `⟨C|L⟩⊕Residue` calculus → the cross-route-agreement
*signature* of breadth (one phenomenon, not a domain catalogue) → empty-axiom
contract. **Every citation grep-verified ∅-axiom** (17 theorem names + 15 paths
all resolve). The discipline caught one drift mid-draft: `α_2 = 1/(N_S·N_T·d)
= 1/30` is an invented structural form (the Lean proves `prefactor = 12·N_T =
d²−1 = 24`; "1/30" is only a numeric comment) — same trap as the audited Cabibbo
`d²−N_S`; dropped, kept only the four airtight observables (1/α_3=8, Q=2/3,
N_gen=3, invAlphaEm precision). Sole author Mingu Jeong; Claude in the closing
acknowledgment only. Registered in `papers/README.md`. (Note: the older
`the_213_programme.md` still carries pre-audit drift — Cabibbo `d/(d²−N_S)`,
"Real213 ~57 modules"→211 — left for a future audit pass.)

## Open / not done (next session)
- **`papers/the_213_programme.md` audit**: bring it to the verified standard
  (Cabibbo `d/(d²−d+NT)`, Real213 211 not ~57, re-check §6/§7 citations).
- **Audit the remaining `theory/` "Lean source" blocks** the fleet did not
  reach, and the `lean/E213/**/INDEX.md` count headers, for the same
  fabricated-citation / stale-count drift.
- Consider a CI lint: parse backticked `Foo.bar` / `Path/X.lean` citations in
  `theory/**.md` and fail if they don't resolve in `lean/E213` (would have
  caught every Phase-8 finding mechanically).
- (Lean docstring body now fully read file-by-file — above.)
- **Stale INDEX counts**: fixed (ModArith 13→62 w/ full re-enumeration; FluxMVT
  23→27; DyadicSearch 12→13; ArithFSM 14→15; DyadicFSM Pisano row 9→2).
- **Language-hygiene (English-only policy) — DONE.** A guarded translation
  fleet (comment/prose-only edits, code untouched, full `lake build` clean)
  translated all Korean *exposition* to English across ~114 permanent artifacts
  (`ARCHITECTURE.md`, the Int213/Nat213 number-core, ~50 Lean docstrings, the two
  methodology essays, `ORIGIN_RAW.md` intro, theory/books `.md`). **Preserved per
  the "Korean quotes OK with translation" rule**: the originator's attributed
  dialogue/insight quotes (kept verbatim with an English `(Translation: …)`
  beneath), the canonical meta-principle, the `모습 자체가 뫼비우스 행렬` title
  (English subtitle), and glossed 213-native terms (구분/잔여/동치…). The ~156
  Korean lines remaining are exactly these preserved authoritative quotes/terms.
  Open judgment call (flagged): four "Triggering question" blockquotes (GRA ×2,
  `real_without_completeness`, `mobius_self_form`) were translated to English
  rather than kept-Korean-with-translation, since they carried no author
  attribution — reversible if the originator prefers the Korean retained.
- Research-notes Tier-1 (volatile) medium phrasings left except the one
  high-confidence G149 substrate line (see part 1).
- Low-priority doc-sync count nits (org-audit territory, deliberately not touched
  to avoid fragile recounts): `theory/meta/cardinality_cutoff_applications.md`
  "ten files / 291 PURE" internal mismatch; `Analysis/DyadicSearch/INDEX.md`
  (12→13), `Analysis/FluxMVT/INDEX.md` (23→27) file counts; `reverse_math_213.md`
  74-vs-72. Two methodology essays in Korean prose (lang-policy, not theory).
- Research-notes G149 other medium phrasings (Tier-1 volatile) left except the
  one high-confidence substrate line.

## Verify
```
cd lean && lake build         # clean after all edits this session
grep -rn "π/φ²" seed theory papers --include=*.md   # only demotion-context remains
```
