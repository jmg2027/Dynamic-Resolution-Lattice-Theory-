# Session Handoff — 2026-04-30 (Δ⁴ Leibniz + Universal Lens metatheory)

## Branch
`claude/review-paper-directory-nDw9L` (committed + pushed).

## State

### Universal Lens metatheory — NEW (G1)

User-articulated thesis (research-notes/G1_universal_lens.md):
"213 is not described from outside; it is the precondition for
any describing".

Formalised in `lean/E213/Meta/UniversalLens.lean`:
  - `IsUniversal L := Function.Injective L.view`
  - `idLens_is_universal` — existence witness
  - `refines_all` — universal ⇒ refines every other lens (0-axiom)
  - ★★★★★ `universal_lens_capstone` (≤ {propext})

Conjecture 2 scaffold (dyadic ↔ K_{3,2}^{(2)} bit-walks):
  - `DyadicConjecture.lean` — bit-walk language, 1/3, 1/5, 1/7
    walk realisability (all STRICT 0-axiom)
  - `DyadicWalkUniversal.lean` — `chooseEdge` constructive
    selector (STRICT 0-axiom)
  - `DyadicSignature.lean` — `nextVertex` deterministic
    transition + `signature` trajectory; concrete classification
    1/3, 1/5, 1/7 pairwise distinguished by step ≤ 9
    (★★★ STRICT 0-axiom).
  - `DyadicClassifier.lean` — ★★★★★ key theorem:
    **aperiodic bits ⇒ aperiodic K_{3,2}^{(2)} signature**
    (≤ {propext, Quot.sound}).  Realises Mingu's intuition that
    K_{3,2}^{(2)} walk classifies irrational types.
  - `DyadicTierBridge.lean` — connects to D2 hierarchy:
    - `EventuallyPeriodic` definition
    - `ev_periodic_sig_imp_ev_periodic_bits` (eventual version)
    - ★ `one_third_signature_periodic` — concrete FORWARD
      direction at Tier 0 (rational): bits period 2 ⇒ signature
      period 2 from step 1.
    Tier 0 (rationals) ⇒ both directions closed.
  - `DyadicForwardPeriodicity.lean` — general forward seed,
    Classical.choice REMOVED via Decidable.byContradiction:
    - `bs_periodic_multiple` (STRICT 0-axiom)
    - `collisionTest`, `pigeonhole_collision`, `joint_state_collision`
      all at ≤ {propext, Quot.sound}.
  - `DyadicForwardClosure.lean` — general forward CLOSED:
    - `sub_is_multiple_of_p`: i ≤ j ∧ i % p = j % p ⇒ p ∣ (j - i)
    - ★★★ `signature_eventually_periodic_of_periodic_bits`:
      bits periodic ⇒ ∃ N P, sig eventually periodic from N
      with period P.  ≤ {propext, Quot.sound}.
    Tier 0 BIDIRECTIONAL closure formally complete.
  - `DyadicBitFSM.lean` — finite-state-machine abstraction:
    - `structure BitFSM (n : Nat)` with `init`, `step`, `out`.
    - `fsm_run_collision`, `fsm_run_eventually_periodic`,
      `fsm_bits_eventually_periodic` — chain via pigeonhole.
    - ★★★★★★ `fsm_signature_eventually_periodic`: BitFSM-generated
      bit stream ⇒ K_{3,2}^{(2)} signature eventually periodic
      (full chain closed, ≤ {propext, Quot.sound}).
    Captures Tier 0 ∪ Tier 1 (FSM-generable bit streams).
    Tier 2 conjecturally OUTSIDE this class.
  - `DyadicForwardEventual.lean` — eventual extension of forward:
    - `signature_eventually_periodic_of_eventually_periodic_bits`
      (≤ {propext, Quot.sound}). Used to close BitFSM → signature
      chain.
  - `DyadicBitFSMBound.lean` — quantitative bound:
    - ★★★★★ `fsm_signature_period_bound`: BitFSM(n) ⇒ signature
      period ≤ 5n explicitly.
  - `DyadicBitFSMExamples.lean` — concrete Tier 0 BitFSMs:
    - `fsm_one_third`, `fsm_one_fifth`, `fsm_one_seventh`.
  - `DyadicBitFSMConverse.lean` — Tier 0 ⇔ BitFSM:
    - `bitFSMOfPure` cyclic shift register.
    - ★★★★★★ `tier0_equiv_bitfsm`: bs purely periodic ⇒ ∃ BitFSM(p).
  - `DyadicSignatureInj.lean` — lossless invariant:
    - ★★★★★★ `signature_eq_iff_bits_eq`: signatures match ⇔
      bit streams match.
  - `DyadicTier2Hardness.lean` — Tier 2 hardness:
    - ★★★★★ `aperiodic_bits_imp_not_BitFSM`: aperiodic ⇒ no BitFSM
    - ★★★★★★ `BitFSM_generable_imp_eventually_periodic`
  - `DyadicCapstone.lean` — ★★★★★★★ single 9-conjunct bundle.
  - `DyadicThueMorse.lean` — Thue-Morse witness:
    - `thueMorse` via testBit fold.
    - aperiodicity verified for periods 1..8.
    - self-similarity t(2n)=t(n), t(2n+1)=¬t(n) verified n ≤ 7.
    Concrete aperiodic but finitely-describable bit stream;
    "Tier 1.5" outside BitFSM but still automatic.
  - `DyadicBitAuto2.lean` — 2-automatic abstraction:
    - structure BitAuto2 with run/bits via testBit fold.
    - thueMorseAuto : BitAuto2 2 (parity DFA).
    - isPow2Auto : BitAuto2 3 (popcount-saturating DFA).
  - `DyadicSubwordComplexity.lean` — quantitative classifier:
    - subwordCount via List.eraseDups.
    - subword_growth_separation: 1/3 vs Thue-Morse strictly
      separated at L=1..4, M=16.
  - `DyadicEdgeSignature.lean` — Fin 12 edge-based lens variant:
    - edgeFromBit, edgeSignature.
    - edge_signatures_differ_at_2: 1/3 vs Thue-Morse diverge
      at step 2.
  - `DyadicArithFSM.lean` — Pell-style multi-state FSM:
    - structure ArithFSM2(n) with (Fin n × Fin n) state.
    - pellFSMmod2 (period 3) + pellFSMmod3 (period 4),
      both periodicity proved STRICT 0-AXIOM.
    - ArithFSM2.toBitFSM encoding (subclass of BitFSM).
    - pellMod_periods_differ: algebraic structure visible.
  - `DyadicArithFSMmod5.lean` — Pell mod 5 (period 10):
    - pellFSMmod5 in (Fin 5 × Fin 5), trajectory returns to (1,1)
      at step 10.  STRICT 0-AXIOM via run/step rewrite induction.
    - pell_period_growth: mod 2 → 3, mod 3 → 4, mod 5 → 10.
  - `DyadicArithFSMSignature.lean` — chains Pell family to signature:
    - pell_family_signatures_eventually_periodic
      (mod 2, 3, 5 all yield eventually-periodic signatures via
      signature_eventually_periodic_of_eventually_periodic_bits).
  - `DyadicArithFSMtoBitFSM.lean` — Tier 1 ⊂ BitFSM(n²):
    - ★★★★ toBitFSM_bits_eq: pair-encoding bit-stream-faithful.
    - ★★★★★ arithFSM2_signature_period_bound: signature period
      ≤ 5n² explicit (joint state argument).
    - ★★★★★★ pellFSMmod5_signature_period_bound: concrete 125 bound.
  - `DyadicArithFSMHardness.lean` — Tier 2 hardness for ArithFSM lens:
    - ★★★★★ aperiodic_bits_imp_not_ArithFSM2: aperiodic bs ⇒
      no ArithFSM2(n) generates it (any modulus).
    - ★★★★★★ ArithFSM2_generable_imp_eventually_periodic.
  - `DyadicConcretePellSig.lean` — TIGHT signature periods:
    - signature_period_of_bits_period_and_anchor (universal closure).
    - ★★★★ pellFSMmod3 signature period 4 (pure).
    - ★★★★★ pellFSMmod5 signature period 10 (pure).
    - ★★★★ pellFSMmod2 signature period 6 from step 1 (pre-period 1,
      "doubled" by bipartite alternation).
  - `DyadicPellCapstone.lean` — ★★★★★★★ pell_capstone:
    9-conjunct Tier 1 bundle (mod 2/3/5 bit + signature periods,
    ArithFSM ⊂ BitFSM equivalence, 5n² bound, aperiodic hardness).
  - `DyadicArithFSM3.lean` — 3-state ArithFSM (cubic / Tribonacci):
    - structure ArithFSM3(n) with (Fin n)³ state.
    - tribFSMmod2: Tribonacci mod 2 (a,b,c) → (b,c,a+b+c).
    - ★★★ tribFSMmod2_run_period_4 (STRICT 0-AXIOM).
    - ★★★★★ tribFSMmod2_signature_period_4_from_1 (pre-period 1).
  - `DyadicArithFSM3toBitFSM.lean` — encoding (a,b,c) ↦ a*n²+b*n+c
    into BitFSM(n³).  Helpers + ArithFSM3.toBitFSM definition.
  - `DyadicArithFSM3Equiv.lean` — run-encoding theorem:
    - ★★★ toBitFSM3_run_encode (≤ {propext, Quot.sound}).
  - `DyadicArithFSM3Bound.lean` — cubic-class bound:
    - ★★★★ toBitFSM3_bits_eq.
    - ★★★★★ arithFSM3_signature_period_bound: 5n³ explicit.
    - ★★★★★★ tribFSMmod2_signature_period_bound: 40 = 5·8.
  - `DyadicArithFSM3Hardness.lean` — cubic Tier 2 hardness:
    - ★★★★★ aperiodic_bits_imp_not_ArithFSM3.
    - ★★★★★★ ArithFSM3_generable_imp_eventually_periodic.
  - `DyadicTribCapstone.lean` — ★★★★★★★ tribonacci_capstone:
    6-conjunct bundle parallel to pell_capstone (cubic Tier 1).
  - `DyadicAlgebraicCapstone.lean` — ★★★★★★★★ algebraic_tier1_capstone:
    unified mega-bundle of pell + tribonacci (quadratic AND cubic).
    Formal expression of Tier 1 ⊊ Tier 2 separation via K_{3,2}^{(2)}.
  - `DyadicArithFSM2to3.lean` — ArithFSM2 ⊂ ArithFSM3:
    - padTo3 inclusion (pad with inert 3rd component).
    - padTo3_run_components, padTo3_bits_eq (STRICT 0-AXIOM).
  - `DyadicSignatureBipartite.lean` — bipartite alternation:
    - ★★★ signature_bipartite_alternation: even ⇒ S, odd ⇒ T.
  - `DyadicAtomicityConnection.lean` — atomic primitives match:
    - ★★★★★ signature_atomicity_capstone (STRICT 0-AXIOM):
      NS=3, NT=2, d=5 — K_{3,2}^{(2)} signature lens is the
      *atomically forced* lens for DRLT.
    - signature_NS_NT_alternation: NS/NT-phrased invariant.

### Δ⁴ Cohomology — Leibniz coverage CLOSED

All four interior-stratum (5, a, b) Universal Cup AW Leibniz
theorems now closed at ≤ {propext, Quot.sound}:

  - (5, 1, 1) — direct decide (10,240 cases)
  - (5, 1, 2) — bilinearity lens (3,200 + structural)
  - (5, 2, 1) — two-sided lens (basis × basis + structural)
  - (5, 2, 2) — two-sided lens (basis × basis + structural)

Bundled into `Delta4LeibnizCapstone.delta4_leibniz_capstone`.

### Universal δ²=0 Prop-lift — full Δ⁴
(5, 0), (5, 1), (5, 2), (5, 3) — all closed.
Plus (3, 0), (3, 1), (4, 0), (4, 1), (4, 2).

### Hodge ⋆⋆ = id — Δ⁴ involution
(5, 1) and (5, 2) closed at ≤ {propext, Quot.sound}.

### Bilinearity lens infrastructure (universal, ≤ {propext})
  - cupAW_add_left/right + function-level _eq forms
  - delta_add + delta_add_eq
  - cupAW_zero_left/right + delta_zero (+ _fn forms)
  - basis decomp_5_1, decomp_5_2 (AND-form, definitional)
  - Cochain5_1DecompR (right-nested for combine_5)
  - XorPairCombine.foldr_xor_pair (List foldr induction, 0-axiom)
  - XorPairCombine.combine_5, combine_10

### Documentation
`lean/LESSONS_KERNEL_DECIDE.md` — 12 patterns + meta-lesson +
strategy-by-universe-size table.  Distilled from the (5,1,2)
closure session.

## Lessons learned (carryover)

Top-3 from this session (full list in LESSONS_KERNEL_DECIDE.md):

1. **Algebraic lens > enumeration.** Bilinearity + linearity
   reduces case count *exponentially*: 327k → 3,200 (~100×).
2. **Definitional reduction shape > logical equivalence.** Use
   `(k.val == j.val) && β k` (AND-form) over `if β k then basis
   else 0` for off-diagonal definitional collapse.
3. **List.foldr induction = right abstraction for finite XOR
   facts.** Strict 0-axiom; specialise to N-pair tuple form.

## Open Problems (priority)

### 1. Conjecture 2 — finer Tier 1 vs Tier 2 distinction (NEW)
Tier 0 (rational) BIDIRECTIONAL closed at ≤ {propext, Quot.sound}:
bits ev-periodic ⇔ signature ev-periodic (both directions, no
Classical).
Tier 1 ∪ Tier 2 vs Tier 0 closed: aperiodic bits ⇒ aperiodic sig.
**Open**: Tier 1 (algebraic) vs Tier 2 (transcendental) at
signature level — needs *trajectory complexity* measure.  Conjecture:
Tier 1 has bounded joint-state (Pell × K_{3,2}^{(2)}) FSM; Tier 2
has unbounded (factorial in Euler's HasModulus N(m, k)).
Formalisation: entropy / Kolmogorov-style finite-witness bound on
Fin 5-valued trajectories.

### 2. Conjecture 1 — universal expressibility (NEW)
Curry–Howard + Raw encoding of arbitrary constructive proofs.
Bishop-style scope.

### 3. Real213 Phase B–H — cohomological calculus extension
General `cutMul` propEq remains the wall.  Possible new attack
through K_{3,2}^{(2)} dyadic lens (G1 §5 Conjecture 2).

### 4. (n, a, b) generalisation of bilinearity lens
Currently hand-specialised at (5,1,2), (5,2,1), (5,2,2).
Could lift to ∀ n via parametric foldr-XOR + general decomp.

### 5. Hodge ⋆⋆ = id at remaining strata
(5, 0) and (5, 3), (5, 4) trivial-ish; bundling capstone needed.

### 6. ℚ²-discrete refinement of `idLens : Lens Raw`
Per G1 derivation, ℚ²-discrete is the structural minimum target.
Currently witness is `Lens Raw` (trivial). Upgrade to `Lens (ℚ × ℚ)`
constructively.

### 7. Rust 213 computation tool (user-led design)

### 8. Next math marathon
Probability 213, Topology 213, Multivariable 213 per
blueprints/math/INDEX.md.

## Authors

- Mingu Jeong (Independent Researcher).
- Claude (Anthropic): formalization + planning.
