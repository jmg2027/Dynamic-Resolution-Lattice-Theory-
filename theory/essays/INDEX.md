# theory/essays/

Cross-cutting essays: on-demand trajectories through the
catalog/book that surface structural insights not localised to
any single chapter.

See `lean/E213/.claude/skills/essay/SKILL.md` for the
derivation+citation+dual-function+cross-frame+self-check
+constructive-accessibility protocol.

## Convention

  · One essay per question / structural insight
  · Cite chapters + Lean theorems (citations ARE the derivation)
  · Land on a syntactic object (constructive accessibility)
  · Document open frontier honestly

## Current essays

| Essay | Triggering question | Anchor chapters |
|-------|---------------------|-----------------|
| `kplus1_alpha_power_graduation.md` | What is `(k+1)` in 213? Why does H^k → α^(k+1)? | `math/cohomology/cup_ladder_graduation.md` + `physics/alpha_em/precision_derivation.md` C1 Step 6 |
| `steenrod_whitehead_bridge.md` | Why does `cup_1(ω, ω) = δ²(ω)` hold at K_{3,2}^{(c=2)}? | `math/cohomology/k32_higher_cohomology.md` + `lean/E213/Lib/Math/Cohomology/Bipartite/FaceCup1At3Cell.lean` |
| `cut_off_marathon.md` | What collapsed in the cardinality cut-off 6-direction marathon? | `math/cohomology/aurifeuillean.md` + `meta/cardinality_cutoff_applications.md` |
| `pure_funext_avoidance.md` | PURE Lean에서 funext-blocked 정리를 어떻게 닫는가? | 4 patterns across `Padic/Neg*` + `Real213/IntValidCut` + `Padic/Setoid*` + `Padic/HenselResidual` |
| `bool_assoc_failure_meaning.md` | b ≥ 3 cutSum_assoc이 Bool level에서 실패하는 것은 무엇을 의미하는가? | `Real213/CutSumAssocB3` + `Theory/Atomicity/Five` `atomic_iff_five` + `Physics/Foundations/AtomicConstantsParametricFullIff` `c2b_full_iff` + `Padic/ZpSqrtD` |
| `4mfd_geometrization_joint_reading.md` | How does 213 read 4-mfd geometrization (cork twist + JSJ + Heegaard jointly)? | `math/exotic_4mfd_cork.md` + `math/geometrization_conjecture.md` + `lean/E213/Lib/Math/AkbulutCork/CrossFrame.lean` |
| `cup_ladder_cork_h1_bridge.md` | How do cup-ladder α²/d² Gram and cork +4 share the same H¹ basis? | `math/cohomology/cup_ladder_graduation.md` + `math/exotic_4mfd_cork.md` + `lean/E213/Lib/Math/AkbulutCork/CrossFrame.lean` |
| `cut_equality_and_atomicity.md` | 213에서 두 cut이 같다는 게 뭐야? Why does one matrix carry both atomicity and cut equality? | `math/mobius_canonical_equivalence.md` + `math/universe_chain.md` + `Theory.Atomicity.Five.atomic_iff_five` |
| `c_counter_as_layer_count.md` | What is `c` in K_{NS, NT}^{(c)} cohomology? Why is the c-counter not a depth parameter? | `math/cohomology/k_nm_c_classification.md` + `V33EnrichedParametric.parametric_c_independent_h2_classes` |
| `disjoint_layers_as_direct_sum.md` | Why does cup-image codim grow linearly with c? | `math/cohomology/k_nm_c_classification.md` + categorical direct sum reading + `parametric_c_independent_h2_classes` |
| `stern_brocot_as_universal_lattice.md` | Where does K_{NS, NT}^{(c)} sit, and why is (3, 2) the atomic anchor? | `math/cohomology/k_nm_c_classification.md` + `math/mobius_canonical_equivalence.md` + `BipartiteStermBrocotClassification` |
| `bipartite_tripartite_self_containment.md` | Why is the framework called 2-1-3 but the cohomology programme bipartite? | `math/mobius213_p_orbit_closure.md` + `TripartiteK213` + Lean-deferred Option I (V32LocalSignature) |
| `p_orbit_naturalness_boundary.md` | Where does the "non-atomic" prime 7 come from in mod-13 period? | `math/mobius213_p_orbit_closure.md` + `POrbitClosure.framework_natural_via_p_orbit_closure` |
| `vandermonde_mediant_counts.md` | How do K_{NS, NT}^{(c)} cell counts split under the Stern-Brocot mediant? | `math/cohomology/k_nm_c_classification.md` §"Mediant cohomology functor" + `MediantCohomologyFunctor.mediant_cohomology_functor_capstone` |
| `p_orbit_closure_master.md` | Is the P-orbit closure structurally forced from atomic data? | `CharPolySelf` + `POrbitRing` + `Theory/Atomicity/OrbitForcing` + `PeriodDepthBounds` + `CrossProductAxes` + `Cohomology/Tripartite/V213ShadowProjection` |
| `pure_nat_ring_methodology.md` | How does PURE Lean prove universal polynomial identities without `ring` / `omega`? | `Lib/Math/NatRing` + `Px/CassiniUniversal` + `Px/PnFibonacciUniversal` |
| `multiplicity_layer_uniformity.md` | 모든 multiplicity layer 에서 같은 ψ-kill 이 작동하는 이유?  `9·m` cancellation 의 구조적 의미? | `math/cohomology/k_nm_c_classification.md` §"Arbitrary-m bilateral kill" + `V33EnrichedParametric.parametric_arbitrary_m_full_kill_capstone` + `NatBeqHelpers.nat_decide_add_left_assoc{1,2}` |
| `cup_image_dual_span.md` | What does it mean for the c ψ-discriminators to SPAN the dual of H²_enr / cup-image? Why PRIMARY (not FULL) cup-image? | `math/cohomology/k_nm_c_classification.md` §"Cup-image dual span" + `V33EnrichedParametricDualSpan.parametric_dual_span_capstone` + `NatBeqHelpers.nine_block_disjoint` |
| `c_counter_programme_closure.md` | How do the five directions (A/B/C/E/T) of the c-counter programme interlock?  Same-shape parallel to P-orbit closure? | `math/cohomology/k_nm_c_classification.md` + `master_Knn_c_counter_resolved` + `parametric_arbitrary_m_full_kill_capstone` + `parametric_dual_span_capstone` + `mediant_cohomology_functor_capstone` + `self_containment_cohomology_verdict` |
| `layer_multiplication_pattern.md` | Why does the same proof shape (invariant + offset + cancellation) appear in cohomology layers, P-orbit depth, AND mediant Vandermonde? | `theory/essays/c_counter_as_layer_count.md` + `theory/essays/p_orbit_closure_master.md` + `theory/essays/vandermonde_mediant_counts.md` + `NatBeqHelpers.nat_decide_add_left_assoc{1,2}` + `Combinatorics/Binomial.binom_add_2` + `Px/CharPolySelf.L_recurrence_2` |
