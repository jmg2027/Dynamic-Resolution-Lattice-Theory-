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
