import E213.Lib.Math.GeometrizationConjecture.ScopeAndDepth
import E213.Lib.Math.Cohomology.Examples.WhyDimFive

/-!
# Geometrization dim spectrum + Sym(3)-capable (steps 6, 14)
-/

namespace E213.Lib.Math.GeometrizationConjecture.ChartAxisAnsatz

/-! ## Geometrization spectrum analysis (R1 step 6)

The 213-Lens reading of the Geometrization conjecture's
dimension-regime split (confinement / critical / smearing) is
sharpened by examining the cohomology-α_3-uniqueness across
manifold dimensions.

Per `Cohomology/Examples/WhyDimFive`, the parametric formula
`b1_bipartite n m c = c*n*m - (n+m) + 1` is evaluated across
many (n, m, c) candidates, sorted by `chartBase = n + m`:

  · chartBase = 4  (d_M = 3, confinement)
      candidates: K_{2,2}^{(c)}, K_{3,1}^{(c)} for c ∈ {1, 2, 3}
      α_3 matches: NONE
  · chartBase = 5  (d_M = 4, critical)
      candidates: K_{3,2}^{(c)}, K_{2,3}^{(c)}, K_{4,1}^{(c)}
      α_3 matches: K_{3,2}^{(c=2)} and K_{2,3}^{(c=2)} ONLY
      (same deployment modulo S/T swap)
  · chartBase = 6  (d_M = 5, smearing)
      candidates: K_{3,3}^{(c)}, K_{4,2}^{(c)} for c ∈ {1, 2, 3}
      α_3 matches: NONE
  · chartBase = 7  (d_M = 6, smearing)
      candidates: K_{4,3}^{(c)} for c ∈ {1, 2, 3}
      α_3 matches: NONE

**Geometrization-spectrum reading**: d_M = 4 is the **unique
critical dimension** at which a 213-deployment matches the α_3
integer.  Other dimensions admit multiple K-deployments but none
match cohomology-α_3 — consistent with the standard-math regime
table (d_M ≤ 3 confinement, d_M ≥ 5 smearing).

This is **not** a re-proof of Geometrization or of the
Donaldson/Freedman dimension-4 anomaly.  It is the 213-Lens
projection of the same dimension-spectrum split, expressed via
deployment-cohomology rather than smooth-structure cardinality.
The convergence of standard-math d_M = 4 critical and 213-Lens
chartBase-5 cohomology-α_3 uniqueness is the empirical anchor
that motivates .
-/

/-- d_M = 3 confinement layer (chartBase = 4): K_{2,2}^{(c)} and
    K_{3,1}^{(c)} options, ALL fail α_3 match. -/
theorem dim_spectrum_dM3_no_match :
    -- K_{2,2}^{(c)} options
    E213.Lib.Math.Cohomology.Examples.TopologyCompare.b1_bipartite 2 2 1 = 1
    ∧ E213.Lib.Math.Cohomology.Examples.TopologyCompare.b1_bipartite 2 2 2 = 5
    ∧ E213.Lib.Math.Cohomology.Examples.TopologyCompare.b1_bipartite 2 2 3 = 9
    -- K_{3,1}^{(c)} options
    ∧ E213.Lib.Math.Cohomology.Examples.TopologyCompare.b1_bipartite 3 1 1 = 1
    ∧ E213.Lib.Math.Cohomology.Examples.TopologyCompare.b1_bipartite 3 1 2 = 3
    -- No α_3 match
    ∧ E213.Lib.Math.Cohomology.Examples.TopologyCompare.b1_bipartite 2 2 2 ≠ 8
    ∧ E213.Lib.Math.Cohomology.Examples.TopologyCompare.b1_bipartite 3 1 2 ≠ 8
    -- chartVisibleAxes confirms d_M = 3
    ∧ chartVisibleAxes 2 2 = 3
    ∧ chartVisibleAxes 3 1 = 3 := by decide

/-- d_M = 4 critical layer (chartBase = 5): K_{3,2}^{(c=2)} UNIQUE
    α_3 match (modulo S/T swap to K_{2,3}^{(c=2)}). -/
theorem dim_spectrum_dM4_unique_match :
    -- K_{3,2}^{(c=2)} matches
    E213.Lib.Math.Cohomology.Examples.TopologyCompare.b1_bipartite 3 2 2 = 8
    -- S/T swap also matches (same deployment modulo labelling)
    ∧ E213.Lib.Math.Cohomology.Examples.TopologyCompare.b1_bipartite 2 3 2 = 8
    -- Other c values for K_{3,2} do not match
    ∧ E213.Lib.Math.Cohomology.Examples.TopologyCompare.b1_bipartite 3 2 1 = 2
    ∧ E213.Lib.Math.Cohomology.Examples.TopologyCompare.b1_bipartite 3 2 3 = 14
    -- K_{4,1}^{(c=2)} also at chartBase=5 — does not match
    ∧ E213.Lib.Math.Cohomology.Examples.TopologyCompare.b1_bipartite 4 1 2 = 4
    -- chartVisibleAxes confirms d_M = 4
    ∧ chartVisibleAxes 3 2 = 4
    ∧ chartVisibleAxes 4 1 = 4 := by decide

/-- d_M = 5 smearing layer (chartBase = 6): K_{3,3}^{(c)} and
    K_{4,2}^{(c)} options, ALL fail α_3 match. -/
theorem dim_spectrum_dM5_no_match :
    -- K_{3,3}^{(c)} options
    E213.Lib.Math.Cohomology.Examples.TopologyCompare.b1_bipartite 3 3 1 = 4
    ∧ E213.Lib.Math.Cohomology.Examples.TopologyCompare.b1_bipartite 3 3 2 = 13
    -- K_{4,2}^{(c)} options
    ∧ E213.Lib.Math.Cohomology.Examples.TopologyCompare.b1_bipartite 4 2 1 = 3
    ∧ E213.Lib.Math.Cohomology.Examples.TopologyCompare.b1_bipartite 4 2 2 = 11
    -- No α_3 match
    ∧ E213.Lib.Math.Cohomology.Examples.TopologyCompare.b1_bipartite 3 3 2 ≠ 8
    ∧ E213.Lib.Math.Cohomology.Examples.TopologyCompare.b1_bipartite 4 2 2 ≠ 8
    -- chartVisibleAxes confirms d_M = 5
    ∧ chartVisibleAxes 3 3 = 5
    ∧ chartVisibleAxes 4 2 = 5 := by decide

/-- d_M = 6 smearing layer (chartBase = 7): K_{4,3}^{(c)} options,
    ALL fail α_3 match. -/
theorem dim_spectrum_dM6_no_match :
    E213.Lib.Math.Cohomology.Examples.TopologyCompare.b1_bipartite 4 3 1 = 6
    ∧ E213.Lib.Math.Cohomology.Examples.TopologyCompare.b1_bipartite 4 3 2 = 18
    ∧ E213.Lib.Math.Cohomology.Examples.TopologyCompare.b1_bipartite 4 3 3 = 30
    ∧ E213.Lib.Math.Cohomology.Examples.TopologyCompare.b1_bipartite 4 3 2 ≠ 8
    ∧ chartVisibleAxes 4 3 = 6 := by decide


/-! ## §S — Sym(3)-capable spectrum (R1 step 14)

Refines the dim-spectrum analysis (step 6) with a Sym(3)-capability
filter: which K_{NS, NT}^{(c)} deployments support natural Sym(3)
action at each chartBase?

**Sym(3)-capable** ⟺ NS = 3 ∨ NT = 3 (filter from step 10).

Enumeration across chartBase ∈ {4, 5, 6, 7}:

  · chartBase = 4 (d_M = 3): K_{3,1}, K_{1,3} for each c ∈ {1, 2, 3}
    = 6 Sym(3)-capable deployments
  · chartBase = 5 (d_M = 4): K_{3,2}, K_{2,3} for each c
    = 6 Sym(3)-capable
  · chartBase = 6 (d_M = 5): K_{3,3} for each c, plus K_{3,k≠3}
    for k satisfying chartBase
    = a few
  · chartBase = 7 (d_M = 6): K_{3,4}, K_{4,3} for each c
    = 6 Sym(3)-capable

Among all these, K_{3,2}^{(c=2)} is the *unique* deployment
satisfying the full cohomology-depth filter from step 10:
  Sym(3)-capable + c=2 binary cover + b_1 = 8 = 1/α_3

**Geometrization-Sym(3) regime correspondence (narrative)**:
The Sym(3) action requirement parallels the *3-dim Lie-group
classification* in standard Thurston framework — both require
"3-ness" of some structural ingredient.  This is a deeper
parallel than the bare 8 enumeration count (step 11 §G).
-/

/-! ### Sym(3)-capable enumeration per chartBase -/

theorem sym3_capable_chartBase_4 :
    -- K_{3,1}, K_{1,3} family at chartBase = 4
    hasNaturalSym3 3 1 = true
    ∧ hasNaturalSym3 1 3 = true
    -- K_{2,2}: NOT Sym(3)-capable
    ∧ hasNaturalSym3 2 2 = false := by decide

theorem sym3_capable_chartBase_5 :
    -- K_{3,2}, K_{2,3} family at chartBase = 5
    hasNaturalSym3 3 2 = true
    ∧ hasNaturalSym3 2 3 = true
    -- K_{4,1}, K_{1,4}: NOT Sym(3)-capable
    ∧ hasNaturalSym3 4 1 = false
    ∧ hasNaturalSym3 1 4 = false := by decide

theorem sym3_capable_chartBase_6 :
    -- K_{3,3}: NS=3 AND NT=3 (Sym(3) on both)
    hasNaturalSym3 3 3 = true
    -- K_{4,2}, K_{2,4}: NOT Sym(3)-capable
    ∧ hasNaturalSym3 4 2 = false
    ∧ hasNaturalSym3 2 4 = false
    -- K_{5,1}, K_{1,5}: NOT Sym(3)-capable
    ∧ hasNaturalSym3 5 1 = false := by decide

theorem sym3_capable_chartBase_7 :
    -- K_{3,4}, K_{4,3}
    hasNaturalSym3 3 4 = true
    ∧ hasNaturalSym3 4 3 = true
    -- K_{5,2}, K_{2,5}: NOT Sym(3)-capable
    ∧ hasNaturalSym3 5 2 = false
    ∧ hasNaturalSym3 2 5 = false := by decide

/-! ### K_{3,2}^{(c=2)} unique at the full-filter intersection -/

/-- Among Sym(3)-capable deployments at each chartBase, only
    chartBase = 5 with c = 2 admits the c=2 binary cover
    compatibility (NT = 2 specifically). -/
theorem sym3_capable_with_c2_binary_match :
    -- chartBase = 4 Sym(3)-capable with c=2: K_{3,1}^{(c=2)}, K_{1,3}^{(c=2)}
    -- These have NT=1 or NS=1, not 2 — FAIL c=2 binary
    (hasNaturalSym3 3 1 && hasC2BinaryCoverMatch 3 1 2) = false
    -- chartBase = 5 Sym(3)-capable with c=2: K_{3,2}, K_{2,3} both PASS
    ∧ (hasNaturalSym3 3 2 && hasC2BinaryCoverMatch 3 2 2) = true
    ∧ (hasNaturalSym3 2 3 && hasC2BinaryCoverMatch 2 3 2) = true
    -- chartBase = 6 Sym(3)-capable K_{3,3} with c=2: NT=3, not 2 — FAIL
    ∧ (hasNaturalSym3 3 3 && hasC2BinaryCoverMatch 3 3 2) = false
    -- chartBase = 7 Sym(3)-capable K_{3,4}, K_{4,3} with c=2: FAIL
    ∧ (hasNaturalSym3 3 4 && hasC2BinaryCoverMatch 3 4 2) = false
    ∧ (hasNaturalSym3 4 3 && hasC2BinaryCoverMatch 4 3 2) = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ★★★★ **K_{3,2}^{(c=2)} unique under triple intersection**:
    Sym(3)-capable + c=2 binary cover + b_1 = 8 only matches at
    chartBase = 5 (K_{3,2}^{(c=2)} or S/T-swap K_{2,3}^{(c=2)}).
    Critical at d_M = 4 is the unique chartBase where all three
    filters coincide. -/
theorem K32_c2_unique_triple_intersection :
    -- chartBase = 4 (d_M = 3): Sym(3) yes, but NS=3 NT=1 no NT=2
    passesCohomologyDepthFilter 3 1 2 = false  -- K_{3,1}^{(c=2)}
    ∧ passesCohomologyDepthFilter 1 3 2 = false  -- K_{1,3}^{(c=2)}
    -- chartBase = 5 (d_M = 4): K_{3,2}^{(c=2)} and S/T swap PASS
    ∧ passesCohomologyDepthFilter 3 2 2 = true
    ∧ passesCohomologyDepthFilter 2 3 2 = true
    -- chartBase = 6 (d_M = 5): K_{3,3}^{(c=2)} fails c=2 binary
    -- (no side has 2 vertices)
    ∧ passesCohomologyDepthFilter 3 3 2 = false
    -- chartBase = 7 (d_M = 6): K_{3,4}^{(c=2)} fails
    ∧ passesCohomologyDepthFilter 3 4 2 = false
    ∧ passesCohomologyDepthFilter 4 3 2 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ★★★★ **Three-criterion regime spectrum (concrete c)**:
    The combined filters (b_1 = 8 + Sym(3) + c=2 binary cover)
    fail uniformly at chartBase = 4 (K_{3,1}^{(c)} family) for
    every c ∈ {1, 2, 3}.  Only chartBase = 5 with (NS, NT) = (3, 2)
    and c = 2 passes all three filters simultaneously. -/
theorem three_criterion_K31_fails_all_c :
    passesCohomologyDepthFilter 3 1 1 = false
    ∧ passesCohomologyDepthFilter 3 1 2 = false
    ∧ passesCohomologyDepthFilter 3 1 3 = false
    -- Same for S/T swap K_{1,3}^{(c)}
    ∧ passesCohomologyDepthFilter 1 3 1 = false
    ∧ passesCohomologyDepthFilter 1 3 2 = false
    ∧ passesCohomologyDepthFilter 1 3 3 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- chartBase = 5 (d_M = 4): K_{3,2}^{(c=2)} is the UNIQUE
    triple-filter pass (modulo S/T swap K_{2,3}^{(c=2)}).
    K_{3,2}^{(c=1)} and K_{3,2}^{(c=3)} fail c=2 OR b_1=8. -/
theorem three_criterion_K32_unique_c :
    -- K_{3,2}^{(c=1)}: c≠2, fails binary cover filter
    passesCohomologyDepthFilter 3 2 1 = false
    -- K_{3,2}^{(c=2)}: passes
    ∧ passesCohomologyDepthFilter 3 2 2 = true
    -- K_{3,2}^{(c=3)}: c=3 fails binary, also b_1 ≠ 8
    ∧ passesCohomologyDepthFilter 3 2 3 = false := by
  refine ⟨?_, ?_, ?_⟩ <;> decide


end E213.Lib.Math.GeometrizationConjecture.ChartAxisAnsatz
