# Catalog 213 — Analysis Library Reference

Library usage manual.  **Name + import path + usage** of each theorem/structure.

---

## Quick start — single import

```lean
import E213.Lib.Math.Analysis213    -- import all Analysis213 results in one line
```

Or by layer:

```lean
import E213.Lib.Math.Analysis       -- existing umbrella
```

---

## A. Basic arithmetic — Cut Algebra

### A.1 Ground type

```lean
import E213.Lib.Math.Real213.CutSumTest
-- def constCut (a b : Nat) : Nat → Nat → Bool := fun m k => decide (a*k ≤ b*m)
```

### A.2 Sum / Mul

```lean
import E213.Lib.Math.Real213.CutSum     -- cutSum, cutSumAux
import E213.Lib.Math.Real213.CutMul     -- cutMul, cutMulOuter, cutMulInner
import E213.Lib.Math.Real213.CutSumComm -- cutSum_comm
import E213.Lib.Math.Real213.CutMulComm -- cutMul_comm
import E213.Lib.Math.Real213.CutSumEq   -- cutSum_cutEq_*, cutMul_cutEq_*
```

### A.3 Core propEq theorems

```lean
import E213.Lib.Math.Real213.CutSumZero  -- cutSum_zero_zero, cutMul_zero_zero, cutMid_zero_zero
import E213.Lib.Math.Real213.CutSumOne   -- cutSum_zero_const, cutSum_const_zero,
                                         -- cutSum_int_int, cutSum_half_general,
                                         -- cutSum_half_half, cutSum_int_half, etc.
import E213.Lib.Math.Real213.CutMulOne   -- cutMul_one_one, cutMul_one_const,
                                         -- cutMul_const_one
import E213.Lib.Math.Real213.CutMidSelf  -- cutMid_self_constCut, cutMid_int_int,
                                         -- cutMid_half_general
```

### A.4 Half / Double / Mid

```lean
import E213.Lib.Math.Real213.CutBisection  -- cutHalf
import E213.Lib.Math.Real213.CutDouble     -- cutDouble
import E213.Lib.Math.Real213.CutPow        -- cutScale a b cx, cutPow x n
import E213.Lib.Math.Real213.CutPowConst   -- cutPow_one_n, cutPow_zero_succ
```

### A.5 Equivalence / Order

```lean
import E213.Lib.Math.Real213.CutPoset      -- cutEq, cutLe, cutEq_refl/symm/trans
```

---

## B. Dyadic structure

### B.1 DyadicBracket

```lean
import E213.Lib.Math.Real213.DyadicBracket
-- structure DyadicBracket where numA numB expE : Nat; hLe : numA ≤ numB
-- DyadicBracket.leftCut, rightCut, midCut, leftHalf, rightHalf, bisectN
```

### B.2 Bisection trajectory

```lean
import E213.Lib.Math.Real213.DyadicTrajectory
-- alwaysTrue, alwaysFalse, unitBracket
-- alwaysTrue_unit_numA/numB/expE n  closed forms
-- alwaysFalse_unit_numA/numB/expE n closed forms
-- ConsistentOracle structure
```

### B.3 Riemann sum

```lean
import E213.Lib.Math.Real213.DyadicRiemann
-- riemannSampleSum f db n
-- riemannSampleSum_constCut a b db n : closed form for constants
```

### B.4 Dyadic interval brackets (★ non-unit FTC)

```lean
import E213.Lib.Math.Real213.IntegralIntInterval    -- intInterval n = [0, n]
import E213.Lib.Math.Real213.IntegralGeneralInt     -- intIntervalAB a b h = [a, b]
import E213.Lib.Math.Real213.IntegralDyadic         -- ★★ dyadicIntervalAB numA numB E h
                                                     -- = [numA/2^E, numB/2^E] universal
```

---

## C. Differential calculus

### C.1 IsSmooth filter

```lean
import E213.Lib.Math.Real213.CutFnData              -- LocallyDeterminedData, addLDD, mulLDD, etc.
import E213.Lib.Math.Real213.IsSmooth
-- structure IsSmooth f extends LocallyDeterminedData f where linearityModulus : Nat → Nat
-- idIsSmooth, constIsSmooth, cutScaleIsSmooth, cutHalfIsSmooth
-- addIsSmooth, mulIsSmooth, composeIsSmooth, midIsSmooth
-- squareIsSmooth, cubeIsSmooth, ..., octicIsSmooth, ..., hexadecicIsSmooth
-- cutPowFnIsSmooth n (★ ∀ n recursive)
```

### C.2 Resolution depth

```lean
import E213.Lib.Math.Real213.ResolutionDepth
-- cutPowFnIsSmooth_modulus n k : (cutPowFnIsSmooth n).linearityModulus k = n*k
-- squareIsSmooth_modulus, cubeIsSmooth_modulus, ..., quarticIsSmooth_modulus
```

### C.3 IsDifferentiable

```lean
import E213.Lib.Math.Real213.IsDifferentiable
-- structure IsDifferentiable f extends IsSmooth f where
--   derivative : Cut → Cut; derivativeSmooth : IsSmooth derivative
-- idIsDifferentiable, constIsDifferentiable, addIsDifferentiable,
-- mulIsDifferentiable, composeIsDifferentiable, cutPowFnIsDifferentiable n

import E213.Lib.Math.Real213.DifferentiableInstances  -- square, cube, quartic + cutScale, cutHalf
import E213.Lib.Math.Real213.DifferentiableHigherPow  -- nonic, decic, dodecic, hexadecic
import E213.Lib.Math.Real213.DifferentiableHighOrder  -- 9, 10, 12, 16
import E213.Lib.Math.Real213.DifferentiableMid        -- midIsDifferentiable + instances
import E213.Lib.Math.Real213.DifferentiableAffine     -- affine, polynomial sums
import E213.Lib.Math.Real213.DifferentiableCompose    -- compose instances
```

### C.4 Derivative closed forms

```lean
import E213.Lib.Math.Real213.DerivativeForms
-- id_derivative_form, const_derivative_form, add_derivative_form,
-- mul_derivative_form, compose_derivative_form
-- cutPow_derivative_step (recurrence)
```

### C.5 ★ Sharp resolution depth

```lean
import E213.Lib.Math.Real213.DerivativeDepth                  -- cutPowFn_derivative_modulus
import E213.Lib.Math.Real213.ConcreteDerivativeModulus        -- square, cube, quartic
import E213.Lib.Math.Real213.ConcreteDerivativeModulusHigh    -- 5-8
import E213.Lib.Math.Real213.ConcreteDerivativeModulusFinal   -- 9, 10, 12, 16
import E213.Lib.Math.Real213.ConcreteDerivativeMega           -- ★ 11-fact bundle
```

---

## D. Cohomological framework

### D.1 FluxCut + 1-cochain

```lean
import E213.Lib.Math.Real213.FluxCut          -- FluxCut, neg, add, sub, ofCut, zero
                                              -- neg_neg, neg_add, sub_self_balanced
import E213.Lib.Math.Real213.FluxCochain      -- fluxAlong f db
import E213.Lib.Math.Real213.FluxDivergence   -- localDivergence, fluxScale
```

### D.2 Setoid bridge (★ no Quotient)

```lean
import E213.Lib.Math.Real213.FluxEquiv        -- cohomEquiv Setoid (0 axioms!)
import E213.Lib.Math.Real213.FluxEquivOps     -- neg/add/sub respect cohomEquiv
```

### D.3 Polynomial flux + MVT framework

```lean
import E213.Lib.Math.Real213.FluxPolynomial   -- localDivergence_square/cube/quartic etc.
import E213.Lib.Math.Real213.FluxMVT          -- fluxBalance + concrete cases
import E213.Lib.Math.Real213.FluxMVTConcrete  -- mvt_id_unitBracket (propEq)
import E213.Lib.Math.Real213.FluxMVTPolynomial -- square, cube at unit (propEq)
import E213.Lib.Math.Real213.FluxMVTHigh      -- quartic at unit
import E213.Lib.Math.Real213.FluxMVTGeneric   -- ★ ∀n cutPow x^(n+1) MVT
import E213.Lib.Math.Real213.FluxMVTPassthrough  -- ★★ general passthrough MVT
import E213.Lib.Math.Real213.FluxMVTApplications -- passthrough corollaries
import E213.Lib.Math.Real213.FluxMVTClosure   -- passthrough closure (compose, mul)
```

---

## E. MVT witnesses + classes

### E.1 Passthrough class

```lean
import E213.Lib.Math.Real213.FluxPassthroughClass    -- Passthrough struct, id_pass, cutPow_pass,
                                                     -- compose_pass, mul_pass + .mvt, .ftc
import E213.Lib.Math.Real213.FluxPassthroughCatalog  -- 7-instance catalog
```

### E.2 ★ HasDyadicMVTWitness

```lean
import E213.Lib.Math.Real213.FluxMVTWitness       -- ★ squareDerivative_at_half (c=1/2)
import E213.Lib.Math.Real213.HasDyadicMVTWitness  -- HasDyadicMVTWitness class
import E213.Lib.Math.Real213.FluxMVTMore          -- mid(x, x²) witness
import E213.Lib.Math.Real213.MVTWitnessCatalog    -- id at any c, x², mid(x,x²), id∘x²
import E213.Lib.Math.Real213.MVTWitnessChain      -- chain rule witness propagation
import E213.Lib.Math.Real213.FluxMVTNested        -- nested mid witness chain
import E213.Lib.Math.Real213.FluxMVTNested2       -- mid(mid, x²) witness
import E213.Lib.Math.Real213.FluxMVTPattern       -- 5-instance catalog
import E213.Lib.Math.Real213.FluxMVTPropagate     -- ★ generic mid propagation
import E213.Lib.Math.Real213.FluxMVTPropagateCompose -- ★ generic id-compose propagation
```

### E.3 ★ ClassicCalc unified class

```lean
import E213.Lib.Math.Real213.ClassicCalc           -- ClassicCalc f := { diff, pass }
                                                   -- id_calc, square_calc, cube_calc + .mvt, .ftc
import E213.Lib.Math.Real213.ClassicCalcHigher     -- degrees 4-8
import E213.Lib.Math.Real213.ClassicCalcExtreme    -- 9, 10, 12, 16
import E213.Lib.Math.Real213.ClassicCalcGeneric    -- ★ cutPow_calc n (∀ n)
import E213.Lib.Math.Real213.ClassicCalcMid        -- mid_calc + instances
import E213.Lib.Math.Real213.ClassicCalcCombinators -- compose_calc, mul_calc
import E213.Lib.Math.Real213.ClassicAnti           -- ClassicCalc → IsAntiderivative
```

---

## F. Integration / antiderivatives

### F.1 IsAntiderivative class

```lean
import E213.Lib.Math.Real213.Antiderivative
-- structure IsAntiderivative F sF f := { eq : sF.derivative = f }
-- IsAntiderivative.id_anti, const_anti

import E213.Lib.Math.Real213.AntiderivativeCombinators  -- mid_anti, add_anti
import E213.Lib.Math.Real213.AntiderivativeStructural   -- fromDifferentiable (★ all IsDiff)
```

### F.2 Integral = flux of antiderivative

```lean
import E213.Lib.Math.Real213.IntegralViaAnti
-- IsAntiderivative.integral hF db := fluxAlong F db

import E213.Lib.Math.Real213.IntegralProperties     -- integral_add, integral_mid, zero_length
import E213.Lib.Math.Real213.IndefiniteIntegral     -- indefIntFromZero

import E213.Lib.Math.Real213.IntegralIntInterval    -- ∫_0^n
import E213.Lib.Math.Real213.IntegralGeneralInt     -- ∫_a^b
import E213.Lib.Math.Real213.IntegralDyadic         -- ★★ ∫ over [a/2^E, b/2^E]
```

### F.3 FTC + Riemann

```lean
import E213.Lib.Math.Real213.FluxFTC                -- ftc_bridge_id_unitBracket
import E213.Lib.Math.Real213.FluxFTCPolynomial      -- square/cube/quartic FTC bridges
import E213.Lib.Math.Real213.FTCRiemann             -- id depth-0 FTC propEq
import E213.Lib.Math.Real213.FTCRiemannSquare       -- x² depth-0
import E213.Lib.Math.Real213.FTCRiemannMid          -- mid(x, x²) depth-0
import E213.Lib.Math.Real213.FTCRiemannGeneric      -- ★ generic via witness
import E213.Lib.Math.Real213.FTCRiemannChain        -- chain instances
```

---

## G. ODE + physics

```lean
import E213.Lib.Math.Real213.ODELinear              -- y' = a (linear)
import E213.Lib.Math.Real213.ODECatalog             -- 5-class trivial RHS
import E213.Lib.Math.Real213.ODESecondOrder         -- y'' = 0 for linear
import E213.Lib.Math.Real213.NewtonFirst            -- F=0 → constant velocity
import E213.Lib.Math.Real213.NewtonSecond           -- v' = a (Newton's 2nd in velocity form)
import E213.Lib.Math.Real213.CubeDerivativeAtZero   -- (x^n)' at 0 = 0
```

---

## H. Series + transcendental functions

### H.1 Series infrastructure

```lean
import E213.Lib.Math.Real213.CutSequence       -- CutSequence (Cauchy)
import E213.Lib.Math.Real213.CutSeries         -- partialSum, SeriesCauchy
import E213.Lib.Math.Real213.CutSeriesConst    -- partialSum constant closed forms
import E213.Lib.Math.Real213.CutSeriesZero     -- partialSum 0 series
import E213.Lib.Math.Real213.CutSeriesConv     -- ratio/comparison test scaffold
import E213.Lib.Math.Real213.CutGeomSeries     -- geomHalfSeries
import E213.Lib.Math.Real213.FluxSeries        -- seriesFlux, geomHalfFlux
import E213.Lib.Math.Real213.GeomSeriesPartialSum  -- ★ S_1, S_2 propEq
```

### H.2 ★★ Transcendentals at zero

```lean
import E213.Lib.Math.Real213.ExpAtZero          -- ★ exp(0) = 1
import E213.Lib.Math.Real213.SinCosAtZero       -- ★ sin(0) = 0, cos(0) = 1
import E213.Lib.Math.Real213.TranscendentalAtZero  -- ★★ 7 functions bundle
                                                   -- exp/sin/cos/tan/sinh/cosh/log
```

---

## I. Capstone theorems

Mega theorems *directly callable* when using the library:

| Capstone | Module | Facts |
|---|---|---|
| `phaseL_unified_capstone` | `Real213PhaseLCapstone` | 8 |
| `allPhase_super_capstone` | `Real213PhaseLCapstone` | 7 |
| `phaseAC_minimum_proposition` | `Real213PhaseACMinimumProposition` | 3 |
| `phaseAD_unified_capstone` | `Real213PhaseADCapstone` | 7 |
| `phaseAE_super_capstone` | `Real213PhaseAESuperCapstone` | 9 |
| `phaseAH_grand_capstone` | `Real213PhaseAHGrandCapstone` | 11 |
| `polynomial_diff_full_coverage` | `Real213DifferentiableMegaCoverage` | 12 |
| `phaseAN_omega_capstone` | `Real213PhaseANOmegaCapstone` | 13 |
| `concrete_derivative_sharp_pattern` | `Real213ConcreteDerivativeMega` | 11 |
| `cohomology_arc_capstone` | `Real213FluxCohomologyCapstone` | 7 |
| `phaseBA_capstone` | `Real213PhaseBACapstone` | 8 |
| `phaseBH_grand_capstone` | `Real213PhaseBHCapstone` | 8 |
| `phaseBQ_omega_capstone` | `Real213PhaseBQOmegaCapstone` | 11 |
| `phaseCM_final_capstone` | `Real213PhaseCMFinalCapstone` | 10 |
| `phaseCS_antiderivative_capstone` | `Real213PhaseCSCapstone` | 8 |
| `phaseDA_omega_omega_capstone` | `Real213PhaseDAOmegaOmega` | 14 |
| **★★★★ `phaseDK_ultimate_capstone`** | `Real213PhaseDKUltimate` | **18** |

---

## J. Usage examples — library call patterns

### J.1 Polynomial differentiation

```lean
import E213.Lib.Math.Analysis213
open E213.Lib.Math.Real213.CutSum

-- polynomial modulus
example : (cutPowFnIsSmooth 5).linearityModulus 3 = 15 :=
  cutPowFnIsSmooth_modulus 5 3

-- directly constructed polynomial differentiation (sharp)
example : squareIsDifferentiable.derivativeSmooth.linearityModulus 7 = 7 :=
  squareIsDifferentiable_derivative_modulus 7

-- explicit form of derivative
example (x : Cut) : squareIsDifferentiable.derivative x
    = cutSum (cutMul (constCut 1 1) x) (cutMul x (constCut 1 1)) := rfl
```

### J.2 MVT application

```lean
-- ANY passthrough function — one-liner
example (f : Cut → Cut)
    (h0 : f (constCut 0 1) = constCut 0 1)
    (h1 : f (constCut 1 1) = constCut 1 1) :
    FluxCut.localDivergence f unitBracket = FluxCut.ofCut (constCut 1 1) :=
  FluxCut.mvt_passthrough_unit f h0 h1

-- polynomial generic — ∀ n
example (n : Nat) :
    FluxCut.localDivergence (fun x => cutPow x (n+1)) unitBracket
      = FluxCut.ofCut (constCut 1 1) :=
  ClassicCalc.cutPow_calc_mvt n
```

### J.3 Integration

```lean
-- ∫_0^n 1 dx = n
example (n : Nat) :
    IsAntiderivative.integral IsAntiderivative.id_anti (intInterval n)
      = { forward := constCut n 1, backward := constCut 0 1 } := rfl

-- ★★ ∫ over arbitrary dyadic interval
example (numA numB E : Nat) (h : numA ≤ numB) :
    IsAntiderivative.integral IsAntiderivative.id_anti
        (dyadicIntervalAB numA numB E h)
      = { forward := constCut numB (2^E), backward := constCut numA (2^E) } := rfl
```

### J.4 Transcendental functions at zero

```lean
-- exp(0) = 1
example (n : Nat) : partialSum expTermsAtZero (n+1) = constCut 1 1 :=
  expAtZero_partial_succ n

-- sin(0) = 0
example (n : Nat) : partialSum sinTermsAtZero n = constCut 0 1 :=
  sinAtZero_partial n
```

### J.5 ODE / Newton

```lean
-- 1st order linear ODE: y' = a
example (a b : Nat) :
    (linearWithIntercept_isDifferentiable a b).derivative
      = constCutFn (constCut a 1) :=
  linearWithIntercept_derivative a b

-- Newton 1st: constant velocity
example (v0 x0 : Nat) (t : Cut) :
    (linearWithIntercept_isDifferentiable v0 x0).derivative t = constCut v0 1 := by
  rw [velocity_is_v0]
```

### J.6 ULTIMATE one-liner

```lean
-- Phase DK — call all core results in one line with 18 facts
example (n k v0 x0 a b numA numB E : Nat)
    (h_num : numA ≤ numB)
    (f : Cut → Cut)
    (h_left : f (constCut 0 1) = constCut 0 1)
    (h_right : f (constCut 1 1) = constCut 1 1) :=
  phaseDK_ultimate_capstone n k v0 x0 a b numA numB E h_num
                            f h_left h_right
```

---

## K. Axiom audit — all results STRICT ∅-AXIOM

```lean
import E213.Lib.Math.Analysis
-- (or any specific module)

#print axioms FluxCut.cohomEquiv_refl
-- 'FluxCut.cohomEquiv_refl' does not depend on any axioms  -- ★ ∅-axiom
```

Per `STRICT_ZERO_AXIOM.md` "Terms (canonical)": the standard is
strict ∅-axiom (`#print axioms` returns "does not depend on any
axioms").

---

## J. Flat ontology + self-reference (§9.3 + §9.5 realisation)

Added 2026-05-20.  Closes the residue framework's self-reference
loop within the Lean tree.

### J.1 `Lens/FlatOntology` — §9.3 forward direction

```lean
import E213.Lens.FlatOntology
-- abbrev Type213 (n : Nat) : Type := (Fin n → Raw) → Bool
-- abbrev UnaryType : Type := Raw → Bool
-- abbrev Relation : Type := Raw → Raw → Bool
-- def Object1 (r : Raw) : Raw → Bool
-- def eqRelation : Relation
-- def functionAsRelation (f : Raw → Raw) : Relation
-- def lensBoolAsType (L : Lens Bool) : UnaryType
-- def lensFibreType {α} [DecidableEq α] (L : Lens α) (a : α) : UnaryType
```

12 PURE / 0 DIRTY.  Realises §9.3's "objects, types, relations,
functions, Lens all as decidable predicates on Raw^n".

### J.2 `Lens/PredicateSelfEncoding` — §9.3 closure direction

```lean
import E213.Lens.PredicateSelfEncoding
-- def truthTableNat (n : Nat) (P : Nat → Bool) : Nat
-- def predicateToRaw (n : Nat) (P : Raw → Bool) : Raw
-- theorem predicate_self_encoding_closure
-- theorem predicateToRaw_kernel
-- theorem predicateToRaw_injective_on_prefix
```

7 PURE / 0 DIRTY.  Encodes finite-prefix Raw-predicates back to
Raw via positional truth-table Gödel numbering.

### J.3 `Lens/UndifferentiatedRaw` — §9.5 K_∞ ≡ point at raw

```lean
import E213.Lens.UndifferentiatedRaw
-- theorem constLens_collapses : ∀ {α} (e : α) (r s : Raw),
--   (constLens e).view r = (constLens e).view s
-- theorem pre_lens_singleton
-- theorem constLens_kernel_total
```

3 PURE / 0 DIRTY.  Witness: under the constant Lens, every Raw
maps to the same value — the no-distinction reading of Raw is a
singleton.

---

## K. Three-direction uniqueness (§1.3 unified bundle)

```lean
import E213.Meta.ThreeDirectionUniqueness
-- theorem three_direction_uniqueness :
--   (below : 4-clause minimality)
--   ∧ (sideways : universal-Lens factoring, 4 witnesses)
--   ∧ (above : Atomic n ↔ n = 5)
```

1 PURE theorem bundling Below (AxiomMinimality) + Sideways
(UniversalLens TripleCapstone) + Above (Atomicity Five).

---

## L. Möbius frozen + dynamic dualism (§3.4 + §8.7)

```lean
import E213.Lib.Math.Mobius213
-- theorem mobius_213_char_poly_at_trace
-- theorem mobius_213_pell_unit_invariant_layer{0..4}
-- theorem pell_unit_at_succ           ★★ X(n+1) = X(n) via Int213.* rw
-- theorem mobius_213_pell_unit_invariant_forall  ★★★ ∀n X(n) = -1
```

`num_n · den_{n+1} − num_{n+1} · den_n = -1` across all convergent
layers, witnessing det [[2,1],[1,1]] = 1.  Same algebraic content
under frozen (fixed-point) + dynamic (iteration) readings.

The ∀n form (`mobius_213_pell_unit_invariant_forall`) closes the
deferred universal form previously blocked by lack of 213-native
Int ring algebra; proven via `cross_step_algebra` (manual rw chain
using `Meta.Int213.*` only — no simp, no omega, no Mathlib).

---

## M. 213-tower L_∞ structural closure (G61, Phase 1 hero)

```lean
import E213.Lib.Math.Mobius213.TowerLInfty
-- theorem tower_trajectory_unique          ★ G61 Q1: deterministic P-iter
-- theorem tower_growth_phi_squared_bracket ★ φ² ∈ (2, 3) at layers 1..7
-- theorem pell_unit_constant_under_iteration ★★★ tower invariant -1
-- theorem g61_partial_capstone             ★★★ Q1 + Q5(part) + L_∞

import E213.Lib.Math.Mobius213.TowerConvergence
-- theorem tower_L_infty_exists  ★★★ Phase 1c hero: L_∞ existence
                                    witness via (Pell-unit ∀n,
                                    φ-bracket, trajectory uniqueness)

import E213.Lib.Math.Real213.PhiCut
-- def pellConvergentCut (n : Nat)  φ approximant Cut at layer n
-- theorem pell_bracket_width_witness  Pell-unit invariant in Nat form
-- theorem phi_bracket_via_pell        concrete φ ∈ (3/2, 5/3)
-- theorem phi_cut_capstone            ★★★ Phase 1b closure (7-conjunct)
```

Closes three of the five G61 structural questions (Q1, Q5 partial,
L_∞ existence).  Q2 + Q3 (213-internal L0 via swap-as-negation) and
Q4 (3-side extension) remain research-thread follow-ups.

---

## N. Minimal Root Lens IVT certificate (G31, Phase 4)

```lean
import E213.Lib.Math.Analysis.DyadicSearch.MinimalRootCapstone
-- def ivt_root_certificate     ★★★ 4-input typed-witness IVT root
-- theorem ivt_four_axis_correspondence  modulus/trajectory/structure/residue
-- theorem g31_phase4_closure   ★★ G31 design realised
```

213-native locatedness as four typed data witnesses, no classical
content imported.  Pairs with the existing
`MinimalRootLens.fromConsistentOracleRatio` infrastructure.

---

## O. Catalog statistics

| Category | Modules | Key theorems |
|---|---|---|
| A. Cut Algebra | 10+ | 50+ propEq |
| B. Dyadic structure | 6 | 30+ |
| C. Differential calculus | 12 | 80+ |
| D. Cohomological | 7 | 30+ |
| E. MVT witnesses | 13 | 40+ |
| F. Integration | 8 | 25+ |
| G. ODE + physics | 6 | 20+ |
| H. Series + transcendental | 9 | 20+ |
| I. Capstone | 17 | 17 mega-conjunction |
| J. Flat ontology + closure | 3 | 22+ |
| K. Three-direction uniqueness | 1 | 1 unified |
| L. Möbius frozen+dynamic | 1 | 8 |
| M. Tower L_∞ closure (G61, Phase 1) | 3 | 14 |
| N. Minimal Root IVT cert (G31, Phase 4) | 1 | 3 |
| **Total** | **96+** (core of 178+ total modules) | **354+ theorems** |

STRICT ∅-AXIOM · 0 sorry · Mathlib-free · 0 Classical · 0 native_decide

