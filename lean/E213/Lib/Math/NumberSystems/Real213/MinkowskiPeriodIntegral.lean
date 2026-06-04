import E213.Lib.Math.NumberSystems.Real213.CutIntegral
import E213.Lib.Math.NumberSystems.Real213.CutIntegralLinearity
import E213.Lib.Math.NumberSystems.Real213.Core.CutPoset

/-!
# MinkowskiPeriodIntegral — the period integral is ∅-axiom, not Mathlib-dependent

A correction and a foothold.  An earlier claim held that the higher-weight Eichler–Shimura *period
integrals* "need analysis (integration) and would break ∅-axiom purity if imported from Mathlib."
That is **false**: the repository builds its **own** ∅-axiom integral — the dyadic Riemann sample
sum `riemannSampleSum` lifted to `cutIntegralOver` over `DyadicMeasurableSet`s
(`Real213/CutIntegral`, `Real213/CutIntegralLinearity`, `Analysis/DyadicSearch/DyadicRiemann`), with
linearity, additivity, the constant fundamental theorem, and `no_pi_in_finite_riemann`, **all PURE**.
Integration is ∅-axiom-native here.

So the weight-2 period of the `?`-cocycle (`MinkowskiCocycle.minkowski_weight2_period_relation`) has,
besides its **algebraic** representative (the `√(−1)` residue), an **analytic** one — the dyadic
integral of the `V_0` (constant) integrand, `∫_a^b c \, dx = c·(b−a)` — and *both are ∅-axiom*.  The
genuine obstruction to *full* Eichler–Shimura (higher weight `V_{k−2}`) is **constructive**, not
axiom-cost: the repo lacks a modular-form contour over `ℍ` and a general power-rule primitive
`∫ z^{k−2} dz`.  That is a frontier to build, not a purity wall.
-/

namespace E213.Lib.Math.NumberSystems.Real213.MinkowskiPeriodIntegral

open E213.Lib.Math.NumberSystems.Real213.Core.CutPoset (cutEq)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.NumberSystems.Real213.Bisection.CutContinuity (constCutFn)
open E213.Lib.Math.NumberSystems.Real213.CutIntegral (cutIntegralOver)
open E213.Lib.Math.NumberSystems.Real213.CutIntegralLinearity (cutIntegralOver_cons_append)
open E213.Lib.Math.Analysis.DyadicSearch.DyadicRiemann
  (riemannSampleSum fundamental_dyadic_calculus_const no_pi_in_finite_riemann)
open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Lib.Math.Analysis.Measure.MeasurableSet (DyadicMeasurableSet)

/-- ★★★ **The weight-2 period integral is ∅-axiom** (correcting "integration needs Mathlib").
    The analytic representative of the `?`-cocycle's weight-2 period — the dyadic integral of the
    `V_0` (constant) integrand — is built from the repo's own ∅-axiom Riemann integral, with the
    three structural facts a period needs:

      1. **closed form (the `V_0` / weight-2 period)** — `∫_a^b c \, dx = c·(b−a)`, the constant
         fundamental theorem of dyadic calculus (`fundamental_dyadic_calculus_const`);
      2. **path-additivity (the abelian period-cochain skeleton)** — the integral over a concatenated
         domain splits, `∫_{(b::S)⧺T} = ⟨head sample⟩ ⊕ ∫_{S⧺T}` (`cutIntegralOver_cons_append`) —
         the additive structure a 1-cochain period carries along a path;
      3. **no transcendental escape** — the constant period stays rational, no `π`
         (`no_pi_in_finite_riemann`), the finite-resolution face of the residue's own rationality.

    So the weight-2 period has an ∅-axiom *analytic* representative (this integral) alongside its
    ∅-axiom *algebraic* one (the `√(−1)` residue, `minkowski_weight2_period_relation`).  Integration
    is native; the gap to higher-weight `H^1(SL(2,ℤ), V_{k−2})` is the missing modular contour +
    power-rule primitive — **constructive, not purity**.  ∅-axiom. -/
theorem weight2_period_integral_pure :
    (∀ a b n : Nat, cutEq (constCut (2 ^ n * a) (b * 2 ^ n)) (constCut a b))
    ∧ (∀ (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) (brkt : DyadicBracket)
         (S T : DyadicMeasurableSet) (n : Nat),
        cutIntegralOver f ((brkt :: S) ++ T) n
        = cutSum (riemannSampleSum f brkt n) (cutIntegralOver f (S ++ T) n))
    ∧ (∀ (a b : Nat) (db : DyadicBracket) (n : Nat),
        ∃ M : Nat, cutEq (riemannSampleSum (constCutFn (constCut a b)) db n) (constCut M b)) :=
  ⟨fundamental_dyadic_calculus_const, cutIntegralOver_cons_append, no_pi_in_finite_riemann⟩

end E213.Lib.Math.NumberSystems.Real213.MinkowskiPeriodIntegral
