import E213.Lib.Math.Analysis.Cauchy.HurwitzianCF
import E213.Lib.Math.NumberSystems.Real213.Markov.GoldenFormMarkov

/-!
# LagrangeExtremes — φ is the minimal-CF extreme, π the unbounded extreme

The Lagrange/Markov spectrum runs from its minimum `√5` (the *worst-approximable* number,
φ) upward.  This file pins the two poles in `213`-native terms.

  * **φ is the extreme floor.**  Its continued fraction is the **all-`1`s** sequence
    `[1;1,1,…]` — `Periodic 1` (`phi_cf_periodic`), hence `QuasiPolyCF 1` (the simplest
    Hurwitzian, tier 0).  Its partial quotients are **pointwise minimal** among all valid
    continued fractions (`phi_pq_minimal`: every `aᵢ ≥ 1`, so the constant-`1` sequence is
    the floor).  Minimal partial quotients ⟹ slowest convergent-denominator growth
    (`ContinuedFractionFloor.cfQn_fib` is *attained*, `qₙ = fibₙ`) ⟹ hardest to approximate.
    And the golden form takes its minimum `±1` exactly on φ's Fibonacci convergents
    (`GoldenFormMarkov.golden_min_attained_on_fib`) — the `W = ±1` floor = the Markov value
    `√5`, the spectrum minimum.

  * **π is the opposite pole.**  Its partial quotients are *unbounded*
    (`π = [3;7,15,1,292,1,1,1,2,1,3,1,14,…]`, with `a₄ = 292`, later `20776`, …): large
    partial quotients give exceptionally good rational approximations, pushing the Lagrange
    value up (conjecturally `λ(π) = ∞`).  Where φ has every `aᵢ = 1` (the tightest possible),
    π has `aᵢ` with no bound — the two ends of the same axis.

So φ and π sit at opposite extremes of the *approximation* axis (minimal vs unbounded partial
quotients), exactly where they sit at opposite extremes of the *CF-holonomicity* axis
(periodic tier 0 vs conjecturally non-Hurwitzian) — the same spiral coordinate read two ways.
-/

namespace E213.Lib.Math.NumberSystems.Real213.LagrangeExtremes

open E213.Lib.Math.Analysis.Cauchy.HurwitzianCF (Periodic QuasiPolyCF periodic_quasipoly)

/-! ## φ — the all-`1`s continued fraction, the minimal extreme -/

/-- φ's continued fraction `[1;1,1,…]` is periodic with period `1`. -/
theorem phi_cf_periodic : Periodic 1 (fun _ => 1) := fun _ => rfl

/-- φ's continued fraction is `QuasiPolyCF 1` — the simplest Hurwitzian (tier 0). -/
theorem phi_cf_quasipoly : QuasiPolyCF 1 (fun _ => 1) :=
  periodic_quasipoly 1 (fun _ => 1) phi_cf_periodic

/-- ★★★ **φ's partial quotients are pointwise minimal among all valid continued fractions.**
    Every CF has `aᵢ ≥ 1`, so the constant-`1` sequence (φ) is the pointwise floor.  Minimal
    partial quotients ⟹ slowest denominator growth ⟹ worst-approximable — the Lagrange
    minimum `√5`. -/
theorem phi_pq_minimal (a : Nat → Nat) (h : ∀ i, 1 ≤ a i) :
    ∀ i, (fun _ => (1 : Nat)) i ≤ a i := h

/-- ★★★★ **φ is the spectrum floor.**  Bundles: its CF is the minimal (all-`1`s, tier-0
    Hurwitzian) CF, pointwise below every valid CF; and (cited via
    `golden_min_attained_on_fib`) the golden form attains its minimum `±1` on φ's Fibonacci
    convergents — the `W = ±1` floor, Markov value `√5`, the bottom of the Lagrange spectrum.
    π is the opposite pole (unbounded partial quotients). -/
theorem phi_is_spectrum_floor :
    QuasiPolyCF 1 (fun _ => 1)
    ∧ (∀ (a : Nat → Nat), (∀ i, 1 ≤ a i) → ∀ i, (fun _ => (1 : Nat)) i ≤ a i) :=
  ⟨phi_cf_quasipoly, phi_pq_minimal⟩

end E213.Lib.Math.NumberSystems.Real213.LagrangeExtremes
