import E213.Lib.Math.Cohomology.Bipartite.SelfPairingTrace
import E213.Lib.Physics.AlphaEM.RefinedCupLadderDerivation
import E213.Lib.Physics.AlphaEM.OmegaPostGramFull

/-!
# Per-layer coupling reformulation — (α/d)^(k+1) as the natural building block

Reformulates the refined cup-ladder formula

      Δ_H^k(c) = ||c||² · α^(k+1) / d^(k+1)

as the cleaner factorisation

      Δ_H^k(c) = ||c||² · (α/d)^(k+1)

exposing the **per-layer coupling ratio** α/d as the natural
structural building block.  An H^k cohomology class then
contributes `(k+1)` factors of this per-layer coupling — one per
cohomology level traversed.

## Structural interpretation

The 5-layer base structure has `d = 5` layers.  The "fine structure
constant per layer" is the ratio α/d — the coupling strength
distributed across each base layer.

For a cohomology class of degree k:
  · k contributes the **filtration depth** (how many cohomology
    levels the class spans);
  · +1 contributes the **top-cell evaluation** (one final coupling
    factor to read the trace);
  · together: `(k+1)` per-layer coupling factors.

This isn't a derivation from cup-product axioms (Phase 7+
frontier remains open on that front).  It IS a clean reformulation
that:
  · names α/d as the structural quantity;
  · proves the refined formula factors `weight² · (α/d)^(k+1)`
    at k = 1, 2 by Nat-level decide;
  · positions the (k+1) graduation as filtration depth + top
    evaluation, not as bilinear cup arity.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Physics.AlphaEM.PerLayerCoupling

open E213.Lib.Math.Cohomology.Bipartite.Filled3CellCohomology
open E213.Lib.Math.Cohomology.Bipartite.SelfPairingTrace
open E213.Lib.Physics.AlphaEM.GradedFormulaPrecision
open E213.Lib.Physics.AlphaEM.GramSelfConsistency
open E213.Lib.Physics.AlphaEM.GramHigherOrder
open E213.Lib.Physics.AlphaEM.OmegaH2Trace
open E213.Lib.Physics.AlphaEM.OmegaPostGramFull
open E213.Lib.Physics.AlphaEM.RefinedCupLadderDerivation

/-! ## §1 — Per-layer coupling (α/d)^j at e9 precision -/

/-- The j-th power of the per-layer coupling ratio α/d at 10⁻⁹
    precision.

      (α/d)^j · 10⁹ = 10^(9·(j+1)) / (d^j · observed_e9^j).

    Numerator `9·(j+1) = 9·j + 9` packs `9·j` for converting α^j
    from absolute to e9 scale, plus `+9` for the final e9
    multiplier. -/
def alpha_over_d_pow_e9 (j : Nat) : Nat :=
  (10 ^ (9 * (j + 1))) / (d_base ^ j * (observed_e9 ^ j))

/-- ★★★ `(α/d)¹ · 10⁹` evaluates to `10¹⁸ / (5 · observed_e9)`
    ≈ 1.46 × 10⁶ (the per-layer fine-structure coupling at
    e9 precision). -/
theorem alpha_over_d_pow_1 :
    alpha_over_d_pow_e9 1 = (10 ^ 18) / (5 * observed_e9) := by
  unfold alpha_over_d_pow_e9 d_base; decide

/-! ## §2 — Refined trace factors as ||c||² · (α/d)^(k+1) -/

/-- ★★★★★ At k = 1: the H¹ Gram self-energy factors as the
    bilinear `1² · (α/d)²` — one cohomology level traversed
    plus the top-cell evaluation gives two per-layer coupling
    factors. -/
theorem refined_trace_factors_at_k1 :
    refined_trace_e9 1 1 = 1 * 1 * alpha_over_d_pow_e9 2 := by
  unfold refined_trace_e9 cup_graduation_denom d_base alpha_over_d_pow_e9
  decide

/-- ★★★★★ At k = 2: the H² ω-weighted contribution factors as
    `NS² · (α/d)³` — two cohomology levels traversed plus the top
    evaluation gives three per-layer coupling factors, with the
    NS² weight from the L²-pairing trace rule (proved in
    `SelfPairingTrace`). -/
theorem refined_trace_factors_at_k2 :
    refined_trace_e9 2 (faceCochainL1 omega_face_vec)
      = 3 * 3 * alpha_over_d_pow_e9 3 := by
  rw [omega_L1_derived]
  unfold refined_trace_e9 cup_graduation_denom d_base alpha_over_d_pow_e9
  decide

/-! ## §3 — Gram and ω-weighted in per-layer form -/

/-- ★★★★ Gram self-energy as `(α/d)²` (rank-1 effective weight). -/
theorem gram_eq_alpha_over_d_sq :
    gram_correction_e9 = alpha_over_d_pow_e9 2 := by
  unfold alpha_over_d_pow_e9 d_base gram_correction_e9
  decide

/-- ★★★★ ω-weighted contribution as `NS² · (α/d)³`. -/
theorem omega_weighted_eq_NS_sq_alpha_over_d_cubed :
    omega_weighted_trace_e9 = 9 * alpha_over_d_pow_e9 3 := by
  unfold alpha_over_d_pow_e9 d_base omega_weighted_trace_e9
         d_cubed omega_weight_sq omega_L2_norm_sq
  decide

/-! ## §4 — Phase 7 master -/

/-- ★★★★★★★★ **PerLayerCoupling master**.  STRICT ∅-AXIOM.

    The refined cup-ladder formula factors cleanly via the
    per-layer coupling ratio α/d:

      Δ_H^k(c) = ||c||² · (α/d)^(k+1).

    The (k+1) graduation reads as `filtration depth + top
    evaluation`: an H^k class spans k cohomology levels (the
    filtration depth), and the trace at top adds one final
    coupling factor.  In total `(k+1)` factors of the per-layer
    coupling α/d.

    Specialisations:
      · k = 1 (H¹ Gram, rank-1): `1 · (α/d)² = α²/d²` = 2130 × 10⁻⁹.
      · k = 2 (H² ω, derived weight NS): `NS² · (α/d)³ = 9·α³/d³`
        = 27 × 10⁻⁹.

    Full residual sum: `(α/d)² + NS²·(α/d)³ = 2157 × 10⁻⁹` =
    raw α_em residual, in two per-layer-graduated terms.

    Status of the refined cup-ladder formula (post-Phase 7):

      | Component | Status |
      |-----------|--------|
      | `||c||² = (L¹-norm)²` | PROVED (Nat identity, Phase 6) |
      | `(α/d)^(k+1)` factoring | PROVED (this Phase, k = 1, 2) |
      | `(k+1) = filtration depth + 1` | POSIT (cohomology-theoretic) |

    The per-layer coupling reformulation makes the (k+1)
    graduation NUMERICALLY explicit at the concrete cases.  Why
    `(k+1)` specifically (vs `k + l` from bilinear cup arity)
    remains the open cohomology-theoretic question — the
    filtration-depth-plus-top-evaluation reading is a structural
    POSIT pending higher-cup or spectral-sequence formalization. -/
theorem per_layer_coupling_master :
    -- Per-layer coupling at (k+1) factors of α/d
    refined_trace_e9 1 1 = 1 * 1 * alpha_over_d_pow_e9 2
    ∧ refined_trace_e9 2 (faceCochainL1 omega_face_vec)
        = 3 * 3 * alpha_over_d_pow_e9 3
    -- Identifications with existing Gram and ω-weighted corrections
    ∧ gram_correction_e9 = alpha_over_d_pow_e9 2
    ∧ omega_weighted_trace_e9 = 9 * alpha_over_d_pow_e9 3
    -- Full residual decomposition in per-layer form
    ∧ alpha_over_d_pow_e9 2 + 9 * alpha_over_d_pow_e9 3 = 2157
    -- Numerical values of per-layer powers
    ∧ alpha_over_d_pow_e9 2 = 2130
    ∧ alpha_over_d_pow_e9 3 = 3 := by
  refine ⟨refined_trace_factors_at_k1, refined_trace_factors_at_k2,
          gram_eq_alpha_over_d_sq, omega_weighted_eq_NS_sq_alpha_over_d_cubed,
          ?_, ?_, ?_⟩ <;>
    (try (unfold alpha_over_d_pow_e9 d_base)) <;> decide

end E213.Lib.Physics.AlphaEM.PerLayerCoupling
