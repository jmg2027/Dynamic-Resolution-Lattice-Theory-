import E213.Lib.Math.Cohomology.Bipartite.Filled3CellCohomology
import E213.Lib.Physics.AlphaEM.RefinedCupLadderDerivation

/-!
# Bilinear self-pairing trace = (L¹-norm)² — first-principles step

Promotes the L²-pairing trace rule from a structural posit to a
proved Nat identity:

  Σ_{i, j ∈ Fin 3} c_i · c_j = (Σ_i c_i)²        (for c : Fin 3 → Bool)

This is the standard "expansion of square" identity, here proved
universally over the 2³ = 8 inhabitants of `Fin 3 → Bool` via
`cases` on each Bool argument followed by `rfl`.

## Decomposition of the refined cup-ladder formula

The refined formula `Δ_H^k(c) = ||c||² · α^(k+1) / d^(k+1)`
factors into two rules.  After this file:

  | Rule | Status |
  |------|--------|
  | L²-pairing trace `||c||² = (L¹-norm)²` | PROVED here as Nat identity |
  | Cup-product graduation `α^(k+1)` at H^k | STRUCTURAL POSIT (no cup axiom yet) |

The L²-pairing side is now first-principles content; the
cup-graduation side remains the open frontier.  At ω the bilinear
self-trace `Σ_{i,j} ω_i · ω_j` evaluates to NS² = 9 directly
from `omega_face_vec`, completing the cohomology-derived input
chain for the Phase 4 NS²·α³/d³ closure.

## Cup-graduation limitation

The existing `Math/Cohomology/Cup/Core.lean` `cup` operation has
arity `Cochain n k × Cochain n l → Cochain n (k+l)` — output
degree is `k + l`, not `k + 1`.  Self-pairing at degree k gives
output at 2k, not k+1.  Hence `α^(k+1)` does NOT follow from the
existing bilinear cup arity; it requires additional structure
(higher-cup machinery, filtration depth, or spectral-sequence
differential) not yet formalized.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.SelfPairingTrace

open E213.Lib.Math.Cohomology.Bipartite.Filled3CellCohomology
open E213.Lib.Physics.AlphaEM.RefinedCupLadderDerivation

/-! ## §1 — Bilinear self-pairing trace via face-pair tensor product

For a face cochain `c : Fin 3 → Bool` over the 3 simple 4-cycles
of `K_{3,2}^{(c=2)}`, the bilinear self-tensor trace sums the
product `c_i · c_j` (integer lift) over all 9 face pairs `(i, j)`
in `Fin 3 × Fin 3`.

This is the L²-pairing trace functional on `C² ⊗ C² → ℤ`. -/

/-- Bilinear self-pairing trace of a face cochain. -/
def bilinearSelfTrace (c : Fin 3 → Bool) : Nat :=
    boolToNat (c ⟨0, by decide⟩) * boolToNat (c ⟨0, by decide⟩)
  + boolToNat (c ⟨0, by decide⟩) * boolToNat (c ⟨1, by decide⟩)
  + boolToNat (c ⟨0, by decide⟩) * boolToNat (c ⟨2, by decide⟩)
  + boolToNat (c ⟨1, by decide⟩) * boolToNat (c ⟨0, by decide⟩)
  + boolToNat (c ⟨1, by decide⟩) * boolToNat (c ⟨1, by decide⟩)
  + boolToNat (c ⟨1, by decide⟩) * boolToNat (c ⟨2, by decide⟩)
  + boolToNat (c ⟨2, by decide⟩) * boolToNat (c ⟨0, by decide⟩)
  + boolToNat (c ⟨2, by decide⟩) * boolToNat (c ⟨1, by decide⟩)
  + boolToNat (c ⟨2, by decide⟩) * boolToNat (c ⟨2, by decide⟩)

/-! ## §2 — L²-pairing trace = (L¹-norm)²

The bilinear self-trace equals the squared L¹-norm — the standard
"expansion of square" identity:

  (Σ_i x_i)² = Σ_i x_i² + 2 Σ_{i < j} x_i x_j = Σ_{i, j} x_i x_j.

Proved universally over `Fin 3 → Bool` by casing each Bool value.
-/

/-- ★★★★★ **L²-pairing trace rule** as a proved Nat identity.

    For any face cochain `c : Fin 3 → Bool`, the bilinear
    self-pairing trace equals the squared L¹-norm of the
    integer lift.

    Proof: `cases` on each of the 3 Bool values gives 2³ = 8
    ground cases, each `rfl` after unfolding `boolToNat`. -/
theorem bilinear_self_trace_eq_L1_sq (c : Fin 3 → Bool) :
    bilinearSelfTrace c = faceCochainL1Sq c := by
  unfold bilinearSelfTrace faceCochainL1Sq faceCochainL1 boolToNat
  cases (c ⟨0, by decide⟩) <;>
    cases (c ⟨1, by decide⟩) <;>
      cases (c ⟨2, by decide⟩) <;> rfl

/-- ★★★★ Specialisation to ω: `bilinearSelfTrace ω = NS² = 9`,
    derived structurally from the `omega_face_vec = fun _ => true`
    definition.  Direct `decide` matches the universal Phase 1+2
    identity above. -/
theorem omega_bilinear_self_trace_value :
    bilinearSelfTrace omega_face_vec = 9 := by decide

/-- ★★★ `bilinearSelfTrace ω = 3 · 3 = NS · NS`, exhibiting the
    L²-pairing as a literal product of NS factors. -/
theorem omega_self_trace_factors_as_NS_squared :
    bilinearSelfTrace omega_face_vec = 3 * 3 := by decide

/-! ## §3 — Bridge to `RefinedCupLadderDerivation.faceCochainL1Sq` -/

/-- ★★★★ The bilinear self-pairing trace agrees with the
    `RefinedCupLadderDerivation.faceCochainL1Sq` definition at ω,
    closing the cohomology-derived input chain:

      omega_face_vec → bilinearSelfTrace = 9 = faceCochainL1Sq = NS².

    Combined with `RefinedCupLadderDerivation.omega_L1Sq_derived`
    this shows the L²-pairing TRACE (bilinear tensor) and the
    L²-pairing NORM (squared L¹-norm) coincide on the H² ω class. -/
theorem omega_bilinear_self_trace_eq_L1_sq :
    bilinearSelfTrace omega_face_vec = faceCochainL1Sq omega_face_vec :=
  bilinear_self_trace_eq_L1_sq omega_face_vec

/-! ## §4 — Cup-product graduation rule (structural posit)

The existing `cup : Cochain n k × Cochain n l → Cochain n (k+l)`
operation in `Math/Cohomology/Cup/Core.lean` has output degree
`k + l`.  Self-pairing at degree k gives output degree 2k.

The α-power graduation `H^k → α^(k+1)` does NOT follow from this
bilinear cup arity (which would give 2k, not k+1).  It requires
additional structure — higher-cup operations, filtration depth, or
spectral-sequence differentials — not yet formalized.

Recorded here as a definition (not a derivation) so that
downstream files can reference the rule uniformly. -/

/-- Cup-product graduation α-power at H^k cohomology class:
    `k + 1`.  Posit beyond the bilinear cup arity; first-principles
    derivation remains the open frontier. -/
def cupGraduationAlphaPower (k : Nat) : Nat := k + 1

theorem cupGraduation_at_H1 : cupGraduationAlphaPower 1 = 2 := rfl
theorem cupGraduation_at_H2 : cupGraduationAlphaPower 2 = 3 := rfl

/-! ## §5 — Phase 6 master -/

/-- ★★★★★★★★ **SelfPairingTrace master**.  STRICT ∅-AXIOM.

    Promotes one of the two refined cup-ladder rules to first-
    principles content:

      · **L²-pairing trace rule**: `||c||² = (Σ_i c_i)²` is the
        bilinear self-tensor trace, proved as a Nat identity over
        all `c : Fin 3 → Bool` by case-analysis on 2³ = 8
        inhabitants.  At ω the trace evaluates to NS² = 9 directly
        from `omega_face_vec`.

      · **Cup-product graduation rule**: `H^k → α^(k+1)` remains a
        structural posit beyond the bilinear cup arity (which
        gives `k + l`, not `k + 1`).  First-principles derivation
        is the open frontier.

    Status of the refined cup-ladder formula
    `Δ_H^k(c) = ||c||² · α^(k+1) / d^(k+1)`:

      | Component | Status |
      |-----------|--------|
      | `||c||² = (L¹-norm)²` | PROVED here (Nat identity) |
      | `α^(k+1)` graduation  | POSIT (cup graduation rule) |
      | denominator `d^(k+1)` | POSIT (5-layer base structure) |

    Half of the structural derivation is now first-principles
    content; the other half remains open pending cup-product
    algebra extension. -/
theorem self_pairing_trace_master :
    -- L²-pairing trace rule: PROVED universally
    (∀ c : Fin 3 → Bool, bilinearSelfTrace c = faceCochainL1Sq c)
    -- ω specialisation: bilinear self-trace = NS²
    ∧ bilinearSelfTrace omega_face_vec = 9
    ∧ bilinearSelfTrace omega_face_vec = 3 * 3
    -- Cup-graduation rule: definition only (posit)
    ∧ cupGraduationAlphaPower 1 = 2
    ∧ cupGraduationAlphaPower 2 = 3 := by
  refine ⟨bilinear_self_trace_eq_L1_sq, ?_, ?_, rfl, rfl⟩ <;> decide

end E213.Lib.Math.Cohomology.Bipartite.SelfPairingTrace
