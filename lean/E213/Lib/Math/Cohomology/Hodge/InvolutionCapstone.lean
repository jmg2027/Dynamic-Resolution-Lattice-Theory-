import E213.Lib.Math.Cohomology.Hodge.InvolutionLifts

/-!
# Hodge involution ⋆⋆ = id — Δ⁴ all-strata capstone

Re-exports the all-strata capstone
`hodge_involution_5strata_capstone` (defined in
`InvolutionLifts.lean`) under the historical name
`hodge_involution_5strata_capstone` in this namespace, for
backward compatibility with downstream consumers that name
`InvolutionCapstone.hodge_involution_5strata_capstone`.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Cohomology.Hodge.InvolutionCapstone

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Hodge.Star (hodgeStar)
open E213.Lib.Physics.Simplex.Counts (binom)

/-- **Hodge ⋆⋆ = id on Δ⁴ (all five strata)** — re-exports the
    all-strata bundle from `InvolutionLifts`. -/
theorem hodge_involution_5strata_capstone :
    (∀ σ : Cochain 5 0, ∀ i : Fin (binom 5 0),
      hodgeStar 5 5 0 (hodgeStar 5 0 5 σ) i = σ i)
    ∧ (∀ σ : Cochain 5 1, ∀ i : Fin (binom 5 1),
        hodgeStar 5 4 1 (hodgeStar 5 1 4 σ) i = σ i)
    ∧ (∀ σ : Cochain 5 2, ∀ i : Fin (binom 5 2),
        hodgeStar 5 3 2 (hodgeStar 5 2 3 σ) i = σ i)
    ∧ (∀ σ : Cochain 5 3, ∀ i : Fin (binom 5 3),
        hodgeStar 5 2 3 (hodgeStar 5 3 2 σ) i = σ i)
    ∧ (∀ σ : Cochain 5 4, ∀ i : Fin (binom 5 4),
        hodgeStar 5 1 4 (hodgeStar 5 4 1 σ) i = σ i) :=
  E213.Lib.Math.Cohomology.Hodge.InvolutionLifts.hodge_involution_5strata_capstone

end E213.Lib.Math.Cohomology.Hodge.InvolutionCapstone
