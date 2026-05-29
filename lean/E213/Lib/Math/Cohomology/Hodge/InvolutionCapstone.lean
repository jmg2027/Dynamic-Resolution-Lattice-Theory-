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

/-- **Hodge ⋆⋆ = id on Δ⁴ (all five strata)** — re-exports the
    all-strata bundle from `InvolutionLifts`. -/
theorem hodge_involution_5strata_capstone :=
  E213.Lib.Math.Cohomology.Hodge.InvolutionLifts.hodge_involution_5strata_capstone

end E213.Lib.Math.Cohomology.Hodge.InvolutionCapstone
