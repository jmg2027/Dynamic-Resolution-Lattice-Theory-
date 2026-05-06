import E213.Math.Cohomology.Hodge.Delta
import E213.Math.Cohomology.Hodge.Involution
import E213.Math.Cohomology.Hodge.InvolutionCapstone
import E213.Math.Cohomology.Hodge.Prop
import E213.Math.Cohomology.Hodge.Prop50
import E213.Math.Cohomology.Hodge.Prop52
import E213.Math.Cohomology.Hodge.Prop53
import E213.Math.Cohomology.Hodge.Prop54
import E213.Math.Cohomology.Hodge.Star

/-! Spec-as-code entry point for `E213.Math.Cohomology.Hodge`.

  Hodge structure on the 213-native cochain complex — the
  Δ-Laplacian + ⋆-involution machinery.

  ## Δ-Laplacian + ⋆ machinery

    * `Star`               — Hodge ⋆ at cochain level
    * `Involution`,
      `InvolutionCapstone` — ⋆⋆ = id involution + capstone
    * `Delta`              — codifferential δ* = ⋆δ⋆

  ## Prop-level capstones

    * `Prop`     — top-level Hodge proposition wrapper
    * `Prop50`,
      `Prop52`,
      `Prop53`,
      `Prop54`   — the Hodge series at increasing complexity
                   (Universal-cochain lift theorems)
-/
