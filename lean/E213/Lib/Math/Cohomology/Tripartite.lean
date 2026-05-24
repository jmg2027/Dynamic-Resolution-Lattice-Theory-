import E213.Lib.Math.Cohomology.Tripartite.V213
import E213.Lib.Math.Cohomology.Tripartite.V213Betti
import E213.Lib.Math.Cohomology.Tripartite.V32V213CohomologyBridge

/-! Spec-as-code entry point for `E213.Lib.Math.Cohomology.Tripartite`.

  Tripartite-graph cohomology — companion to `Bipartite/`.  The
  central object is `K_{NT, det, NS} = K_{2, 1, 3}`, the complete
  tripartite graph with rainbow triangles filled as 2-cells.

  ## Files

    * `V213`                     — cochain definitions (V/E/△),
                                   coboundaries δ⁰ / δ¹
    * `V213Betti`                — Betti capstone:
                                   (b₀, b₁, b₂) = (1, 0, 0).
                                   δ¹ surjective via direct-edge
                                   pivots → cohomologically trivial.
    * `V32V213CohomologyBridge`  — cross-frame comparison with
                                   `Bipartite/V32Betti`: atomic-level
                                   duality holds (|E| = |△| = 6),
                                   cohomology-level duality fails
                                   (b₁ = 8 vs b₁ = 0).

  Cross-link: `Mobius213/Px/TripartiteK213.lean` for the atomic-count
  layer; this chapter adds the cohomology layer (δ¹ surjectivity,
  b₁ = 0, b₂ = 0) and the bridge to `Bipartite/V32Betti`.

  All declarations PURE (∅-axiom).
-/
