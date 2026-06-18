import E213.Lib.Math.Cohomology.Tripartite.V213
import E213.Lib.Math.Cohomology.Tripartite.V213Betti
import E213.Lib.Math.Cohomology.Tripartite.V213ShadowProjection

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
    * `V213ShadowProjection`     — Massey shadow projection
                                   vanishing.  Any projection into
                                   `H²(K_{2,1,3}) = 0` is zero;
                                   Massey content does not transfer.

  Cross-link: `Mobius213/Px/TripartiteK213.lean` for the atomic-count
  layer; this chapter adds the cohomology layer (δ¹ surjectivity,
  b₁ = 0, b₂ = 0).

  All declarations PURE (∅-axiom).
-/
