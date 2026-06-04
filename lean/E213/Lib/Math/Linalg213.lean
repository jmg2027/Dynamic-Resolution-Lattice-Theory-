import E213.Lib.Math.Linalg213.Bridge
import E213.Lib.Math.Linalg213.Capstone
import E213.Lib.Math.Linalg213.Chiral
import E213.Lib.Math.Linalg213.DetN
import E213.Lib.Math.Linalg213.FibCassiniDet
import E213.Lib.Math.Linalg213.Laplace
import E213.Lib.Math.Linalg213.CayleyHamilton
import E213.Lib.Math.Linalg213.PhaseChiralBridge
import E213.Lib.Math.Linalg213.Gap
import E213.Lib.Math.Linalg213.Gram
import E213.Lib.Math.Linalg213.Permutation
import E213.Lib.Math.Linalg213.PermClosure
import E213.Lib.Math.Linalg213.Rank
import E213.Lib.Math.Linalg213.Rank5Concrete
import E213.Lib.Math.Linalg213.Span
import E213.Lib.Math.Linalg213.Vector

/-! Spec-as-code entry point for `E213.Lib.Math.Linalg213`.

  213-native linear algebra (Mathlib-free, ∅-axiom).

  ## Core types + ops

    * `Vector`         — Vector type + ops
    * `Gram`           — Gram matrix `G_ij = <v_i, v_j>`
    * `Span`           — span enumeration over Vec families
    * `Rank`           — rank computation
    * `Rank5Concrete`  — rank verification at d = 5

  ## Chiral structure

    * `Chiral`            — chiral decomposition (mode-A / mode-B
                            split forced by atomicity)
    * `PhaseChiralBridge` — phase ↔ chiral bridge

  ## Gap-fill (matrix multiplication / determinant / tensor /
  eigenvalues)

    * `Gap`               — sub-cluster umbrella; pulls in
                            `Gap.{MatrixMul, Determinant,
                            TensorProduct, Eigen, Capstone}`

  ## Capstones

    * `Capstone`          — top-level Linalg213 capstone
    * `Bridge`            — bridge to Physics K_{3,2}^{(2)}
                            cohomology (Math.Cohomology.Bipartite)
-/
