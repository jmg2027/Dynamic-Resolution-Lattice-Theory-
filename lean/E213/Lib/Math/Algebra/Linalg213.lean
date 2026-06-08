import E213.Lib.Math.Algebra.Linalg213.Bridge
import E213.Lib.Math.Algebra.Linalg213.Capstone
import E213.Lib.Math.Algebra.Linalg213.Chiral
import E213.Lib.Math.Algebra.Linalg213.DetN
import E213.Lib.Math.Algebra.Linalg213.FibCassiniDet
import E213.Lib.Math.Algebra.Linalg213.Laplace
import E213.Lib.Math.Algebra.Linalg213.DetTranspose
import E213.Lib.Math.Algebra.Linalg213.DetMul
import E213.Lib.Math.Algebra.Linalg213.PolyDet
import E213.Lib.Math.Algebra.Linalg213.CharPolyAdj
import E213.Lib.Math.Algebra.Linalg213.CayleyHamilton
import E213.Lib.Math.Algebra.Linalg213.PhaseChiralBridge
import E213.Lib.Math.Algebra.Linalg213.Gap
import E213.Lib.Math.Algebra.Linalg213.Gram
import E213.Lib.Math.Algebra.Linalg213.Permutation
import E213.Lib.Math.Algebra.Linalg213.PermGroup
import E213.Lib.Math.Algebra.Linalg213.ProdLperm
import E213.Lib.Math.Algebra.Linalg213.ProdCongr
import E213.Lib.Math.Algebra.Linalg213.SumLinear
import E213.Lib.Math.Algebra.Linalg213.RowDependence
import E213.Lib.Math.Algebra.Linalg213.DetTriangular
import E213.Lib.Math.Algebra.Linalg213.DetScale
import E213.Lib.Math.Algebra.Linalg213.DetZeroCol
import E213.Lib.Math.Algebra.Linalg213.DetRowOps
import E213.Lib.Math.Algebra.Linalg213.PermClosure
import E213.Lib.Math.Algebra.Linalg213.PermSign
import E213.Lib.Math.Algebra.Linalg213.PermBridge
import E213.Lib.Math.Algebra.Linalg213.Rank
import E213.Lib.Math.Algebra.Linalg213.Rank5Concrete
import E213.Lib.Math.Algebra.Linalg213.Span
import E213.Lib.Math.Algebra.Linalg213.Vector

/-! Spec-as-code entry point for `E213.Lib.Math.Algebra.Linalg213`.

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
