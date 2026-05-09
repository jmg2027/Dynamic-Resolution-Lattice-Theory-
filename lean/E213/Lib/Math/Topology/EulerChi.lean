import E213.Lib.Physics.Simplex.Counts

/-!
# Topology — Euler characteristic (atomic simplex counting)

For a simplicial complex `K`, the Euler characteristic
`χ(K) = V − E + F − ...` is the alternating sum of face counts.

In 213, the canonical simplices Δ⁴ (= 4-simplex on 5 vertices) and
K_5 (= complete graph on 5 vertices) both yield `χ = 1`, computed
atomically from `binom 5 k`.

  χ(Δ⁴) = C(5,1) − C(5,2) + C(5,3) − C(5,4) + C(5,5)
        = 5 − 10 + 10 − 5 + 1
        = 1

This matches the topological fact that Δ⁴ is contractible
(homotopy-equivalent to a point, χ = 1).

Atomic content: alternating-sum is *just signed Nat addition*
since all faces have non-negative count and the sum is small;
implemented via `Int` arithmetic to keep negative intermediates
straight.
-/

namespace E213.Lib.Math.Topology.EulerChi

open E213.Lib.Physics.Simplex.Counts (binom)

/-- Euler characteristic of Δ⁴ as an `Int` (alternating sum). -/
def chi_delta_4 : Int :=
  (binom 5 1 : Int) - (binom 5 2 : Int) + (binom 5 3 : Int)
    - (binom 5 4 : Int) + (binom 5 5 : Int)

/-- ★ **`χ(Δ⁴) = 1`** ★ — contractibility of the 4-simplex,
    decided by atomic Int arithmetic. -/
theorem chi_delta_4_eq_one : chi_delta_4 = 1 := by decide

/-- Reduced Euler characteristic of Δ⁴ (= χ − 1) is 0. -/
def chi_reduced_delta_4 : Int := chi_delta_4 - 1

theorem chi_reduced_eq_zero : chi_reduced_delta_4 = 0 := by decide

/-- Sub-simplex face counts of Δ⁴: 5 vertices, 10 edges,
    10 triangles, 5 tetrahedra, 1 top.  Sum = 31 = 2⁵ − 1. -/
theorem face_count_total :
    binom 5 1 + binom 5 2 + binom 5 3 + binom 5 4 + binom 5 5 = 31 :=
  by decide

/-- Including the empty face (binom 5 0 = 1): total = 32 = 2⁵. -/
theorem face_count_with_empty :
    binom 5 0 + binom 5 1 + binom 5 2 + binom 5 3 + binom 5 4 + binom 5 5
    = 32 := by decide

/-- Euler char of the boundary ∂Δ⁴ = S³ (3-sphere): 5 vertices,
    10 edges, 10 triangles, 5 tetrahedra (no top).
    χ(S³) = 5 − 10 + 10 − 5 = 0. -/
def chi_S3_boundary : Int :=
  (binom 5 1 : Int) - (binom 5 2 : Int) + (binom 5 3 : Int)
    - (binom 5 4 : Int)

/-- χ(S³) = 0 (odd-dim sphere). -/
theorem chi_S3_eq_zero : chi_S3_boundary = 0 := by decide

/-- Euler char of K_{3,2}^{(c=2)}: 5 vertices, 12 edges (cross-only,
    multiplicity 2 on each of 6 ST edges), 0 higher faces (graph).
    χ = 5 − 12 = −7. -/
def chi_K_32_c2 : Int := 5 - 12

theorem chi_K_32_c2_eq : chi_K_32_c2 = -7 := by decide

end E213.Lib.Math.Topology.EulerChi
