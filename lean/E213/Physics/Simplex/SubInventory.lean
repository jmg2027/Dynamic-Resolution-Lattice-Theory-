import E213.Math.Cohomology.Paper1Chiral

/-!
# Sub-simplex inventory of the (3+2)-partitioned 4-simplex.

User insight (2026-04): each non-empty sub-simplex is a candidate
"geometric impedance" channel; the total contributes to 1/α_em(IR).

Total count:  Σ_{(i,j) ≠ (0,0)} chiralDim(i, j)  =  31  =  2^d − 1.
Including empty:                                 =  32  =  2^d.

Per-simplex-dimension breakdown (k+1 = i+j vertices):
  dim 0 (vertices)   : 5  = C(5, 1)   = (3) + (2)         [A + B]
  dim 1 (edges)      : 10 = C(5, 2)   = (3) + (6) + (1)   [AA + AB + BB]
  dim 2 (triangles)  : 10 = C(5, 3)   = (1) + (6) + (3)   [AAA + AAB + ABB]
  dim 3 (tetrahedra) : 5  = C(5, 4)   = (2) + (3)         [AAAB + AABB]
  dim 4 (hypercell)  : 1  = C(5, 5)   = (1)               [AAABB]
                       ─
                       31

All `rfl`-closed via chiralDim = binom(NS, i)·binom(NT, j).
-/

namespace E213.Physics.Simplex.SubInventory

open E213.Math.Cohomology.Paper1Chiral (chiralDim)

/-- 5 vertices = single-vertex sub-simplices. -/
theorem dim_0_count : chiralDim 1 0 + chiralDim 0 1 = 5 := by decide

/-- 10 edges = two-vertex sub-simplices. -/
theorem dim_1_count :
    chiralDim 2 0 + chiralDim 1 1 + chiralDim 0 2 = 10 := by decide

/-- 10 triangles = three-vertex sub-simplices. -/
theorem dim_2_count :
    chiralDim 3 0 + chiralDim 2 1 + chiralDim 1 2 = 10 := by decide

/-- 5 tetrahedra = four-vertex sub-simplices. -/
theorem dim_3_count :
    chiralDim 3 1 + chiralDim 2 2 = 5 := by decide

/-- 1 hypercell = the full 5-vertex simplex. -/
theorem dim_4_count : chiralDim 3 2 = 1 := by decide

/-- ★ Total non-empty sub-simplices = 2^d − 1 = 31. -/
theorem total_non_empty :
    chiralDim 1 0 + chiralDim 0 1
    + chiralDim 2 0 + chiralDim 1 1 + chiralDim 0 2
    + chiralDim 3 0 + chiralDim 2 1 + chiralDim 1 2
    + chiralDim 3 1 + chiralDim 2 2
    + chiralDim 3 2 = 31 := by decide

/-- 31 = 2^d − 1 with d = 5. -/
theorem thirty_one_is_two_d_minus_1 : 2 ^ 5 - 1 = 31 := by decide

end E213.Physics.Simplex.SubInventory

#print axioms E213.Physics.Simplex.SubInventory.total_non_empty
#print axioms E213.Physics.Simplex.SubInventory.thirty_one_is_two_d_minus_1
