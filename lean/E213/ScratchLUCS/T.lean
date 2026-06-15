import E213.Meta.Int213.Core
import E213.Meta.Int213.Order
import E213.Meta.Int213.PolyIntMTactic
namespace E213.ScratchLUCS.T
open E213.Meta.Int213 (mul_sub int_eq_zero_of_mul_left mul_add mul_left_comm mul_comm mul_assoc)
open E213.Meta.Int213.Order (eq_of_sub_eq_zero sub_self_zero)

theorem mulCancelL {x a b : Int} (hx : x ≠ 0) (h : x * a = x * b) : a = b := by
  apply eq_of_sub_eq_zero
  apply int_eq_zero_of_mul_left hx
  rw [mul_sub, h, sub_self_zero]

-- cross_V_kernel attempt
theorem cross_V_kernel (P Q u0 u1 v0 v1 : Int)
    (hA : 2 * u1 = P * u0 + v0) (hB : 2 * v1 = (P * P - 4 * Q) * u0 + P * v0) :
    2 * (P * v1 - Q * v0) = (P * P - 4 * Q) * u1 + P * v1 := by
  -- multiply by 2 (cancel later). Build doubled equation manually.
  have key : 2 * (2 * (P * v1 - Q * v0)) = 2 * ((P * P - 4 * Q) * u1 + P * v1) := by
    -- rewrite each side into a form containing (2 * v1)
    have lhs : 2 * (2 * (P * v1 - Q * v0)) = P * (2 * v1) + P * (2 * v1) - 4 * (Q * v0) := by
      ring_intZ
    have rhs : 2 * ((P * P - 4 * Q) * u1 + P * v1) = 2 * ((P * P - 4 * Q) * u1) + P * (2 * v1) := by
      ring_intZ
    rw [lhs, rhs, hB]
    have hv0 : v0 = 2 * u1 - P * u0 := by rw [hA]; ring_intZ
    rw [hv0]; ring_intZ
  exact mulCancelL (show (2:Int) ≠ 0 by decide) key
#print axioms cross_V_kernel
end E213.ScratchLUCS.T
