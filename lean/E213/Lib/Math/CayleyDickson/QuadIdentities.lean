import E213.Meta.Int213.Core

/-!
# `quad_norm` identities — ∅-axiom polynomial identities

Generic Int polynomial identities for the four CayleyDickson rings'
`normSq_mul` proofs.  Each identity is closed by `simp only` with the
PURE Int213 ring set + a `cancel_two_pairs` finishing helper that
handles the cross-term cancellation.

PURE `simp only` set:
  Int.sub_eq_add_neg, Int213.{neg_mul, mul_neg, add_mul, mul_add,
    mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm,
    add_left_comm, zero_add}, Int.{neg_neg, add_zero}.
-/

namespace E213.Lib.Math.CayleyDickson.QuadIdentities

open E213.Theory.Internal.Int213

/-- ∅-axiom helper: `(z + z) + (-z + -z) = 0`. -/
private theorem zz_neg_zz_zero (z : Int) : (z + z) + (-z + -z) = 0 := by
  rw [← add_assoc (z + z) (-z) (-z), add_assoc z z (-z),
      add_neg_cancel z, Int.add_zero z]
  exact add_neg_cancel z

/-- ∅-axiom helper: cancellation pattern emerging from `simp only`
    AC-normalisation of 4-variable Diophantus identity. -/
theorem cancel_two_pairs (A B C D z : Int) :
    A + (B + (z + (z + (C + (D + (-z + -z)))))) = A + (B + (C + D)) := by
  rw [← add_assoc z z (C + (D + (-z + -z)))]
  rw [← add_assoc C D (-z + -z)]
  rw [add_left_comm (z + z) (C + D) (-z + -z)]
  rw [zz_neg_zz_zero z, Int.add_zero]

/-- ★ ∅-axiom **Diophantus identity** for ZI:
    `(ac - bd)² + (ad + bc)² = (a²+b²)(c²+d²)`. -/
theorem int_quad_diophantus (a b c d : Int) :
    (a*c - b*d)*(a*c - b*d) + (a*d + b*c)*(a*d + b*c)
  = (a*a + b*b) * (c*c + d*d) := by
  simp only [Int.sub_eq_add_neg, neg_mul, mul_neg, Int.neg_neg,
             add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm,
             add_assoc, add_comm, add_left_comm, Int.add_zero, zero_add]
  rw [cancel_two_pairs]

/-- ★ ∅-axiom **D-twisted Diophantus identity** for ZSqrt[D]:
    `(ac - D·bd)² + D·(ad + bc)² = (a² + D·b²)(c² + D·d²)`. -/
theorem int_quad_diophantus_sqrt (D a b c d : Int) :
    (a*c - D*(b*d))*(a*c - D*(b*d)) + D*((a*d + b*c)*(a*d + b*c))
  = (a*a + D*(b*b)) * (c*c + D*(d*d)) := by
  simp only [Int.sub_eq_add_neg, neg_mul, mul_neg, Int.neg_neg,
             add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm,
             add_assoc, add_comm, add_left_comm, Int.add_zero, zero_add]
  rw [cancel_two_pairs]

/-- ★ ∅-axiom **Diophantus identity** for ZSqrt2 (D=2):
    `(ac - 2·bd)² + 2·(ad + bc)² = (a² + 2·b²)(c² + 2·d²)`. -/
theorem int_quad_diophantus_sqrt2 (a b c d : Int) :
    (a*c - 2*(b*d))*(a*c - 2*(b*d)) + 2*((a*d + b*c)*(a*d + b*c))
  = (a*a + 2*(b*b)) * (c*c + 2*(d*d)) := by
  simp only [Int.sub_eq_add_neg, neg_mul, mul_neg, Int.neg_neg,
             add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm,
             add_assoc, add_comm, add_left_comm, Int.add_zero, zero_add]
  rw [cancel_two_pairs]

/-- ∅-axiom helper: `A + X + (Y + Z) = A + Y + (Z + X)`.
    Closes the simp residue for ZI mul_assoc identities. -/
private theorem add_4_reorder (A X Y Z : Int) :
    A + X + (Y + Z) = A + Y + (Z + X) := by
  rw [add_assoc A X (Y+Z), ← add_assoc X Y Z, add_comm X Y,
      add_assoc Y X Z, add_comm X Z, ← add_assoc A Y (Z+X)]

/-- ★ ∅-axiom **ZI mul_assoc real component** identity. -/
theorem int_zi_mul_assoc_re (a b c d e f : Int) :
    (a*c - b*d)*e - (a*d + b*c)*f
  = a*(c*e - d*f) - b*(c*f + d*e) := by
  simp only [Int.sub_eq_add_neg, neg_mul, mul_neg, Int.neg_neg,
             neg_add, add_mul, mul_add, mul_assoc]
  rw [add_4_reorder]

/-- ★ ∅-axiom **ZI mul_assoc imag component** identity. -/
theorem int_zi_mul_assoc_im (a b c d e f : Int) :
    (a*c - b*d)*f + (a*d + b*c)*e
  = a*(c*f + d*e) + b*(c*e - d*f) := by
  simp only [Int.sub_eq_add_neg, neg_mul, mul_neg, Int.neg_neg,
             neg_add, add_mul, mul_add, mul_assoc]
  rw [add_4_reorder]

end E213.Lib.Math.CayleyDickson.QuadIdentities
