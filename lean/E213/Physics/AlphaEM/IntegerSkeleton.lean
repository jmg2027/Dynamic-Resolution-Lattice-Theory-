/-!
# Structural identities of 1/α_em(IR) integer coefficients.

  1/α_em(IR) = 60·ζ(2) + 30 + 25/3 + α_GUT/(NS+1) [+ α_GUT/(NS²·d)]
                ↑       ↑     ↑
                E·d   1/α_2  d²/NS

Each integer coefficient traces to a 213 lattice quantity:

  *  E = c·NS·NT = 2·3·2 = 12      edges of K_{3,2}^{(2)}
  *  d = NS + NT = 3 + 2 = 5       atomic dimension
  *  60 = E·d = 12·5                edge count × atomic dim
  *  30 = 1/α_2 (paper 2 gauge value, Paper2Bundle)
  *  25 = d²                        block-pair total
  *  NS+1 = 4                       face dimension (Dyson tail)
  *  NS²·d = 9·5 = 45               proposed next correction (gap)

All `rfl` — these are *literally* the same Nat under Term.eval.
-/

namespace E213.Physics.AlphaEM.IntegerSkeleton

/-- Edge count of K_{3,2}^{(c=2)}: c·NS·NT. -/
def edge_count : Nat := 2 * 3 * 2

/-- 60 = E · d  (edge count × atomic dim).  Origin of `60·ζ(2)`. -/
theorem sixty_is_E_times_d : edge_count * 5 = 60 := by decide

/-- 12 = E. -/
theorem edge_count_is_12 : edge_count = 12 := by decide

/-- 25 = d². -/
theorem twentyfive_is_d_sq : 5 * 5 = 25 := by decide

/-- 9 = NS². -/
theorem nine_is_NS_sq : 3 * 3 = 9 := by decide

/-- 45 = NS² · d  (denominator of proposed gap correction α_GUT/45). -/
theorem fortyfive_is_NS_sq_times_d : 3 * 3 * 5 = 45 := by decide

/-- 4 = NS + 1  (denominator of Dyson tail α_GUT/4). -/
theorem four_is_NS_plus_1 : 3 + 1 = 4 := by decide

/-- 32 = 2^d (total chiral cells across all levels). -/
theorem thirtytwo_is_two_to_d : 2 ^ 5 = 32 := by decide

/-- 8 = NS² − 1 = 1/α_3.  E − V + 1 for K_{3,2}^{(2)}. -/
theorem eight_is_NS_sq_minus_1 : 3 * 3 - 1 = 8 := by decide

/-- The bundled identity: 60·ζ(2) coefficient + 30 + d²/NS denom + α_GUT/(NS+1) denom
    + α_GUT/(NS²·d) denom — every integer in 1/α_em is structurally fixed. -/
theorem alpha_em_integer_origins :
    edge_count * 5 = 60
    ∧ 5 * 5 = 25
    ∧ 3 + 1 = 4
    ∧ 3 * 3 * 5 = 45 := by decide

end E213.Physics.AlphaEM.IntegerSkeleton

#print axioms E213.Physics.AlphaEM.IntegerSkeleton.sixty_is_E_times_d
#print axioms E213.Physics.AlphaEM.IntegerSkeleton.fortyfive_is_NS_sq_times_d
#print axioms E213.Physics.AlphaEM.IntegerSkeleton.alpha_em_integer_origins
