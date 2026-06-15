import E213.Meta.Int213.PolyIntMTactic

/-!
# Sum-of-two-squares multiplicative closure (∅-axiom)

The Gaussian-integer norm multiplicativity `N(z)·N(w) = N(z·w)`, read as an
**existential closure**: the predicate "is a sum of two squares" is closed under
multiplication.  The engine is the Brahmagupta–Fibonacci / Diophantus identity
`(ac−bd)² + (ad+bc)² = (a²+b²)(c²+d²)`, supplied as the witness map.

Genuinely absent: the corpus has the Diophantus *identity*
(`QuadIdentities.int_quad_diophantus`) but not the `∃`-quantified closure of the
sum-of-two-squares predicate.  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.SumTwoSquares

open E213.Meta.Int213.PolyIntM

/-- `n` is a sum of two integer squares. -/
def isSumTwoSq (n : Int) : Prop := ∃ a b : Int, n = a*a + b*b

theorem isSumTwoSq_zero : isSumTwoSq 0 := ⟨0, 0, by decide⟩

theorem isSumTwoSq_one : isSumTwoSq 1 := ⟨1, 0, by decide⟩

/-- Every perfect square `a²` is a sum of two squares (`a² + 0²`). -/
theorem isSumTwoSq_sq (a : Int) : isSumTwoSq (a*a) :=
  ⟨a, 0, by rw [Int.mul_zero, Int.add_zero]⟩

/-- ★★ **Sum-of-two-squares closure.**  If `m` and `n` are each a sum of two
    squares, so is `m·n`.  Witnesses `(ac−bd, ad+bc)` via Brahmagupta. -/
theorem isSumTwoSq_mul {m n : Int}
    (hm : isSumTwoSq m) (hn : isSumTwoSq n) : isSumTwoSq (m * n) := by
  obtain ⟨a, b, hm⟩ := hm
  obtain ⟨c, d, hn⟩ := hn
  exact ⟨a*c - b*d, a*d + b*c, by rw [hm, hn]; ring_intZ⟩

/-- ★ **Sign-twin closure.**  The conjugate witness map `(ac+bd, ad−bc)` gives the
    same multiplicative closure. -/
theorem isSumTwoSq_mul' {m n : Int}
    (hm : isSumTwoSq m) (hn : isSumTwoSq n) : isSumTwoSq (m * n) := by
  obtain ⟨a, b, hm⟩ := hm
  obtain ⟨c, d, hn⟩ := hn
  exact ⟨a*c + b*d, a*d - b*c, by rw [hm, hn]; ring_intZ⟩

/-! ## Concrete smokes -/

theorem smoke_2 : isSumTwoSq 2 := ⟨1, 1, by ring_intZ⟩
theorem smoke_5 : isSumTwoSq 5 := ⟨2, 1, by ring_intZ⟩
/-- `10 = 5·2` is `3² + 1²`. -/
theorem smoke_10 : isSumTwoSq 10 := ⟨3, 1, by ring_intZ⟩
/-- `10` obtained by closure from `5` and `2`. -/
theorem smoke_10_via_closure : isSumTwoSq 10 := isSumTwoSq_mul smoke_5 smoke_2

end E213.Lib.Math.NumberTheory.SumTwoSquares
