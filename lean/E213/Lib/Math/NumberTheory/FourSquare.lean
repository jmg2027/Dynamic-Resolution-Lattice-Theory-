import E213.Lib.Math.NumberTheory.FourSquareSeed
import E213.Lib.Math.NumberTheory.ModArith.CenteredDivision
import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.OrderMul

/-!
# FourSquare — Lagrange's four-square theorem via Euler descent (Pillar II)

The descent route to `∀ n, n = a²+b²+c²+d²`, staying entirely over `ℤ` with ring identities and
`centered_div_int` — sidestepping the non-commutative Hurwitz-quaternion gcd.

  * ★★★ `four_sq_id` — **Euler's four-square identity** (multiplicativity, a ring identity).
  * `isSum4` / `isSum4_mul` — "is a sum of four squares" is closed under multiplication.

(The descent step `m·p = Σ4², 1 < m < p ⟹ ∃ r < m, r·p = Σ4²` and the assembly to all `n`
build on these — see `research-notes/frontiers/four_square_marathon.md`.)

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.FourSquare

/-- ★★★ **Euler's four-square identity.**  The product of two sums of four squares is a sum of
    four squares — the bilinear combination is the quaternion-norm multiplicativity, here a bare
    `ℤ` polynomial identity. -/
theorem four_sq_id (a1 a2 a3 a4 b1 b2 b3 b4 : Int) :
    (a1 * a1 + a2 * a2 + a3 * a3 + a4 * a4) * (b1 * b1 + b2 * b2 + b3 * b3 + b4 * b4)
    = (a1 * b1 + a2 * b2 + a3 * b3 + a4 * b4) * (a1 * b1 + a2 * b2 + a3 * b3 + a4 * b4)
    + (a1 * b2 - a2 * b1 + a3 * b4 - a4 * b3) * (a1 * b2 - a2 * b1 + a3 * b4 - a4 * b3)
    + (a1 * b3 - a2 * b4 - a3 * b1 + a4 * b2) * (a1 * b3 - a2 * b4 - a3 * b1 + a4 * b2)
    + (a1 * b4 + a2 * b3 - a3 * b2 - a4 * b1) * (a1 * b4 + a2 * b3 - a3 * b2 - a4 * b1) := by
  ring_intZ

/-- `n` is a sum of four integer squares. -/
def isSum4 (n : Int) : Prop := ∃ a b c d : Int, n = a * a + b * b + c * c + d * d

/-- **Sum-of-four-squares is multiplicative** (Euler): `isSum4 m`, `isSum4 n` ⟹ `isSum4 (m·n)`. -/
theorem isSum4_mul {m n : Int} (hm : isSum4 m) (hn : isSum4 n) : isSum4 (m * n) := by
  obtain ⟨a1, a2, a3, a4, hm⟩ := hm
  obtain ⟨b1, b2, b3, b4, hn⟩ := hn
  refine ⟨a1 * b1 + a2 * b2 + a3 * b3 + a4 * b4, a1 * b2 - a2 * b1 + a3 * b4 - a4 * b3,
    a1 * b3 - a2 * b4 - a3 * b1 + a4 * b2, a1 * b4 + a2 * b3 - a3 * b2 - a4 * b1, ?_⟩
  rw [hm, hn]; exact four_sq_id a1 a2 a3 a4 b1 b2 b3 b4

end E213.Lib.Math.NumberTheory.FourSquare
