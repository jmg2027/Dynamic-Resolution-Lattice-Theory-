import E213.Meta.Int213.Core
import E213.Meta.Int213.PolyIntMTactic

/-!
# Cross-domain identities — geometry / number theory *as* ℤ ring identities

A family of famous cross-domain facts that, compiled to the proof-ISA, are each a
**pure `ℤ` ring identity** (an EQUIV / identity-certificate: two readings of the
same algebraic object coincide), discharged by `ring_intZ` (∅-axiom).  Each is a
"hard" result in its home domain whose content collapses to an algebraic identity.

(`ring_intZ` reifies `+ * - neg`, not `^`, so powers are written as explicit
products.)
-/

namespace E213.Lib.Math.Algebra.CrossDomainIdentities

open E213.Meta.Int213

/-- **Heron's formula** (geometry ↔ algebra): `16·Area²` of a triangle with
    sides `a,b,c` is determined by the sides alone, two ways —
    `(a+b+c)(−a+b+c)(a−b+c)(a+b−c) = 2a²b² + 2b²c² + 2c²a² − a⁴ − b⁴ − c⁴`. -/
theorem heron (a b c : Int) :
    (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c)
    = 2 * (a * a) * (b * b) + 2 * (b * b) * (c * c) + 2 * (c * c) * (a * a)
      - (a * a) * (a * a) - (b * b) * (b * b) - (c * c) * (c * c) := by
  ring_intZ

/-- **Euler's four-square identity** (number theory ↔ quaternion norm):
    the product of two sums of four squares is a sum of four squares — `|z|²|w|² =
    |z·w|²` for quaternions.  The engine of Lagrange's four-square theorem. -/
theorem euler_four_square (a1 a2 a3 a4 b1 b2 b3 b4 : Int) :
    (a1 * a1 + a2 * a2 + a3 * a3 + a4 * a4)
      * (b1 * b1 + b2 * b2 + b3 * b3 + b4 * b4)
    = (a1 * b1 - a2 * b2 - a3 * b3 - a4 * b4)
        * (a1 * b1 - a2 * b2 - a3 * b3 - a4 * b4)
      + (a1 * b2 + a2 * b1 + a3 * b4 - a4 * b3)
        * (a1 * b2 + a2 * b1 + a3 * b4 - a4 * b3)
      + (a1 * b3 - a2 * b4 + a3 * b1 + a4 * b2)
        * (a1 * b3 - a2 * b4 + a3 * b1 + a4 * b2)
      + (a1 * b4 + a2 * b3 - a3 * b2 + a4 * b1)
        * (a1 * b4 + a2 * b3 - a3 * b2 + a4 * b1) := by
  ring_intZ

/-- **Sophie Germain's identity** (algebra → number-theoretic
    factorization): `a⁴ + 4b⁴ = (a² + 2b² − 2ab)(a² + 2b² + 2ab)` — shows
    `a⁴ + 4b⁴` is composite for `b ≥ 1, a > b` (an Aurifeuillian factorization). -/
theorem sophie_germain (a b : Int) :
    a * a * a * a + 4 * (b * b * b * b)
    = (a * a + 2 * (b * b) - 2 * (a * b)) * (a * a + 2 * (b * b) + 2 * (a * b)) := by
  ring_intZ

end E213.Lib.Math.Algebra.CrossDomainIdentities
