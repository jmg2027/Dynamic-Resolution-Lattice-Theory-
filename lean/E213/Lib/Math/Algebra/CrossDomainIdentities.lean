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

/-- **The polynomial identity underlying Heron's formula** (a pure `ℤ` ring
    identity, `ring_intZ`).  NOT Heron's formula itself: there is no `√`, no area,
    no triangle here — only the algebraic fact
    `(a+b+c)(−a+b+c)(a−b+c)(a+b−c) = 2a²b²+2b²c²+2c²a²−a⁴−b⁴−c⁴`, which *equals*
    `16·Area²` once one adds the (separate) geometric content that the LHS is
    `16` times the squared area of a triangle with sides `a,b,c`. -/
theorem heron (a b c : Int) :
    (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c)
    = 2 * (a * a) * (b * b) + 2 * (b * b) * (c * c) + 2 * (c * c) * (a * a)
      - (a * a) * (a * a) - (b * b) * (b * b) - (c * c) * (c * c) := by
  ring_intZ

/-- **Euler's four-square identity** — a pure `ℤ` ring identity (`ring_intZ`):
    a product of two sums of four squares is a sum of four squares (the norm of a
    product of quaternions).  This is *only* the bilinear identity; it is the
    algebraic *engine* of Lagrange's four-square theorem, but that theorem (every
    `n` is a sum of four squares, which needs descent / a pigeonhole) is NOT proved
    here. -/
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

/-- **Sophie Germain's factorization identity** — a pure `ℤ` ring identity
    (`ring_intZ`): `a⁴ + 4b⁴ = (a²+2b²−2ab)(a²+2b²+2ab)`.  This is *only* the
    identity; the number-theoretic corollary (`a⁴+4b⁴` is composite for suitable
    `a,b`, i.e. both factors `> 1`) is NOT proved here — it needs an order argument
    on the factors. -/
theorem sophie_germain (a b : Int) :
    a * a * a * a + 4 * (b * b * b * b)
    = (a * a + 2 * (b * b) - 2 * (a * b)) * (a * a + 2 * (b * b) + 2 * (a * b)) := by
  ring_intZ

end E213.Lib.Math.Algebra.CrossDomainIdentities
