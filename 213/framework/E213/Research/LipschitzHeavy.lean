import E213.Research.CDDouble
import E213.Tactic.HurwitzRing

/-!
# Research: Lipschitz "heavy" identities via `hurwitz_ring`

Identities too large for `quad_norm` alone, closed by the
new `hurwitz_ring` tactic which descends through
`Lipschitz.ext` and `ZI.ext` before invoking the polynomial
AC-normalisation + `omega`.
-/

namespace E213.Research.Lipschitz

open E213.Tactic

/-- **Universal associativity** of Lipschitz multiplication.
    `(u·v)·w = u·(v·w)` — a 12-variable Int polynomial
    identity.  Closed by `hurwitz_ring`. -/
theorem mul_assoc (u v w : Lipschitz) :
    (u * v) * w = u * (v * w) := by hurwitz_ring

end E213.Research.Lipschitz

namespace E213.Research.Lipschitz

open E213.Tactic E213.Research.ZI

/-- **Hurwitz norm-multiplicativity** at Lipschitz level:
    `|u·v|² = |u|² · |v|²`.  8-variable Int polynomial
    identity with ~100 monomials per side.  Closed by
    `hurwitz_ring`. -/
theorem normSq_mul (u v : Lipschitz) :
    normSq (u * v) = normSq u * normSq v := by
  show (u * v).re.normSq + (u * v).im.normSq
     = (u.re.normSq + u.im.normSq) * (v.re.normSq + v.im.normSq)
  unfold ZI.normSq
  hurwitz_ring

end E213.Research.Lipschitz
