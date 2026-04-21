import E213.Research.Cayley
import E213.Tactic.HurwitzRing

namespace E213.Research.Cayley

open E213.Tactic

/-- **Left alternativity** (universal): `(a·a)·b = a·(a·b)`. -/
theorem alt_left (a b : Cayley) : (a * a) * b = a * (a * b) := by
  hurwitz_ring

end E213.Research.Cayley

namespace E213.Research.Cayley

open E213.Tactic

/-- **Right alternativity** (universal): `a·(b·b) = (a·b)·b`. -/
theorem alt_right (a b : Cayley) : a * (b * b) = (a * b) * b := by
  hurwitz_ring

/-- **Flexibility** (universal): `(a·b)·a = a·(b·a)`. -/
theorem flexible (a b : Cayley) : (a * b) * a = a * (b * a) := by
  hurwitz_ring

end E213.Research.Cayley

namespace E213.Research.Cayley

open E213.Tactic E213.Research.Lipschitz E213.Research.ZI

/-- Cayley (octonion) norm-squared:
    `re.normSq + im.normSq` at Lipschitz level. -/
def normSq (u : Cayley) : Int :=
  Lipschitz.normSq u.re + Lipschitz.normSq u.im

/-
**Cayley/octonion Hurwitz identity** `|u·v|² = |u|² · |v|²`
is a 32-variable Int-polynomial identity (16 coords per
Cayley term, both sides).  Descent through `Cayley` /
`Lipschitz` / `ZI` gives a monolithic Int identity that
exceeds `omega`'s practical atom count.  The classical
proof uses the Moufang identity and 8 cross-identities
that classically compose; a compositional tactic plus
intermediate lemmas is the right path.  Deferred.
-/

end E213.Research.Cayley
