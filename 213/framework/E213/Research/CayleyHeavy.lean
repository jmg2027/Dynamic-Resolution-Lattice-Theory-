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

set_option maxHeartbeats 4000000 in
/-- **Cayley (octonion) Hurwitz identity**: `|u·v|² = |u|² · |v|²`.
    Classical theorem that octonions form a composition
    algebra.  32-var polynomial identity; closed by
    `hurwitz_ring` after extended heartbeat budget. -/
theorem normSq_mul (u v : Cayley) :
    normSq (u * v) = normSq u * normSq v := by
  show Lipschitz.normSq (u * v).re + Lipschitz.normSq (u * v).im
     = (Lipschitz.normSq u.re + Lipschitz.normSq u.im) *
       (Lipschitz.normSq v.re + Lipschitz.normSq v.im)
  unfold Lipschitz.normSq
  unfold ZI.normSq
  hurwitz_ring

end E213.Research.Cayley
