import E213.Research.CayleyDickson.Pathion
import E213.Tactic.HurwitzRing

/-!
# Research: Pathion layer 5 heavy identities

Testing `hurwitz_ring` at CD layer 5 (64-dim, 128 Int coords).
1-variable identity = 128 Int vars.
-/

namespace E213.Research.Pathion

open E213.Tactic

set_option maxHeartbeats 128000000 in
/-- Involutivity at CD layer 5 — 128 Int vars, 1-variable. -/
theorem conj_conj (u : Pathion) : conj (conj u) = u := by
  hurwitz_ring

end E213.Research.Pathion
