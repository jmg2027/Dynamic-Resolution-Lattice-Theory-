import E213.Lib.Math.CayleyDickson.Pathion
import E213.Lib.Math.Tactic.HurwitzRing

/-!
# Pathion layer 5 heavy identities

Testing `hurwitz_ring` at CD layer 5 (64-dim, 128 Int coords).
1-variable identity = 128 Int vars.
-/

namespace E213.Lib.Math.CayleyDickson.PathionHeavy


open E213.Lib.Math.CayleyDickson.ZI
open E213.Lib.Math.CayleyDickson.ZI.ZI
open E213.Lib.Math.CayleyDickson.Pathion
open E213.Lib.Math.CayleyDickson.Pathion.Pathion
open E213.Lib.Math.CayleyDickson.Trigintaduonion
open E213.Lib.Math.CayleyDickson.Trigintaduonion.Trigintaduonion
open E213.Lib.Math.CayleyDickson.Sedenion
open E213.Lib.Math.CayleyDickson.Sedenion.Sedenion
open E213.Lib.Math.CayleyDickson.Cayley
open E213.Lib.Math.CayleyDickson.CDDouble
open E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz
open E213.Tactic

set_option maxHeartbeats 128000000 in
/-- Involutivity at CD layer 5 — 128 Int vars, 1-variable. -/
theorem conj_conj (u : Pathion) : conj (conj u) = u := by
  hurwitz_ring

end E213.Lib.Math.CayleyDickson.PathionHeavy
