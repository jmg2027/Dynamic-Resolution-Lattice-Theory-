import E213.Lib.Math.CayleyDickson.CDDouble
import E213.Lib.Math.CayleyDickson.ZIAlgebra213
import E213.Theory.Internal.Algebra213
import E213.Theory.Internal.Int213

/-!
# `Lipschitz` as an `IntegerNormed213` instance

Hierarchical-modular CD layer 1.  Ring axioms proven by reducing
componentwise / structurally to ZI's PURE ring axioms — no Int
polynomial expansion at this layer.
-/

namespace E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz

open E213.Lib.Math.CayleyDickson.ZI
open E213.Lib.Math.CayleyDickson.ZI.ZI
open E213.Theory.Internal.Algebra213

/-- `ofInt n = ⟨ZI.ofInt n, 0⟩`. -/
def ofInt (n : Int) : Lipschitz := ⟨ZI.ZI.ofInt n, 0⟩

private theorem add_assoc' (u v w : Lipschitz) : u + v + w = u + (v + w) := by
  apply ext
  · exact Ring213.add_assoc u.re v.re w.re
  · exact Ring213.add_assoc u.im v.im w.im

private theorem add_comm' (u v : Lipschitz) : u + v = v + u := by
  apply ext
  · exact Ring213.add_comm u.re v.re
  · exact Ring213.add_comm u.im v.im

private theorem add_zero' (u : Lipschitz) : u + 0 = u := by
  apply ext
  · exact Ring213.add_zero u.re
  · exact Ring213.add_zero u.im

private theorem add_left_neg' (u : Lipschitz) : -u + u = 0 := by
  apply ext
  · exact Ring213.add_left_neg u.re
  · exact Ring213.add_left_neg u.im

end E213.Lib.Math.CayleyDickson.CDDouble.Lipschitz
