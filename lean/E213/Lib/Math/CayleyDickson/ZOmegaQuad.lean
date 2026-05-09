import E213.Lib.Math.CayleyDickson.ZOmegaDouble

/-!
# `ZOmegaQuad` — CD-doubling of `ZOmegaDouble` (one more layer)

Mechanical extension.  Observe: does associativity hold or break?
-/

namespace E213.Lib.Math.CayleyDickson.ZOmegaQuad

open E213.Lib.Math.CayleyDickson.ZOmega
open E213.Lib.Math.CayleyDickson.ZOmegaDouble
open E213.Lib.Math.CayleyDickson.ZOmegaDouble.ZOmegaDouble

-- Need Add/Neg/Sub on ZOmegaDouble
namespace _root_.E213.Lib.Math.CayleyDickson.ZOmegaDouble.ZOmegaDouble

instance : Add ZOmegaDouble :=
  ⟨fun u v => ⟨u.re + v.re, u.im + v.im⟩⟩
instance : Neg ZOmegaDouble :=
  ⟨fun u => ⟨-u.re, -u.im⟩⟩
instance : Sub ZOmegaDouble := ⟨fun u v => u + (-v)⟩

end _root_.E213.Lib.Math.CayleyDickson.ZOmegaDouble.ZOmegaDouble

structure ZOmegaQuad where
  re : ZOmegaDouble
  im : ZOmegaDouble
  deriving DecidableEq, Repr

namespace ZOmegaQuad

instance : Zero ZOmegaQuad := ⟨⟨0, 0⟩⟩

theorem ext {u v : ZOmegaQuad} (hr : u.re = v.re) (hi : u.im = v.im) :
    u = v := by cases u; cases v; congr

/-- CD multiplication.  Same formula, applied to the inner ZOmegaDouble. -/
def mul (u v : ZOmegaQuad) : ZOmegaQuad :=
  ⟨u.re * v.re - (ZOmegaDouble.conj v.im) * u.im,
    v.im * u.re + u.im * (ZOmegaDouble.conj v.re)⟩

instance : Mul ZOmegaQuad := ⟨mul⟩

def conj (u : ZOmegaQuad) : ZOmegaQuad :=
  ⟨ZOmegaDouble.conj u.re, -u.im⟩

def normSq (u : ZOmegaQuad) : Int :=
  ZOmegaDouble.normSq u.re + ZOmegaDouble.normSq u.im

end ZOmegaQuad

end E213.Lib.Math.CayleyDickson.ZOmegaQuad
