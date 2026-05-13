import E213.Lib.Math.CayleyDickson.Integer.ZOmegaQuad

/-!
# `ZOmegaOct` — CD doubling of `ZOmegaQuad` (one more layer)

16-dim algebra over Eisenstein base.  Mechanical observation only.
-/

namespace E213.Lib.Math.CayleyDickson.Integer.ZOmegaOct

open E213.Lib.Math.CayleyDickson.Integer.ZOmega
open E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble
open E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble.ZOmegaDouble
open E213.Lib.Math.CayleyDickson.Integer.ZOmegaQuad
open E213.Lib.Math.CayleyDickson.Integer.ZOmegaQuad.ZOmegaQuad

namespace _root_.E213.Lib.Math.CayleyDickson.Integer.ZOmegaQuad.ZOmegaQuad

instance : Add ZOmegaQuad :=
  ⟨fun u v => ⟨u.re + v.re, u.im + v.im⟩⟩
instance : Neg ZOmegaQuad :=
  ⟨fun u => ⟨-u.re, -u.im⟩⟩
instance : Sub ZOmegaQuad := ⟨fun u v => u + (-v)⟩

end _root_.E213.Lib.Math.CayleyDickson.Integer.ZOmegaQuad.ZOmegaQuad

structure ZOmegaOct where
  re : ZOmegaQuad
  im : ZOmegaQuad
  deriving DecidableEq, Repr

namespace ZOmegaOct

instance : Zero ZOmegaOct := ⟨⟨0, 0⟩⟩

theorem ext {u v : ZOmegaOct} (hr : u.re = v.re) (hi : u.im = v.im) :
    u = v := by cases u; cases v; congr

def mul (u v : ZOmegaOct) : ZOmegaOct :=
  ⟨u.re * v.re - (ZOmegaQuad.conj v.im) * u.im,
    v.im * u.re + u.im * (ZOmegaQuad.conj v.re)⟩

instance : Mul ZOmegaOct := ⟨mul⟩

def conj (u : ZOmegaOct) : ZOmegaOct :=
  ⟨ZOmegaQuad.conj u.re, -u.im⟩

def normSq (u : ZOmegaOct) : Int :=
  ZOmegaQuad.normSq u.re + ZOmegaQuad.normSq u.im

end ZOmegaOct

end E213.Lib.Math.CayleyDickson.Integer.ZOmegaOct
