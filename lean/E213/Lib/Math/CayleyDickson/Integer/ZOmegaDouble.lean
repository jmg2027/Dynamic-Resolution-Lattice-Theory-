import E213.Lib.Math.CayleyDickson.Integer.ZOmega
import E213.Meta.Int213.Core

/-!
# `ZOmegaDouble` — CD-doubling of Eisenstein integers

Mechanical construction.  `decide`-checked observations only.
-/

namespace E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble

open E213.Lib.Math.CayleyDickson.Integer.ZOmega
open E213.Lib.Math.CayleyDickson.Integer.ZOmega.ZOmega

-- Add/Neg for ZOmega (componentwise on Int)
namespace _root_.E213.Lib.Math.CayleyDickson.Integer.ZOmega.ZOmega

instance : Add ZOmega := ⟨fun u v => ⟨u.re + v.re, u.im + v.im⟩⟩
instance : Neg ZOmega := ⟨fun u => ⟨-u.re, -u.im⟩⟩
instance : Sub ZOmega := ⟨fun u v => u + (-v)⟩

end _root_.E213.Lib.Math.CayleyDickson.Integer.ZOmega.ZOmega

structure ZOmegaDouble where
  re : ZOmega
  im : ZOmega
  deriving DecidableEq, Repr

namespace ZOmegaDouble

instance : Zero ZOmegaDouble := ⟨⟨0, 0⟩⟩

theorem ext {u v : ZOmegaDouble} (hr : u.re = v.re) (hi : u.im = v.im) :
    u = v := by cases u; cases v; congr

/-- CD multiplication: `(a, b)·(c, d) = (a·c - conj(d)·b, d·a + b·conj(c))`. -/
def mul (u v : ZOmegaDouble) : ZOmegaDouble :=
  ⟨u.re * v.re - (ZOmega.conj v.im) * u.im,
    v.im * u.re + u.im * (ZOmega.conj v.re)⟩

instance : Mul ZOmegaDouble := ⟨mul⟩

/-- CD conjugation. -/
def conj (u : ZOmegaDouble) : ZOmegaDouble :=
  ⟨ZOmega.conj u.re, -u.im⟩

/-- Norm = sum of inner Eisenstein norms. -/
def normSq (u : ZOmegaDouble) : Int :=
  ZOmega.normSq u.re + ZOmega.normSq u.im

-- Basis elements
def e1 : ZOmegaDouble := ⟨⟨1, 0⟩, 0⟩       -- real unit
def e2 : ZOmegaDouble := ⟨⟨0, 1⟩, 0⟩       -- ω axis
def e3 : ZOmegaDouble := ⟨0, ⟨1, 0⟩⟩       -- j-like
def e4 : ZOmegaDouble := ⟨0, ⟨0, 1⟩⟩       -- ωj-like

end ZOmegaDouble

end E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble
