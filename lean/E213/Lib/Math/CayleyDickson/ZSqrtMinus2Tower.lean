import E213.Lib.Math.CayleyDickson.ZSqrt
import E213.Theory.Internal.Int213

/-!
ZSqrt[-2] = ℤ[√-2] = `ZSqrt 2` (D=2 since ZSqrt D = ℤ[√-D]).
norm = a² + 2b².  Units: (±1, 0) only — 2 units.
-/

namespace E213.Lib.Math.CayleyDickson.ZSqrtMinus2

open E213.Lib.Math.CayleyDickson.ZSqrt
open E213.Lib.Math.CayleyDickson.ZSqrt.ZSqrt

abbrev Z2 := ZSqrt 2  -- ℤ[√-2]

namespace _root_.E213.Lib.Math.CayleyDickson.ZSqrt.ZSqrt
  variable {D : Int}
  instance : Add (ZSqrt D) := ⟨fun u v => ⟨u.re + v.re, u.im + v.im⟩⟩
  instance : Neg (ZSqrt D) := ⟨fun u => ⟨-u.re, -u.im⟩⟩
  instance : Sub (ZSqrt D) := ⟨fun u v => u + (-v)⟩
end _root_.E213.Lib.Math.CayleyDickson.ZSqrt.ZSqrt

-- L3
structure L3T where
  re : Z2
  im : Z2
  deriving DecidableEq, Repr

namespace L3T

instance : Zero L3T := ⟨⟨0, 0⟩⟩

def mul (u v : L3T) : L3T :=
  ⟨u.re * v.re - (ZSqrt.conj v.im) * u.im,
    v.im * u.re + u.im * (ZSqrt.conj v.re)⟩
instance : Mul L3T := ⟨mul⟩

def conj (u : L3T) : L3T := ⟨ZSqrt.conj u.re, -u.im⟩

def normSq (u : L3T) : Int :=
  ZSqrt.normSq u.re + ZSqrt.normSq u.im

end L3T

end E213.Lib.Math.CayleyDickson.ZSqrtMinus2

namespace E213.Lib.Math.CayleyDickson.ZSqrtMinus2

namespace _root_.E213.Lib.Math.CayleyDickson.ZSqrtMinus2.L3T
  instance : Add L3T := ⟨fun u v => ⟨u.re + v.re, u.im + v.im⟩⟩
  instance : Neg L3T := ⟨fun u => ⟨-u.re, -u.im⟩⟩
  instance : Sub L3T := ⟨fun u v => u + (-v)⟩
end _root_.E213.Lib.Math.CayleyDickson.ZSqrtMinus2.L3T

-- L4
structure L4T where
  re : L3T
  im : L3T
  deriving DecidableEq, Repr

namespace L4T

instance : Zero L4T := ⟨⟨0, 0⟩⟩

def mul (u v : L4T) : L4T :=
  ⟨u.re * v.re - (L3T.conj v.im) * u.im,
    v.im * u.re + u.im * (L3T.conj v.re)⟩
instance : Mul L4T := ⟨mul⟩

def normSq (u : L4T) : Int :=
  L3T.normSq u.re + L3T.normSq u.im

end L4T

end E213.Lib.Math.CayleyDickson.ZSqrtMinus2

namespace E213.Lib.Math.CayleyDickson.ZSqrtMinus2

namespace L4T
  instance : Add L4T := ⟨fun u v => ⟨u.re + v.re, u.im + v.im⟩⟩
  instance : Neg L4T := ⟨fun u => ⟨-u.re, -u.im⟩⟩
  instance : Sub L4T := ⟨fun u v => u + (-v)⟩

  def conj (u : L4T) : L4T := ⟨L3T.conj u.re, -u.im⟩
end L4T

structure L5T where
  re : L4T
  im : L4T
  deriving DecidableEq, Repr

namespace L5T

instance : Zero L5T := ⟨⟨0, 0⟩⟩

def mul (u v : L5T) : L5T :=
  ⟨u.re * v.re - (L4T.conj v.im) * u.im,
    v.im * u.re + u.im * (L4T.conj v.re)⟩
instance : Mul L5T := ⟨mul⟩

def normSq (u : L5T) : Int :=
  L4T.normSq u.re + L4T.normSq u.im

end L5T

end E213.Lib.Math.CayleyDickson.ZSqrtMinus2
namespace E213.Lib.Math.CayleyDickson.ZSqrtMinus2

namespace L5T
  instance : Add L5T := ⟨fun u v => ⟨u.re + v.re, u.im + v.im⟩⟩
  instance : Neg L5T := ⟨fun u => ⟨-u.re, -u.im⟩⟩
  instance : Sub L5T := ⟨fun u v => u + (-v)⟩

  def conj (u : L5T) : L5T := ⟨L4T.conj u.re, -u.im⟩
end L5T

-- L6 (shifted "sedenion" position; 32 units expected, past Moufang)
structure L6T where
  re : L5T
  im : L5T
  deriving DecidableEq, Repr

namespace L6T

instance : Zero L6T := ⟨⟨0, 0⟩⟩

def mul (u v : L6T) : L6T :=
  ⟨u.re * v.re - (L5T.conj v.im) * u.im,
    v.im * u.re + u.im * (L5T.conj v.re)⟩
instance : Mul L6T := ⟨mul⟩

def normSq (u : L6T) : Int :=
  L5T.normSq u.re + L5T.normSq u.im

instance : Add L6T := ⟨fun u v => ⟨u.re + v.re, u.im + v.im⟩⟩
instance : Neg L6T := ⟨fun u => ⟨-u.re, -u.im⟩⟩
instance : Sub L6T := ⟨fun u v => u + (-v)⟩

def conj (u : L6T) : L6T := ⟨L5T.conj u.re, -u.im⟩

end L6T

end E213.Lib.Math.CayleyDickson.ZSqrtMinus2
