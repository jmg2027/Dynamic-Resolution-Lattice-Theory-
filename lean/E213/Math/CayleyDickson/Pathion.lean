import E213.Math.CayleyDickson.Trigintaduonion

/-!
# Cayley–Dickson layer 5 — integer pathions

`Pathion = Trigintaduonion × Trigintaduonion`, 64-dim.
-/

namespace E213.Math.CayleyDickson.Pathion


open E213.Math.CayleyDickson.ZI
open E213.Math.CayleyDickson.ZI.ZI
open E213.Math.CayleyDickson.Trigintaduonion
open E213.Math.CayleyDickson.Trigintaduonion.Trigintaduonion
structure Pathion where
  re : Trigintaduonion
  im : Trigintaduonion
  deriving DecidableEq

namespace Pathion

instance : Zero Pathion := ⟨⟨0, 0⟩⟩

theorem ext {u v : Pathion} (hr : u.re = v.re) (hi : u.im = v.im) :
    u = v := by cases u; cases v; congr

def mul (u v : Pathion) : Pathion :=
  ⟨u.re * v.re - v.im.conj * u.im,
   v.im * u.re + u.im * v.re.conj⟩

instance : Mul Pathion := ⟨mul⟩
instance : Add Pathion := ⟨fun u v => ⟨u.re + v.re, u.im + v.im⟩⟩
instance : Neg Pathion := ⟨fun u => ⟨-u.re, -u.im⟩⟩
instance : Sub Pathion := ⟨fun u v => u + (-v)⟩

def conj (u : Pathion) : Pathion := ⟨u.re.conj, -u.im⟩

-- Projection lemmas
theorem mul_re (u v : Pathion) :
    (u * v).re = u.re * v.re - v.im.conj * u.im := rfl
theorem mul_im (u v : Pathion) :
    (u * v).im = v.im * u.re + u.im * v.re.conj := rfl
theorem conj_re (u : Pathion) : (conj u).re = u.re.conj := rfl
theorem conj_im (u : Pathion) : (conj u).im = -u.im := rfl
theorem add_re (u v : Pathion) : (u + v).re = u.re + v.re := rfl
theorem add_im (u v : Pathion) : (u + v).im = u.im + v.im := rfl
theorem neg_re (u : Pathion) : (-u).re = -u.re := rfl
theorem neg_im (u : Pathion) : (-u).im = -u.im := rfl
theorem sub_re (u v : Pathion) : (u - v).re = u.re - v.re := rfl
theorem sub_im (u v : Pathion) : (u - v).im = u.im - v.im := rfl
theorem zero_re : (0 : Pathion).re = 0 := rfl
theorem zero_im : (0 : Pathion).im = 0 := rfl

end Pathion

end E213.Math.CayleyDickson.Pathion
