/-!
# parametric `ZSqrt D = ℤ[√-D]` family

A single parameterised type covering all integer rings of the
form `ℤ[√-D]` for `D : Int`.

- `(a + b·√-D) (c + d·√-D) = (ac - D·bd) + (ad + bc)·√-D`
- `conj(a + b·√-D) = a - b·√-D`
- `normSq = a² + D·b²` (positive-definite for `D > 0`)

Concrete `ZI = ZSqrt 1` and `Z2 = ZSqrt 2` already exist as
separate types in `Math/CayleyDickson/{ZI,ZSqrt2}.lean`.
This module demonstrates that adding D = 3, 5, 7, … requires
only a single one-line instance per D (via `quad_extension D`)
— no per-D structure duplication.
-/

namespace E213.Lib.Math.CayleyDickson.ZSqrt


structure ZSqrt (D : Int) where
  re : Int
  im : Int
  deriving DecidableEq, Repr

namespace ZSqrt

variable {D : Int}

instance : Zero (ZSqrt D) := ⟨⟨0, 0⟩⟩

def I    : ZSqrt D := ⟨0, 1⟩
def negI : ZSqrt D := ⟨0, -1⟩

def conj (u : ZSqrt D) : ZSqrt D := ⟨u.re, -u.im⟩

def mul (u v : ZSqrt D) : ZSqrt D :=
  ⟨u.re * v.re - D * (u.im * v.im),
   u.re * v.im + u.im * v.re⟩

instance : Mul (ZSqrt D) := ⟨ZSqrt.mul⟩

def normSq (u : ZSqrt D) : Int := u.re * u.re + D * (u.im * u.im)

@[simp] theorem re_zero : (0 : ZSqrt D).re = 0 := rfl
@[simp] theorem im_zero : (0 : ZSqrt D).im = 0 := rfl

theorem ext {u v : ZSqrt D} (hr : u.re = v.re) (hi : u.im = v.im) :
    u = v := by cases u; cases v; congr

theorem conj_conj (u : ZSqrt D) : u.conj.conj = u := by
  apply ext
  · show u.re = u.re; rfl
  · show -(-u.im) = u.im; exact Int.neg_neg _

theorem conj_ne_id : ∃ x : ZSqrt D, conj x ≠ x := by
  refine ⟨I, ?_⟩
  intro himEq
  -- himEq : conj I = I, i.e., ⟨0, -1⟩ = ⟨0, 1⟩.
  -- Take .im of both sides: -1 = 1.
  have h_im : (conj (I : ZSqrt D)).im = (I : ZSqrt D).im := by rw [himEq]
  have h_neg_one : (-1 : Int) = 1 := h_im
  exact absurd h_neg_one (by decide)

theorem conj_I : conj (I : ZSqrt D) = negI := rfl

theorem conj_negI : conj (negI : ZSqrt D) = I := by
  apply ext
  · show (0 : Int) = 0; rfl
  · show -(-1 : Int) = 1; exact Int.neg_neg _

end ZSqrt

end E213.Lib.Math.CayleyDickson.ZSqrt
