import E213.Meta.Int213.Core

/-!
# Eisenstein integers `ℤ[ω]`, ω² + ω + 1 = 0

Third E2 witness (cross-term `-ab` Eisenstein norm).
- Multiplication: `(a + bω)(c + dω) = (ac - bd) + (ad + bc - bd)ω`
- Conjugation swaps ω ↔ ω² = -1 - ω:
  `conj(a + bω) = (a - b) + (-b)ω`
- Norm: `a² - ab + b²` (multiplicative).

Bases for the Lens: `Omega = ω`, `Omega2 = ω² = -1 - ω`.
The `derive_conjugation_codomain` elab finds `conj_Omega` and
`conj_Omega2` by name-suffix convention.
-/

namespace E213.Lib.Math.CayleyDickson.Integer.ZOmega


structure ZOmega where
  re : Int
  im : Int
  deriving DecidableEq, Repr

namespace ZOmega

instance : Zero ZOmega := ⟨⟨0, 0⟩⟩

def Omega  : ZOmega := ⟨0, 1⟩
def Omega2 : ZOmega := ⟨-1, -1⟩

def conj (u : ZOmega) : ZOmega := ⟨u.re - u.im, -u.im⟩

def mul (u v : ZOmega) : ZOmega :=
  ⟨u.re * v.re - u.im * v.im,
   u.re * v.im + u.im * v.re - u.im * v.im⟩

instance : Mul ZOmega := ⟨ZOmega.mul⟩

def normSq (u : ZOmega) : Int :=
  u.re * u.re - u.re * u.im + u.im * u.im

@[simp] theorem re_zero : (0 : ZOmega).re = 0 := rfl
@[simp] theorem im_zero : (0 : ZOmega).im = 0 := rfl

theorem ext {u v : ZOmega} (hr : u.re = v.re) (hi : u.im = v.im) :
    u = v := by cases u; cases v; congr

theorem conj_conj (u : ZOmega) : u.conj.conj = u := by
  apply ext
  · show (u.re - u.im) - (-u.im) = u.re
    -- (a - b) - (-b) = (a - b) + b = a (via sub_add_cancel_int)
    have h1 : (u.re - u.im) - (-u.im) = (u.re - u.im) + u.im := by
      show (u.re - u.im) + (-(-u.im)) = (u.re - u.im) + u.im
      rw [Int.neg_neg]
    rw [h1]
    exact E213.Theory.Internal.Int213.sub_add_cancel_int u.re u.im
  · show -(-u.im) = u.im; exact Int.neg_neg _

theorem conj_ne_id : ∃ x : ZOmega, conj x ≠ x := by
  refine ⟨Omega, ?_⟩
  intro hEq
  have h_re : (conj Omega).re = (Omega : ZOmega).re := by rw [hEq]
  have h_neg_one : (-1 : Int) = 0 := h_re
  exact absurd h_neg_one (by decide)

theorem conj_Omega : conj Omega = Omega2 := rfl

theorem conj_Omega2 : conj Omega2 = Omega := by
  apply ext
  · show -1 - -1 = (0 : Int)
    rw [Int.sub_eq_add_neg, Int.neg_neg]
    rfl
  · show -(-1) = (1 : Int); exact Int.neg_neg _

end ZOmega

end E213.Lib.Math.CayleyDickson.Integer.ZOmega
