/-!
# `ℤ[√-2]` — second quadratic-extension `ConjugationCodomain` witness

Companion to `ZI = ℤ[i]`.  Same structure as `ZI` but with
`i² = -2` instead of `i² = -1`, so multiplication becomes

  `(a + b√-2)(c + d√-2) = (ac - 2bd) + (ad + bc)√-2`

and `normSq(a + b√-2) = a² + 2 b²`.

Together with `ZI`, `ZOmega`, and the parametric `ZSqrt D`
family, `ℤ[√-2]` confirms that the three-tier codomain spec
(`CommBinaryCodomain` + `NonVanishingCodomain` +
`ConjugationCodomain` — formerly "R1–R4" in the deprecated
R1–R5 judgment-game frame) does NOT pin the codomain to ℂ:
multiple non-isomorphic countable quadratic extensions all
satisfy it.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrt2


/-- Elements of `ℤ[√-2]`: pairs `re + im · √-2`. -/
structure Z2 where
  re : Int
  im : Int
  deriving DecidableEq, Repr

namespace Z2

instance : Zero Z2 := ⟨⟨0, 0⟩⟩

def I  : Z2 := ⟨0, 1⟩
def negI : Z2 := ⟨0, -1⟩

def conj (u : Z2) : Z2 := ⟨u.re, -u.im⟩

/-- Multiplication in `ℤ[√-2]`: `(a + b√-2)(c + d√-2) =
    (ac - 2bd) + (ad + bc)√-2`. -/
def mul (u v : Z2) : Z2 :=
  ⟨u.re * v.re - 2 * (u.im * v.im),
   u.re * v.im + u.im * v.re⟩

instance : Mul Z2 := ⟨Z2.mul⟩

/-- Norm: `a² + 2 b²`. -/
def normSq (u : Z2) : Int := u.re * u.re + 2 * (u.im * u.im)

@[simp] theorem re_zero : (0 : Z2).re = 0 := rfl
@[simp] theorem im_zero : (0 : Z2).im = 0 := rfl

theorem ext {u v : Z2} (hr : u.re = v.re) (hi : u.im = v.im) : u = v := by
  cases u; cases v; congr

theorem conj_conj (u : Z2) : u.conj.conj = u := by
  apply ext
  · show u.re = u.re; rfl
  · show -(-u.im) = u.im; exact Int.neg_neg _

theorem conj_ne_id : ∃ x : Z2, conj x ≠ x := by
  refine ⟨I, ?_⟩
  intro himEq
  have h_im : (conj I).im = (I : Z2).im := by rw [himEq]
  have h_neg_one : (-1 : Int) = 1 := h_im
  exact absurd h_neg_one (by decide)

end Z2

end E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrt2
