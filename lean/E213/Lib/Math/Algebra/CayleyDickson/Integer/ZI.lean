/-!
# Gaussian integers `ℤ[i]`

The first non-trivial witness for the `ConjugationCodomain`
typeclass (`Meta/SelfRecognising.lean`).  Defines `ZI = ℤ[i]`,
its arithmetic, and complex conjugation.

Used as a counter-example showing that `CommBinaryCodomain` +
`NonVanishingCodomain` + `ConjugationCodomain` do **not** force the
codomain to be ℂ — `ℤ[i]` already satisfies all three.  Sibling examples: `Z2 = ℤ[√-2]`,
`ZOmega = ℤ[ω]`, parametric `ZSqrt D` family.

Pure Lean 4 core; no Mathlib, no `ring`.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI

/-- Gaussian integer `re + im · i`. -/
structure ZI where
  re : Int
  im : Int
  deriving DecidableEq, Repr

namespace ZI

instance : Zero ZI := ⟨⟨0, 0⟩⟩

/-- The generator `i` (imaginary unit). -/
def I : ZI := ⟨0, 1⟩

/-- The generator `-i`. -/
def negI : ZI := ⟨0, -1⟩

/-- Complex conjugation: `re + im·i ↦ re − im·i`. -/
def conj (u : ZI) : ZI := ⟨u.re, -u.im⟩

/-- Gaussian-integer multiplication. -/
def mul (u v : ZI) : ZI :=
  ⟨u.re * v.re - u.im * v.im, u.re * v.im + u.im * v.re⟩

instance : Mul ZI := ⟨ZI.mul⟩

/-- Squared norm `N(re + im·i) = re² + im²`. -/
def normSq (u : ZI) : Int := u.re * u.re + u.im * u.im

-- ═══ Basic structural lemmas ═══

@[simp] theorem re_zero : (0 : ZI).re = 0 := rfl
@[simp] theorem im_zero : (0 : ZI).im = 0 := rfl

theorem ext {u v : ZI} (hr : u.re = v.re) (hi : u.im = v.im) : u = v := by
  cases u; cases v; congr

theorem conj_conj (u : ZI) : u.conj.conj = u := by
  apply ext
  · show u.re = u.re; rfl
  · show -(-u.im) = u.im; exact Int.neg_neg _

theorem conj_ne_id : ∃ x : ZI, conj x ≠ x := by
  refine ⟨I, ?_⟩
  intro himEq
  have h_im : (conj I).im = (I : ZI).im := by rw [himEq]
  have h_neg_one : (-1 : Int) = 1 := h_im
  exact absurd h_neg_one (by decide)

end ZI

end E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI
