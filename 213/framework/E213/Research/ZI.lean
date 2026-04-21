/-!
# Research: Gaussian integers `ℤ[i]`

Part of the r5-critique research track. Defines `ZI = ℤ[i]`,
its arithmetic, and complex conjugation. This is the codomain
used in `ZILens.lean` to test whether R1–R4 alone force `ℂ`.

Pure Lean 4 core; no Mathlib, no `ring`.
-/

namespace E213.Research

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
  apply ext <;> simp [conj]

theorem conj_ne_id : conj ≠ id := by
  intro h
  have hI : conj I = id I := congrFun h I
  have himEq : (⟨0, -1⟩ : ZI) = ⟨0, 1⟩ := hI
  have : (-1 : Int) = 1 := (ZI.mk.injEq ..).mp himEq |>.2
  exact absurd this (by decide)

end ZI

end E213.Research
