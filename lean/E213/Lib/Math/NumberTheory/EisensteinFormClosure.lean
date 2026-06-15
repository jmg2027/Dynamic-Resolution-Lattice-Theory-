import E213.Meta.Int213.PolyIntMTactic

/-!
# Eisenstein-form (`a²+ab+b²`, disc −3) multiplicative closure (∅-axiom)

The disc-−3 analog of the sum-of-two-squares closure: the **Loeschian** predicate
"is a value of `a²+ab+b²`" (the norm form of the Eisenstein integers `ℤ[ω]`,
`ω²=−ω−1`) is closed under multiplication.

  ★ **`isEisForm_mul`** : `isEisForm m → isEisForm n → isEisForm (m·n)`, witnesses
    `X = ac−bd`, `Y = ad+bc+bd` (the norm of `(a+bω)(c+dω)`).

Genuinely absent: the corpus pins the disc-−3 Brahmagupta *identity* in the
*minus* convention (`EisensteinSplitting.eisForm_composition`, `a²−ab+b²`); the
existential closure in the standard *plus* (Loeschian) convention is new.
Inlined `ring_intZ` (self-contained, convention-pinned).  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.EisensteinFormClosure

open E213.Meta.Int213.PolyIntM

/-- `n` is an Eisenstein (Loeschian) value: `n = a² + ab + b²` for some `a, b`. -/
def isEisForm (n : Int) : Prop := ∃ a b : Int, n = a * a + a * b + b * b

/-- ★ **Eisenstein-form multiplicative closure** — the `ℤ[ω]`-norm multiplicativity:
    witnesses `X = ac − bd`, `Y = ad + bc + bd`. -/
theorem isEisForm_mul {m n : Int} (hm : isEisForm m) (hn : isEisForm n) :
    isEisForm (m * n) := by
  obtain ⟨a, b, hm⟩ := hm
  obtain ⟨c, d, hn⟩ := hn
  exact ⟨a * c - b * d, a * d + b * c + b * d, by rw [hm, hn]; ring_intZ⟩

/-! ## Basics -/

theorem isEisForm_zero : isEisForm 0 := ⟨0, 0, by ring_intZ⟩
theorem isEisForm_one : isEisForm 1 := ⟨1, 0, by ring_intZ⟩
/-- `3 = 1² + 1·1 + 1²` (the ramified prime). -/
theorem isEisForm_three : isEisForm 3 := ⟨1, 1, by ring_intZ⟩

/-- Every square is a value: `k² = k² + k·0 + 0²`.  (`ring_intZ` cannot collapse the
    literal `k·0`/`0·0`; discharged by the ∅-axiom `Int.mul_zero`/`Int.add_zero` —
    `Int.zero_mul` is propext-dirty, so `Int.mul_zero (0:Int)` for `0·0`.) -/
theorem isEisForm_sq (k : Int) : isEisForm (k * k) :=
  ⟨k, 0, by rw [Int.mul_zero k, Int.mul_zero (0:Int), Int.add_zero, Int.add_zero]⟩

/-- Smoke: `7 = 1² + 1·2 + 2²` (the first split prime `≡ 1 mod 3`). -/
theorem isEisForm_seven : isEisForm 7 := ⟨1, 2, by ring_intZ⟩

/-- `21 = 3 · 7` via the closure. -/
theorem isEisForm_twentyone : isEisForm 21 := by
  have h : (21 : Int) = 3 * 7 := by ring_intZ
  rw [h]
  exact isEisForm_mul isEisForm_three isEisForm_seven

end E213.Lib.Math.NumberTheory.EisensteinFormClosure
