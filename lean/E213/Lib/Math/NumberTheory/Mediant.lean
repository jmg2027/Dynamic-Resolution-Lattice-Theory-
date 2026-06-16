import E213.Meta.Nat.PolyNatMTactic
import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.Core

/-!
# Mediant inequality + Stern–Brocot / Farey adjacency (∅-axiom)

The fraction `a/b` is compared with `c/d` via the cross-product (`a*d` vs `b*c`,
division-free).  Three genuinely-absent facts about the **mediant**
`(a/b) ⊕ (c/d) = (a+c)/(b+d)`:

  * **Mediant inequality** (`mediant_strictly_between`): `a/b < c/d ⟹
    a/b < (a+c)/(b+d) < c/d` — the mediant lies strictly between its parents.
  * **Stern–Brocot / Farey adjacency** (`mediant_adjacent_both`): if `b*c − a*d = 1`
    (adjacent fractions) then the mediant is adjacent to both parents
    (`b*(a+c) − a*(b+d) = 1`, `(b+d)*c − (a+c)*d = 1`) — the SL₂(ℤ) unimodularity
    that the continuant cross-determinant `(−1)ⁿ` is the iterated form of.
  * **Mediant in lowest terms** (`mediant_lowest_terms`): adjacency forces the
    mediant `(a+c)/(b+d)` to be reduced (any common divisor of `a+c`, `b+d` ∣ 1).

The `dvd_subZ`/`dvd_mul_leftZ` Int helpers are kept local (the same two trivial
lemmas appear in `Real213/ContinuedFraction/ConvergentCoprime`; importing the
Real213 CF tree here would be the wrong dependency direction — Int213 has no
shared `∣`-helper module yet, a known consolidation target).  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.Mediant

/-! ## Mediant inequality (over Nat, cross-multiplied) -/

/-- ★ **Mediant inequality, left half**: if `a*d < c*b` then `a*(b+d) < (a+c)*b`
    (`a/b < (a+c)/(b+d)`). -/
theorem mediant_lt_left (a b c d : Nat) (h : a * d < c * b) :
    a * (b + d) < (a + c) * b := by
  have e1 : a * (b + d) = a * b + a * d := by ring_nat
  have e2 : (a + c) * b = a * b + c * b := by ring_nat
  have step : a * b + a * d < a * b + c * b := Nat.add_lt_add_left h (a * b)
  calc a * (b + d) = a * b + a * d := e1
    _ < a * b + c * b := step
    _ = (a + c) * b := e2.symm

/-- ★ **Mediant inequality, right half**: if `a*d < c*b` then `(a+c)*d < c*(b+d)`
    (`(a+c)/(b+d) < c/d`). -/
theorem mediant_lt_right (a b c d : Nat) (h : a * d < c * b) :
    (a + c) * d < c * (b + d) := by
  have e1 : (a + c) * d = a * d + c * d := by ring_nat
  have e2 : c * (b + d) = c * b + c * d := by ring_nat
  have step : a * d + c * d < c * b + c * d := Nat.add_lt_add_right h (c * d)
  calc (a + c) * d = a * d + c * d := e1
    _ < c * b + c * d := step
    _ = c * (b + d) := e2.symm

/-- ★ **Mediant strictly between** (conjunction form). -/
theorem mediant_strictly_between (a b c d : Nat) (h : a * d < c * b) :
    a * (b + d) < (a + c) * b ∧ (a + c) * d < c * (b + d) :=
  ⟨mediant_lt_left a b c d h, mediant_lt_right a b c d h⟩

/-! ## Stern–Brocot / Farey adjacency preservation (over Int) -/

/-- ★ **Adjacency preserved, left**: from `b*c − a*d = 1`,
    `b*(a+c) − a*(b+d) = 1`. -/
theorem mediant_adjacent_left (a b c d : Int) (h : b * c - a * d = 1) :
    b * (a + c) - a * (b + d) = 1 := by
  have e : b * (a + c) - a * (b + d) = b * c - a * d := by ring_intZ
  calc b * (a + c) - a * (b + d) = b * c - a * d := e
    _ = 1 := h

/-- ★ **Adjacency preserved, right**: from `b*c − a*d = 1`,
    `(b+d)*c − (a+c)*d = 1`. -/
theorem mediant_adjacent_right (a b c d : Int) (h : b * c - a * d = 1) :
    (b + d) * c - (a + c) * d = 1 := by
  have e : (b + d) * c - (a + c) * d = b * c - a * d := by ring_intZ
  calc (b + d) * c - (a + c) * d = b * c - a * d := e
    _ = 1 := h

/-- ★ **Unimodularity preserved** (conjunction form). -/
theorem mediant_adjacent_both (a b c d : Int) (h : b * c - a * d = 1) :
    b * (a + c) - a * (b + d) = 1 ∧ (b + d) * c - (a + c) * d = 1 :=
  ⟨mediant_adjacent_left a b c d h, mediant_adjacent_right a b c d h⟩

/-! ## Mediant in lowest terms when parents are adjacent (over Int) -/

/-- `g ∣ x → g ∣ y → g ∣ (x − y)` for `Int` (PURE, explicit witness). -/
theorem dvd_subZ {g x y : Int} (hx : g ∣ x) (hy : g ∣ y) : g ∣ (x - y) := by
  obtain ⟨w₁, hw₁⟩ := hx
  obtain ⟨w₂, hw₂⟩ := hy
  refine ⟨w₁ - w₂, ?_⟩
  rw [hw₁, hw₂]
  show g * w₁ - g * w₂ = g * (w₁ - w₂)
  ring_intZ

/-- `g ∣ x → g ∣ (b * x)` for `Int` (PURE, witness `b * w`). -/
theorem dvd_mul_leftZ {g x : Int} (b : Int) (hx : g ∣ x) : g ∣ (b * x) := by
  obtain ⟨w, hw⟩ := hx
  refine ⟨b * w, ?_⟩
  rw [hw]
  show b * (g * w) = g * (b * w)
  ring_intZ

/-- ★ **Mediant is in lowest terms when parents are adjacent**.
    From `b*c − a*d = 1`, any common divisor `g` of the mediant numerator `a+c`
    and denominator `b+d` divides `1` — so `(a+c)/(b+d)` is automatically reduced.
    `g ∣ (a+c) ⟹ g ∣ b*(a+c)`, `g ∣ (b+d) ⟹ g ∣ a*(b+d)`, so
    `g ∣ (b*(a+c) − a*(b+d)) = b*c − a*d = 1`. -/
theorem mediant_lowest_terms (a b c d g : Int)
    (h : b * c - a * d = 1)
    (hn : g ∣ (a + c)) (hden : g ∣ (b + d)) : g ∣ (1 : Int) := by
  have hbn : g ∣ b * (a + c) := dvd_mul_leftZ b hn
  have had : g ∣ a * (b + d) := dvd_mul_leftZ a hden
  have hdiff : g ∣ (b * (a + c) - a * (b + d)) := dvd_subZ hbn had
  have heq : b * (a + c) - a * (b + d) = 1 := mediant_adjacent_left a b c d h
  rw [heq] at hdiff
  exact hdiff


/-- ★ **Mediant cross-difference (Stern–Brocot determinant)**: `b(a+c) − a(b+d) = bc − ad`
    — the mediant's cross-determinant with its left parent equals the parents'
    cross-determinant `bc − ad` (the `det = ±1` adjacency invariant of the Stern–Brocot tree). -/
theorem mediant_cross_diff (a b c d : Int) :
    b * (a + c) - a * (b + d) = b * c - a * d := by ring_intZ

/-- ★ The mediant denominator strictly exceeds each parent denominator (`b, d > 0`). -/
theorem mediant_den_gt {b d : Nat} (hb : 0 < b) (hd : 0 < d) :
    b < b + d ∧ d < b + d :=
  ⟨Nat.lt_add_of_pos_right hd, Nat.lt_add_of_pos_left hb⟩
end E213.Lib.Math.NumberTheory.Mediant
