import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.AddMod213

/-!
# Sum-of-squares obstructions (∅-axiom)

The elementary quadratic-residue obstructions behind the sum-of-squares theorems,
stated cleanly for arbitrary `Nat` (the corpus's `GaussianTwoSquare` results are
prime-restricted, over `Int`):

  * **Fermat (mod 4)**: a sum of two squares is never `≡ 3 (mod 4)`
    (`not_sum_two_squares_mod4`) — every square is `≡ 0` or `1 (mod 4)`.
  * **Legendre (mod 8)**: a sum of three squares is never `≡ 7 (mod 8)`
    (`three_squares_ne_7_mod8`, `not_three_squares_of_mod8_seven`) — every
    square is `≡ 0, 1`, or `4 (mod 8)`, and `{0,1,4}+{0,1,4}+{0,1,4}` never
    hits `7 (mod 8)`.  This is the obstruction half of Legendre's three-square
    theorem.

Proof route: reduce `a*a % m` to `(a%m)*(a%m) % m` (`mul_mod_pure`), case-split the
finite residue table by `match` on `a % m` (with a `Nat.mod_lt` bound killing the
overflow branch), then `decide` the finite residue-sum table.

All ∅-axiom: `decide`, `rw`, `match`, `rcases`, `Nat.mod_lt`, and the PURE
mod-arithmetic twins (`mul_mod_pure`, `add_mod_gen`, `mod_mod`).
-/

namespace E213.Lib.Math.NumberTheory.ModArith.SumOfSquaresObstruction

open E213.Meta.Nat.MulMod213 (mul_mod_pure)
open E213.Meta.Nat.AddMod213 (add_mod_gen mod_mod)

/-- A perfect square is `≡ 0, 1`, or `4 (mod 8)`. -/
theorem sq_mod8 (a : Nat) : a * a % 8 = 0 ∨ a * a % 8 = 1 ∨ a * a % 8 = 4 := by
  have hbound : a % 8 < 8 := Nat.mod_lt a (by decide)
  have hreduce : a * a % 8 = (a % 8) * (a % 8) % 8 := mul_mod_pure a a 8
  -- Case on the residue `r = a % 8 ∈ {0,...,7}`.
  match h : a % 8 with
  | 0 => exact Or.inl (by rw [hreduce, h])
  | 1 => exact Or.inr (Or.inl (by rw [hreduce, h]))
  | 2 => exact Or.inr (Or.inr (by rw [hreduce, h]))
  | 3 => exact Or.inr (Or.inl (by rw [hreduce, h]))
  | 4 => exact Or.inl (by rw [hreduce, h])
  | 5 => exact Or.inr (Or.inl (by rw [hreduce, h]))
  | 6 => exact Or.inr (Or.inr (by rw [hreduce, h]))
  | 7 => exact Or.inr (Or.inl (by rw [hreduce, h]))
  | k + 8 =>
      exfalso
      rw [h] at hbound
      exact Nat.lt_irrefl 8 (Nat.lt_of_le_of_lt (Nat.le_add_left 8 k) hbound)

/-- A sum of three squares reduced `(mod 8)` equals the reduced sum of the
    three residues, each of which lies in `{0,1,4}`.  Auxiliary form that
    pins `(a*a + b*b + c*c) % 8` to a sum of residue-representatives. -/
theorem three_sq_residue (a b c : Nat) :
    (a * a + b * b + c * c) % 8
      = (a * a % 8 + b * b % 8 + c * c % 8) % 8 := by
  -- (x + y + z) % 8 = ((x+y) + z) % 8, peel `z` then the inner `(x+y)`.
  have h1 : (a * a + b * b + c * c) % 8
      = ((a * a + b * b) % 8 + c * c % 8) % 8 :=
    add_mod_gen (a * a + b * b) (c * c) 8
  have h2 : (a * a + b * b) % 8 = (a * a % 8 + b * b % 8) % 8 :=
    add_mod_gen (a * a) (b * b) 8
  rw [h1, h2]
  -- Now: ((a*a%8 + b*b%8) % 8 + c*c%8) % 8 = (a*a%8 + b*b%8 + c*c%8) % 8.
  have h3 : (a * a % 8 + b * b % 8 + c * c % 8) % 8
      = ((a * a % 8 + b * b % 8) % 8 + (c * c % 8) % 8) % 8 :=
    add_mod_gen (a * a % 8 + b * b % 8) (c * c % 8) 8
  rw [h3, mod_mod (c * c) 8]

/-- ★★★★ **Legendre's three-square obstruction.**
    A sum of three squares is never `≡ 7 (mod 8)`. -/
theorem three_squares_ne_7_mod8 (a b c : Nat) :
    (a * a + b * b + c * c) % 8 ≠ 7 := by
  rw [three_sq_residue a b c]
  rcases sq_mod8 a with ha | ha | ha <;>
    rcases sq_mod8 b with hb | hb | hb <;>
      rcases sq_mod8 c with hc | hc | hc <;>
        · rw [ha, hb, hc]; decide

/-- ★★★★ **No representation form.**  If `n ≡ 7 (mod 8)` then `n` is not a
    sum of three squares. -/
theorem not_three_squares_of_mod8_seven (n : Nat) (hn : n % 8 = 7) :
    ¬ ∃ a b c : Nat, a * a + b * b + c * c = n := by
  rintro ⟨a, b, c, h⟩
  have : (a * a + b * b + c * c) % 8 = 7 := by rw [h]; exact hn
  exact three_squares_ne_7_mod8 a b c this

/-- A perfect square is `≡ 0` or `1 (mod 4)`. -/
theorem sq_mod4 (a : Nat) : a * a % 4 = 0 ∨ a * a % 4 = 1 := by
  have hbound : a % 4 < 4 := Nat.mod_lt a (by decide)
  have hreduce : a * a % 4 = (a % 4) * (a % 4) % 4 := mul_mod_pure a a 4
  match h : a % 4 with
  | 0 => exact Or.inl (by rw [hreduce, h])
  | 1 => exact Or.inr (by rw [hreduce, h])
  | 2 => exact Or.inl (by rw [hreduce, h])
  | 3 => exact Or.inr (by rw [hreduce, h])
  | k + 4 =>
      exfalso
      rw [h] at hbound
      exact Nat.lt_irrefl 4 (Nat.lt_of_le_of_lt (Nat.le_add_left 4 k) hbound)

/-- ★★★ **Fermat's two-square obstruction.**  A sum of two squares is never
    `≡ 3 (mod 4)` — the elementary half of Fermat's two-square theorem. -/
theorem not_sum_two_squares_mod4 (a b : Nat) : (a * a + b * b) % 4 ≠ 3 := by
  have hres : (a * a + b * b) % 4 = (a * a % 4 + b * b % 4) % 4 :=
    add_mod_gen (a * a) (b * b) 4
  rw [hres]
  rcases sq_mod4 a with ha | ha <;> rcases sq_mod4 b with hb | hb <;>
    · rw [ha, hb]; decide

end E213.Lib.Math.NumberTheory.ModArith.SumOfSquaresObstruction
