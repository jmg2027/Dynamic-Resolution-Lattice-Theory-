/-!
# Triangle Iteration: 213's atomic generation rule (∅-axiom)

Mingu's hypothesis:
> "초항이 1이고 a_n+1 = a_n C 2 + a_n"
> (Translation: "First term is 1, and a_n+1 = a_n C 2 + a_n")

Reading `a_n C 2` as `C(a_n, 2)` = binomial coefficient
"choose 2 from a_n" = `a_n · (a_n − 1) / 2`:

  `a_{n+1} = C(a_n, 2) + a_n = a_n(a_n+1)/2 = T(a_n)`

This is the **triangle number** of `a_n`.

Starting from `a_1 = 2` (binary base):
  * `a_1 = 2` (= N_T)
  * `a_2 = T(2) = 3` (= N_S) ✓
  * `a_3 = T(3) = 6`
  * `a_4 = T(6) = 21`
  * `a_5 = T(21) = 231`

OEIS A007501.  The (3, 2) atomicity = first two terms!

213-native: the 25-level CD tower's (N_S, N_T) = (3, 2) is the
**initial pair** of this triangle-iteration sequence starting
from binary 2.
-/

namespace E213.Lib.Math.Geometry.GenerationRule.TriangleIteration

/-- Triangle number `T(n) = n(n+1)/2 = C(n+1, 2)`. -/
def T (n : Nat) : Nat := n * (n + 1) / 2

/-- ★ `T(0) = 0`. -/
theorem T_zero : T 0 = 0 := rfl

/-- ★ `T(1) = 1`. -/
theorem T_one : T 1 = 1 := rfl

/-- ★ `T(2) = 3` — the first non-trivial step: `2 → 3`. -/
theorem T_two : T 2 = 3 := rfl

/-- ★ `T(3) = 6`. -/
theorem T_three : T 3 = 6 := rfl

/-- ★ `T(6) = 21`. -/
theorem T_six : T 6 = 21 := rfl

/-- ★ `T(21) = 231`. -/
theorem T_twentyone : T 21 = 231 := rfl

/-- The triangle-iteration sequence starting from `a_0`. -/
def triIter (a₀ : Nat) : Nat → Nat
  | 0 => a₀
  | n + 1 => T (triIter a₀ n)

/-- ★ `triIter 2 0 = 2` (initial). -/
theorem triIter_2_0 : triIter 2 0 = 2 := rfl

/-- ★ `triIter 2 1 = 3` — **N_T → N_S transition**. -/
theorem triIter_2_1 : triIter 2 1 = 3 := rfl

/-- ★ `triIter 2 2 = 6`. -/
theorem triIter_2_2 : triIter 2 2 = 6 := rfl

/-- ★ `triIter 2 3 = 21`. -/
theorem triIter_2_3 : triIter 2 3 = 21 := rfl

/-- ★ `triIter 2 4 = 231`. -/
theorem triIter_2_4 : triIter 2 4 = 231 := rfl

/-- ★ **The (N_T, N_S) = (2, 3) atomicity is the first two terms
    of triangle iteration starting from binary base 2.** -/
theorem atomicity_first_two :
    triIter 2 0 = 2 ∧ triIter 2 1 = 3 :=
  ⟨rfl, rfl⟩

end E213.Lib.Math.Geometry.GenerationRule.TriangleIteration
