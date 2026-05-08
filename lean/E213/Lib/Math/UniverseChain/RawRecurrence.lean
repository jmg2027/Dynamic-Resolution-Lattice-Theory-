import E213.Lib.Math.UniverseChain.RawDepth3

/-!
# Raw inhabitant count recurrence (∅-axiom)

Mingu's discovered recurrence (correcting the earlier
`a_{n+1} = a_n + C(a_n, 2)` guess):

  **|S_n| = 2 + C(|S_{n-1}|, 2)**, |S_0| = 2

|S_0| = 2, |S_1| = 3, |S_2| = 5, |S_3| = 12, |S_4| = 68, |S_5| = 2280

## Why

`|S_n|` = canonical Raws of depth ≤ n
   = (2 atoms) + (slashes of depth ≤ n)
   = 2 + (unordered distinct pairs of `S_{n-1}` elements)
   = 2 + C(|S_{n-1}|, 2).

Each canonical slash of depth ≤ n is a UNIQUE unordered pair
`(x, y)` of `S_{n-1}` elements.
-/

namespace E213.Lib.Math.UniverseChain.RawRecurrence

open E213.Lib.Math.UniverseChain.RawDepthCount (depthLe2List)
open E213.Lib.Math.UniverseChain.RawDepth3 (depthLe3List)

/-- Binomial C(n, 2) via structural recursion (no `/2`). -/
def choose2 : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => choose2 (n + 1) + (n + 1)

theorem choose2_2 : choose2 2 = 1 := rfl
theorem choose2_3 : choose2 3 = 3 := rfl
theorem choose2_5 : choose2 5 = 10 := by decide
theorem choose2_12 : choose2 12 = 66 := by decide
theorem choose2_68 : choose2 68 = 2278 := by decide

/-- Recursive Raw inhabitant count: `|S_n| = 2 + C(|S_{n-1}|, 2)`. -/
def rawCount : Nat → Nat
  | 0 => 2
  | n + 1 => 2 + choose2 (rawCount n)

/-- ★ Recurrence step (definitional). -/
theorem rawCount_succ (n : Nat) :
    rawCount (n + 1) = 2 + choose2 (rawCount n) := rfl

/-- ★ Concrete values. -/
theorem rawCount_0 : rawCount 0 = 2 := rfl
theorem rawCount_1 : rawCount 1 = 3 := by decide
theorem rawCount_2 : rawCount 2 = 5 := by decide
theorem rawCount_3 : rawCount 3 = 12 := by decide
theorem rawCount_4 : rawCount 4 = 68 := by decide
theorem rawCount_5 : rawCount 5 = 2280 := by decide

/-- ★ Match: rawCount 2 = depthLe2List.length. -/
theorem rawCount_2_matches : rawCount 2 = depthLe2List.length := by decide

/-- ★ Match: rawCount 3 = depthLe3List.length. -/
theorem rawCount_3_matches : rawCount 3 = depthLe3List.length := by decide

/-- ★ The recurrence DIFFERS from the earlier guess
    `a_{n+1} = a_n + C(a_n, 2)`: at n = 2,
       guess: 3 + 3 = 6, actual: 2 + C(3, 2) = 5. -/
theorem differs_from_naive_guess :
    2 + choose2 3 = 5 ∧ 3 + choose2 3 = 6 := by decide

/-- ★★★ **Recurrence capstone**: clean closed form for Raw. -/
theorem rawCount_recurrence_witness :
    rawCount 0 = 2 ∧ rawCount 1 = 3 ∧ rawCount 2 = 5
    ∧ rawCount 3 = 12 ∧ rawCount 4 = 68 ∧ rawCount 5 = 2280
    ∧ rawCount 2 = depthLe2List.length
    ∧ rawCount 3 = depthLe3List.length :=
  ⟨rfl, by decide, by decide, by decide, by decide, by decide,
   by decide, by decide⟩

end E213.Lib.Math.UniverseChain.RawRecurrence
