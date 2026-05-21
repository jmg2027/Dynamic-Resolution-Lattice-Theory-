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

/-- Recursive Raw inhabitant count: `|S_n| = 2 + C(|S_{n-1}|, 2)`. -/
def rawCount : Nat → Nat
  | 0 => 2
  | n + 1 => 2 + choose2 (rawCount n)

/-- ★ Recurrence step (definitional).  Kept as a lemma since `rfl`-form
    is the cleanest external witness for the recurrence. -/
theorem rawCount_succ (n : Nat) :
    rawCount (n + 1) = 2 + choose2 (rawCount n) := rfl

/-- ★★★ **Recurrence capstone**: clean closed form for Raw.

    Bundles concrete `choose2` values (n = 2, 3, 5, 12, 68), all six
    `rawCount` values (depth 0..5), the depth-2/3 list-length matches,
    and the contrast with the earlier naive guess `a_{n+1} = a_n +
    C(a_n, 2)` (5 vs 6 at n = 2). -/
theorem rawCount_recurrence_witness :
    -- choose2 concrete table
    choose2 2 = 1 ∧ choose2 3 = 3 ∧ choose2 5 = 10
    ∧ choose2 12 = 66 ∧ choose2 68 = 2278
    -- rawCount table (depth 0..5)
    ∧ rawCount 0 = 2 ∧ rawCount 1 = 3 ∧ rawCount 2 = 5
    ∧ rawCount 3 = 12 ∧ rawCount 4 = 68 ∧ rawCount 5 = 2280
    -- list-length matches at depth 2, 3
    ∧ rawCount 2 = depthLe2List.length
    ∧ rawCount 3 = depthLe3List.length
    -- naive-guess contrast: correct 5 vs naive 6 at n = 2
    ∧ (2 + choose2 3 = 5 ∧ 3 + choose2 3 = 6) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  <;> first | rfl | decide

end E213.Lib.Math.UniverseChain.RawRecurrence
