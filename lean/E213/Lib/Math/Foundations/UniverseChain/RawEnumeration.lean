import E213.Lib.Math.Foundations.UniverseChain.RawRecurrence
import E213.Meta.Tactic.List213

/-!
# Raw enumeration: general theorem |S_n| = rawCount n (∅-axiom)

General recurrence proof: actual canonical-Tree enumeration length
matches `rawCount n` for ALL n.

Avoids Lean-core `List.length_append` and `List.length_map` (which
leak `propext`); uses the shared `E213.Tactic.List213` replacements
`length_append_rev` and `length_map`.
-/

namespace E213.Lib.Math.Foundations.UniverseChain.RawEnumeration

open E213.Term.Internal (Tree)
open E213.Lib.Math.Foundations.UniverseChain.RawRecurrence (choose2)
open E213.Tactic.List213 (length_append_rev length_map)

/-- Local alias for the reversed-order length-of-append from
    `E213.Tactic.List213`.  Retained for readability of downstream
    proofs that already cite `myLengthAppend`. -/
theorem myLengthAppend (L1 L2 : List α) :
    (L1 ++ L2).length = L2.length + L1.length :=
  length_append_rev L1 L2

/-- Local alias for `length_map`. -/
theorem myLengthMap (L : List α) (f : α → β) :
    (L.map f).length = L.length :=
  length_map L f

/-- `choose2 (n+1) = n + choose2 n` (bridge for clean recurrence). -/
theorem choose2_succ (n : Nat) : choose2 (n + 1) = n + choose2 n := by
  match n with
  | 0 => rfl
  | k + 1 =>
    show choose2 (k + 1) + (k + 1) = (k + 1) + choose2 (k + 1)
    exact Nat.add_comm _ _

/-- For each (x, y) pair where x is earlier than y, generate
    `Tree.slash x y`. -/
def newSlashes : List Tree → List Tree
  | [] => []
  | x :: rest => rest.map (Tree.slash x) ++ newSlashes rest

/-- ★ `newSlashes` length = `choose2` of input length. -/
theorem newSlashes_length : ∀ L : List Tree,
    (newSlashes L).length = choose2 L.length
  | [] => rfl
  | x :: rest => by
    show (rest.map (Tree.slash x) ++ newSlashes rest).length
       = choose2 (rest.length + 1)
    rw [myLengthAppend, myLengthMap, newSlashes_length, choose2_succ]
    exact Nat.add_comm _ _

/-- Recursive enumeration of canonical Trees at depth ≤ n. -/
def enumTreeDepth : Nat → List Tree
  | 0 => [Tree.a, Tree.b]
  | n + 1 => [Tree.a, Tree.b] ++ newSlashes (enumTreeDepth n)

/-- ★★★ **Enumeration capstone** — general recurrence + low-n checks.

    Bundles:
      · ∀ n, (enumTreeDepth n).length = rawCount n  (general)
      · concrete witnesses at n = 0..3  (depth-0..3 counts 2, 3, 5, 12). -/
theorem enumeration_capstone :
    (∀ n, (enumTreeDepth n).length
        = E213.Lib.Math.Foundations.UniverseChain.RawRecurrence.rawCount n)
    ∧ (enumTreeDepth 0).length = 2
    ∧ (enumTreeDepth 1).length = 3
    ∧ (enumTreeDepth 2).length = 5
    ∧ (enumTreeDepth 3).length = 12 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n
    induction n with
    | zero => rfl
    | succ k ih =>
      show ([Tree.a, Tree.b] ++ newSlashes (enumTreeDepth k)).length
         = 2 + choose2 (E213.Lib.Math.Foundations.UniverseChain.RawRecurrence.rawCount k)
      rw [myLengthAppend, newSlashes_length, ih]
      exact Nat.add_comm _ _
  all_goals decide

end E213.Lib.Math.Foundations.UniverseChain.RawEnumeration
