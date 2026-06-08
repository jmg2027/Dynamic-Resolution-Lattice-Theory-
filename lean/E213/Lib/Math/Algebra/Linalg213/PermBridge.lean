import E213.Lib.Math.Algebra.Linalg213.Permutation
import E213.Lib.Math.Combinatorics.Permutations

/-!
# Linalg213 — the two permutation enumerations coincide (the Leibniz index set has `n!` members)

Two `insert-everywhere` enumerations of orderings were developed independently:

  · `Combinatorics.Permutations.perms` — the generic enumeration carrying the **count**
    `perms_length : (perms l).length = fact l.length` (built for Sperner's chains / Ramsey);
  · `Linalg213.Permutation.permsOf` / `perms` — the **index set of the Leibniz determinant**
    `leibDet n M = Σ_{σ ∈ perms n} sign(σ)·Πᵢ M i (σ i)` (with soundness / completeness / nodup
    re-derived count-style in `PermClosure`).

They differ only in the propext-free `flatMap213` vs core `List.flatMap` (which compute the same
concatenation) — so they are the **same list** (`permsOf_eq`).  That bridge transports the
factorial count to the determinant's index set: ★ `leibDet_card` — the Leibniz determinant is a
sum of exactly `n!` signed diagonal products.

All ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.Linalg213.PermBridge

open E213.Lib.Math.Algebra.Linalg213.Permutation (permsOf perms iota insertEverywhere leibDet leibTerm sumZ)
open E213.Lib.Math.Combinatorics.Permutations
  renaming perms → cperms, insertEverywhere → cinsEv, flatMap213 → cflatMap,
           perms_length → cperms_length, fact → fact
open E213.Tactic.List213 (length_append)

/-! ## §1 — the two enumerations are the same list -/

/-- Core `List.flatMap` and the propext-free `flatMap213` concatenate identically. -/
theorem flatMap_eq {α β : Type _} (f : α → List β) : ∀ l : List α, l.flatMap f = cflatMap f l
  | []     => rfl
  | a :: l => by show f a ++ l.flatMap f = f a ++ cflatMap f l; rw [flatMap_eq f l]

/-- `flatMap213` pointwise congruence (no `funext`: induction on the list). -/
theorem cflatMap_congr {α β : Type _} {f g : α → List β} (h : ∀ a, f a = g a) :
    ∀ l : List α, cflatMap f l = cflatMap g l
  | []     => rfl
  | a :: l => by show f a ++ cflatMap f l = g a ++ cflatMap g l; rw [h a, cflatMap_congr h l]

/-- The two `insertEverywhere` definitions agree (identical recursion). -/
theorem insEv_eq (a : Nat) : ∀ l : List Nat, insertEverywhere a l = cinsEv a l
  | []     => rfl
  | b :: l => by
    show (a :: b :: l) :: (insertEverywhere a l).map (fun L => b :: L)
       = (a :: b :: l) :: (cinsEv a l).map (b :: ·)
    rw [insEv_eq a l]

/-- ★ **The Leibniz index enumeration is the combinatorics enumeration.**  `permsOf xs` (the
    determinant's permutation value-lists) equals `Combinatorics.perms xs`. -/
theorem permsOf_eq : ∀ xs : List Nat, permsOf xs = cperms xs
  | []      => rfl
  | x :: xs => by
    show (permsOf xs).flatMap (insertEverywhere x) = cflatMap (cinsEv x) (cperms xs)
    rw [permsOf_eq xs, flatMap_eq (insertEverywhere x), cflatMap_congr (insEv_eq x) (cperms xs)]

/-! ## §2 — the `n!` cardinality of the Leibniz index set -/

/-- `(iota n).length = n`. -/
theorem iota_length : ∀ n, (iota n).length = n
  | 0     => rfl
  | n + 1 => by
    show (iota n ++ [n]).length = n + 1
    rw [length_append (iota n) [n], iota_length n,
        show ([n] : List Nat).length = 1 from rfl]

/-- ★ **The Leibniz index set has `n!` members.**  `perms n` (the value-lists `leibDet` sums
    over) enumerates exactly `fact n` orderings. -/
theorem perms_card (n : Nat) : (perms n).length = fact n := by
  show (permsOf (iota n)).length = fact n
  rw [permsOf_eq (iota n), cperms_length (iota n), iota_length n]

/-- ★★ **The Leibniz determinant is a sum of exactly `n!` signed diagonal products.**
    `leibDet n M = sumZ L` with `|L| = fact n`. -/
theorem leibDet_card (n : Nat) (M : Nat → Nat → Int) :
    ∃ L : List Int, leibDet n M = sumZ L ∧ L.length = fact n :=
  ⟨(perms n).map (leibTerm M), rfl, by
    rw [E213.Tactic.List213.length_map (perms n) (leibTerm M), perms_card n]⟩

end E213.Lib.Math.Algebra.Linalg213.PermBridge
