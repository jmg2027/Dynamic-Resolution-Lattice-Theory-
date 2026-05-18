/-!
# Meta.Tactic.List213 — propext-free `List` helpers for 213 PURE proofs

Lean 4 core's `List.append_assoc`, `List.append_nil`,
`List.length_append` all carry `propext` per `#print axioms`.
This module provides strict ∅-axiom (`congrArg`-based)
replacements for use in 213 PURE-target proofs.

The three lemmas are stated identically to the core versions but
implemented manually via `congrArg` / direct `Nat`-induction so
that they do not pull in any non-Lean-core axiom.

Cross-reference: trick #11 in `seed/CLOSED_FORM_SPEC.md`.

∅-axiom standard.
-/

namespace E213.Tactic.List213

universe u

/-- `xs ++ [] = xs` (propext-free version of `List.append_nil`). -/
theorem append_nil {α : Type u} : ∀ (xs : List α), xs ++ [] = xs
  | []      => rfl
  | x :: xs => congrArg (x :: ·) (append_nil xs)

/-- `(xs ++ ys) ++ zs = xs ++ (ys ++ zs)` (propext-free version of
    `List.append_assoc`). -/
theorem append_assoc {α : Type u} :
    ∀ (xs ys zs : List α), (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
  | [],      _, _   => rfl
  | x :: xs, ys, zs => congrArg (x :: ·) (append_assoc xs ys zs)

/-- `(xs ++ ys).length = xs.length + ys.length` (propext-free version
    of `List.length_append`). -/
theorem length_append {α : Type u} :
    ∀ (xs ys : List α), (xs ++ ys).length = xs.length + ys.length
  | [],      ys => by
      show ys.length = 0 + ys.length
      rw [Nat.zero_add]
  | x :: xs, ys => by
      show (xs ++ ys).length + 1 = (xs.length + 1) + ys.length
      rw [length_append xs ys, Nat.add_right_comm]

end E213.Tactic.List213
