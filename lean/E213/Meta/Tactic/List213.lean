/-!
# Meta.Tactic.List213 — propext-free `List` helpers for 213 PURE proofs

Lean 4 core's `List.append_assoc`, `List.append_nil`,
`List.length_append`, `List.length_map` all carry `propext` per
`#print axioms`.  This module provides strict ∅-axiom
(`congrArg`-based) replacements for use in 213 PURE-target proofs.

Cross-reference: trick #12 in `seed/CLOSED_FORM_SPEC.md`.

∅-axiom standard.
-/

namespace E213.Tactic.List213

universe u v

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

/-- Reversed-order length-of-append, useful when the standard form's
    `0 + n` reduction is awkward.  Pure `rfl` in the nil case (no
    `Nat.zero_add` needed). -/
theorem length_append_rev {α : Type u} :
    ∀ (xs ys : List α), (xs ++ ys).length = ys.length + xs.length
  | [],      _  => rfl
  | _ :: xs, ys => congrArg (· + 1) (length_append_rev xs ys)

/-- `(xs.map f).length = xs.length` (propext-free version of
    `List.length_map`). -/
theorem length_map {α : Type u} {β : Type v} :
    ∀ (xs : List α) (f : α → β), (xs.map f).length = xs.length
  | [],      _ => rfl
  | _ :: xs, f => congrArg (· + 1) (length_map xs f)

end E213.Tactic.List213
