import E213.Lib.Math.Cohomology.Cup.LeibnizLexListLevel

/-!
# Cohomology.Cup.RangeFoldXor — `List.range`-foldl ↔ `xorRange`

PURE conversion between `(List.range n).foldl (fun a i => xor a (f i)) acc`
and `xor acc (xorRange n f)`, bypassing the propext-tainted
`List.range_succ` from Lean core.

Proves via two structural facts about `List.range.loop`:

  · `range_loop_eq_range_append` :
      `List.range.loop n acc = List.range n ++ acc`
  · `foldl_append` :
      `(l₁ ++ l₂).foldl step acc = l₂.foldl step (l₁.foldl step acc)`

Both prove by structural induction (no propext, no Mathlib).
-/

namespace E213.Lib.Math.Cohomology.Cup.RangeFoldXor

open E213.Lib.Math.Cohomology.Cup.LeibnizLexListLevel (xorRange)

/-- `List.append` is associative — PURE structural induction. -/
theorem append_assoc {α} (l₁ l₂ l₃ : List α) :
    (l₁ ++ l₂) ++ l₃ = l₁ ++ (l₂ ++ l₃) := by
  induction l₁ with
  | nil => rfl
  | cons a as ih =>
    show a :: ((as ++ l₂) ++ l₃) = a :: (as ++ (l₂ ++ l₃))
    rw [ih]

/-- `List.foldl` distributes over append.  PURE structural induction. -/
theorem foldl_append {α β} (step : β → α → β) (l₁ l₂ : List α) (acc : β) :
    (l₁ ++ l₂).foldl step acc
    = l₂.foldl step (l₁.foldl step acc) := by
  induction l₁ generalizing acc with
  | nil => rfl
  | cons a as ih =>
    show (as ++ l₂).foldl step (step acc a)
       = l₂.foldl step (as.foldl step (step acc a))
    exact ih (step acc a)

/-- `range.loop n acc = range n ++ acc`.  PURE structural induction. -/
theorem range_loop_eq_range_append :
    ∀ (n : Nat) (acc : List Nat),
      List.range.loop n acc = List.range n ++ acc := by
  intro n
  induction n with
  | zero =>
    intro acc
    show acc = [] ++ acc
    rfl
  | succ n' ih =>
    intro acc
    show List.range.loop n' (n' :: acc)
       = List.range (n' + 1) ++ acc
    rw [ih (n' :: acc)]
    show List.range n' ++ (n' :: acc)
       = List.range.loop (n' + 1) [] ++ acc
    show List.range n' ++ ([n'] ++ acc)
       = List.range.loop n' [n'] ++ acc
    rw [ih [n'], ← append_assoc]

/-- ★★ `List.range (n+1) = List.range n ++ [n]` — PURE replacement
    for `List.range_succ` (propext-tainted in Lean core). -/
theorem range_succ' (n : Nat) :
    List.range (n + 1) = List.range n ++ [n] := by
  show List.range.loop n [n] = List.range n ++ [n]
  exact range_loop_eq_range_append n [n]

/-- ★★★ **`range`-foldl ↔ `xorRange` conversion** — the key bridge
    between Lean-core `List.range`-style folds and the
    custom `xorRange` of `LeibnizLexListLevel`.  PURE. -/
theorem foldl_xor_range_eq_xorRange (f : Nat → Bool) :
    ∀ (n : Nat) (acc : Bool),
      (List.range n).foldl (fun a i => xor a (f i)) acc
      = xor acc (xorRange n f) := by
  intro n
  induction n with
  | zero =>
    intro acc
    show acc = xor acc false
    cases acc <;> rfl
  | succ n' ih =>
    intro acc
    rw [range_succ', foldl_append]
    show xor ((List.range n').foldl (fun a i => xor a (f i)) acc) (f n')
       = xor acc (xor (xorRange n' f) (f n'))
    rw [ih acc]
    cases acc <;> cases xorRange n' f <;> cases f n' <;> rfl

end E213.Lib.Math.Cohomology.Cup.RangeFoldXor
