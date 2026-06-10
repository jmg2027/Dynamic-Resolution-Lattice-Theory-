import E213.Meta.Tactic.NatHelper

/-!
# Meta.Tactic.ListHelper — PURE List helpers for the 213 framework

Centralised propext-free replacements for Lean-core `List.*` lemmas
that import `propext` or `Quot.sound` via `simp`-based proofs.

This is the **List-side companion** to `Meta/Tactic/NatHelper.lean`.
Consumers (e.g. `Lib/Math/Cohomology/Cup/{KSubsetStructural,FinBridgeGeneral}`)
use these directly or via `@[reducible]` aliases at their original sites.

All theorems below are **PURE** (`#print axioms` reports
"does not depend on any axioms").
-/

namespace E213.Tactic.ListHelper

/-! ## §1.  Length / append-singleton -/

/-- `(l ++ [x]).length = l.length + 1` — PURE via direct induction.
    Specialised to `Nat` (the dominant use site).  Replaces
    `List.length_append + List.length_singleton`-style chains that
    bring propext via `simp`. -/
theorem length_append_singleton (l : List Nat) (x : Nat) :
    (l ++ [x]).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    show (ys ++ [x]).length + 1 = ys.length + 1 + 1
    rw [ih]

/-! ## §2.  Take/drop append behaviour -/

/-- `(l₁ ++ l₂).take k = l₁.take k` when `k ≤ l₁.length`.  PURE.
    Replaces `List.take_append_of_le_length` (propext + Quot.sound). -/
theorem take_append_le (l₁ l₂ : List Nat) (k : Nat)
    (h : k ≤ l₁.length) :
    (l₁ ++ l₂).take k = l₁.take k := by
  induction l₁ generalizing k with
  | nil =>
    cases k with
    | zero => rfl
    | succ k' => exact absurd h (Nat.not_succ_le_zero k')
  | cons a as ih =>
    cases k with
    | zero => rfl
    | succ k' =>
      show a :: (as ++ l₂).take k' = a :: as.take k'
      rw [ih k' (Nat.le_of_succ_le_succ h)]

/-- `(l₁ ++ l₂).drop k = l₁.drop k ++ l₂` when `k ≤ l₁.length`.  PURE. -/
theorem drop_append_le (l₁ l₂ : List Nat) (k : Nat)
    (h : k ≤ l₁.length) :
    (l₁ ++ l₂).drop k = l₁.drop k ++ l₂ := by
  induction l₁ generalizing k with
  | nil =>
    cases k with
    | zero => rfl
    | succ k' => exact absurd h (Nat.not_succ_le_zero k')
  | cons a as ih =>
    cases k with
    | zero => rfl
    | succ k' =>
      show (as ++ l₂).drop k' = as.drop k' ++ l₂
      exact ih k' (Nat.le_of_succ_le_succ h)

/-! ## §3.  Take/drop full-length behaviour -/

/-- `l.take l.length = l`.  PURE.  Replaces `List.take_length`
    (propext). -/
theorem take_length_self (l : List Nat) : l.take l.length = l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    show a :: as.take as.length = a :: as
    rw [ih]

/-- `l.drop l.length = []`.  PURE. -/
theorem drop_length_self (l : List Nat) : l.drop l.length = [] := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    show as.drop as.length = []
    exact ih

/-- `l.length ≤ k → l.take k = l`.  PURE.  Replaces
    `List.take_of_length_le` (propext). -/
theorem take_of_length_le (l : List Nat) (k : Nat)
    (h : l.length ≤ k) : l.take k = l := by
  induction l generalizing k with
  | nil =>
    cases k with
    | zero => rfl
    | succ _ => rfl
  | cons a as ih =>
    cases k with
    | zero => exact absurd h (Nat.not_succ_le_zero _)
    | succ k' =>
      show a :: as.take k' = a :: as
      rw [ih k' (Nat.le_of_succ_le_succ h)]

/-- `l.length ≤ k → l.drop k = []`.  PURE. -/
theorem drop_of_length_le (l : List Nat) (k : Nat)
    (h : l.length ≤ k) : l.drop k = [] := by
  induction l generalizing k with
  | nil =>
    cases k with
    | zero => rfl
    | succ _ => rfl
  | cons a as ih =>
    cases k with
    | zero => exact absurd h (Nat.not_succ_le_zero _)
    | succ k' =>
      show as.drop k' = []
      exact ih k' (Nat.le_of_succ_le_succ h)

/-! ## §4.  Membership / append-singleton -/

/-- `x ∈ l ++ [m] → x ∈ l ∨ x = m`.  PURE via inductive `List.Mem`
    case-analysis (bypasses `List.mem_append`/`mem_singleton`
    propext-iff). -/
theorem mem_append_singleton :
    ∀ (l : List Nat) (m x : Nat), x ∈ l ++ [m] → x ∈ l ∨ x = m := by
  intro l m x
  induction l with
  | nil =>
    intro h
    cases h with
    | head _ => exact Or.inr rfl
    | tail _ h' => exact absurd h' (List.not_mem_nil x)
  | cons y ys ih =>
    intro h
    cases h with
    | head _ => exact Or.inl (List.Mem.head ys)
    | tail _ h' =>
      rcases ih h' with h_in | h_eq
      · exact Or.inl (List.Mem.tail y h_in)
      · exact Or.inr h_eq

/-- `m ∈ l ++ [m]` — PURE constructive proof via `List.Mem`. -/
theorem mem_append_singleton_right :
    ∀ (l : List Nat) (m : Nat), m ∈ l ++ [m] := by
  intro l m
  induction l with
  | nil => exact List.Mem.head []
  | cons y ys ih => exact List.Mem.tail y ih

/-! ## §5.  Append injectivity at singleton -/

/-- `l₁ ++ [x] = l₂ ++ [x] → l₁ = l₂`.  PURE via cons-injection +
    length contradiction (using `length_append_singleton` +
    `Nat.noConfusion` instead of propext-tainted
    `Nat.succ_ne_zero`). -/
theorem append_singleton_inj :
    ∀ (l₁ l₂ : List Nat) (x : Nat), l₁ ++ [x] = l₂ ++ [x] → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ x h
    cases l₂ with
    | nil => rfl
    | cons y ys =>
      injection h with _ h_tail
      have h_len : ([] : List Nat).length = (ys ++ [x]).length :=
        congrArg List.length h_tail
      rw [length_append_singleton] at h_len
      exact Nat.noConfusion h_len
  | cons a as ih =>
    intro l₂ x h
    cases l₂ with
    | nil =>
      injection h with _ h_tail
      have h_len : (as ++ [x]).length = ([] : List Nat).length :=
        congrArg List.length h_tail
      rw [length_append_singleton] at h_len
      exact Nat.noConfusion h_len
    | cons b bs =>
      injection h with h_head h_tail
      rw [h_head, ih bs x h_tail]

/-! ## §6.  `eraseIdx` interaction with `++ [x]`

Two structural lemmas about `(l ++ [x]).eraseIdx i`:

  · `eraseIdx_append_singleton_low`: when `i < l.length`, the
    `eraseIdx` lands inside `l` and the trailing `[x]` is preserved.
  · `eraseIdx_append_singleton_at_len`: when `i = l.length`, the
    `eraseIdx` removes the trailing `[x]`, returning `l`.

Used by the `kSubset_eraseIdx_eq` structural lemma. -/

/-- `(l ++ [x]).eraseIdx i = l.eraseIdx i ++ [x]` when `i < l.length`. -/
theorem eraseIdx_append_singleton_low :
    ∀ (l : List Nat) (x : Nat) (i : Nat),
      i < l.length → (l ++ [x]).eraseIdx i = l.eraseIdx i ++ [x] := by
  intro l x
  induction l with
  | nil =>
    intro i h
    exact absurd h (Nat.not_lt_zero i)
  | cons a as ih =>
    intro i h
    cases i with
    | zero => rfl
    | succ i' =>
      have h' : i' < as.length := Nat.lt_of_succ_lt_succ h
      have ih' := ih i' h'
      show a :: (as ++ [x]).eraseIdx i' = a :: as.eraseIdx i' ++ [x]
      rw [ih']; rfl

/-- `(l ++ [x]).eraseIdx l.length = l` — removing the trailing singleton
    returns the prefix.  PURE. -/
theorem eraseIdx_append_singleton_at_len :
    ∀ (l : List Nat) (x : Nat), (l ++ [x]).eraseIdx l.length = l := by
  intro l x
  induction l with
  | nil => rfl
  | cons a as ih =>
    show a :: (as ++ [x]).eraseIdx as.length = a :: as
    rw [ih]

/-- `(l.eraseIdx i).length + 1 = l.length` when `i < l.length`.  PURE.
    Replaces the propext-tainted `List.length_eraseIdx` from Lean core. -/
theorem length_eraseIdx_of_lt :
    ∀ (l : List Nat) (i : Nat),
      i < l.length → (l.eraseIdx i).length + 1 = l.length := by
  intro l
  induction l with
  | nil =>
    intro i h
    exact absurd h (Nat.not_lt_zero i)
  | cons a as ih =>
    intro i h
    cases i with
    | zero =>
      show as.length + 1 = as.length + 1
      rfl
    | succ i' =>
      have h' : i' < as.length := Nat.lt_of_succ_lt_succ h
      have := ih i' h'
      show (as.eraseIdx i').length + 1 + 1 = as.length + 1
      rw [this]

/-! ## §7.  Σ-over-list — `sigmaList`

Single primitive for "sum `f` over the elements of `xs`".  Unifies the
`(xs.map f).foldl (· + ·) 0` skeleton recurring across math (Vec.inner,
routeSum) and physics (observable_sum, focc_spectrum_master) layers.

Reducible so that `decide` unfolds it transparently; PURE
(no `propext`, no `Classical`). -/

/-- Σ over a list with respect to a Nat-valued weight. -/
@[reducible] def sigmaList {α : Type u} (xs : List α) (f : α → Nat) : Nat :=
  (xs.map f).foldl (· + ·) 0

/-- `sigmaList` of the empty list is `0`. -/
theorem sigmaList_nil {α : Type u} (f : α → Nat) :
    sigmaList ([] : List α) f = 0 := rfl

/-- `sigmaList` over `range (n+1)` indexed by `r : Nat → Nat`
    matches the bare `foldl (fun acc k => acc + r k) 0` shape that
    `PhaseRouting.routeSum` previously inlined. -/
theorem sigmaList_range_eq_foldl_acc (n : Nat) (r : Nat → Nat) :
    sigmaList (List.range (n+1)) r
      = (List.range (n+1)).foldl (fun acc k => acc + r k) 0 := by
  show ((List.range (n+1)).map r).foldl (· + ·) 0
     = (List.range (n+1)).foldl (fun acc k => acc + r k) 0
  generalize hxs : List.range (n+1) = xs
  clear hxs
  suffices h : ∀ (acc : Nat),
      (xs.map r).foldl (· + ·) acc
        = xs.foldl (fun a k => a + r k) acc by
    exact h 0
  intro acc
  induction xs generalizing acc with
  | nil => rfl
  | cons y ys ih => exact ih (acc + r y)

end E213.Tactic.ListHelper
