import E213.Lib.Math.Combinatorics.BoolEnum

/-!
# Nodup cardinality toolkit (∅-axiom)

Counting a finite set two ways requires "same elements + no duplicates ⇒
same length".  Core Lean's `List.Nodup` / `List.Subset` / `erase`
cardinality lemmas carry `propext`, so the strict-∅-axiom versions are
re-proved here by structural induction — **`filter (· ≠ a)` is used in
place of `List.erase`** (on a `Nodup` list they agree, and `filter`'s
length lemmas are cheap to prove pure).

  - `length_filter_le`, `length_filter_lt_of_mem` — filter shrinks length,
    strictly when it drops a present element;
  - `mem_filter`, `nodup_filter` — membership / nodup under filter;
  - `nodup_length_le_of_subset` — a nodup list inside another is no longer;
  - `nodup_length_eq_of_mem_iff` — nodup lists with the same elements have
    the same length.

The carrier is any type with `DecidableEq` (the Bool-cochain use needs
`List Bool`).  This is the cardinality-equality base under
`Combinatorics.BoolEnum`.

Companion: `theory/math/combinatorics/bool_enumeration.md`.
-/

namespace E213.Lib.Math.Combinatorics.ListCount

open E213.Lib.Math.Combinatorics.BoolEnum (mem_append_iff)

variable {α : Type _}

/-! ## Filter length -/

/-- Filtering never increases length. -/
theorem length_filter_le (p : α → Bool) :
    ∀ (l : List α), (l.filter p).length ≤ l.length
  | [] => Nat.le_refl 0
  | a :: l => by
      cases h : p a with
      | true =>
          rw [List.filter_cons_of_pos h, List.length_cons, List.length_cons]
          exact Nat.succ_le_succ (length_filter_le p l)
      | false =>
          rw [List.filter_cons_of_neg (by rw [h]; exact Bool.noConfusion),
              List.length_cons]
          exact Nat.le_succ_of_le (length_filter_le p l)

/-- If `a` is present and dropped by `p`, the filter is strictly shorter. -/
theorem length_filter_lt_of_mem {p : α → Bool} {a : α} :
    ∀ {l : List α}, a ∈ l → p a = false → (l.filter p).length < l.length
  | x :: l, h, hpa => by
      cases hx : p x with
      | true =>
          rw [List.filter_cons_of_pos hx, List.length_cons, List.length_cons]
          refine Nat.succ_lt_succ ?_
          cases h with
          | head => rw [hx] at hpa; exact Bool.noConfusion hpa
          | tail _ h' => exact length_filter_lt_of_mem h' hpa
      | false =>
          rw [List.filter_cons_of_neg (by rw [hx]; exact Bool.noConfusion),
              List.length_cons]
          exact Nat.lt_succ_of_le (length_filter_le p l)

/-! ## Membership / nodup under filter -/

/-- `x ∈ l.filter p ↔ x ∈ l ∧ p x = true`. -/
theorem mem_filter {p : α → Bool} {x : α} :
    ∀ {l : List α}, x ∈ l.filter p → x ∈ l ∧ p x = true
  | a :: l, h => by
      cases ha : p a with
      | true =>
          rw [List.filter_cons_of_pos ha] at h
          cases h with
          | head => exact ⟨List.Mem.head _, ha⟩
          | tail _ h' =>
              have := mem_filter h'
              exact ⟨List.Mem.tail _ this.1, this.2⟩
      | false =>
          rw [List.filter_cons_of_neg (by rw [ha]; exact Bool.noConfusion)] at h
          have := mem_filter h
          exact ⟨List.Mem.tail _ this.1, this.2⟩

/-- Membership into a filter from the two sides. -/
theorem mem_filter_of {p : α → Bool} {x : α} :
    ∀ {l : List α}, x ∈ l → p x = true → x ∈ l.filter p
  | a :: l, h, hpx => by
      cases ha : p a with
      | true =>
          rw [List.filter_cons_of_pos ha]
          cases h with
          | head => exact List.Mem.head _
          | tail _ h' => exact List.Mem.tail _ (mem_filter_of h' hpx)
      | false =>
          cases h with
          | head => rw [ha] at hpx; exact Bool.noConfusion hpx
          | tail _ h' =>
              rw [List.filter_cons_of_neg (by rw [ha]; exact Bool.noConfusion)]
              exact mem_filter_of h' hpx

/-- Filtering preserves `Nodup`. -/
theorem nodup_filter (p : α → Bool) :
    ∀ {l : List α}, l.Nodup → (l.filter p).Nodup
  | [], _ => List.Pairwise.nil
  | a :: l, h => by
      cases h with
      | cons ha hl =>
          cases hp : p a with
          | true =>
              rw [List.filter_cons_of_pos hp]
              refine List.Pairwise.cons ?_ (nodup_filter p hl)
              intro y hy
              exact ha y (mem_filter hy).1
          | false =>
              rw [List.filter_cons_of_neg (by rw [hp]; exact Bool.noConfusion)]
              exact nodup_filter p hl

/-! ## Nodup cardinality comparison -/

/-- The head-drop predicate `x ↦ (x ≠ a)`, as a `Bool`-valued filter via
    `DecidableEq` (`ite` reduces with `if_pos`/`if_neg`, which are pure;
    core `bne` lemmas carry `propext`). -/
private def neqp [DecidableEq α] (a x : α) : Bool := if x = a then false else true

/-- A `Nodup` list contained in another is no longer.  `DecidableEq` lets
    us drop the matched head with `filter (neqp a)`. -/
theorem nodup_length_le_of_subset [DecidableEq α] :
    ∀ {l₁ l₂ : List α}, l₁.Nodup → (∀ x, x ∈ l₁ → x ∈ l₂) →
      l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, l₂, h, hsub => by
      cases h with
      | cons hat ht =>
          have haL₂ : a ∈ l₂ := hsub a (List.Mem.head _)
          -- t ⊆ l₂.filter (neqp a)
          have hsub' : ∀ x, x ∈ t → x ∈ l₂.filter (neqp a) := by
            intro x hx
            exact mem_filter_of (hsub x (List.Mem.tail _ hx))
              (if_neg (Ne.symm (hat x hx)))
          have hle : t.length ≤ (l₂.filter (neqp a)).length :=
            nodup_length_le_of_subset ht hsub'
          have hlt : (l₂.filter (neqp a)).length < l₂.length :=
            length_filter_lt_of_mem haL₂ (if_pos rfl)
          rw [List.length_cons]
          exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hle hlt)

/-- **Nodup lists with the same elements have the same length.** -/
theorem nodup_length_eq_of_mem_iff [DecidableEq α] {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) :
    l₁.length = l₂.length :=
  Nat.le_antisymm
    (nodup_length_le_of_subset h₁ (fun x hx => (hmem x).mp hx))
    (nodup_length_le_of_subset h₂ (fun x hx => (hmem x).mpr hx))

end E213.Lib.Math.Combinatorics.ListCount
