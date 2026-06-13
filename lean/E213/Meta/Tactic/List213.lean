/-!
# Meta.Tactic.List213 — propext-free `List` library for 213 PURE proofs

Lean 4 core's `List` lemmas — `append_*`, `length_*`, `mem_*`, `Nodup`,
`filter`, `getD`, `flatMap` — carry `propext` (and some `Quot.sound`) per
`#print axioms`.  This module provides strict ∅-axiom replacements
(structural induction / `congrArg`-based) for use in 213 PURE-target
proofs:

  - **append / length**: `append_nil`, `append_assoc`, `length_append`,
    `length_map`;
  - **membership**: `mem_map_of_mem`, `exists_of_mem_map`,
    `mem_append_left/right/iff`, `mem_flatMap_intro/elim`;
  - **nodup**: `nodup_append`, `nodup_map_of_inj`, `nodup_filter`;
  - **map**: `map_congr`, `map_eq_comp`;
  - **getD**: `getD_ge`, `getD_map_ib`, `list_ext_getD`;
  - **filter**: `length_filter_le`, `length_filter_lt_of_mem`,
    `mem_filter`, `mem_filter_of`;
  - **cardinality**: `nodup_length_le_of_subset`,
    `nodup_length_eq_of_mem_iff` (same elements + nodup ⇒ same length).

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

/-! ## Membership (propext-free; core `List.mem_*` carry propext) -/

/-- `b ∈ l → f b ∈ l.map f`. -/
theorem mem_map_of_mem {α β : Type _} (f : α → β) {b : α} :
    ∀ {l : List α}, b ∈ l → f b ∈ l.map f
  | _ :: _, List.Mem.head _ => List.Mem.head _
  | _ :: _, List.Mem.tail _ h => List.Mem.tail _ (mem_map_of_mem f h)

/-- `a ∈ l.map f → ∃ b ∈ l, f b = a`. -/
theorem exists_of_mem_map {α β : Type _} {f : α → β} {a : β} :
    ∀ {l : List α}, a ∈ l.map f → ∃ b, b ∈ l ∧ f b = a
  | x :: _, List.Mem.head _ => ⟨x, List.Mem.head _, rfl⟩
  | _ :: xs, List.Mem.tail _ h =>
      let ⟨b, hb, hfb⟩ := exists_of_mem_map (l := xs) h
      ⟨b, List.Mem.tail _ hb, hfb⟩

/-- `a ∈ l₁ → a ∈ l₁ ++ l₂`. -/
theorem mem_append_left {α : Type _} {a : α} {l₂ : List α} :
    ∀ {l₁ : List α}, a ∈ l₁ → a ∈ l₁ ++ l₂
  | _ :: _, List.Mem.head _ => List.Mem.head _
  | _ :: _, List.Mem.tail _ h => List.Mem.tail _ (mem_append_left h)

/-- `a ∈ l₂ → a ∈ l₁ ++ l₂`. -/
theorem mem_append_right {α : Type _} {a : α} :
    ∀ (l₁ : List α) {l₂ : List α}, a ∈ l₂ → a ∈ l₁ ++ l₂
  | [], _, h => h
  | _ :: xs, _, h => List.Mem.tail _ (mem_append_right xs h)

/-- Membership in an append splits. -/
theorem mem_append_iff {α : Type _} {a : α} {l₁ l₂ : List α}
    (h : a ∈ l₁ ++ l₂) : a ∈ l₁ ∨ a ∈ l₂ := by
  induction l₁ with
  | nil => exact Or.inr h
  | cons x xs ih =>
      cases h with
      | head => exact Or.inl (List.Mem.head _)
      | tail _ h' => exact (ih h').imp (List.Mem.tail _) id

/-- `flatMap` membership introduction. -/
theorem mem_flatMap_intro {α β : Type _} {f : α → List β} {b : β} {a : α} :
    ∀ {l : List α}, a ∈ l → b ∈ f a → b ∈ l.flatMap f
  | x :: t, ha, hb => by
      show b ∈ f x ++ t.flatMap f
      cases ha with
      | head => exact mem_append_left hb
      | tail _ h' => exact mem_append_right _ (mem_flatMap_intro h' hb)

/-- `flatMap` membership elimination. -/
theorem mem_flatMap_elim {α β : Type _} {f : α → List β} {b : β} :
    ∀ {l : List α}, b ∈ l.flatMap f → ∃ a, a ∈ l ∧ b ∈ f a
  | x :: t, h => by
      rcases mem_append_iff (show b ∈ f x ++ t.flatMap f from h) with h' | h'
      · exact ⟨x, List.Mem.head _, h'⟩
      · rcases mem_flatMap_elim h' with ⟨a, ha, hb⟩
        exact ⟨a, List.Mem.tail _ ha, hb⟩

/-! ## Nodup -/

/-- Append preserves `Nodup` for disjoint lists. -/
theorem nodup_append {α : Type _} {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (hd : ∀ a, a ∈ l₁ → a ∈ l₂ → False) : (l₁ ++ l₂).Nodup := by
  induction l₁ with
  | nil => exact h₂
  | cons x xs ih =>
      cases h₁ with
      | cons hx hxs =>
          refine List.Pairwise.cons ?_
            (ih hxs (fun a ha hb => hd a (List.Mem.tail _ ha) hb))
          intro y hy
          rcases mem_append_iff hy with hy₁ | hy₂
          · exact hx y hy₁
          · exact fun he => hd x (List.Mem.head _) (he ▸ hy₂)

/-- A map injective on a `Nodup` list produces a `Nodup` image. -/
theorem nodup_map_of_inj {α β : Type _} {f : α → β} :
    ∀ {l : List α}, (∀ a, a ∈ l → ∀ b, b ∈ l → f a = f b → a = b) →
      l.Nodup → (l.map f).Nodup
  | [], _, _ => List.Pairwise.nil
  | a :: t, hinj, h => by
      cases h with
      | cons hat ht =>
          refine List.Pairwise.cons ?_
            (nodup_map_of_inj
              (fun x hx y hy => hinj x (List.Mem.tail _ hx) y (List.Mem.tail _ hy)) ht)
          intro y hy
          rcases exists_of_mem_map hy with ⟨b, hb, rfl⟩
          intro hcontra
          exact hat b hb (hinj a (List.Mem.head _) b (List.Mem.tail _ hb) hcontra)

/-! ## `map` congruence / extraction -/

/-- Pointwise-equal functions give equal maps. -/
theorem map_congr {α β : Type _} {f g : α → β} :
    ∀ {l : List α}, (∀ x, x ∈ l → f x = g x) → l.map f = l.map g
  | [], _ => rfl
  | a :: t, h => by
      show f a :: t.map f = g a :: t.map g
      rw [h a (List.Mem.head _), map_congr (fun x hx => h x (List.Mem.tail _ hx))]

/-- `l.map f = l.map g → ∀ x ∈ l, f x = g x`. -/
theorem map_eq_comp {α β : Type _} {f g : α → β} :
    ∀ {l : List α}, l.map f = l.map g → ∀ x, x ∈ l → f x = g x
  | a :: t, he, x, hx => by
      have h1 : f a = g a := by injection he
      have h2 : t.map f = t.map g := by injection he
      cases hx with
      | head => exact h1
      | tail _ h' => exact map_eq_comp h2 x h'

/-! ## `getD` -/

/-- `getD` past the end is the default. -/
theorem getD_ge {α : Type _} (d : α) :
    ∀ {l : List α} {i : Nat}, l.length ≤ i → l.getD i d = d
  | [], _, _ => rfl
  | _ :: _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: t, i + 1, h => getD_ge d (l := t) (Nat.le_of_succ_le_succ h)

/-- `getD` into the left summand of an append (in-bounds index). -/
theorem getD_append_left {α : Type _} (d : α) :
    ∀ (A B : List α) (i : Nat), i < A.length → (A ++ B).getD i d = A.getD i d
  | [],      _, i,     h => absurd h (Nat.not_lt_zero i)
  | _ :: _,  _, 0,     _ => rfl
  | _ :: A', B, i + 1, h => getD_append_left d A' B i (Nat.lt_of_succ_lt_succ h)

/-- `getD` into the right summand of an append (index shifted past the left). -/
theorem getD_append_right {α : Type _} (d : α) :
    ∀ (A B : List α) (j : Nat), (A ++ B).getD (A.length + j) d = B.getD j d
  | [],      B, j => by show B.getD (0 + j) d = B.getD j d; rw [Nat.zero_add]
  | a :: A', B, j => by
      show (a :: (A' ++ B)).getD (A'.length + 1 + j) d = B.getD j d
      rw [Nat.add_right_comm]
      show (A' ++ B).getD (A'.length + j) d = B.getD j d
      exact getD_append_right d A' B j

/-- `getD` of `map` in bounds. -/
theorem getD_map_ib {α β : Type _} (f : α → β) (d' : α) (d : β) :
    ∀ (l : List α) (i : Nat), i < l.length → (l.map f).getD i d = f (l.getD i d')
  | _ :: _, 0, _ => rfl
  | _ :: t, i + 1, h => getD_map_ib f d' d t i (Nat.lt_of_succ_lt_succ h)
  | [], i, h => absurd h (Nat.not_lt_zero i)

/-- List extensionality via `getD`. -/
theorem list_ext_getD {α : Type _} (d : α) :
    ∀ {σ τ : List α}, σ.length = τ.length →
      (∀ i, σ.getD i d = τ.getD i d) → σ = τ
  | [], [], _, _ => rfl
  | a :: s, c :: t, hl, hg => by
      rw [show a = c from hg 0,
          show s = t from list_ext_getD d (Nat.succ.inj hl) (fun i => hg (i + 1))]
  | [], _ :: _, hl, _ => Nat.noConfusion hl
  | _ :: _, [], hl, _ => Nat.noConfusion hl

/-! ## `filter` -/

/-- Filtering never increases length. -/
theorem length_filter_le {α : Type _} (p : α → Bool) :
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
theorem length_filter_lt_of_mem {α : Type _} {p : α → Bool} {a : α} :
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

/-- `x ∈ l.filter p → x ∈ l ∧ p x = true`. -/
theorem mem_filter {α : Type _} {p : α → Bool} {x : α} :
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
theorem mem_filter_of {α : Type _} {p : α → Bool} {x : α} :
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
theorem nodup_filter {α : Type _} (p : α → Bool) :
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

/-- The head-drop predicate `x ↦ (x ≠ a)`, via `DecidableEq` (`ite`
    reduces with `if_pos`/`if_neg`, both pure). -/
private def neqp {α : Type _} [DecidableEq α] (a x : α) : Bool :=
  if x = a then false else true

/-- A `Nodup` list contained in another is no longer. -/
theorem nodup_length_le_of_subset {α : Type _} [DecidableEq α] :
    ∀ {l₁ l₂ : List α}, l₁.Nodup → (∀ x, x ∈ l₁ → x ∈ l₂) →
      l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, l₂, h, hsub => by
      cases h with
      | cons hat ht =>
          have haL₂ : a ∈ l₂ := hsub a (List.Mem.head _)
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
theorem nodup_length_eq_of_mem_iff {α : Type _} [DecidableEq α] {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) :
    l₁.length = l₂.length :=
  Nat.le_antisymm
    (nodup_length_le_of_subset h₁ (fun x hx => (hmem x).mp hx))
    (nodup_length_le_of_subset h₂ (fun x hx => (hmem x).mpr hx))

end E213.Tactic.List213
