import E213.Lib.Math.Linalg213.Permutation

/-!
# Linalg213 — the permutation enumeration realizes the symmetric-group action

The remaining gate for the Leibniz determinant's **alternating** property: the enumeration
`perms n` is closed (up to `LPerm`) under an adjacent position-swap `swapAt k`, and every
listed permutation is a genuine rearrangement of `[0,…,n−1]` (sound) with no repeats (nodup).

This file builds that closure bottom-up: clean (∅-axiom) `List` membership helpers → `LPerm`
structural lemmas → enumeration **soundness** (each output is a rearrangement) → (later)
completeness, nodup, and the closure itself.

The core `List.mem_*` iff-lemmas are `propext`/`Quot.sound`-tainted, so membership is done
structurally on the `List.Mem` constructors.  All ∅-axiom.
-/

namespace E213.Lib.Math.Linalg213.PermClosure

open E213.Lib.Math.Linalg213.Permutation
  (LPerm insertEverywhere permsOf perms swapAt swapAt_lperm)

/-! ## §0 — clean (∅-axiom) `List` membership helpers -/

/-- `q ∈ L1 ++ L2 → q ∈ L1 ∨ q ∈ L2` (structural, no `propext`). -/
theorem mem_append' {α : Type} {q : α} : ∀ {L1 L2 : List α}, q ∈ L1 ++ L2 → q ∈ L1 ∨ q ∈ L2
  | [],      _,  h => Or.inr h
  | _ :: _,  _,  h => by
    cases h with
    | head      => exact Or.inl (List.Mem.head _)
    | tail _ h' => rcases mem_append' h' with h1 | h2
                   · exact Or.inl (List.Mem.tail _ h1)
                   · exact Or.inr h2

/-- `q ∈ L.map f → ∃ x ∈ L, f x = q` (structural). -/
theorem mem_map' {α β : Type} (f : α → β) {q : β} : ∀ {L : List α},
    q ∈ L.map f → ∃ x, x ∈ L ∧ f x = q
  | [],      h => by cases h
  | a :: as, h => by
    cases h with
    | head      => exact ⟨a, List.Mem.head _, rfl⟩
    | tail _ h' => rcases mem_map' f h' with ⟨x, hx, e⟩; exact ⟨x, List.Mem.tail _ hx, e⟩

/-- `q ∈ L.flatMap f → ∃ x ∈ L, q ∈ f x` (structural). -/
theorem mem_flatMap' {α β : Type} (f : α → List β) {q : β} : ∀ {L : List α},
    q ∈ L.flatMap f → ∃ x, x ∈ L ∧ q ∈ f x
  | [],      h => by cases h
  | a :: as, h => by
    rcases mem_append' h with h1 | h2
    · exact ⟨a, List.Mem.head _, h1⟩
    · rcases mem_flatMap' f h2 with ⟨x, hx, hqx⟩; exact ⟨x, List.Mem.tail _ hx, hqx⟩

/-- `q ∈ [a] → q = a` (structural). -/
theorem mem_singleton' {α : Type} {q a : α} (h : q ∈ [a]) : q = a := by
  cases h with
  | head      => rfl
  | tail _ h' => cases h'

/-! ## §1 — `LPerm` structural lemmas -/

/-- `LPerm` preserves membership. -/
theorem LPerm.mem {α : Type} {a : α} {L1 L2 : List α} (h : LPerm L1 L2) : a ∈ L1 → a ∈ L2 := by
  induction h with
  | nil => exact id
  | cons x _ ih =>
    intro hm
    cases hm with
    | head      => exact List.Mem.head _
    | tail _ h' => exact List.Mem.tail _ (ih h')
  | swap x y l =>
    intro hm
    cases hm with
    | head      => exact List.Mem.tail _ (List.Mem.head _)
    | tail _ h' =>
      cases h' with
      | head       => exact List.Mem.head _
      | tail _ h'' => exact List.Mem.tail _ (List.Mem.tail _ h'')
  | trans _ _ ih₁ ih₂ => intro hm; exact ih₂ (ih₁ hm)

/-- An adjacent swap after a prefix is an `LPerm`. -/
theorem lperm_swap_prefix {α : Type} (pre : List α) (x y : α) (l : List α) :
    LPerm (pre ++ x :: y :: l) (pre ++ y :: x :: l) := by
  induction pre with
  | nil          => exact LPerm.swap y x l
  | cons a pre ih => exact LPerm.cons a ih

/-! ## §2 — enumeration soundness (every output is a rearrangement) -/

/-- Every list produced by `insertEverywhere a p` is a rearrangement of `a :: p`. -/
theorem insEv_sound (a : Nat) : ∀ (p q : List Nat), q ∈ insertEverywhere a p → LPerm q (a :: p)
  | [],      q, h => by
    have hq : q = [a] := mem_singleton' h
    subst hq; exact LPerm.refl [a]
  | b :: ys, q, h => by
    cases h with
    | head => exact LPerm.refl (a :: b :: ys)
    | tail _ hmap =>
      rcases mem_map' _ hmap with ⟨q', hq', hb⟩
      subst hb
      exact LPerm.trans (LPerm.cons b (insEv_sound a ys q' hq')) (LPerm.swap a b ys)

/-- Every list in `permsOf xs` is a rearrangement of `xs`. -/
theorem permsOf_sound : ∀ (xs q : List Nat), q ∈ permsOf xs → LPerm q xs
  | [],      q, h => by
    have hq : q = [] := mem_singleton' h
    subst hq; exact LPerm.nil
  | a :: ys, q, h => by
    rcases mem_flatMap' _ h with ⟨p, hp, hq⟩
    exact LPerm.trans (insEv_sound a p q hq) (LPerm.cons a (permsOf_sound ys p hp))

/-! ## §3 — length and occurrence-count under `LPerm`

Toward `LPerm` cancellation (needed for completeness): the **occurrence count** `cnt a` and
its `LPerm`-invariance.  The reverse — count-equality ⟹ `LPerm` — is the cancellation engine
(next). -/

/-- `LPerm` preserves length. -/
theorem LPerm.length_eq {α : Type} {L1 L2 : List α} (h : LPerm L1 L2) :
    L1.length = L2.length := by
  induction h with
  | nil               => rfl
  | cons x _ ih        => exact congrArg (· + 1) ih
  | swap x y l         => rfl
  | trans _ _ ih₁ ih₂  => exact ih₁.trans ih₂

/-- Occurrence count of `a` in a list. -/
def cnt {α : Type} [DecidableEq α] (a : α) : List α → Nat
  | []     => 0
  | b :: l => (if b = a then 1 else 0) + cnt a l

/-- `LPerm` preserves every occurrence count. -/
theorem cnt_lperm {α : Type} [DecidableEq α] {a : α} {L1 L2 : List α} (h : LPerm L1 L2) :
    cnt a L1 = cnt a L2 := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    show (if x = a then 1 else 0) + cnt a _ = (if x = a then 1 else 0) + cnt a _
    rw [ih]
  | swap x y l =>
    show (if y = a then 1 else 0) + ((if x = a then 1 else 0) + cnt a l)
       = (if x = a then 1 else 0) + ((if y = a then 1 else 0) + cnt a l)
    exact Nat.add_left_comm _ _ _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## §4 — count-equality ⟹ `LPerm` (the cancellation engine)

Two lists with identical occurrence counts are `LPerm`-related.  Proven by induction on the
first list: peel its head `b`, locate `b` in the second list (`cnt_pos_mem` + `mem_split`),
cancel one `b` from every count (`Nat.add_left_cancel`), recurse, and move `b` back to its
place (`lperm_mid_to_front`).  This is the engine behind completeness and the closure. -/

/-- `cnt` distributes over append. -/
theorem cnt_append {α : Type} [DecidableEq α] (a : α) : ∀ (L1 L2 : List α),
    cnt a (L1 ++ L2) = cnt a L1 + cnt a L2
  | [],     L2 => by show cnt a L2 = 0 + cnt a L2; rw [Nat.zero_add]
  | b :: l, L2 => by
    show (if b = a then 1 else 0) + cnt a (l ++ L2)
       = ((if b = a then 1 else 0) + cnt a l) + cnt a L2
    rw [cnt_append a l L2, Nat.add_assoc]

/-- A list with all occurrence counts zero is empty. -/
theorem cnt_eq_zero_nil {α : Type} [DecidableEq α] : ∀ {L : List α}, (∀ a, cnt a L = 0) → L = []
  | [],     _ => rfl
  | b :: l, h => by
    have hpos : 0 < cnt b (b :: l) := by
      rw [show cnt b (b :: l) = (if b = b then 1 else 0) + cnt b l from rfl, if_pos rfl]
      exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right 1 (cnt b l))
    exact absurd (h b) (Nat.ne_of_gt hpos)

/-- Positive count implies membership. -/
theorem cnt_pos_mem {α : Type} [DecidableEq α] : ∀ {L : List α} {a : α}, 0 < cnt a L → a ∈ L
  | [],     a, h => absurd h (Nat.lt_irrefl 0)
  | b :: l, a, h => by
    by_cases hba : b = a
    · exact hba ▸ List.Mem.head _
    · rw [show cnt a (b :: l) = (if b = a then 1 else 0) + cnt a l from rfl, if_neg hba,
          Nat.zero_add] at h
      exact List.Mem.tail _ (cnt_pos_mem h)

/-- Membership splits a list around the element. -/
theorem mem_split {α : Type} {a : α} : ∀ (L : List α), a ∈ L → ∃ L1 L2, L = L1 ++ a :: L2
  | [],     h => by cases h
  | b :: l, h => by
    cases h with
    | head      => exact ⟨[], l, rfl⟩
    | tail _ h' => rcases mem_split l h' with ⟨L1, L2, he⟩; exact ⟨b :: L1, L2, congrArg (b :: ·) he⟩

/-- Moving an element from the front to a middle position is an `LPerm`. -/
theorem lperm_mid_to_front {α : Type} (b : α) : ∀ (L1 L2 : List α),
    LPerm (b :: (L1 ++ L2)) (L1 ++ b :: L2)
  | [],      L2 => LPerm.refl _
  | c :: L1, L2 =>
    LPerm.trans (LPerm.swap c b (L1 ++ L2)) (LPerm.cons c (lperm_mid_to_front b L1 L2))

/-- Left cancellation for `Nat` addition (propext-free; core's pulls `propext`). -/
theorem add_left_cancel' : ∀ (a : Nat) {b c : Nat}, a + b = a + c → b = c
  | 0,     _, _, h => by rw [Nat.zero_add, Nat.zero_add] at h; exact h
  | a + 1, _, _, h => by rw [Nat.succ_add, Nat.succ_add] at h; exact add_left_cancel' a (Nat.succ.inj h)

/-- ★ **Count-equality implies `LPerm`** — the cancellation engine. -/
theorem lperm_of_cnt_eq {α : Type} [DecidableEq α] :
    ∀ (L1 L2 : List α), (∀ a, cnt a L1 = cnt a L2) → LPerm L1 L2
  | [],      L2, hc => by
    have : L2 = [] := cnt_eq_zero_nil (fun a => (hc a).symm)
    subst this; exact LPerm.nil
  | b :: l1, L2, hc => by
    have hb : 0 < cnt b L2 := by
      rw [← hc b, show cnt b (b :: l1) = (if b = b then 1 else 0) + cnt b l1 from rfl, if_pos rfl]
      exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right 1 (cnt b l1))
    rcases mem_split L2 (cnt_pos_mem hb) with ⟨L2a, L2b, hsplit⟩
    have key : ∀ a, cnt a l1 = cnt a (L2a ++ L2b) := by
      intro a
      have h := hc a
      rw [hsplit, cnt_append] at h
      change (if b = a then 1 else 0) + cnt a l1
           = cnt a L2a + ((if b = a then 1 else 0) + cnt a L2b) at h
      rw [Nat.add_left_comm (cnt a L2a)] at h
      rw [cnt_append]
      exact add_left_cancel' _ h
    exact LPerm.trans (LPerm.cons b (lperm_of_cnt_eq l1 (L2a ++ L2b) key))
      (hsplit ▸ lperm_mid_to_front b L2a L2b)

/-! ## §5 — `swapAt` is an involution; count under an involution-map

`swapAt k` applied twice is the identity, so counting `q` in `map (swapAt k) L` counts
`swapAt k q` in `L`.  This reduces the closure `LPerm (map (swapAt k) (perms n)) (perms n)` to
the count equality `cnt (swapAt k q) (perms n) = cnt q (perms n)`. -/

/-- `swapAt k` is an involution. -/
theorem swapAt_invol (k : Nat) (p : List Nat) : swapAt k (swapAt k p) = p := by
  induction p generalizing k with
  | nil => cases k <;> rfl
  | cons a r ih =>
    cases k with
    | zero =>
      cases r with
      | nil       => rfl
      | cons b r' => rfl
    | succ k => show a :: swapAt k (swapAt k r) = a :: r; rw [ih]

/-- Counting under an involution-map: `cnt q (map f L) = cnt (f q) L`. -/
theorem cnt_map_inv {α : Type} [DecidableEq α] (f : α → α) (hf : ∀ x, f (f x) = x) (q : α) :
    ∀ (L : List α), cnt q (L.map f) = cnt (f q) L
  | []     => rfl
  | b :: l => by
    rw [show cnt q ((b :: l).map f) = (if f b = q then 1 else 0) + cnt q (l.map f) from rfl,
        show cnt (f q) (b :: l) = (if b = f q then 1 else 0) + cnt (f q) l from rfl,
        cnt_map_inv f hf q l]
    by_cases hbq : b = f q
    · rw [if_pos hbq, if_pos ((congrArg f hbq).trans (hf q))]
    · rw [if_neg hbq, if_neg (fun h : f b = q => hbq ((hf b).symm.trans (congrArg f h)))]

end E213.Lib.Math.Linalg213.PermClosure
