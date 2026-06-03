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
  (LPerm insertEverywhere permsOf perms iota swapAt swapAt_lperm)

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

/-! ## §6 — enumeration completeness (every rearrangement is enumerated) -/

/-- `mem`-introduction for `map`. -/
theorem mem_map_mpr {α β : Type} (f : α → β) {x : α} : ∀ {L : List α}, x ∈ L → f x ∈ L.map f
  | [],      h => by cases h
  | _ :: _,  h => by
    cases h with
    | head      => exact List.Mem.head _
    | tail _ h' => exact List.Mem.tail _ (mem_map_mpr f h')

/-- `mem`-introduction for append (left). -/
theorem mem_append_left {α : Type} {q : α} : ∀ {L1 : List α} (L2 : List α), q ∈ L1 → q ∈ L1 ++ L2
  | _ :: _, L2, h => by
    cases h with
    | head      => exact List.Mem.head _
    | tail _ h' => exact List.Mem.tail _ (mem_append_left L2 h')

/-- `mem`-introduction for append (right). -/
theorem mem_append_right {α : Type} {q : α} : ∀ (L1 : List α) {L2 : List α}, q ∈ L2 → q ∈ L1 ++ L2
  | [],     _, h => h
  | _ :: l, _, h => List.Mem.tail _ (mem_append_right l h)

/-- `mem`-introduction for `flatMap`. -/
theorem mem_flatMap_mpr {α β : Type} (f : α → List β) {x : α} {q : β} :
    ∀ {L : List α}, x ∈ L → q ∈ f x → q ∈ L.flatMap f
  | _ :: l, hx, hq => by
    cases hx with
    | head      => exact mem_append_left _ hq
    | tail _ h' => exact mem_append_right _ (mem_flatMap_mpr f h' hq)

/-- `a :: p` is the head insertion. -/
theorem insEv_head (a : Nat) (p : List Nat) : (a :: p) ∈ insertEverywhere a p := by
  cases p <;> exact List.Mem.head _

/-- `insertEverywhere a` produces every insertion of `a`. -/
theorem insEv_complete (a : Nat) : ∀ (q1 q2 : List Nat),
    (q1 ++ a :: q2) ∈ insertEverywhere a (q1 ++ q2)
  | [],      q2 => insEv_head a q2
  | c :: q1, q2 => List.Mem.tail _ (mem_map_mpr (c :: ·) (insEv_complete a q1 q2))

/-- ★ **Completeness**: every rearrangement of `xs` is enumerated in `permsOf xs`. -/
theorem permsOf_complete : ∀ (xs q : List Nat), LPerm q xs → q ∈ permsOf xs
  | [],      q, h => by
    have hq : q = [] := cnt_eq_zero_nil (fun a => cnt_lperm h)
    subst hq; exact List.Mem.head _
  | a :: ys, q, h => by
    have ha : a ∈ q := LPerm.mem (LPerm.symm h) (List.Mem.head _)
    rcases mem_split q ha with ⟨q1, q2, hq⟩
    subst hq
    have hlp : LPerm (q1 ++ q2) ys := by
      apply lperm_of_cnt_eq
      intro b
      have hc := cnt_lperm h (a := b)
      rw [cnt_append] at hc
      change cnt b q1 + ((if a = b then 1 else 0) + cnt b q2) = (if a = b then 1 else 0) + cnt b ys
        at hc
      rw [Nat.add_left_comm] at hc
      rw [cnt_append]
      exact add_left_cancel' _ hc
    exact mem_flatMap_mpr (insertEverywhere a) (permsOf_complete ys (q1 ++ q2) hlp)
      (insEv_complete a q1 q2)

/-! ## §7 — nodup (`permsOf` has no repeats)

`Nodup L := ∀ a, cnt a L ≤ 1` (clean, no `Pairwise`).  `permsOf xs` is nodup when `xs` is,
because inserting the fresh `a` is recoverable (`removeFirst a`), making the `flatMap` fibers
disjoint and each `insertEverywhere a r` repeat-free. -/

/-- No-repeats, as: every element occurs at most once. -/
def Nodup {α : Type} [DecidableEq α] (L : List α) : Prop := ∀ a, cnt a L ≤ 1

/-- Membership gives a positive count. -/
theorem cnt_pos_of_mem {α : Type} [DecidableEq α] {a : α} : ∀ {L : List α}, a ∈ L → 0 < cnt a L
  | b :: l, h => by
    cases h with
    | head =>
      show 0 < (if a = a then 1 else 0) + cnt a l
      rw [if_pos rfl]; exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right 1 _)
    | tail _ h' =>
      show 0 < (if b = a then 1 else 0) + cnt a l
      exact Nat.lt_of_lt_of_le (cnt_pos_of_mem h') (Nat.le_add_left _ _)

/-- Non-membership gives zero count. -/
theorem cnt_eq_zero_of_not_mem {α : Type} [DecidableEq α] {a : α} {L : List α} (h : a ∉ L) :
    cnt a L = 0 := by
  cases Nat.eq_zero_or_pos (cnt a L) with
  | inl hz => exact hz
  | inr hp => exact absurd (cnt_pos_mem hp) h

/-- `Nodup` is inherited by the tail. -/
theorem nodup_tail {α : Type} [DecidableEq α] {x : α} {L : List α} (h : Nodup (x :: L)) :
    Nodup L := fun a => Nat.le_trans (Nat.le_add_left _ _) (h a)

/-- A nodup `x :: L` has no further `x`. -/
theorem nodup_head_cnt_zero {α : Type} [DecidableEq α] {x : α} {L : List α} (h : Nodup (x :: L)) :
    cnt x L = 0 := by
  have hx := h x
  rw [show cnt x (x :: L) = (if x = x then 1 else 0) + cnt x L from rfl, if_pos rfl] at hx
  cases Nat.eq_zero_or_pos (cnt x L) with
  | inl hz => exact hz
  | inr hp => exact absurd (Nat.le_trans (Nat.add_le_add_left hp 1) hx) (Nat.not_succ_le_self 1)

/-- A nodup `x :: L` has `x ∉ L`. -/
theorem nodup_head_not_mem {α : Type} [DecidableEq α] {x : α} {L : List α} (h : Nodup (x :: L)) :
    x ∉ L := by
  intro hm
  have hp := cnt_pos_of_mem hm
  rw [nodup_head_cnt_zero h] at hp
  exact Nat.lt_irrefl 0 hp

/-- Cons preserves `Nodup` when the head is new. -/
theorem nodup_cons {α : Type} [DecidableEq α] {x : α} {L : List α} (hx : x ∉ L) (hL : Nodup L) :
    Nodup (x :: L) := by
  intro a
  show (if x = a then 1 else 0) + cnt a L ≤ 1
  by_cases hxa : x = a
  · rw [if_pos hxa, cnt_eq_zero_of_not_mem (hxa ▸ hx)]; exact Nat.le_refl 1
  · rw [if_neg hxa, Nat.zero_add]; exact hL a

/-- Counting an in-range value under an injective map: `cnt (f c) (map f L) = cnt c L`. -/
theorem cnt_map_inj_eq {α β : Type} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : ∀ x y, f x = f y → x = y) (c : α) :
    ∀ (L : List α), cnt (f c) (L.map f) = cnt c L
  | []     => rfl
  | d :: l => by
    rw [show cnt (f c) ((d :: l).map f) = (if f d = f c then 1 else 0) + cnt (f c) (l.map f) from rfl,
        show cnt c (d :: l) = (if d = c then 1 else 0) + cnt c l from rfl, cnt_map_inj_eq hf c l]
    by_cases hdc : d = c
    · rw [if_pos hdc, if_pos (congrArg f hdc)]
    · rw [if_neg hdc, if_neg (fun he => hdc (hf d c he))]

/-- An injective `map` preserves `Nodup`. -/
theorem nodup_map {α β : Type} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : ∀ x y, f x = f y → x = y) : ∀ {L : List α}, Nodup L → Nodup (L.map f)
  | [],     _  => fun q => Nat.zero_le _
  | d :: l, hL => fun q => by
    show (if f d = q then 1 else 0) + cnt q (l.map f) ≤ 1
    by_cases hfdq : f d = q
    · rw [if_pos hfdq, ← hfdq, cnt_map_inj_eq hf d l, nodup_head_cnt_zero hL]
      exact Nat.le_refl 1
    · rw [if_neg hfdq, Nat.zero_add]
      exact nodup_map hf (nodup_tail hL) q

/-- Remove the first occurrence of `a`. -/
def removeFirst (a : Nat) : List Nat → List Nat
  | []     => []
  | b :: l => if b = a then l else b :: removeFirst a l

/-- From `a ∉ b :: ys`: `a ≠ b` and `a ∉ ys`. -/
theorem ne_and_not_mem {a b : Nat} {ys : List Nat} (h : a ∉ b :: ys) : a ≠ b ∧ a ∉ ys := by
  constructor
  · intro e; subst e; exact h (List.Mem.head _)
  · intro hm; exact h (List.Mem.tail _ hm)

/-- `removeFirst a` recovers `r` from any insertion of `a` into `r` (when `a ∉ r`). -/
theorem removeFirst_insEv (a : Nat) : ∀ (r : List Nat), a ∉ r → ∀ (q : List Nat),
    q ∈ insertEverywhere a r → removeFirst a q = r
  | [],      _,  q, h => by
    have hq : q = [a] := mem_singleton' h
    subst hq; show (if a = a then [] else a :: removeFirst a []) = []; rw [if_pos rfl]
  | b :: ys, hr, q, h => by
    have hab := ne_and_not_mem hr
    cases h with
    | head =>
      show (if a = a then b :: ys else a :: removeFirst a (b :: ys)) = b :: ys
      rw [if_pos rfl]
    | tail _ hmap =>
      rcases mem_map' _ hmap with ⟨q', hq', hb⟩
      subst hb
      show (if b = a then q' else b :: removeFirst a q') = b :: ys
      rw [if_neg (fun e => hab.1 e.symm), removeFirst_insEv a ys hab.2 q' hq']

/-- `insertEverywhere a r` has no repeats (when `a ∉ r`). -/
theorem nodup_insEv (a : Nat) : ∀ (r : List Nat), a ∉ r → Nodup (insertEverywhere a r)
  | [],      _  => nodup_cons (fun h => by cases h) (fun _ => Nat.zero_le _)
  | b :: ys, hr => by
    have hab := ne_and_not_mem hr
    apply nodup_cons
    · intro hm
      rcases mem_map' _ hm with ⟨x, _, hx⟩
      exact hab.1 (List.cons.inj hx).1.symm
    · exact nodup_map (fun x y hxy => (List.cons.inj hxy).2) (nodup_insEv a ys hab.2)

/-- `flatMap` is nodup when the base is nodup, each fiber is nodup, and a section `s` recovers
    the base index from any fiber element. -/
theorem nodup_flatMap {α β : Type} [DecidableEq α] [DecidableEq β] (g : α → List β) (s : β → α) :
    ∀ (P : List α), Nodup P → (∀ r ∈ P, Nodup (g r)) → (∀ r ∈ P, ∀ q, q ∈ g r → s q = r) →
      Nodup (P.flatMap g)
  | [],      _,  _,  _  => fun _ => Nat.zero_le _
  | r :: P', hP, hg, hs => fun q => by
    show cnt q (g r ++ (P'.flatMap g)) ≤ 1
    rw [cnt_append]
    cases Nat.eq_zero_or_pos (cnt q (g r)) with
    | inl h0 =>
      rw [h0, Nat.zero_add]
      exact nodup_flatMap g s P' (nodup_tail hP)
        (fun r' hr' => hg r' (List.Mem.tail _ hr')) (fun r' hr' => hs r' (List.Mem.tail _ hr')) q
    | inr hpos =>
      have hsq : s q = r := hs r (List.Mem.head _) q (cnt_pos_mem hpos)
      have hzero : cnt q (P'.flatMap g) = 0 := by
        apply cnt_eq_zero_of_not_mem
        intro hmem
        rcases mem_flatMap' g hmem with ⟨r', hr', hqr'⟩
        have hrr : r = r' := hsq ▸ (hs r' (List.Mem.tail _ hr') q hqr')
        exact nodup_head_not_mem hP (hrr.symm ▸ hr')
      rw [hzero]
      exact hg r (List.Mem.head _) q

/-- ★ **`permsOf xs` has no repeats** when `xs` does. -/
theorem nodup_permsOf : ∀ {xs : List Nat}, Nodup xs → Nodup (permsOf xs)
  | [],      _   => nodup_cons (fun h => by cases h) (fun _ => Nat.zero_le _)
  | a :: ys, hxs => by
    have hays : a ∉ ys := nodup_head_not_mem hxs
    have hys : Nodup ys := nodup_tail hxs
    refine nodup_flatMap (insertEverywhere a) (removeFirst a) (permsOf ys)
      (nodup_permsOf hys) ?_ ?_
    · exact fun r hr => nodup_insEv a r (fun hm => hays (LPerm.mem (permsOf_sound ys r hr) hm))
    · exact fun r hr q hq =>
        removeFirst_insEv a r (fun hm => hays (LPerm.mem (permsOf_sound ys r hr) hm)) q hq

/-! ## §8 — `iota` is nodup, and the closure under `swapAt` -/

/-- `cnt` of a singleton. -/
theorem cnt_singleton {α : Type} [DecidableEq α] (a x : α) : cnt a [x] = if x = a then 1 else 0 := by
  show (if x = a then 1 else 0) + cnt a ([] : List α) = if x = a then 1 else 0
  exact Nat.add_zero _

/-- Append-a-fresh-singleton preserves `Nodup`. -/
theorem nodup_append_singleton {α : Type} [DecidableEq α] {x : α} {L : List α}
    (hx : x ∉ L) (hL : Nodup L) : Nodup (L ++ [x]) := by
  intro a
  rw [cnt_append, cnt_singleton]
  by_cases hxa : x = a
  · rw [if_pos hxa, cnt_eq_zero_of_not_mem (hxa ▸ hx), Nat.zero_add]; exact Nat.le_refl 1
  · rw [if_neg hxa, Nat.add_zero]; exact hL a

/-- Every element of `iota n` is `< n`. -/
theorem lt_of_mem_iota : ∀ {n a : Nat}, a ∈ iota n → a < n
  | 0,     _, h => by cases h
  | n + 1, a, h => by
    rcases mem_append' h with h1 | h2
    · exact Nat.lt_succ_of_lt (lt_of_mem_iota h1)
    · rw [mem_singleton' h2]; exact Nat.lt_succ_self n

/-- `n ∉ iota n`. -/
theorem not_mem_iota (n : Nat) : n ∉ iota n := fun h => Nat.lt_irrefl n (lt_of_mem_iota h)

/-- `iota n` has no repeats. -/
theorem nodup_iota : ∀ n, Nodup (iota n)
  | 0     => fun _ => Nat.zero_le _
  | n + 1 => nodup_append_singleton (not_mem_iota n) (nodup_iota n)

/-- `n ≤ 1` and `0 < n` force `n = 1` (propext-free). -/
theorem eq_one_of_le_one_of_pos : ∀ {n : Nat}, n ≤ 1 → 0 < n → n = 1
  | 0,     _, hp => absurd hp (Nat.lt_irrefl 0)
  | 1,     _, _  => rfl
  | _ + 2, h, _  => absurd (Nat.le_of_succ_le_succ h) (Nat.not_succ_le_zero _)

/-- Under `Nodup`, count depends only on the membership status. -/
theorem cnt_eq_of_iff_mem {α : Type} [DecidableEq α] {L : List α} {q q' : α}
    (hnd : Nodup L) (hiff : q ∈ L ↔ q' ∈ L) : cnt q L = cnt q' L := by
  cases Nat.eq_zero_or_pos (cnt q L) with
  | inl h0 =>
    have hq : q ∉ L := fun hm => absurd (h0 ▸ cnt_pos_of_mem hm) (Nat.lt_irrefl 0)
    rw [h0, cnt_eq_zero_of_not_mem (fun h => hq (hiff.mpr h))]
  | inr hp =>
    rw [eq_one_of_le_one_of_pos (hnd q) hp,
        eq_one_of_le_one_of_pos (hnd q') (cnt_pos_of_mem (hiff.mp (cnt_pos_mem hp)))]

/-- ★★★ **The enumeration is closed under an adjacent position-swap** (up to `LPerm`). -/
theorem perms_swap_closed (n k : Nat) : LPerm ((perms n).map (swapAt k)) (perms n) := by
  apply lperm_of_cnt_eq
  intro q
  rw [cnt_map_inv (swapAt k) (swapAt_invol k) q (perms n)]
  refine cnt_eq_of_iff_mem (nodup_permsOf (nodup_iota n)) ?_
  constructor
  · exact fun hm => permsOf_complete (iota n) q
      (LPerm.trans (LPerm.symm (swapAt_lperm k q)) (permsOf_sound (iota n) _ hm))
  · exact fun hm => permsOf_complete (iota n) (swapAt k q)
      (LPerm.trans (swapAt_lperm k q) (permsOf_sound (iota n) q hm))

end E213.Lib.Math.Linalg213.PermClosure
