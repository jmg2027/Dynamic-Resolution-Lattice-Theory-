import E213.Lib.Math.Algebra.Linalg213.Permutation
import E213.Meta.Tactic.List213
import E213.Meta.Int213.Core

/-!
# Linalg213 — the permutation enumeration realizes the symmetric-group action

The gate for the Leibniz determinant's **alternating** property: the enumeration
`perms n` is closed (up to `LPerm`) under an adjacent position-swap `swapAt k`, and every
listed permutation is a genuine rearrangement of `[0,…,n−1]` (sound) with no repeats (nodup).

The closure is built bottom-up: clean (∅-axiom) `List` membership helpers → `LPerm`
structural lemmas → enumeration **soundness** (each output is a rearrangement) →
completeness, nodup, and the swap-closure itself, then `leibDet_rowSwap` (alternating),
equal-rows-vanish, multilinearity, and the degeneracy corollaries.

The core `List.mem_*` iff-lemmas are `propext`/`Quot.sound`-tainted, so membership is done
structurally on the `List.Mem` constructors.  All ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.Linalg213.PermClosure

open E213.Lib.Math.Algebra.Linalg213.Permutation
  (LPerm insertEverywhere permsOf perms iota swapAt swapAt_lperm swapAt_prefix
   sumZ sumZ_lperm sumZ_map_neg map_lperm leibTerm leibDet rowSwapAt leibTerm_rowSwap
   prodDiagFrom psign rowSwapAt_other rowSwapAt_at prodDiagFrom_append)
open E213.Tactic.List213 (length_append)

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

/-! ## §9 — the alternating property (adjacent row swap negates `leibDet`)

Clean `List` helpers (core's are `propext`-tainted), the split of a permutation at position
`k`, and the assembly: each term negates (`leibTerm_rowSwap` on the split), `sumZ_map_neg`
factors the sign, and `perms_swap_closed` reindexes the sum — so `leibDet (rowSwapAt k M) =
−leibDet M`. -/

/-- `map` fusion (∅-axiom). -/
theorem map_map' {α β γ : Type} (f : α → β) (g : β → γ) :
    ∀ (L : List α), (L.map f).map g = L.map (fun x => g (f x))
  | []     => rfl
  | a :: l => by
    show g (f a) :: (l.map f).map g = g (f a) :: l.map (fun x => g (f x))
    rw [map_map' f g l]

/-- `map` congruence on members (∅-axiom). -/
theorem map_eq_of_mem {α β : Type} (f g : α → β) : ∀ {L : List α},
    (∀ x ∈ L, f x = g x) → L.map f = L.map g
  | [],     _ => rfl
  | a :: l, h => by
    show f a :: l.map f = g a :: l.map g
    rw [h a (List.Mem.head _), map_eq_of_mem f g (fun x hx => h x (List.Mem.tail _ hx))]

/-- `(iota n).length = n`. -/
theorem length_iota : ∀ n, (iota n).length = n
  | 0     => rfl
  | n + 1 => by
    show (iota n ++ [n]).length = n + 1
    rw [length_append (iota n) [n], length_iota n, show ([n] : List Nat).length = 1 from rfl]

/-- `LPerm` carries `Nodup` backward. -/
theorem nodup_of_lperm {α : Type} [DecidableEq α] {p L : List α} (h : LPerm p L) (hL : Nodup L) :
    Nodup p := fun a => Nat.le_trans (Nat.le_of_eq (cnt_lperm h)) (hL a)

/-- In a nodup `pre ++ y :: x :: l`, the two adjacent entries differ. -/
theorem ne_of_nodup_adjacent {pre : List Nat} {y x : Nat} {l : List Nat}
    (h : Nodup (pre ++ y :: x :: l)) : x ≠ y := by
  intro e
  have hc := h y
  rw [cnt_append] at hc
  change cnt y pre + ((if y = y then 1 else 0) + ((if x = y then 1 else 0) + cnt y l)) ≤ 1 at hc
  rw [if_pos rfl, if_pos e] at hc
  have h2 : 1 + 1 ≤ 1 :=
    Nat.le_trans (Nat.add_le_add_left (Nat.le_add_right 1 (cnt y l)) 1)
      (Nat.le_trans (Nat.le_add_left _ (cnt y pre)) hc)
  exact absurd h2 (Nat.not_succ_le_self 1)

/-- Split a list at position `k` (when `k+1 < length`). -/
theorem split_at : ∀ (p : List Nat) (k : Nat), k + 1 < p.length →
    ∃ pre y x l, p = pre ++ y :: x :: l ∧ pre.length = k
  | [],          _,     h => absurd h (Nat.not_lt_zero _)
  | [_],         _,     h => absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero _)
  | a :: b :: p', 0,    _ => ⟨[], a, b, p', rfl, rfl⟩
  | a :: b :: p', k + 1, h => by
    rcases split_at (b :: p') k (Nat.lt_of_succ_lt_succ h) with ⟨pre, y, x, l, he, hl⟩
    exact ⟨a :: pre, y, x, l, congrArg (a :: ·) he, congrArg (· + 1) hl⟩

/-- The per-term identity for a genuine permutation `p ∈ perms n` (decomposed at position `k`). -/
theorem leibTerm_rowSwap_mem (M : Nat → Nat → Int) (n k : Nat) (hk : k + 1 < n)
    (p : List Nat) (hp : p ∈ perms n) :
    leibTerm (rowSwapAt k M) p = - leibTerm M (swapAt k p) := by
  have hsound : LPerm p (iota n) := permsOf_sound (iota n) p hp
  have hlen : p.length = n := (LPerm.length_eq hsound).trans (length_iota n)
  have hnd : Nodup p := nodup_of_lperm hsound (nodup_iota n)
  rcases split_at p k (hlen ▸ hk) with ⟨pre, y, x, l, he, hl⟩
  subst he
  rw [← hl, swapAt_prefix]
  exact leibTerm_rowSwap M pre l (ne_of_nodup_adjacent hnd)

/-- ★★★ **The alternating property**: an adjacent row swap negates the Leibniz determinant. -/
theorem leibDet_rowSwap (M : Nat → Nat → Int) (n k : Nat) (hk : k + 1 < n) :
    leibDet n (rowSwapAt k M) = - leibDet n M := by
  show sumZ ((perms n).map (leibTerm (rowSwapAt k M))) = - sumZ ((perms n).map (leibTerm M))
  rw [map_eq_of_mem (leibTerm (rowSwapAt k M)) (fun p => - leibTerm M (swapAt k p))
        (fun p hp => leibTerm_rowSwap_mem M n k hk p hp),
      sumZ_map_neg (fun p => leibTerm M (swapAt k p)) (perms n)]
  congr 1
  rw [(map_map' (swapAt k) (leibTerm M) (perms n)).symm]
  exact sumZ_lperm (map_lperm (leibTerm M) (perms_swap_closed n k))

/-! ## §10 — equal adjacent rows ⟹ `leibDet = 0` -/

/-- `prodDiagFrom` respects pointwise matrix equality. -/
theorem prodDiagFrom_congr {M M' : Nat → Nat → Int} (h : ∀ r c, M r c = M' r c) :
    ∀ (i : Nat) (p : List Nat), prodDiagFrom M i p = prodDiagFrom M' i p
  | _, []      => rfl
  | i, a :: ps => by
    show M i a * prodDiagFrom M (i + 1) ps = M' i a * prodDiagFrom M' (i + 1) ps
    rw [h i a, prodDiagFrom_congr h (i + 1) ps]

/-- `leibDet` respects pointwise matrix equality. -/
theorem leibDet_congr (n : Nat) {M M' : Nat → Nat → Int} (h : ∀ r c, M r c = M' r c) :
    leibDet n M = leibDet n M' := by
  show sumZ ((perms n).map (leibTerm M)) = sumZ ((perms n).map (leibTerm M'))
  rw [map_eq_of_mem (leibTerm M) (leibTerm M') (fun p _ => by
    show psign p * prodDiagFrom M 0 p = psign p * prodDiagFrom M' 0 p
    rw [prodDiagFrom_congr h 0 p])]

/-- Equal rows `k, k+1` make `rowSwapAt k M` agree with `M` pointwise. -/
theorem rowSwapAt_eq_of_rows_eq (M : Nat → Nat → Int) (k : Nat)
    (hrows : ∀ c, M k c = M (k + 1) c) (r c : Nat) : rowSwapAt k M r c = M r c := by
  show (if r = k then M (k + 1) c else if r = k + 1 then M k c else M r c) = M r c
  by_cases h1 : r = k
  · rw [if_pos h1, h1]; exact (hrows c).symm
  · rw [if_neg h1]
    by_cases h2 : r = k + 1
    · rw [if_pos h2, h2]; exact hrows c
    · rw [if_neg h2]

/-- ★★★ **Two equal adjacent rows ⟹ the Leibniz determinant vanishes.** -/
theorem leibDet_eq_zero_of_rows_eq (M : Nat → Nat → Int) (n k : Nat) (hk : k + 1 < n)
    (hrows : ∀ c, M k c = M (k + 1) c) : leibDet n M = 0 :=
  E213.Meta.Int213.int_eq_zero_of_eq_neg
    ((leibDet_congr n (rowSwapAt_eq_of_rows_eq M k hrows)).symm.trans (leibDet_rowSwap M n k hk))

/-! ## §11 — general equal rows (any gap) ⟹ `leibDet = 0` -/

/-- Rows `a` and `a+d+1` equal ⟹ `leibDet = 0`.  Induction on the gap `d`: swap the adjacent
    rows just below the lower one, shrinking the gap by one (the lower row keeps matching). -/
theorem leibDet_rows_eq_gap (n : Nat) : ∀ (d a : Nat) (M : Nat → Nat → Int),
    a + d + 1 < n → (∀ c, M a c = M (a + d + 1) c) → leibDet n M = 0
  | 0,     a, M, hk, hrows => leibDet_eq_zero_of_rows_eq M n a hk hrows
  | d + 1, a, M, hk, hrows => by
    have hne0 : a ≠ a + d + 1 := Nat.ne_of_lt (Nat.lt_add_of_pos_right (Nat.succ_pos d))
    have hne1 : a ≠ (a + d + 1) + 1 := Nat.ne_of_lt (Nat.lt_add_of_pos_right (Nat.succ_pos (d + 1)))
    have hrows' : ∀ c, (rowSwapAt (a + d + 1) M) a c = (rowSwapAt (a + d + 1) M) (a + d + 1) c := by
      intro c
      rw [rowSwapAt_other (a + d + 1) M hne0 hne1 c, rowSwapAt_at (a + d + 1) M c]
      exact hrows c
    have hlt : a + d + 1 < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_of_lt hk)
    have hz : leibDet n (rowSwapAt (a + d + 1) M) = 0 :=
      leibDet_rows_eq_gap n d a (rowSwapAt (a + d + 1) M) hlt hrows'
    have hswap := leibDet_rowSwap M n (a + d + 1) hk
    have heq : - leibDet n M = 0 := hswap.symm.trans hz
    exact ((Int.neg_neg (leibDet n M)).symm).trans (congrArg Neg.neg heq)

/-- ★ **Any two equal rows ⟹ `leibDet = 0`** (general form). -/
theorem leibDet_eq_zero_of_two_rows_eq (M : Nat → Nat → Int) (n a b : Nat)
    (hab : a < b) (hb : b < n) (hrows : ∀ c, M a c = M b c) : leibDet n M = 0 := by
  obtain ⟨d, hd⟩ := Nat.le.dest hab
  have hbd : a + d + 1 = b := by rw [Nat.add_right_comm]; exact hd
  exact leibDet_rows_eq_gap n d a M (hbd.symm ▸ hb) (fun c => hbd.symm ▸ hrows c)

/-! ## §12 — multilinearity of `leibDet` (linear in each row) -/

/-- Replace row `i` of `M` by the vector `r`. -/
def setRow (i : Nat) (r : Nat → Int) (M : Nat → Nat → Int) : Nat → Nat → Int :=
  fun a c => if a = i then r c else M a c

theorem setRow_off (i : Nat) (r : Nat → Int) (M : Nat → Nat → Int) {a : Nat} (h : a ≠ i) (c : Nat) :
    setRow i r M a c = M a c := by show (if a = i then r c else M a c) = M a c; rw [if_neg h]

theorem setRow_at (i : Nat) (r : Nat → Int) (M : Nat → Nat → Int) (c : Nat) :
    setRow i r M i c = r c := by show (if i = i then r c else M i c) = r c; rw [if_pos rfl]

/-- Below row `i`: `setRow` leaves `prodDiagFrom` unchanged. -/
theorem prodDiagFrom_setRow_below (i : Nat) (r : Nat → Int) (M : Nat → Nat → Int) :
    ∀ (j : Nat) (p : List Nat), j + p.length ≤ i →
      prodDiagFrom (setRow i r M) j p = prodDiagFrom M j p
  | _, [],      _ => rfl
  | j, q :: qs, h => by
    have hji : j < i := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.succ_pos qs.length)) h
    have hle : (j + 1) + qs.length ≤ i := by rw [Nat.add_assoc, Nat.add_comm 1 qs.length]; exact h
    show setRow i r M j q * prodDiagFrom (setRow i r M) (j + 1) qs = M j q * prodDiagFrom M (j + 1) qs
    rw [setRow_off i r M (Nat.ne_of_lt hji) q, prodDiagFrom_setRow_below i r M (j + 1) qs hle]

/-- Above row `i`: `setRow` leaves `prodDiagFrom` unchanged. -/
theorem prodDiagFrom_setRow_above (i : Nat) (r : Nat → Int) (M : Nat → Nat → Int) :
    ∀ (j : Nat) (p : List Nat), i < j → prodDiagFrom (setRow i r M) j p = prodDiagFrom M j p
  | _, [],      _ => rfl
  | j, q :: qs, h => by
    show setRow i r M j q * prodDiagFrom (setRow i r M) (j + 1) qs = M j q * prodDiagFrom M (j + 1) qs
    rw [setRow_off i r M (Ne.symm (Nat.ne_of_lt h)) q,
        prodDiagFrom_setRow_above i r M (j + 1) qs (Nat.lt_succ_of_lt h)]

/-- Split a list at position `i` (single element). -/
theorem split_at1 : ∀ (p : List Nat) (i : Nat), i < p.length →
    ∃ pre x l, p = pre ++ x :: l ∧ pre.length = i
  | [],      _,     h => absurd h (Nat.not_lt_zero _)
  | a :: p', 0,     _ => ⟨[], a, p', rfl, rfl⟩
  | a :: p', i + 1, h => by
    rcases split_at1 p' i (Nat.lt_of_succ_lt_succ h) with ⟨pre, x, l, he, hl⟩
    exact ⟨a :: pre, x, l, congrArg (a :: ·) he, congrArg (· + 1) hl⟩

/-- The diagonal product factors the row-`i` entry out linearly (after splitting `p` at `i`). -/
theorem prodDiagFrom_setRow_split (i : Nat) (r : Nat → Int) (M : Nat → Nat → Int)
    (pre : List Nat) (x : Nat) (l : List Nat) (hpre : pre.length = i) :
    prodDiagFrom (setRow i r M) 0 (pre ++ x :: l)
      = prodDiagFrom M 0 pre * (r x * prodDiagFrom M (i + 1) l) := by
  subst hpre
  rw [prodDiagFrom_append (setRow pre.length r M) 0 pre (x :: l),
      prodDiagFrom_setRow_below pre.length r M 0 pre (Nat.le_of_eq (Nat.zero_add pre.length)),
      Nat.zero_add]
  show prodDiagFrom M 0 pre * (setRow pre.length r M pre.length x *
         prodDiagFrom (setRow pre.length r M) (pre.length + 1) l)
     = prodDiagFrom M 0 pre * (r x * prodDiagFrom M (pre.length + 1) l)
  rw [setRow_at, prodDiagFrom_setRow_above pre.length r M (pre.length + 1) l (Nat.lt_succ_self _)]

/-- Every `p ∈ perms n` has length `n`. -/
theorem perm_length {n : Nat} {p : List Nat} (hp : p ∈ perms n) : p.length = n :=
  (LPerm.length_eq (permsOf_sound (iota n) p hp)).trans (length_iota n)

/-- A `leibTerm` is additive in row `i` (for a permutation reaching row `i`). -/
theorem leibTerm_setRow_add (i : Nat) (r1 r2 : Nat → Int) (M : Nat → Nat → Int) (p : List Nat)
    (hp : i < p.length) :
    leibTerm (setRow i (fun c => r1 c + r2 c) M) p
      = leibTerm (setRow i r1 M) p + leibTerm (setRow i r2 M) p := by
  rcases split_at1 p i hp with ⟨pre, x, l, he, hl⟩
  subst he
  show psign (pre ++ x :: l) * prodDiagFrom (setRow i (fun c => r1 c + r2 c) M) 0 (pre ++ x :: l)
     = psign (pre ++ x :: l) * prodDiagFrom (setRow i r1 M) 0 (pre ++ x :: l)
       + psign (pre ++ x :: l) * prodDiagFrom (setRow i r2 M) 0 (pre ++ x :: l)
  rw [prodDiagFrom_setRow_split i (fun c => r1 c + r2 c) M pre x l hl,
      prodDiagFrom_setRow_split i r1 M pre x l hl, prodDiagFrom_setRow_split i r2 M pre x l hl]
  ring_intZ

/-- A `leibTerm` is scalar-homogeneous in row `i`. -/
theorem leibTerm_setRow_smul (i : Nat) (a : Int) (r : Nat → Int) (M : Nat → Nat → Int)
    (p : List Nat) (hp : i < p.length) :
    leibTerm (setRow i (fun c => a * r c) M) p = a * leibTerm (setRow i r M) p := by
  rcases split_at1 p i hp with ⟨pre, x, l, he, hl⟩
  subst he
  show psign (pre ++ x :: l) * prodDiagFrom (setRow i (fun c => a * r c) M) 0 (pre ++ x :: l)
     = a * (psign (pre ++ x :: l) * prodDiagFrom (setRow i r M) 0 (pre ++ x :: l))
  rw [prodDiagFrom_setRow_split i (fun c => a * r c) M pre x l hl,
      prodDiagFrom_setRow_split i r M pre x l hl]
  ring_intZ

/-- A pointwise-sum maps to a sum of sums. -/
theorem sumZ_map_add {α : Type} (f g : α → Int) : ∀ (L : List α),
    sumZ (L.map (fun a => f a + g a)) = sumZ (L.map f) + sumZ (L.map g)
  | []     => rfl
  | a :: l => by
    show (f a + g a) + sumZ (l.map (fun a => f a + g a))
       = (f a + sumZ (l.map f)) + (g a + sumZ (l.map g))
    rw [sumZ_map_add f g l]; ring_intZ

/-- A pointwise-scalar maps to a scaled sum. -/
theorem sumZ_map_smul {α : Type} (c : Int) (f : α → Int) : ∀ (L : List α),
    sumZ (L.map (fun a => c * f a)) = c * sumZ (L.map f)
  | []     => ((E213.Meta.Int213.mul_comm c 0).trans (E213.Meta.Int213.zero_mul c)).symm
  | a :: l => by
    show c * f a + sumZ (l.map (fun a => c * f a)) = c * (f a + sumZ (l.map f))
    rw [sumZ_map_smul c f l]; ring_intZ

/-- ★ **`leibDet` is additive in any row.** -/
theorem leibDet_setRow_add (n i : Nat) (hi : i < n) (r1 r2 : Nat → Int) (M : Nat → Nat → Int) :
    leibDet n (setRow i (fun c => r1 c + r2 c) M)
      = leibDet n (setRow i r1 M) + leibDet n (setRow i r2 M) := by
  show sumZ ((perms n).map (leibTerm (setRow i (fun c => r1 c + r2 c) M))) = _
  rw [map_eq_of_mem (leibTerm (setRow i (fun c => r1 c + r2 c) M))
        (fun p => leibTerm (setRow i r1 M) p + leibTerm (setRow i r2 M) p)
        (fun p hp => leibTerm_setRow_add i r1 r2 M p ((perm_length hp).symm ▸ hi))]
  exact sumZ_map_add (leibTerm (setRow i r1 M)) (leibTerm (setRow i r2 M)) (perms n)

/-- ★ **`leibDet` is scalar-homogeneous in any row.** -/
theorem leibDet_setRow_smul (n i : Nat) (hi : i < n) (a : Int) (r : Nat → Int) (M : Nat → Nat → Int) :
    leibDet n (setRow i (fun c => a * r c) M) = a * leibDet n (setRow i r M) := by
  show sumZ ((perms n).map (leibTerm (setRow i (fun c => a * r c) M))) = _
  rw [map_eq_of_mem (leibTerm (setRow i (fun c => a * r c) M))
        (fun p => a * leibTerm (setRow i r M) p)
        (fun p hp => leibTerm_setRow_smul i a r M p ((perm_length hp).symm ▸ hi))]
  exact sumZ_map_smul a (leibTerm (setRow i r M)) (perms n)

/-! ## §13 — degeneracy corollaries (singular ⟹ `leibDet = 0`) -/

/-- Two equal rows at *any* distinct positions ⟹ `leibDet = 0`. -/
theorem leibDet_rows_eq_ne (M : Nat → Nat → Int) (n i j : Nat) (hij : i ≠ j) (hi : i < n) (hj : j < n)
    (hrows : ∀ c, M i c = M j c) : leibDet n M = 0 := by
  rcases Nat.lt_or_ge i j with h | h
  · exact leibDet_eq_zero_of_two_rows_eq M n i j h hj hrows
  · exact leibDet_eq_zero_of_two_rows_eq M n j i (Nat.lt_of_le_of_ne h (fun e => hij e.symm)) hi
      (fun c => (hrows c).symm)

/-- ★ **Proportional rows ⟹ `leibDet = 0`.**  Row `i = a · row j` (`i ≠ j`). -/
theorem leibDet_proportional_rows (n i j : Nat) (hij : i ≠ j) (hi : i < n) (hj : j < n) (a : Int)
    (M : Nat → Nat → Int) (hp : ∀ c, M i c = a * M j c) : leibDet n M = 0 := by
  have e1 : leibDet n M = leibDet n (setRow i (fun c => a * M j c) M) :=
    leibDet_congr n (fun b c => by
      by_cases hb : b = i
      · subst hb; rw [setRow_at]; exact hp c
      · rw [setRow_off i _ M hb c])
  rw [e1, leibDet_setRow_smul n i hi a (fun c => M j c) M,
      leibDet_rows_eq_ne (setRow i (fun c => M j c) M) n i j hij hi hj (fun c => by
        rw [setRow_at, setRow_off i _ M (Ne.symm hij)]),
      E213.Meta.Int213.mul_comm, E213.Meta.Int213.zero_mul]

/-- ★ **A zero row ⟹ `leibDet = 0`.** -/
theorem leibDet_zero_row (n i : Nat) (hi : i < n) (M : Nat → Nat → Int) (hz : ∀ c, M i c = 0) :
    leibDet n M = 0 := by
  have e1 : leibDet n M = leibDet n (setRow i (fun c => (0 : Int) * M i c) M) :=
    leibDet_congr n (fun b c => by
      by_cases hb : b = i
      · subst hb; rw [setRow_at, E213.Meta.Int213.zero_mul]; exact hz c
      · rw [setRow_off i _ M hb c])
  rw [e1, leibDet_setRow_smul n i hi 0 (fun c => M i c) M, E213.Meta.Int213.zero_mul]

end E213.Lib.Math.Algebra.Linalg213.PermClosure
