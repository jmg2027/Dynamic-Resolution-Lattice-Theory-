import E213.Lib.Math.Combinatorics.Sperner

/-!
# Sperner's theorem — the geometric chain model (discharging the rung)

Instantiates `Sperner.sperner_upper_bound` with the concrete chain model:
maximal chains of `2^[n]` are the orderings of the positions `[0..n−1]`
(`perms (idxList n)`), and `inc A c` holds iff the first `|A|` positions of the
chain `c` form exactly the set `A`.  Proving the two hypotheses — `hcap` (≤ 1
antichain member per chain, from prefix-set nesting) and `hlow` (≥ `k!·(n−k)!`
chains through a size-`k` member, from the `truePos ++ falsePos` injection) —
closes the *named* Sperner upper bound unconditionally.
-/

namespace E213.Lib.Math.Combinatorics.SpernerChains

open E213.Lib.Math.Combinatorics.Sperner
open E213.Lib.Math.Combinatorics.Permutations
open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Tactic.List213
  (length_append mem_append_iff nodup_append mem_map_of_mem exists_of_mem_map
   nodup_map_of_inj mem_filter_of nodup_length_le_of_subset)

/-! ## §1 — the model -/

/-- The position list `[0, 1, …, n−1]`. -/
def idxList : Nat → List Nat
  | 0 => []
  | n + 1 => idxList n ++ [n]

theorem idxList_length : ∀ n, (idxList n).length = n
  | 0 => rfl
  | n + 1 => by
      show (idxList n ++ [n]).length = n + 1
      rw [length_append, idxList_length n]; rfl

/-- `Bool` membership of a `Nat` in a `List Nat`. -/
def elemNat (a : Nat) : List Nat → Bool
  | [] => false
  | x :: xs => Nat.beq x a || elemNat a xs

/-- `elemTake i c k`: is `i` among the first `k` entries of `c`? -/
def elemTake (i : Nat) : List Nat → Nat → Bool
  | [], _ => false
  | _ :: _, 0 => false
  | x :: xs, k + 1 => Nat.beq x i || elemTake i xs k

theorem elemTake_nil (i k : Nat) : elemTake i [] k = false := rfl

theorem elemTake_zero (i : Nat) : ∀ c, elemTake i c 0 = false
  | [] => rfl
  | _ :: _ => rfl

/-- Being among the first `a` extends to the first `b ≥ a`. -/
theorem elemTake_mono (i : Nat) :
    ∀ (c : List Nat) (a b : Nat), a ≤ b → elemTake i c a = true → elemTake i c b = true
  | c, 0, _, _, h => by rw [elemTake_zero i c] at h; exact Bool.noConfusion h
  | [], _ + 1, _, _, h => by rw [elemTake_nil] at h; exact Bool.noConfusion h
  | x :: xs, a' + 1, b, hab, h => by
      cases b with
      | zero => exact absurd hab (Nat.not_succ_le_zero a')
      | succ b' =>
          show (Nat.beq x i || elemTake i xs b') = true
          have h' : (Nat.beq x i || elemTake i xs a') = true := h
          cases hbx : Nat.beq x i with
          | true => rfl
          | false =>
              rw [hbx] at h'
              exact elemTake_mono i xs a' b' (Nat.le_of_succ_le_succ hab) h'

/-- `Bool` equality. -/
def boolEq : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | _, _ => false

/-- `Bool`-list equality. -/
def beqBoolList : List Bool → List Bool → Bool
  | [], [] => true
  | x :: xs, y :: ys => boolEq x y && beqBoolList xs ys
  | _, _ => false

theorem beqBoolList_refl : ∀ l, beqBoolList l l = true
  | [] => rfl
  | x :: xs => by
      show (boolEq x x && beqBoolList xs xs) = true
      rw [beqBoolList_refl xs]; cases x <;> rfl

theorem eq_of_beqBoolList : ∀ (x y : List Bool), beqBoolList x y = true → x = y
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | a :: xs, b :: ys, h => by
      cases a <;> cases b <;>
        first
          | exact Bool.noConfusion h
          | (rw [eq_of_beqBoolList xs ys h])

/-- The size-`k` prefix-set of a chain `c`, as a length-`n` `Bool` vector. -/
def prefixVec (n : Nat) (c : List Nat) (k : Nat) : List Bool :=
  (idxList n).map (fun i => elemTake i c k)

/-- `inc A c`: the size-`|A|` prefix-set of chain `c` equals `A`. -/
def inc (n : Nat) (A : List Bool) (c : List Nat) : Bool :=
  beqBoolList (prefixVec n c (cardB A)) A

/-! ## §2 — the easy hypotheses -/

/-- `#chains = n!`. -/
theorem chains_length (n : Nat) : (perms (idxList n)).length = fact n := by
  rw [perms_length, idxList_length]

/-- `|A| ≤ |A|` as a list — `cardB` counts a subset of the entries. -/
theorem cardB_le_length : ∀ l, cardB l ≤ l.length
  | [] => Nat.le_refl 0
  | true :: l => Nat.succ_le_succ (cardB_le_length l)
  | false :: l => Nat.le_succ_of_le (cardB_le_length l)

/-! ## §3 — `hcap`: prefix-set nesting ⟹ ≤ 1 antichain member per chain -/

theorem impl_of {p q : Bool} (h : p = true → q = true) : impl p q = true := by
  cases p with
  | false => rfl
  | true => exact h rfl

theorem subseteqB_map {α : Type _} (f g : α → Bool) (h : ∀ x, impl (f x) (g x) = true) :
    ∀ (L : List α), subseteqB (L.map f) (L.map g) = true
  | [] => rfl
  | x :: xs => by
      show (impl (f x) (g x) && subseteqB (xs.map f) (xs.map g)) = true
      rw [h x, subseteqB_map f g h xs]; rfl

/-- The size-`a` prefix-set sits inside the size-`b` one for `a ≤ b`. -/
theorem prefixVec_subseteq {n : Nat} {c : List Nat} {a b : Nat} (hab : a ≤ b) :
    subseteqB (prefixVec n c a) (prefixVec n c b) = true :=
  subseteqB_map _ _ (fun i => impl_of (elemTake_mono i c a b hab)) (idxList n)

theorem lcount_eq_zero {β : Type _} {p : β → Bool} :
    ∀ {L : List β}, (∀ x, x ∈ L → p x = false) → lcount p L = 0
  | [], _ => rfl
  | a :: l, h => by
      show ((bif p a then 1 else 0) + lcount p l) = 0
      rw [h a (List.Mem.head _)]
      show (0 + lcount p l) = 0
      rw [Nat.zero_add, lcount_eq_zero (fun x hx => h x (List.Mem.tail _ hx))]

theorem lcount_le_one_of {β : Type _} {p : β → Bool} :
    ∀ {L : List β},
      (∀ A, A ∈ L → ∀ B, B ∈ L → p A = true → p B = true → A = B) → L.Nodup →
      lcount p L ≤ 1
  | [], _, _ => Nat.zero_le 1
  | a :: l, huniq, hnd => by
      have haL : a ∉ l := by cases hnd with | cons hh _ => exact fun hm => (hh a hm) rfl
      have hnd' : l.Nodup := by cases hnd with | cons _ ht => exact ht
      show ((bif p a then 1 else 0) + lcount p l) ≤ 1
      cases hpa : p a with
      | false =>
          show (0 + lcount p l) ≤ 1
          rw [Nat.zero_add]
          exact lcount_le_one_of
            (fun A hA B hB => huniq A (List.Mem.tail _ hA) B (List.Mem.tail _ hB)) hnd'
      | true =>
          have hz : lcount p l = 0 := lcount_eq_zero (fun x hx => by
            cases hpx : p x with
            | false => rfl
            | true =>
                have hax : a = x := huniq a (List.Mem.head _) x (List.Mem.tail _ hx) hpa hpx
                exact absurd (hax.symm ▸ hx) haL)
          show (1 + lcount p l) ≤ 1
          rw [hz]; exact Nat.le_refl 1

/-- Two members incident to the same chain are comparable (prefix-sets nest). -/
theorem inc_comparable {n : Nat} (A B : List Bool) (c : List Nat)
    (hA : inc n A c = true) (hB : inc n B c = true) : comparable A B = true := by
  have heqA : prefixVec n c (cardB A) = A := eq_of_beqBoolList _ _ hA
  have heqB : prefixVec n c (cardB B) = B := eq_of_beqBoolList _ _ hB
  show (subseteqB A B || subseteqB B A) = true
  rcases Nat.le_total (cardB A) (cardB B) with hab | hba
  · have hs : subseteqB A B = true := by rw [← heqA, ← heqB]; exact prefixVec_subseteq hab
    rw [hs]; rfl
  · have hs : subseteqB B A = true := by rw [← heqA, ← heqB]; exact prefixVec_subseteq hba
    rw [hs]; cases subseteqB A B <;> rfl

/-- ★ **`hcap`**: each chain meets the antichain at most once. -/
theorem chain_cap {n : Nat} (F : List (List Bool)) (hF : IsAntichain F) (hnd : F.Nodup) :
    ∀ c, c ∈ perms (idxList n) → lcount (fun A => inc n A c) F ≤ 1 := by
  intro c _
  refine lcount_le_one_of ?_ hnd
  intro A hA B hB hpA hpB
  have hcomp := inc_comparable A B c hpA hpB
  cases (inferInstance : Decidable (A = B)) with
  | isTrue h => exact h
  | isFalse h => exact Bool.noConfusion ((hF A hA B hB h) ▸ hcomp)

/-! ## §4 — `hlow`: the `k!·(n−k)!` chain count

The chains through `A` are the orderings of `A`'s true-positions followed by the
orderings of its false-positions.  This section builds that split. -/

/-- Move `a` across a prefix: `a :: (X ++ Y) ~ X ++ a :: Y`. -/
theorem lperm_cons_append {α : Type _} (a : α) :
    ∀ (X Y : List α), LPerm (a :: (X ++ Y)) (X ++ a :: Y)
  | [], _ => LPerm.refl _
  | x :: X', Y =>
      LPerm.trans (LPerm.swap x a (X' ++ Y)) (LPerm.cons x (lperm_cons_append a X' Y))

/-- The positions where `A` is `true` (read off the parallel list `ps`). -/
def truePos : List Bool → List Nat → List Nat
  | true :: A, p :: ps => p :: truePos A ps
  | false :: A, p :: ps => truePos A ps
  | _, _ => []

/-- The positions where `A` is `false`. -/
def falsePos : List Bool → List Nat → List Nat
  | false :: A, p :: ps => p :: falsePos A ps
  | true :: A, p :: ps => falsePos A ps
  | _, _ => []

/-- `truePos ++ falsePos` re-permutes the position list. -/
theorem truePos_falsePos_perm :
    ∀ (A : List Bool) (ps : List Nat), A.length = ps.length →
      LPerm ps (truePos A ps ++ falsePos A ps)
  | [], [], _ => LPerm.nil
  | true :: A, p :: ps, hlen =>
      LPerm.cons p (truePos_falsePos_perm A ps (Nat.succ.inj hlen))
  | false :: A, p :: ps, hlen =>
      LPerm.trans (LPerm.cons p (truePos_falsePos_perm A ps (Nat.succ.inj hlen)))
        (lperm_cons_append p (truePos A ps) (falsePos A ps))
  | [], _ :: _, hlen => Nat.noConfusion hlen
  | _ :: _, [], hlen => Nat.noConfusion hlen

/-- `|truePos A ps| = |A|` (the count of `true`s). -/
theorem truePos_length :
    ∀ (A : List Bool) (ps : List Nat), A.length = ps.length → (truePos A ps).length = cardB A
  | [], [], _ => rfl
  | true :: A, p :: ps, hlen => by
      show (p :: truePos A ps).length = cardB A + 1
      rw [List.length_cons, truePos_length A ps (Nat.succ.inj hlen)]
  | false :: A, p :: ps, hlen => truePos_length A ps (Nat.succ.inj hlen)
  | [], _ :: _, hlen => Nat.noConfusion hlen
  | _ :: _, [], hlen => Nat.noConfusion hlen

/-- Propext-free `(n+1) − m = (n − m) + 1` for `m ≤ n`. -/
private theorem succ_sub_clean : ∀ {m n : Nat}, m ≤ n → (n + 1) - m = (n - m) + 1
  | 0, n, _ => by rw [Nat.sub_zero, Nat.sub_zero]
  | m + 1, n, h => by
      cases n with
      | zero => exact absurd h (Nat.not_succ_le_zero m)
      | succ n' =>
          rw [Nat.succ_sub_succ_eq_sub, Nat.succ_sub_succ_eq_sub]
          exact succ_sub_clean (Nat.le_of_succ_le_succ h)

/-- `|falsePos A ps| = |A| − cardB A` (the count of `false`s). -/
theorem falsePos_length :
    ∀ (A : List Bool) (ps : List Nat), A.length = ps.length →
      (falsePos A ps).length = A.length - cardB A
  | [], [], _ => rfl
  | true :: A, p :: ps, hlen => by
      show (falsePos A ps).length = (A.length + 1) - (cardB A + 1)
      rw [Nat.succ_sub_succ_eq_sub, falsePos_length A ps (Nat.succ.inj hlen)]
  | false :: A, p :: ps, hlen => by
      show (p :: falsePos A ps).length = (A.length + 1) - cardB A
      rw [List.length_cons, falsePos_length A ps (Nat.succ.inj hlen),
          succ_sub_clean (cardB_le_length A)]
  | [], _ :: _, hlen => Nat.noConfusion hlen
  | _ :: _, [], hlen => Nat.noConfusion hlen

/-! ### Recovery: the prefix-set of a built chain is `A` -/

private theorem beq_false_of_ne {p i : Nat} (h : p ≠ i) : Nat.beq p i = false := by
  cases hb : Nat.beq p i with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem lmap_congr {α β : Type _} {f g : α → β} :
    ∀ {L : List α}, (∀ x, x ∈ L → f x = g x) → L.map f = L.map g
  | [], _ => rfl
  | a :: l, h => by
      show f a :: l.map f = g a :: l.map g
      rw [h a (List.Mem.head _), lmap_congr (fun x hx => h x (List.Mem.tail _ hx))]

/-- The first `|σ|` entries of `σ ++ τ` are exactly `σ`. -/
theorem elemTake_append_eq_elemNat (i : Nat) :
    ∀ (σ τ : List Nat) (k : Nat), σ.length = k → elemTake i (σ ++ τ) k = elemNat i σ
  | [], τ, k, hk => by
      cases k with
      | zero => exact (elemTake_zero i ([] ++ τ)).trans rfl
      | succ _ => exact Nat.noConfusion hk
  | x :: σ', τ, k, hk => by
      cases k with
      | zero => exact Nat.noConfusion hk
      | succ k' =>
          show (Nat.beq x i || elemTake i (σ' ++ τ) k') = (Nat.beq x i || elemNat i σ')
          rw [elemTake_append_eq_elemNat i σ' τ k' (Nat.succ.inj hk)]

theorem mem_of_elemNat {i : Nat} : ∀ {l : List Nat}, elemNat i l = true → i ∈ l
  | [], h => Bool.noConfusion h
  | x :: xs, h => by
      have h2 : (Nat.beq x i || elemNat i xs) = true := h
      cases hbx : Nat.beq x i with
      | true => rw [Nat.eq_of_beq_eq_true hbx]; exact List.Mem.head _
      | false => rw [hbx] at h2; exact List.Mem.tail _ (mem_of_elemNat h2)

theorem elemNat_eq_true_of_mem {i : Nat} : ∀ {l : List Nat}, i ∈ l → elemNat i l = true
  | x :: xs, h => by
      cases h with
      | head =>
          show (Nat.beq _ _ || elemNat _ xs) = true
          rw [beq_self _, Bool.true_or]
      | tail _ h' =>
          show (Nat.beq x i || elemNat i xs) = true
          rw [elemNat_eq_true_of_mem h']; cases Nat.beq x i <;> rfl

theorem elemNat_eq_false_of_not_mem {i : Nat} : ∀ {l : List Nat}, i ∉ l → elemNat i l = false
  | [], _ => rfl
  | x :: xs, h => by
      show (Nat.beq x i || elemNat i xs) = false
      have hxi : Nat.beq x i = false :=
        beq_false_of_ne (fun he => h (by rw [he]; exact List.Mem.head _))
      rw [hxi, elemNat_eq_false_of_not_mem (fun hm => h (List.Mem.tail _ hm)), Bool.false_or]

theorem elemNat_eq_of_lperm {i : Nat} {l l' : List Nat} (h : LPerm l l') :
    elemNat i l = elemNat i l' := by
  cases hl : elemNat i l with
  | true => rw [elemNat_eq_true_of_mem (mem_of_lperm h (mem_of_elemNat hl))]
  | false =>
      cases hl' : elemNat i l' with
      | false => rfl
      | true =>
          have hc : elemNat i l = true :=
            elemNat_eq_true_of_mem (mem_of_lperm (LPerm.symm h) (mem_of_elemNat hl'))
          rw [hl] at hc; exact Bool.noConfusion hc

theorem elemNat_cons_ne {i p : Nat} (h : Nat.beq p i = false) (L : List Nat) :
    elemNat i (p :: L) = elemNat i L := by
  show (Nat.beq p i || elemNat i L) = elemNat i L
  rw [h, Bool.false_or]

theorem mem_truePos {i : Nat} : ∀ (A : List Bool) (ps : List Nat), i ∈ truePos A ps → i ∈ ps
  | [], _, h => nomatch h
  | true :: _, [], h => nomatch h
  | false :: _, [], h => nomatch h
  | true :: _, _ :: ps, h => by
      cases h with
      | head => exact List.Mem.head _
      | tail _ h' => exact List.Mem.tail _ (mem_truePos _ ps h')
  | false :: _, _ :: ps, h => List.Mem.tail _ (mem_truePos _ ps h)

/-- ★ Recovery: reading "is this index a true-position" over the index list
    returns `A`. -/
theorem recoverA :
    ∀ (A : List Bool) (ps : List Nat), ps.Nodup → A.length = ps.length →
      ps.map (fun i => elemNat i (truePos A ps)) = A
  | [], [], _, _ => rfl
  | true :: A, p :: ps, hnd, hlen => by
      have hpps : p ∉ ps := by cases hnd with | cons hh _ => exact fun hm => (hh p hm) rfl
      have hnd' : ps.Nodup := by cases hnd with | cons _ ht => exact ht
      show (elemNat p (p :: truePos A ps))
            :: ps.map (fun i => elemNat i (p :: truePos A ps)) = true :: A
      have hhead : elemNat p (p :: truePos A ps) = true :=
        elemNat_eq_true_of_mem (List.Mem.head _)
      have htail : ps.map (fun i => elemNat i (p :: truePos A ps)) = A :=
        (lmap_congr (fun i hi => elemNat_cons_ne
            (beq_false_of_ne (fun he => hpps (by rw [he]; exact hi))) (truePos A ps))).trans
          (recoverA A ps hnd' (Nat.succ.inj hlen))
      rw [hhead, htail]
  | false :: A, p :: ps, hnd, hlen => by
      have hpps : p ∉ ps := by cases hnd with | cons hh _ => exact fun hm => (hh p hm) rfl
      have hnd' : ps.Nodup := by cases hnd with | cons _ ht => exact ht
      show (elemNat p (truePos A ps))
            :: ps.map (fun i => elemNat i (truePos A ps)) = false :: A
      have hhead : elemNat p (truePos A ps) = false :=
        elemNat_eq_false_of_not_mem (fun hm => hpps (mem_truePos A ps hm))
      rw [hhead, recoverA A ps hnd' (Nat.succ.inj hlen)]
  | [], _ :: _, _, hlen => Nat.noConfusion hlen
  | _ :: _, [], _, hlen => Nat.noConfusion hlen

theorem mem_idxList_lt : ∀ {n i : Nat}, i ∈ idxList n → i < n
  | 0, _, h => nomatch h
  | n + 1, i, h => by
      rcases mem_append_iff (l₁ := idxList n) (l₂ := [n]) h with h1 | h2
      · exact Nat.lt_succ_of_lt (mem_idxList_lt h1)
      · cases h2 with
        | head => exact Nat.lt_succ_self n
        | tail _ h' => nomatch h'

theorem idxList_nodup : ∀ n, (idxList n).Nodup
  | 0 => List.Pairwise.nil
  | n + 1 => by
      refine nodup_append (idxList_nodup n)
        (List.Pairwise.cons (by intro y hy; nomatch hy) List.Pairwise.nil) ?_
      intro a ha hn
      cases hn with
      | head => exact Nat.lt_irrefl n (mem_idxList_lt ha)
      | tail _ h' => nomatch h'

/-- ★ A built chain `σ ++ τ` (with `σ` ordering the true-positions of `A`) is
    incident to `A`. -/
theorem inc_concat {n : Nat} (A : List Bool) (hAn : A.length = n)
    (σ τ : List Nat) (hσ : σ ∈ perms (truePos A (idxList n))) :
    inc n A (σ ++ τ) = true := by
  have hps : A.length = (idxList n).length := by rw [hAn, idxList_length]
  have hσlen : σ.length = cardB A := by
    rw [perms_length_const (truePos A (idxList n)) σ hσ, truePos_length A (idxList n) hps]
  show beqBoolList (prefixVec n (σ ++ τ) (cardB A)) A = true
  have key : prefixVec n (σ ++ τ) (cardB A) = A := by
    show (idxList n).map (fun i => elemTake i (σ ++ τ) (cardB A)) = A
    rw [lmap_congr (fun i _ => elemTake_append_eq_elemNat i σ τ (cardB A) hσlen),
        lmap_congr (fun i _ => elemNat_eq_of_lperm
          (perms_sound (truePos A (idxList n)) σ hσ))]
    exact recoverA A (idxList n) (idxList_nodup n) hps
  rw [key]; exact beqBoolList_refl A

/-! ### The injection count and `hlow` -/

theorem append_left_cancel {α : Type _} :
    ∀ (σ : List α) {τ τ' : List α}, σ ++ τ = σ ++ τ' → τ = τ'
  | [], _, _, h => h
  | _ :: σ', _, _, h => by injection h with _ h'; exact append_left_cancel σ' h'

theorem append_inj_left {α : Type _} :
    ∀ (σ σ' : List α) {τ τ' : List α}, σ.length = σ'.length → σ ++ τ = σ' ++ τ' → σ = σ'
  | [], [], _, _, _, _ => rfl
  | x :: σ', y :: σ'', _, _, hlen, h => by
      injection h with hxy h'
      rw [hxy, append_inj_left σ' σ'' (Nat.succ.inj hlen) h']
  | [], _ :: _, _, _, hlen, _ => Nat.noConfusion hlen
  | _ :: _, [], _, _, hlen, _ => Nat.noConfusion hlen

theorem mem_falsePos {i : Nat} : ∀ (A : List Bool) (ps : List Nat), i ∈ falsePos A ps → i ∈ ps
  | [], _, h => nomatch h
  | true :: _, [], h => nomatch h
  | false :: _, [], h => nomatch h
  | false :: _, _ :: ps, h => by
      cases h with
      | head => exact List.Mem.head _
      | tail _ h' => exact List.Mem.tail _ (mem_falsePos _ ps h')
  | true :: _, _ :: ps, h => List.Mem.tail _ (mem_falsePos _ ps h)

theorem truePos_nodup :
    ∀ (A : List Bool) (ps : List Nat), ps.Nodup → (truePos A ps).Nodup
  | [], _, _ => List.Pairwise.nil
  | true :: _, [], _ => List.Pairwise.nil
  | false :: _, [], _ => List.Pairwise.nil
  | true :: A, p :: ps, hnd => by
      have hpps : p ∉ ps := by cases hnd with | cons hh _ => exact fun hm => (hh p hm) rfl
      have hnd' : ps.Nodup := by cases hnd with | cons _ ht => exact ht
      exact List.Pairwise.cons
        (fun y hy he => hpps (by rw [he]; exact mem_truePos A ps hy))
        (truePos_nodup A ps hnd')
  | false :: A, _ :: ps, hnd =>
      truePos_nodup A ps (by cases hnd with | cons _ ht => exact ht)

theorem falsePos_nodup :
    ∀ (A : List Bool) (ps : List Nat), ps.Nodup → (falsePos A ps).Nodup
  | [], _, _ => List.Pairwise.nil
  | true :: _, [], _ => List.Pairwise.nil
  | false :: _, [], _ => List.Pairwise.nil
  | false :: A, p :: ps, hnd => by
      have hpps : p ∉ ps := by cases hnd with | cons hh _ => exact fun hm => (hh p hm) rfl
      have hnd' : ps.Nodup := by cases hnd with | cons _ ht => exact ht
      exact List.Pairwise.cons
        (fun y hy he => hpps (by rw [he]; exact mem_falsePos A ps hy))
        (falsePos_nodup A ps hnd')
  | true :: A, _ :: ps, hnd =>
      falsePos_nodup A ps (by cases hnd with | cons _ ht => exact ht)

theorem lcount_eq_filter_length {β : Type _} (p : β → Bool) :
    ∀ (L : List β), (L.filter p).length = lcount p L
  | [] => rfl
  | a :: rest => by
      cases h : p a with
      | true =>
          rw [List.filter_cons_of_pos h, List.length_cons, lcount_eq_filter_length p rest]
          show lcount p rest + 1 = (bif p a then 1 else 0) + lcount p rest
          rw [h]; exact Nat.add_comm _ _
      | false =>
          rw [List.filter_cons_of_neg (by rw [h]; exact Bool.noConfusion),
              lcount_eq_filter_length p rest]
          show lcount p rest = (bif p a then 1 else 0) + lcount p rest
          rw [h]; exact (Nat.zero_add _).symm

theorem lcount_ge_nodup_subset {β : Type _} [DecidableEq β] {p : β → Bool} {S L : List β}
    (hSnd : S.Nodup) (hsub : ∀ x, x ∈ S → x ∈ L ∧ p x = true) : S.length ≤ lcount p L := by
  rw [← lcount_eq_filter_length]
  exact nodup_length_le_of_subset hSnd (fun x hx => mem_filter_of (hsub x hx).1 (hsub x hx).2)

/-- ★ **`hlow`**: at least `|A|!·(n−|A|)!` chains pass through `A`. -/
theorem chain_low {n : Nat} (A : List Bool) (hAn : A.length = n) :
    fact (cardB A) * fact (n - cardB A) ≤ lcount (inc n A) (perms (idxList n)) := by
  have hps : A.length = (idxList n).length := by rw [hAn, idxList_length]
  have hTnd : (truePos A (idxList n)).Nodup := truePos_nodup A (idxList n) (idxList_nodup n)
  have hFnd : (falsePos A (idxList n)).Nodup := falsePos_nodup A (idxList n) (idxList_nodup n)
  -- the injected family of chains through A
  have hSnd : (flatMap213
      (fun σ => (perms (falsePos A (idxList n))).map (fun τ => σ ++ τ))
      (perms (truePos A (idxList n)))).Nodup := by
    refine nodup_flatMap213 (perms_nodup _ hTnd) (fun σ _ => ?_) (fun σ σ' hσ hσ' hne z hz hz' => ?_)
    · exact nodup_map_of_inj (fun τ _ τ' _ h => append_left_cancel σ h) (perms_nodup _ hFnd)
    · obtain ⟨τ, _, hzτ⟩ := exists_of_mem_map hz
      obtain ⟨τ', _, hzτ'⟩ := exists_of_mem_map hz'
      have hlen_eq : σ.length = σ'.length := by
        rw [perms_length_const _ σ hσ, perms_length_const _ σ' hσ']
      exact hne (append_inj_left σ σ' hlen_eq (hzτ.trans hzτ'.symm))
  have hsub : ∀ x, x ∈ flatMap213
      (fun σ => (perms (falsePos A (idxList n))).map (fun τ => σ ++ τ))
      (perms (truePos A (idxList n))) →
      x ∈ perms (idxList n) ∧ inc n A x = true := by
    intro x hx
    obtain ⟨σ, hσ, hxσ⟩ := mem_flatMap213 hx
    obtain ⟨τ, hτ, hxτ⟩ := exists_of_mem_map hxσ
    refine ⟨?_, ?_⟩
    · rw [← hxτ]
      exact perms_respects (LPerm.symm (truePos_falsePos_perm A (idxList n) hps)) _
              (perms_append_mem _ _ σ τ hσ hτ)
    · rw [← hxτ]; exact inc_concat A hAn σ τ hσ
  have hSlen := lcount_ge_nodup_subset hSnd hsub
  rw [length_flatMap213_const _ (perms (falsePos A (idxList n))).length
        (fun σ _ => E213.Tactic.List213.length_map _ _),
      perms_length, perms_length,
      truePos_length A (idxList n) hps, falsePos_length A (idxList n) hps, hAn] at hSlen
  rw [Nat.mul_comm]
  exact hSlen

/-! ## §5 — Sperner's theorem (named upper bound), unconditional -/

/-- ★★ **Sperner's theorem.**  Any antichain of the Boolean lattice `2^[n]` (a
    duplicate-free family of length-`n` `Bool` vectors, no two comparable) has
    at most `C(n, ⌊n/2⌋)` members.  The named upper bound, ∅-axiom — the chain
    model discharges both `sperner_upper_bound` hypotheses. -/
theorem sperner {n : Nat} (F : List (List Bool)) (hF : IsAntichain F) (hnd : F.Nodup)
    (hlen : ∀ A, A ∈ F → A.length = n) : F.length ≤ binom n (half n) :=
  sperner_upper_bound n F (perms (idxList n)) (inc n)
    (chains_length n)
    (fun A hA => Nat.le_trans (cardB_le_length A) (Nat.le_of_eq (hlen A hA)))
    (chain_cap F hF hnd)
    (fun A hA => chain_low A (hlen A hA))

/-- ★★★ **Sperner's theorem (both halves).**  The largest antichain of the
    Boolean lattice `2^[n]` has size exactly `C(n, ⌊n/2⌋)`: every antichain is
    bounded by it (`sperner`), and the middle layer achieves it
    (`Sperner.lower_bound`).  Both directions ∅-axiom. -/
theorem sperner_theorem (n : Nat) :
    (∀ (F : List (List Bool)), IsAntichain F → F.Nodup →
        (∀ A, A ∈ F → A.length = n) → F.length ≤ binom n (half n))
    ∧ (∃ L, IsAntichain L ∧ L.Nodup ∧ L.length = binom n (half n)) :=
  ⟨fun F hF hnd hlen => sperner F hF hnd hlen, Sperner.lower_bound n⟩

end E213.Lib.Math.Combinatorics.SpernerChains
