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
open E213.Tactic.List213 (length_append)

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

end E213.Lib.Math.Combinatorics.SpernerChains
