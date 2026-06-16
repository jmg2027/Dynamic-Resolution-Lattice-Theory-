import E213.Lib.Math.NumberTheory.ModArith.WilsonTheorem
import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
import E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative
import E213.Lib.Math.NumberTheory.EulerTotient
import E213.Lib.Math.Combinatorics.Permutations
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.Gcd213
import E213.Meta.Tactic.NatHelper

/-!
# Euler's theorem `a^φ(n) ≡ 1 (mod n)` (∅-axiom) — Route B (totative product)

Scratch development.
-/

namespace E213.Lib.Math.NumberTheory.EulerTheorem

open E213.Tactic.NatHelper (gcd213)
open E213.Lib.Math.NumberTheory.ModArith.WilsonTheorem (prodMod prodMod_cons)
open E213.Lib.Math.Combinatorics.Permutations (LPerm)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure mul_mod_pure)
open E213.Meta.Nat.AddMod213 (mod_mod)
open E213.Meta.Nat.Gcd213 (gcd213_comm gcd213_rec gcd213_self)

/-! ## §1 — `prodMod` is `LPerm`-invariant -/

/-- `prodMod` is invariant under permutation of the list. -/
theorem prodMod_lperm {p : Nat} : ∀ {l₁ l₂ : List Nat}, LPerm l₁ l₂ →
    prodMod p l₁ = prodMod p l₂ := by
  intro l₁ l₂ h
  induction h with
  | nil => rfl
  | cons a _ ih => rw [prodMod_cons, prodMod_cons, ih]
  | swap a b l =>
    -- prodMod (b::a::l) = prodMod (a::b::l)
    rw [prodMod_cons, prodMod_cons, prodMod_cons, prodMod_cons]
    -- (b * ((a * R) % p)) % p = (a * ((b * R) % p)) % p
    rw [← mul_mod_right_pure b (a * prodMod p l) p,
        ← mul_mod_right_pure a (b * prodMod p l) p]
    rw [E213.Tactic.NatHelper.mul_left_comm b a (prodMod p l)]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## §2 — `LPerm` from NoDup + same membership -/

open E213.Lib.Math.Combinatorics.Permutations (eraseFirst)

/-- `a ∈ l → LPerm (a :: eraseFirst a l) l`. -/
theorem lperm_cons_eraseFirst {α : Type _} [DecidableEq α] (a : α) :
    ∀ {l : List α}, a ∈ l → LPerm (a :: eraseFirst a l) l
  | x :: xs, h => by
    by_cases hx : x = a
    · subst hx
      show LPerm (x :: eraseFirst x (x :: xs)) (x :: xs)
      have he : eraseFirst x (x :: xs) = xs := by
        show (if x = x then xs else x :: eraseFirst x xs) = xs
        rw [if_pos rfl]
      rw [he]; exact LPerm.refl _
    · -- x ≠ a, so a ∈ xs
      have ha_xs : a ∈ xs := by
        cases h with
        | head => exact absurd rfl hx
        | tail _ h' => exact h'
      have he : eraseFirst a (x :: xs) = x :: eraseFirst a xs := by
        show (if x = a then xs else x :: eraseFirst a xs) = x :: eraseFirst a xs
        rw [if_neg hx]
      rw [he]
      -- LPerm (a :: x :: eraseFirst a xs) (x :: xs)
      -- via swap: (a :: x :: R) ~ (x :: a :: R), then cons x (a :: R ~ xs)
      refine LPerm.trans (LPerm.swap x a (eraseFirst a xs)) ?_
      exact LPerm.cons x (lperm_cons_eraseFirst a ha_xs)

/-- Membership in `eraseFirst a l` implies membership in `l`. -/
theorem mem_of_mem_eraseFirst {α : Type _} [DecidableEq α] {a y : α} :
    ∀ {l : List α}, y ∈ eraseFirst a l → y ∈ l
  | x :: xs, hy => by
    by_cases hxa : x = a
    · subst hxa
      have : eraseFirst x (x :: xs) = xs := by
        show (if x = x then xs else x :: eraseFirst x xs) = xs
        rw [if_pos rfl]
      rw [this] at hy; exact List.Mem.tail _ hy
    · have he : eraseFirst a (x :: xs) = x :: eraseFirst a xs := by
        show (if x = a then xs else x :: eraseFirst a xs) = x :: eraseFirst a xs
        rw [if_neg hxa]
      rw [he] at hy
      cases hy with
      | head => exact List.Mem.head _
      | tail _ h' => exact List.Mem.tail _ (mem_of_mem_eraseFirst h')

/-- For NoDup `l`, membership in `eraseFirst a l` ⟺ member of `l` and `≠ a`. -/
theorem mem_eraseFirst_of_ne {α : Type _} [DecidableEq α] {a y : α} :
    ∀ {l : List α}, l.Nodup → y ∈ l → y ≠ a → y ∈ eraseFirst a l
  | x :: xs, h, hy, hya => by
    cases h with
    | cons hx hxs =>
      by_cases hxa : x = a
      · subst hxa
        have he : eraseFirst x (x :: xs) = xs := by
          show (if x = x then xs else x :: eraseFirst x xs) = xs
          rw [if_pos rfl]
        rw [he]
        cases hy with
        | head => exact absurd rfl hya
        | tail _ h' => exact h'
      · have he : eraseFirst a (x :: xs) = x :: eraseFirst a xs := by
          show (if x = a then xs else x :: eraseFirst a xs) = x :: eraseFirst a xs
          rw [if_neg hxa]
        rw [he]
        cases hy with
        | head => exact List.Mem.head _
        | tail _ h' => exact List.Mem.tail _ (mem_eraseFirst_of_ne hxs h' hya)

/-- Erasing the head element preserves NoDup. -/
theorem nodup_eraseFirst {α : Type _} [DecidableEq α] (a : α) :
    ∀ {l : List α}, l.Nodup → (eraseFirst a l).Nodup
  | [], _ => List.Pairwise.nil
  | x :: xs, h => by
    cases h with
    | cons hx hxs =>
      by_cases hxa : x = a
      · subst hxa
        show (if x = x then xs else x :: eraseFirst x xs).Nodup
        rw [if_pos rfl]; exact hxs
      · show (if x = a then xs else x :: eraseFirst a xs).Nodup
        rw [if_neg hxa]
        refine List.Pairwise.cons ?_ (nodup_eraseFirst a hxs)
        intro y hy
        exact hx y (mem_of_mem_eraseFirst hy)

/-- `a ∉ eraseFirst a l` for NoDup `l` (a occurs once, erased ⟹ absent). -/
theorem a_notin_eraseFirst {α : Type _} [DecidableEq α] {a : α} :
    ∀ {l : List α}, l.Nodup → a ∈ eraseFirst a l → False
  | x :: xs, h, hmem => by
    cases h with
    | cons hx hxs =>
      by_cases hxa : x = a
      · subst hxa
        have he : eraseFirst x (x :: xs) = xs := by
          show (if x = x then xs else x :: eraseFirst x xs) = xs
          rw [if_pos rfl]
        rw [he] at hmem
        exact hx x hmem rfl
      · have he : eraseFirst a (x :: xs) = x :: eraseFirst a xs := by
          show (if x = a then xs else x :: eraseFirst a xs) = x :: eraseFirst a xs
          rw [if_neg hxa]
        rw [he] at hmem
        cases hmem with
        | head => exact hxa rfl
        | tail _ h' => exact a_notin_eraseFirst hxs h'

/-- **`LPerm` from NoDup + same membership** (fuel-bounded on `l₁.length`).
    Two NoDup lists with the same elements are permutations of each other. -/
theorem lperm_of_nodup_mem_iff_fuel {α : Type _} [DecidableEq α] :
    ∀ (n : Nat) (l₁ l₂ : List α), l₁.length ≤ n →
      l₁.Nodup → l₂.Nodup → (∀ x, x ∈ l₁ ↔ x ∈ l₂) → LPerm l₁ l₂
  | _, [], l₂, _, _, h₂, hmem => by
    -- l₂ empty too (same membership)
    cases l₂ with
    | nil => exact LPerm.nil
    | cons b bs =>
      exact absurd ((hmem b).mpr (List.Mem.head _)) (by intro hb; nomatch hb)
  | 0, a :: t, _, hlen, _, _, _ => by
    exact absurd hlen (Nat.not_succ_le_zero t.length)
  | n + 1, a :: t, l₂, hlen, h₁, h₂, hmem => by
    -- a ∈ l₂
    have ha2 : a ∈ l₂ := (hmem a).mp (List.Mem.head _)
    have hat : a ∉ t := by cases h₁ with | cons hh _ => exact fun hm => hh a hm rfl
    have htnd : t.Nodup := by cases h₁ with | cons _ ht => exact ht
    -- LPerm l₂ (a :: eraseFirst a l₂)
    have hperm2 : LPerm (a :: eraseFirst a l₂) l₂ := lperm_cons_eraseFirst a ha2
    -- recurse: t and eraseFirst a l₂ have same membership, both nodup
    have he_nd : (eraseFirst a l₂).Nodup := nodup_eraseFirst a h₂
    have hmem' : ∀ x, x ∈ t ↔ x ∈ eraseFirst a l₂ := by
      intro x
      constructor
      · intro hx
        have hxne : x ≠ a := fun he => hat (he ▸ hx)
        have hxl2 : x ∈ l₂ := (hmem x).mp (List.Mem.tail _ hx)
        exact mem_eraseFirst_of_ne h₂ hxl2 hxne
      · intro hx
        have hxl2 : x ∈ l₂ := mem_of_mem_eraseFirst hx
        have hxal : x ∈ a :: t := (hmem x).mpr hxl2
        cases hxal with
        | head =>
          -- x = a, but x ∈ eraseFirst a l₂ contradicts NoDup-erase
          exfalso
          -- a ∈ eraseFirst a l₂ : a occurs once in l₂, erased ⟹ absent
          exact a_notin_eraseFirst h₂ hx
        | tail _ h' => exact h'
    have hlen_t : t.length ≤ n := Nat.le_of_succ_le_succ hlen
    have hrec : LPerm t (eraseFirst a l₂) :=
      lperm_of_nodup_mem_iff_fuel n t (eraseFirst a l₂) hlen_t htnd he_nd hmem'
    -- a :: t  ~  a :: eraseFirst a l₂  ~  l₂
    exact LPerm.trans (LPerm.cons a hrec) hperm2

/-- **`LPerm` from NoDup + same membership.** -/
theorem lperm_of_nodup_mem_iff {α : Type _} [DecidableEq α] {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (hmem : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : LPerm l₁ l₂ :=
  lperm_of_nodup_mem_iff_fuel l₁.length l₁ l₂ (Nat.le_refl _) h₁ h₂ hmem

/-! ## §3 — the totative list `[k ∈ [1,n) : gcd(k,n)=1]` -/

open E213.Lib.Math.NumberTheory.EulerTotient (totient coprimeInd)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo)

/-- Totatives among residues `1..m` coprime to `n`, descending.  Built so that its
    `length` matches `sumTo m (coprimeInd · n)`. -/
def totListUpto (n : Nat) : Nat → List Nat
  | 0     => []
  | m + 1 => (if gcd213 (m + 1) n = 1 then [m + 1] else []) ++ totListUpto n m

/-- The totative list of `n`: all `k ∈ [1, n)` with `gcd(k,n)=1`. -/
def totativeList (n : Nat) : List Nat := totListUpto n n

/-- `length (totListUpto n m) = sumTo m (coprimeInd · n)`. -/
theorem length_totListUpto (n : Nat) : ∀ m,
    (totListUpto n m).length = sumTo m (fun k => coprimeInd k n)
  | 0 => rfl
  | m + 1 => by
    show ((if gcd213 (m + 1) n = 1 then [m + 1] else []) ++ totListUpto n m).length
       = sumTo m (fun k => coprimeInd k n) + coprimeInd m n
    rw [E213.Tactic.List213.length_append, length_totListUpto n m]
    -- coprimeInd m n = (gcd213 (m+1) n == 1).toNat ; head length = that
    have hci : coprimeInd m n = (if gcd213 (m + 1) n = 1 then [m + 1] else ([] : List Nat)).length := by
      show (gcd213 (m + 1) n == 1).toNat = _
      by_cases hg : gcd213 (m + 1) n = 1
      · rw [hg]
        show ((1 : Nat) == 1).toNat = (if (1 : Nat) = 1 then [1+0+m] else ([]:List Nat)).length
        rw [if_pos rfl]; rfl
      · rw [if_neg hg]
        show (gcd213 (m + 1) n == 1).toNat = 0
        rw [E213.Meta.Nat.Beq213.nat_beq_op_eq_false_of_ne hg]; rfl
    rw [hci, Nat.add_comm]

/-- ★ `length (totativeList n) = totient n`. -/
theorem length_totativeList (n : Nat) : (totativeList n).length = totient n :=
  length_totListUpto n n

/-- Membership in `totListUpto n m`: `x ∈ list ↔ 1 ≤ x ≤ m ∧ gcd(x,n)=1`. -/
theorem mem_totListUpto {n : Nat} : ∀ {m x : Nat},
    x ∈ totListUpto n m ↔ (1 ≤ x ∧ x ≤ m ∧ gcd213 x n = 1)
  | 0, x => by
    constructor
    · intro h; exact absurd h (by intro hh; nomatch hh)
    · intro ⟨h1, h2, _⟩; exact absurd (Nat.le_trans h1 h2) (by decide)
  | m + 1, x => by
    show x ∈ ((if gcd213 (m + 1) n = 1 then [m + 1] else []) ++ totListUpto n m) ↔ _
    constructor
    · intro h
      rcases E213.Tactic.List213.mem_append_iff h with hhd | htl
      · -- in head
        by_cases hg : gcd213 (m + 1) n = 1
        · rw [if_pos hg] at hhd
          cases hhd with
          | head => exact ⟨Nat.succ_le_succ (Nat.zero_le m), Nat.le_refl _, hg⟩
          | tail _ h' => nomatch h'
        · rw [if_neg hg] at hhd; nomatch hhd
      · obtain ⟨h1, h2, h3⟩ := mem_totListUpto.mp htl
        exact ⟨h1, Nat.le_succ_of_le h2, h3⟩
    · intro ⟨h1, h2, h3⟩
      rcases Nat.lt_or_eq_of_le h2 with hlt | heq
      · -- x ≤ m
        have hxm : x ≤ m := Nat.le_of_lt_succ hlt
        exact E213.Tactic.List213.mem_append_right _ (mem_totListUpto.mpr ⟨h1, hxm, h3⟩)
      · -- x = m+1
        have hg : gcd213 (m + 1) n = 1 := heq ▸ h3
        refine E213.Tactic.List213.mem_append_left ?_
        rw [if_pos hg, ← heq]; exact List.Mem.head _

/-- `totListUpto n m` is NoDup (entries strictly descending; tail entries `≤ m`). -/
theorem nodup_totListUpto (n : Nat) : ∀ m, (totListUpto n m).Nodup
  | 0 => List.Pairwise.nil
  | m + 1 => by
    show ((if gcd213 (m + 1) n = 1 then [m + 1] else []) ++ totListUpto n m).Nodup
    by_cases hg : gcd213 (m + 1) n = 1
    · rw [if_pos hg]
      -- [m+1] ++ tail, with m+1 ∉ tail (tail entries ≤ m)
      have hsingle : ([m + 1] : List Nat).Nodup :=
        List.Pairwise.cons (by intro y hy; nomatch hy) List.Pairwise.nil
      refine E213.Tactic.List213.nodup_append hsingle (nodup_totListUpto n m) ?_
      intro x hx hxt
      -- x ∈ [m+1] ⟹ x = m+1 ; x ∈ tail ⟹ x ≤ m
      cases hx with
      | head =>
        obtain ⟨_, hle, _⟩ := mem_totListUpto.mp hxt
        exact absurd hle (Nat.not_succ_le_self m)
      | tail _ h' => nomatch h'
    · rw [if_neg hg]; exact nodup_totListUpto n m

/-- Members of `totativeList n` are coprime to `n`. -/
theorem totativeList_coprime {n x : Nat} (h : x ∈ totativeList n) : gcd213 x n = 1 :=
  (mem_totListUpto.mp h).2.2

/-- Members of `totativeList n` are positive. -/
theorem totativeList_pos {n x : Nat} (h : x ∈ totativeList n) : 1 ≤ x :=
  (mem_totListUpto.mp h).1

/-- Members of `totativeList n` are `≤ n`. -/
theorem totativeList_le {n x : Nat} (h : x ∈ totativeList n) : x ≤ n :=
  (mem_totListUpto.mp h).2.1

theorem nodup_totativeList (n : Nat) : (totativeList n).Nodup := nodup_totListUpto n n

/-! ## §4 — factoring `a` out of the image product -/

/-- `prodMod n (map (fun x => (a*x) % n) L) = (a^|L| · prodMod n L) % n`. -/
theorem prodMod_map_factor (n a : Nat) : ∀ (L : List Nat),
    prodMod n (L.map (fun x => (a * x) % n))
      = (a ^ L.length * prodMod n L) % n
  | [] => by
    show (1 : Nat) % n = (a ^ 0 * (1 % n)) % n
    rw [Nat.pow_zero, Nat.one_mul, mod_mod]
  | x :: t => by
    show prodMod n ((a * x) % n :: t.map (fun x => (a * x) % n))
       = (a ^ (t.length + 1) * prodMod n (x :: t)) % n
    rw [prodMod_cons, prodMod_map_factor n a t, prodMod_cons]
    -- LHS = (((a*x)%n) * ((a^|t| * prodMod n t)%n)) % n
    -- reduce both mods:
    rw [← mul_mod_pure (a * x) (a ^ t.length * prodMod n t) n]
    rw [← mul_mod_right_pure (a ^ (t.length + 1)) (x * prodMod n t) n]
    -- now both are (BIG) % n with mod removed; show the products equal
    -- (a*x) * (a^|t| * prodMod n t) = a^(|t|+1) * (x * prodMod n t)
    have hpow : a ^ (t.length + 1) = a * a ^ t.length := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [hpow]
    have hprod : a * x * (a ^ t.length * prodMod n t)
               = a * a ^ t.length * (x * prodMod n t) :=
      calc a * x * (a ^ t.length * prodMod n t)
          = a * x * a ^ t.length * prodMod n t := by
            rw [E213.Tactic.NatHelper.mul_assoc (a * x) (a ^ t.length) (prodMod n t)]
        _ = a * a ^ t.length * x * prodMod n t := by
            rw [E213.Tactic.NatHelper.mul_assoc a x (a ^ t.length),
                Nat.mul_comm x (a ^ t.length),
                ← E213.Tactic.NatHelper.mul_assoc a (a ^ t.length) x]
        _ = a * a ^ t.length * (x * prodMod n t) := by
            rw [E213.Tactic.NatHelper.mul_assoc (a * a ^ t.length) x (prodMod n t)]
    rw [hprod]

/-! ## §5 — the multiplication map permutes the totatives -/

open E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative (coprime_mul_of_coprime)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (inverse_of_coprime)
open E213.Lib.Math.NumberTheory.ModArith.ModBezout (modBezout)

/-- gcd is invariant under reducing the first argument mod `n`:
    `gcd213 (k % n) n = gcd213 k n` for `0 < n`. -/
theorem gcd_mod_left (k n : Nat) (hn : 0 < n) : gcd213 (k % n) n = gcd213 k n := by
  -- gcd213 n k = gcd213 (k % n) n  (Euclid step)
  have h := gcd213_rec n k hn
  -- h : gcd213 n k = gcd213 (k % n) n
  rw [gcd213_comm k n]; exact h.symm

/-- For a unit `a` (`gcd(a,n)=1`) and a totative `x` (`gcd(x,n)=1`), the image
    `(a*x) % n` is coprime to `n`. -/
theorem image_coprime {a x n : Nat} (hn : 0 < n)
    (ha : gcd213 a n = 1) (hx : gcd213 x n = 1) :
    gcd213 ((a * x) % n) n = 1 := by
  rw [gcd_mod_left (a * x) n hn]
  -- gcd213 (a*x) n = gcd213 n (a*x) = 1
  rw [gcd213_comm (a * x) n]
  exact coprime_mul_of_coprime (by rw [gcd213_comm n a]; exact ha)
    (by rw [gcd213_comm n x]; exact hx)

/-- A totative is positive and `< n` (for `1 < n`). -/
theorem totative_lt_n {x n : Nat} (hn : 1 < n) (h : gcd213 x n = 1) (hpos : 1 ≤ x) (hle : x ≤ n) :
    x < n := by
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · -- x = n ⟹ gcd(n,n) = n ≠ 1
    exfalso
    rw [heq, gcd213_self n] at h
    exact absurd (h ▸ hn) (Nat.lt_irrefl 1)

/-- The image `(a*x) % n` (for unit `a`, totative `x`, `1 < n`) is a totative:
    in `[1, n)` and coprime to `n`. -/
theorem image_mem_totativeList {a x n : Nat} (hn : 1 < n)
    (ha : gcd213 a n = 1) (hx : x ∈ totativeList n) :
    (a * x) % n ∈ totativeList n := by
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hn)
  have hxco : gcd213 x n = 1 := totativeList_coprime hx
  have himgco : gcd213 ((a * x) % n) n = 1 := image_coprime hnpos ha hxco
  -- (a*x)%n < n, and coprime ⟹ ≠ 0 ⟹ ≥ 1
  have hlt : (a * x) % n < n := Nat.mod_lt _ hnpos
  have hpos : 1 ≤ (a * x) % n := by
    rcases Nat.eq_zero_or_pos ((a * x) % n) with h0 | hp
    · exfalso
      rw [h0, E213.Meta.Nat.Gcd213.gcd213_zero_left n] at himgco
      exact absurd (himgco ▸ hn) (Nat.lt_irrefl 1)
    · exact hp
  exact mem_totListUpto.mpr ⟨hpos, Nat.le_of_lt hlt, himgco⟩

/-! ## §6 — modular inverse cancellation -/

open E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative (dvd_trans_213 eq_one_of_dvd_one)

/-- The Bezout inverse of `a` mod `n`. -/
def aInv (a n : Nat) : Nat := (modBezout a n).2

/-- `(a · aInv a n) % n = 1 % n` for a unit `a`. -/
theorem aInv_spec {a n : Nat} (hn : 0 < n) (ha : gcd213 a n = 1) :
    (a * aInv a n) % n = 1 % n := inverse_of_coprime a n hn ha

/-- `aInv a n` is itself coprime to `n`. -/
theorem aInv_coprime {a n : Nat} (hn : 1 < n) (ha : gcd213 a n = 1) :
    gcd213 (aInv a n) n = 1 := by
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hn)
  have hspec : (a * aInv a n) % n = 1 % n := aInv_spec hnpos ha
  have h1mod : (1 : Nat) % n = 1 := Nat.mod_eq_of_lt hn
  rw [h1mod] at hspec
  have hdm : n * (a * aInv a n / n) + (a * aInv a n) % n = a * aInv a n :=
    E213.Meta.Nat.AddMod213.div_add_mod (a * aInv a n) n
  rw [hspec] at hdm
  -- hdm : n*Q + 1 = a*aInv a n
  have g_dvd_inv : gcd213 (aInv a n) n ∣ aInv a n :=
    E213.Meta.Nat.Gcd213.gcd213_dvd_left (aInv a n) n
  have g_dvd_n : gcd213 (aInv a n) n ∣ n :=
    E213.Meta.Nat.Gcd213.gcd213_dvd_right (aInv a n) n
  have g_dvd_prod : gcd213 (aInv a n) n ∣ a * aInv a n :=
    dvd_trans_213 g_dvd_inv ⟨a, Nat.mul_comm a (aInv a n)⟩
  have g_dvd_nQ : gcd213 (aInv a n) n ∣ n * (a * aInv a n / n) :=
    dvd_trans_213 g_dvd_n ⟨a * aInv a n / n, rfl⟩
  -- abbreviate Q := a*aInv/n
  have hle : n * (a * aInv a n / n) ≤ a * aInv a n :=
    Nat.le.intro hdm
  have g_dvd_diff : gcd213 (aInv a n) n ∣ (a * aInv a n - n * (a * aInv a n / n)) :=
    E213.Meta.Nat.Gcd213.dvd_sub_213 (n * (a * aInv a n / n)) (a * aInv a n)
      (gcd213 (aInv a n) n) hle g_dvd_nQ g_dvd_prod
  -- a*aInv - n*Q = 1 : from hdm (n*Q + 1 = a*aInv)
  have hdiff1 : a * aInv a n - n * (a * aInv a n / n) = 1 := by
    have : a * aInv a n - n * (a * aInv a n / n)
         = (n * (a * aInv a n / n) + 1) - n * (a * aInv a n / n) := by rw [hdm]
    rw [this, Nat.add_comm (n * (a * aInv a n / n)) 1,
        E213.Tactic.NatHelper.add_sub_cancel_right 1 (n * (a * aInv a n / n))]
  rw [hdiff1] at g_dvd_diff
  exact eq_one_of_dvd_one g_dvd_diff

/-- **Modular cancellation by the inverse**: `(aInv a n · ((a·x) % n)) % n = x % n`. -/
theorem inv_mul_image {a x n : Nat} (hn : 0 < n) (ha : gcd213 a n = 1) :
    (aInv a n * ((a * x) % n)) % n = x % n := by
  -- aInv * ((a*x)%n) ≡ aInv*a*x ≡ (a*aInv)*x ≡ 1*x = x
  rw [← mul_mod_right_pure (aInv a n) (a * x) n]
  -- (aInv * (a*x)) % n = (aInv*a)*x % n
  rw [← E213.Tactic.NatHelper.mul_assoc (aInv a n) a x]
  -- ((aInv*a)*x) % n = (((aInv*a)%n)*x) % n
  rw [mul_mod_left_pure (aInv a n * a) x n]
  -- (aInv*a)%n = (a*aInv)%n = 1%n
  have haa : (aInv a n * a) % n = 1 % n := by
    rw [Nat.mul_comm (aInv a n) a]; exact aInv_spec hn ha
  rw [haa]
  -- ((1%n)*x) % n = x % n
  rw [← mul_mod_left_pure 1 x n, Nat.one_mul]

/-- Symmetric form: `(a · ((aInv a n · y) % n)) % n = y % n`. -/
theorem mul_inv_image {a y n : Nat} (hn : 0 < n) (ha : gcd213 a n = 1) :
    (a * ((aInv a n * y) % n)) % n = y % n := by
  rw [← mul_mod_right_pure a (aInv a n * y) n]
  rw [← E213.Tactic.NatHelper.mul_assoc a (aInv a n) y]
  rw [mul_mod_left_pure (a * aInv a n) y n]
  rw [aInv_spec hn ha]
  rw [← mul_mod_left_pure 1 y n, Nat.one_mul]

/-! ## §7 — the multiplication map is a bijection on the totative list -/

/-- The image map is **injective** on the totative list (for `1 < n`, unit `a`). -/
theorem image_inj {a n : Nat} (hn : 1 < n) (ha : gcd213 a n = 1) :
    ∀ x, x ∈ totativeList n → ∀ y, y ∈ totativeList n →
      (a * x) % n = (a * y) % n → x = y := by
  intro x hx y hy heq
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hn)
  -- apply inv to both
  have hcx : (aInv a n * ((a * x) % n)) % n = x % n := inv_mul_image hnpos ha
  have hcy : (aInv a n * ((a * y) % n)) % n = y % n := inv_mul_image hnpos ha
  rw [heq] at hcx
  -- hcx : (aInv*((a*y)%n))%n = x%n ;  hcy : same LHS = y%n
  have hxy : x % n = y % n := hcx.symm.trans hcy
  -- x, y < n
  have hxlt : x < n := totative_lt_n hn (totativeList_coprime hx) (totativeList_pos hx) (totativeList_le hx)
  have hylt : y < n := totative_lt_n hn (totativeList_coprime hy) (totativeList_pos hy) (totativeList_le hy)
  rw [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at hxy
  exact hxy

/-- The preimage `(aInv a n · y) % n` of a totative `y` is itself a totative. -/
theorem preimage_mem {a y n : Nat} (hn : 1 < n) (ha : gcd213 a n = 1)
    (hy : y ∈ totativeList n) : (aInv a n * y) % n ∈ totativeList n := by
  -- aInv a n is a unit; reuse image_mem_totativeList with a := aInv a n
  exact image_mem_totativeList hn (aInv_coprime hn ha) hy

/-- ★★ **The image of the totative list under `x ↦ (a·x) % n` is a permutation of it.** -/
theorem lperm_image {a n : Nat} (hn : 1 < n) (ha : gcd213 a n = 1) :
    LPerm (totativeList n) ((totativeList n).map (fun x => (a * x) % n)) := by
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hn)
  -- both NoDup
  have hnd1 : (totativeList n).Nodup := nodup_totativeList n
  have hnd2 : ((totativeList n).map (fun x => (a * x) % n)).Nodup :=
    E213.Tactic.List213.nodup_map_of_inj (image_inj hn ha) hnd1
  -- same membership
  refine lperm_of_nodup_mem_iff hnd1 hnd2 (fun z => ?_)
  constructor
  · -- z ∈ totativeList ⟹ z ∈ image : z = (a * ((aInv*z)%n)) % n with (aInv*z)%n a totative
    intro hz
    have hpre : (aInv a n * z) % n ∈ totativeList n := preimage_mem hn ha hz
    have himg : (a * ((aInv a n * z) % n)) % n = z := by
      rw [mul_inv_image hnpos ha]
      exact Nat.mod_eq_of_lt (totative_lt_n hn (totativeList_coprime hz) (totativeList_pos hz) (totativeList_le hz))
    -- z = f (preimage), so z ∈ map f
    rw [← himg]
    exact E213.Tactic.List213.mem_map_of_mem (fun x => (a * x) % n) hpre
  · -- z ∈ image ⟹ z ∈ totativeList
    intro hz
    obtain ⟨x, hx, rfl⟩ := E213.Tactic.List213.exists_of_mem_map hz
    exact image_mem_totativeList hn ha hx

/-! ## §8 — the totative product is a unit; cancellation -/

/-- `prodMod n L` is coprime to `n` when every element of `L` is (for `0 < n`). -/
theorem prodMod_coprime {n : Nat} (hn : 0 < n) :
    ∀ (L : List Nat), (∀ x, x ∈ L → gcd213 x n = 1) → gcd213 (prodMod n L) n = 1
  | [], _ => by
    show gcd213 (1 % n) n = 1
    rw [gcd_mod_left 1 n hn]
    -- gcd213 1 n = 1
    rw [gcd213_comm 1 n]
    exact E213.Lib.Math.NumberTheory.ModArith.CoprimeMultiplicative.gcd213_one_right n
  | x :: t, hall => by
    show gcd213 ((x * prodMod n t) % n) n = 1
    rw [gcd_mod_left (x * prodMod n t) n hn]
    -- gcd213 (x * prodMod n t) n = 1
    rw [gcd213_comm (x * prodMod n t) n]
    refine coprime_mul_of_coprime ?_ ?_
    · rw [gcd213_comm n x]; exact hall x (List.Mem.head _)
    · rw [gcd213_comm n (prodMod n t)]
      exact prodMod_coprime hn t (fun y hy => hall y (List.Mem.tail _ hy))

/-- `prodMod n L < n` for `0 < n`. -/
theorem prodMod_lt {n : Nat} (hn : 0 < n) : ∀ (L : List Nat), prodMod n L < n
  | [] => Nat.mod_lt _ hn
  | _ :: _ => Nat.mod_lt _ hn

/-- **Left cancellation by a unit**: `gcd(P,n)=1, (P·u)%n = (P·v)%n, v < n ⟹ u%n = v`. -/
theorem cancel_unit {P u v n : Nat} (hn : 1 < n) (hP : gcd213 P n = 1)
    (heq : (P * u) % n = (P * v) % n) (hv : v < n) : u % n = v := by
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hn)
  -- multiply both sides by aInv P n
  have hcu : (aInv P n * ((P * u) % n)) % n = u % n := inv_mul_image hnpos hP
  have hcv : (aInv P n * ((P * v) % n)) % n = v % n := inv_mul_image hnpos hP
  rw [heq] at hcu
  have : u % n = v % n := hcu.symm.trans hcv
  rw [this, Nat.mod_eq_of_lt hv]

/-! ## §9 — ★★★ Euler's theorem -/

/-- ★★★ **Euler's theorem.**  For `1 < n` and `gcd(a, n) = 1`,
    `a^φ(n) ≡ 1 (mod n)`, i.e. `a ^ totient n % n = 1 % n`.

    Proof (Route B, totative product).  Let `L = totativeList n` (the `φ(n)`
    residues in `[1,n)` coprime to `n`) and `P = prodMod n L`.  The map
    `x ↦ (a·x) % n` permutes `L` (`lperm_image`: injective by modular
    cancellation, surjective via the Bezout inverse), so `prodMod` is
    unchanged: `P = prodMod n (map f L)`.  Factoring the `a`'s out of the
    image product (`prodMod_map_factor`) gives `prodMod n (map f L) =
    (a^|L| · P) % n = (a^φ(n) · P) % n`.  Hence `(a^φ(n) · P) % n = P % n`.
    `P` is a unit (`prodMod_coprime`: product of units), so cancelling it
    (`cancel_unit`) leaves `a^φ(n) % n = 1 % n`. -/
theorem euler_theorem (a n : Nat) (hn : 1 < n) (hcop : gcd213 a n = 1) :
    a ^ (totient n) % n = 1 % n := by
  have hnpos : 0 < n := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hn)
  -- L := totativeList n,  P := prodMod n L
  -- perm-invariance: prodMod n L = prodMod n (map f L)
  have hperm : prodMod n (totativeList n)
             = prodMod n ((totativeList n).map (fun x => (a * x) % n)) :=
    prodMod_lperm (lperm_image hn hcop)
  -- factor: prodMod n (map f L) = (a^|L| * prodMod n L) % n
  have hfac := prodMod_map_factor n a (totativeList n)
  -- length L = totient n
  have hlen : (totativeList n).length = totient n := length_totativeList n
  rw [hlen] at hfac
  -- combine: prodMod n L = (a^φ * prodMod n L) % n
  have hPeq : prodMod n (totativeList n)
            = (a ^ totient n * prodMod n (totativeList n)) % n := hperm.trans hfac
  -- P < n, so P = P % n
  have hPlt : prodMod n (totativeList n) < n := prodMod_lt hnpos (totativeList n)
  -- rewrite to cancel form: (P * a^φ) % n = (P * 1) % n
  have hcancelform :
      (prodMod n (totativeList n) * a ^ totient n) % n
        = (prodMod n (totativeList n) * 1) % n := by
    rw [Nat.mul_one, Nat.mul_comm (prodMod n (totativeList n)) (a ^ totient n)]
    -- (a^φ * P) % n = P % n
    rw [← hPeq, Nat.mod_eq_of_lt hPlt]
  -- P is a unit
  have hPunit : gcd213 (prodMod n (totativeList n)) n = 1 :=
    prodMod_coprime hnpos (totativeList n) (fun x hx => totativeList_coprime hx)
  -- cancel P:  a^φ % n = 1
  have hres : a ^ totient n % n = 1 :=
    cancel_unit hn hPunit hcancelform hn
  rw [hres, Nat.mod_eq_of_lt hn]

/-! ## §10 — smokes -/

/-- Smoke: Euler at composite `n`.  φ(9)=6, 2^6=64≡1 mod 9. -/
theorem euler_smoke_2_9 : (2 : Nat) ^ (totient 9) % 9 = 1 % 9 :=
  euler_theorem 2 9 (by decide) (by decide)

/-- Smoke: φ(10)=4, 3^4=81≡1 mod 10. -/
theorem euler_smoke_3_10 : (3 : Nat) ^ (totient 10) % 10 = 1 % 10 :=
  euler_theorem 3 10 (by decide) (by decide)

/-- Smoke: φ(8)=4, 3^4=81≡1 mod 8. -/
theorem euler_smoke_3_8 : (3 : Nat) ^ (totient 8) % 8 = 1 % 8 :=
  euler_theorem 3 8 (by decide) (by decide)

/-- Smoke: prime case recovered.  φ(7)=6, 3^6≡1 mod 7. -/
theorem euler_smoke_3_7 : (3 : Nat) ^ (totient 7) % 7 = 1 % 7 :=
  euler_theorem 3 7 (by decide) (by decide)

end E213.Lib.Math.NumberTheory.EulerTheorem
