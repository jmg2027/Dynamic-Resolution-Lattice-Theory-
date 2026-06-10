import E213.Meta.Tactic.NatHelper

/-!
# Int213 — ∅-axiom Int arithmetic helpers

Lean-core `Int.add_comm`, `Int.neg_add` are proved via `simp`-heavy
tactics that pull in `propext`.  `Theory/Raw/FoldSwap.lean` needs
both identities to make `Tree.fold_signed_swap` ∅-axiom; this file
provides 213-native term-mode replacements.

Strategy: case-split on the two Int constructors (`ofNat`,
`negSucc`), reduce via core Nat lemmas (`Nat.zero_add`,
`Nat.succ_add`, `Nat.zero_sub`, `Nat.succ_sub_succ_eq_sub`, all
∅-axiom), and recurse where needed (`neg_subNatNat`).  No `simp`,
no `omega`, no Mathlib.
-/

namespace E213.Meta.Int213

open E213.Tactic.NatHelper

/-- ∅-axiom `Int.add_comm`. -/
theorem add_comm : ∀ (a b : Int), a + b = b + a
  | .ofNat m,   .ofNat n   => by
      show Int.ofNat (m + n) = Int.ofNat (n + m)
      rw [Nat.add_comm]
  | .ofNat _,   .negSucc _ => rfl
  | .negSucc _, .ofNat _   => rfl
  | .negSucc m, .negSucc n => by
      show Int.negSucc (m + n).succ = Int.negSucc (n + m).succ
      rw [Nat.add_comm]

/-- subNatNat reverses under negation: `-(m -ℕ n) = n -ℕ m`. -/
theorem neg_subNatNat : ∀ (m n : Nat),
    -(Int.subNatNat m n) = Int.subNatNat n m := by
  intro m n
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => rfl
      | succ k =>
          show Int.ofNat (k+1)
              = (match 0 - (k+1) with
                 | 0 => Int.ofNat ((k+1) - 0)
                 | j+1 => Int.negSucc j)
          rw [Nat.zero_sub]; rfl
  | succ m ih =>
      cases n with
      | zero =>
          show -(match 0 - (m+1) with
                 | 0 => Int.ofNat ((m+1) - 0)
                 | k+1 => Int.negSucc k)
                = Int.negSucc m
          rw [Nat.zero_sub]; rfl
      | succ k =>
          show -(match (k+1) - (m+1) with
                 | 0 => Int.ofNat ((m+1) - (k+1))
                 | j+1 => Int.negSucc j)
                = (match (m+1) - (k+1) with
                   | 0 => Int.ofNat ((k+1) - (m+1))
                   | j+1 => Int.negSucc j)
          rw [Nat.succ_sub_succ_eq_sub, Nat.succ_sub_succ_eq_sub]
          exact ih k

/-- ∅-axiom `Int.neg_add`: `-(a+b) = -a + -b`. -/
theorem neg_add : ∀ (a b : Int), -(a + b) = -a + -b := by
  intro a b
  cases a with
  | ofNat m =>
      cases b with
      | ofNat n =>
          cases m with
          | zero =>
              cases n with
              | zero => rfl
              | succ k =>
                  show -(Int.ofNat (0 + (k+1))) = Int.ofNat 0 + Int.negSucc k
                  rw [Nat.zero_add]; rfl
          | succ m =>
              cases n with
              | zero => rfl
              | succ k =>
                  show Int.negSucc ((m+1) + k) = Int.negSucc ((m + k).succ)
                  rw [Nat.succ_add]
      | negSucc n =>
          cases m with
          | zero =>
              show Int.ofNat (n+1) = Int.ofNat (0 + (n+1))
              rw [Nat.zero_add]
          | succ m =>
              show -(Int.subNatNat (m+1) (n+1)) = Int.subNatNat (n+1) (m+1)
              rw [Int213.neg_subNatNat]
  | negSucc m =>
      cases b with
      | ofNat n =>
          cases n with
          | zero => rfl
          | succ k =>
              show -(Int.subNatNat (k+1) (m+1)) = Int.subNatNat (m+1) (k+1)
              rw [Int213.neg_subNatNat]
      | negSucc n =>
          show Int.ofNat ((m + n + 1) + 1) = Int.ofNat ((m + 1) + n + 1)
          rw [Nat.succ_add m n]

/-- ∅-axiom `Int.mul_comm` via 4-case analysis on Int constructors. -/
theorem mul_comm : ∀ (a b : Int), a * b = b * a
  | .ofNat m, .ofNat n => by
    show Int.ofNat (m * n) = Int.ofNat (n * m); rw [Nat.mul_comm]
  | .ofNat m, .negSucc n => by
    show Int.negOfNat (m * (n+1)) = Int.negOfNat ((n+1) * m); rw [Nat.mul_comm]
  | .negSucc m, .ofNat n => by
    show Int.negOfNat ((m+1) * n) = Int.negOfNat (n * (m+1)); rw [Nat.mul_comm]
  | .negSucc m, .negSucc n => by
    show Int.ofNat ((m+1) * (n+1)) = Int.ofNat ((n+1) * (m+1)); rw [Nat.mul_comm]

/-- ∅-axiom `Int.zero_mul`. -/
theorem zero_mul : ∀ (a : Int), 0 * a = 0
  | .ofNat n => by
    show Int.ofNat (0 * n) = (0 : Int); rw [Nat.zero_mul]; rfl
  | .negSucc n => by
    show Int.negOfNat (0 * (n+1)) = (0 : Int); rw [Nat.zero_mul]; rfl

/-- ∅-axiom `Int.add_left_neg`: `-a + a = 0`. -/
theorem add_left_neg : ∀ (a : Int), -a + a = 0
  | .ofNat 0 => rfl
  | .ofNat (n+1) => by
    show Int.subNatNat (n+1) (n+1) = 0
    rw [Int.subNatNat_self]
  | .negSucc n => by
    show Int.subNatNat (n+1) (n+1) = 0
    rw [Int.subNatNat_self]

/-- ∅-axiom `Int.add_nonneg`: `0 ≤ a → 0 ≤ b → 0 ≤ a + b`.
    Replaces propext-bearing `Int.add_nonneg`. -/
theorem add_nonneg : ∀ {a b : Int}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
  | .ofNat m, .ofNat n, _, _ => by
    show (0 : Int) ≤ Int.ofNat (m + n); exact Int.ofNat_nonneg _
  | .ofNat _, .negSucc _, _, hb => by cases hb
  | .negSucc _, _, ha, _ => by cases ha

/-- ∅-axiom: from `0 ≤ a`, `0 ≤ b`, `a + b = 0`, derive both zero. -/
theorem add_eq_zero_of_nonneg :
    ∀ {a b : Int}, 0 ≤ a → 0 ≤ b → a + b = 0 → a = 0 ∧ b = 0
  | .ofNat m, .ofNat n, _, _, h => by
    have h1 : Int.ofNat (m + n) = (0 : Int) := h
    have h2 : m + n = 0 := Int.ofNat.inj h1
    have hm : m = 0 := Nat.eq_zero_of_add_eq_zero_right h2
    have hn : n = 0 := Nat.eq_zero_of_add_eq_zero_left h2
    refine ⟨?_, ?_⟩
    · rw [hm]; rfl
    · rw [hn]; rfl
  | .ofNat _, .negSucc _, _, hb, _ => by cases hb
  | .negSucc _, _, ha, _, _ => by cases ha

/-- ∅-axiom Nat helper: `a * b = 0 → a = 0 ∨ b = 0`. -/
theorem mul_eq_zero_nat : ∀ {a b : Nat}, a * b = 0 → a = 0 ∨ b = 0
  | 0, _, _ => Or.inl rfl
  | _+1, 0, _ => Or.inr rfl
  | a+1, b+1, h =>
    let h1 : (a+1) * (b+1) = (a+1) * b + (a+1) := Nat.mul_succ (a+1) b
    let h2 : (a+1) * b + (a+1) = 0 := h1 ▸ h
    let h3 : (a+1) * b + (a + 1) = ((a+1) * b + a).succ := Nat.add_succ _ _
    let h4 : ((a+1) * b + a).succ = 0 := h3 ▸ h2
    Nat.noConfusion h4

/-- ∅-axiom `Int.mul_eq_zero` (forward direction): no zero divisors
    in `Int`.  Replaces the propext-bearing Iff `Int.mul_eq_zero`. -/
theorem mul_eq_zero : ∀ {a b : Int}, a * b = 0 → a = 0 ∨ b = 0
  | .ofNat m, .ofNat n, h => by
    have h2 : m * n = 0 := Int.ofNat.inj h
    rcases mul_eq_zero_nat h2 with hm | hn
    · left; rw [hm]; rfl
    · right; rw [hn]; rfl
  | .ofNat 0, .negSucc _, _ => Or.inl rfl
  | .ofNat (k+1), .negSucc n, h => by
    exfalso
    have h1 : Int.negOfNat ((k+1) * (n+1)) = (0 : Int) := h
    have hpos : (k+1) * (n+1) = ((k+1) * n + k).succ := by
      rw [Nat.mul_succ, Nat.add_succ]
    rw [hpos] at h1
    cases h1
  | .negSucc m, .ofNat 0, _ => Or.inr rfl
  | .negSucc m, .ofNat (k+1), h => by
    exfalso
    have h1 : Int.negOfNat ((m+1) * (k+1)) = (0 : Int) := h
    have hpos : (m+1) * (k+1) = ((m+1) * k + m).succ := by
      rw [Nat.mul_succ, Nat.add_succ]
    rw [hpos] at h1
    cases h1
  | .negSucc m, .negSucc n, h => by
    have h1 : Int.ofNat ((m+1) * (n+1)) = (0 : Int) := h
    have h2 : (m+1) * (n+1) = 0 := Int.ofNat.inj h1
    rcases mul_eq_zero_nat h2 with hm | hn
    · exact Nat.noConfusion hm
    · exact Nat.noConfusion hn

/-- ∅-axiom `Int.mul_nonneg`: `0 ≤ a → 0 ≤ b → 0 ≤ a * b`. -/
theorem mul_nonneg : ∀ {a b : Int}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
  | .ofNat m, .ofNat n, _, _ => by
    show (0 : Int) ≤ Int.ofNat (m * n); exact Int.ofNat_nonneg _
  | .ofNat _, .negSucc _, _, hb => by cases hb
  | .negSucc _, _, ha, _ => by cases ha

/-- ∅-axiom `Int.neg_mul`: `(-a) * b = -(a * b)` via 8-case analysis. -/
theorem neg_mul : ∀ (a b : Int), (-a) * b = -(a * b)
  | .ofNat 0, .ofNat n => by
    show Int.ofNat (0 * n) = -Int.ofNat (0 * n); rw [Nat.zero_mul]; rfl
  | .ofNat 0, .negSucc n => by
    show Int.negOfNat (0 * (n+1)) = -Int.negOfNat (0 * (n+1))
    rw [Nat.zero_mul]; rfl
  | .ofNat (k+1), .ofNat 0 => by
    show Int.negOfNat ((k+1) * 0) = -Int.ofNat ((k+1) * 0)
    rw [Nat.mul_zero]; rfl
  | .ofNat (_+1), .ofNat (_+1) => rfl
  | .ofNat (_+1), .negSucc _ => rfl
  | .negSucc m, .ofNat 0 => by
    show Int.ofNat ((m+1) * 0) = -Int.negOfNat ((m+1) * 0)
    rw [Nat.mul_zero]; rfl
  | .negSucc _, .ofNat (_+1) => rfl
  | .negSucc _, .negSucc _ => rfl

/-- ∅-axiom `Int.mul_neg`: `a * (-b) = -(a * b)` via `mul_comm` + `neg_mul`. -/
theorem mul_neg (a b : Int) : a * (-b) = -(a * b) := by
  rw [mul_comm a (-b), neg_mul, mul_comm b a]

/-- ∅-axiom Nat helper: `a ≤ b → a - b = 0`. -/
private theorem sub_eq_zero_of_le_nat : ∀ {a b : Nat}, a ≤ b → a - b = 0
  | 0, b, _ => Nat.zero_sub b
  | _+1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | a'+1, b'+1, h => by
    show (a' + 1) - (b' + 1) = 0
    rw [Nat.succ_sub_succ_eq_sub]
    exact sub_eq_zero_of_le_nat (Nat.le_of_succ_le_succ h)

/-- ∅-axiom: `subNatNat (a+1) (b+1) = subNatNat a b`. -/
theorem subNatNat_succ_succ (a b : Nat) :
    Int.subNatNat (a+1) (b+1) = Int.subNatNat a b := by
  show (match (b+1) - (a+1) with
        | 0 => Int.ofNat ((a+1) - (b+1))
        | j+1 => Int.negSucc j)
       = (match b - a with
          | 0 => Int.ofNat (a - b)
          | j+1 => Int.negSucc j)
  rw [Nat.succ_sub_succ_eq_sub, Nat.succ_sub_succ_eq_sub]

/-- ∅-axiom: `subNatNat (a+c) (b+c) = subNatNat a b`. -/
theorem subNatNat_add_add : ∀ (a b c : Nat),
    Int.subNatNat (a + c) (b + c) = Int.subNatNat a b := by
  intro a b c
  induction c with
  | zero => rfl
  | succ k ih =>
    show Int.subNatNat ((a + k) + 1) ((b + k) + 1) = Int.subNatNat a b
    rw [subNatNat_succ_succ]
    exact ih

/-- ★★★★★ ∅-axiom: `subNatNat m n + ofNat n = ofNat m`.
    The keystone identity for deriving `Int.add_assoc` /
    `Int.sub_add_cancel` PURE. -/
theorem subNatNat_add_self : ∀ (m n : Nat),
    Int.subNatNat m n + Int.ofNat n = Int.ofNat m := by
  intro m n
  show (match (n - m : Nat) with
        | 0 => Int.ofNat (m - n)
        | k+1 => Int.negSucc k) + Int.ofNat n = Int.ofNat m
  match h : n - m with
  | 0 =>
    show Int.ofNat ((m - n) + n) = Int.ofNat m
    have hle : n ≤ m := Nat.le_of_sub_eq_zero h
    rw [sub_add_cancel hle]
  | k+1 =>
    show Int.subNatNat n (k+1) = Int.ofNat m
    show (match ((k+1) - n : Nat) with
          | 0 => Int.ofNat (n - (k+1))
          | j+1 => Int.negSucc j) = Int.ofNat m
    have hle : m ≤ n := by
      rcases Nat.lt_or_ge n m with h_lt | h_ge
      · have h0 : n - m = 0 := sub_eq_zero_of_le_nat (Nat.le_of_lt h_lt)
        rw [h0] at h
        exact Nat.noConfusion h
      · exact h_ge
    have hn_eq : n = m + (k+1) := by
      have hsa : (n - m) + m = n := by
        rw [Nat.add_comm]; exact add_sub_of_le hle
      rw [h, Nat.add_comm] at hsa
      exact hsa.symm
    have h_n_ge : k + 1 ≤ n := by rw [hn_eq]; exact Nat.le_add_left _ _
    have h_kn_zero : (k+1) - n = 0 := sub_eq_zero_of_le_nat h_n_ge
    rw [h_kn_zero]
    show Int.ofNat (n - (k+1)) = Int.ofNat m
    rw [hn_eq, add_sub_cancel_right]

/-- ∅-axiom: `subNatNat m 0 = ofNat m`. -/
theorem subNatNat_zero (m : Nat) : Int.subNatNat m 0 = Int.ofNat m := by
  show (match (0 - m : Nat) with
        | 0 => Int.ofNat (m - 0)
        | k+1 => Int.negSucc k) = Int.ofNat m
  rw [Nat.zero_sub]; rfl

/-- ∅-axiom: `subNatNat 0 (m+1) = negSucc m`. -/
theorem subNatNat_zero_succ (m : Nat) : Int.subNatNat 0 (m+1) = Int.negSucc m := rfl

/-- ★★★★★ ∅-axiom: `subNatNat k m + negSucc k = negSucc m`.
    The negSucc analog of `subNatNat_add_self`.  Critical for
    the negSucc/negSucc case of `Int.sub_add_cancel`. -/
theorem subNatNat_add_negSucc_self (k m : Nat) :
    Int.subNatNat k m + Int.negSucc k = Int.negSucc m := by
  rcases Nat.lt_or_ge m k with h_lt | h_ge
  · have h_eq : m - k = 0 := sub_eq_zero_of_le_nat (Nat.le_of_lt h_lt)
    show (match m - k with | 0 => Int.ofNat (k - m) | j+1 => Int.negSucc j)
            + Int.negSucc k = Int.negSucc m
    rw [h_eq]
    show Int.subNatNat (k - m) (k + 1) = Int.negSucc m
    have h_k1 : k + 1 = (m + 1) + (k - m) := by
      have h_km : m + (k - m) = k := add_sub_of_le (Nat.le_of_lt h_lt)
      rw [Nat.add_right_comm, h_km]
    rw [h_k1]
    have hsa : Int.subNatNat (0 + (k - m)) ((m + 1) + (k - m))
                = Int.subNatNat 0 (m+1) :=
      subNatNat_add_add 0 (m+1) (k-m)
    rw [Nat.zero_add] at hsa
    rw [hsa]
    rfl
  · rcases Nat.eq_or_lt_of_le h_ge with h_eq | h_gt
    · rw [← h_eq]
      show Int.subNatNat k k + Int.negSucc k = Int.negSucc k
      rw [Int.subNatNat_self]
      rfl
    · have h_ge1 : 1 ≤ m - k := sub_pos_of_lt h_gt
      have h_eq : m - k = (m - k - 1) + 1 := by
        rw [Nat.sub_one_add_one_eq_of_pos h_ge1]
      show (match m - k with | 0 => Int.ofNat (k - m) | j+1 => Int.negSucc j)
              + Int.negSucc k = Int.negSucc m
      rw [h_eq]
      show Int.negSucc ((m - k - 1) + k).succ = Int.negSucc m
      congr 1
      show (m - k - 1) + k + 1 = m
      have h1 : (m - k - 1) + 1 = m - k := by rw [← h_eq]
      rw [Nat.add_right_comm (m - k - 1) k 1, h1]
      exact sub_add_cancel (Nat.le_of_lt h_gt)

/-- ★★★★★★★ ∅-axiom: `Int.sub_add_cancel`: `a - b + b = a`.
    Foundation for `Int.add_assoc` of specific shapes. -/
theorem sub_add_cancel_int (a b : Int) : a - b + b = a := by
  rw [Int.sub_eq_add_neg]
  cases b with
  | ofNat n =>
    cases n with
    | zero =>
      show a + 0 + 0 = a
      rw [Int.add_zero, Int.add_zero]
    | succ k =>
      show a + Int.negSucc k + Int.ofNat (k+1) = a
      cases a with
      | ofNat m =>
        show Int.subNatNat m (k+1) + Int.ofNat (k+1) = Int.ofNat m
        exact subNatNat_add_self m (k+1)
      | negSucc m =>
        show Int.subNatNat (k+1) (m+k+1+1) = Int.negSucc m
        have heq : m+k+1+1 = (m+1) + (k+1) := by
          rw [Nat.add_right_comm m k 1, Nat.add_assoc (m+1) k 1]
        rw [heq]
        have h1 : Int.subNatNat ((0 : Nat) + (k+1)) ((m+1) + (k+1))
                = Int.subNatNat 0 (m+1) := subNatNat_add_add 0 (m+1) (k+1)
        rw [Nat.zero_add] at h1
        rw [h1]
        rfl
  | negSucc k =>
    show a + Int.ofNat (k+1) + Int.negSucc k = a
    cases a with
    | ofNat m =>
      show Int.subNatNat (m + (k+1)) (k+1) = Int.ofNat m
      have h1 : Int.subNatNat (m + (k+1)) (0 + (k+1)) = Int.subNatNat m 0 :=
        subNatNat_add_add m 0 (k+1)
      rw [Nat.zero_add] at h1
      rw [h1, subNatNat_zero]
    | negSucc m =>
      show Int.subNatNat (k+1) (m+1) + Int.negSucc k = Int.negSucc m
      rw [subNatNat_succ_succ]
      exact subNatNat_add_negSucc_self k m

/-- ∅-axiom: when `b ≤ a`, `subNatNat a b = ofNat (a - b)`. -/
theorem subNatNat_of_le {a b : Nat} (h : b ≤ a) :
    Int.subNatNat a b = Int.ofNat (a - b) := by
  show (match (b - a : Nat) with
        | 0 => Int.ofNat (a - b)
        | k+1 => Int.negSucc k) = Int.ofNat (a - b)
  have hba : b - a = 0 := sub_eq_zero_of_le_nat h
  rw [hba]

/-- ∅-axiom: when `a < b`, `subNatNat a b = negSucc (b - a - 1)`. -/
theorem subNatNat_of_lt {a b : Nat} (h : a < b) :
    Int.subNatNat a b = Int.negSucc (b - a - 1) := by
  show (match (b - a : Nat) with
        | 0 => Int.ofNat (a - b)
        | k+1 => Int.negSucc k) = Int.negSucc (b - a - 1)
  have h1 : 1 ≤ b - a := sub_pos_of_lt h
  generalize hba : b - a = m at h1 ⊢
  cases m with
  | zero => exact absurd h1 (by decide)
  | succ k => rfl

/-- ∅-axiom Nat helper: `(a-b) + (c-d) = (a+c) - (b+d)` when `b ≤ a, d ≤ c`. -/
theorem nat_diff_add_diff {a b c d : Nat} (h1 : b ≤ a) (h2 : d ≤ c) :
    (a - b) + (c - d) = (a + c) - (b + d) := by
  -- Strategy: ((a-b)+(c-d)) + (b+d) = a+c, then add_sub_cancel_right.
  have h_eq : ((a - b) + (c - d)) + (b + d) = a + c := by
    -- Rearrange: ((a-b)+(c-d)) + (b+d) = ((a-b)+b) + ((c-d)+d) = a + c.
    have rearrange : ((a - b) + (c - d)) + (b + d)
                   = ((a - b) + b) + ((c - d) + d) := by
      rw [Nat.add_assoc (a - b) (c - d) (b + d),
          ← Nat.add_assoc (c - d) b d,
          Nat.add_comm (c - d) b,
          Nat.add_assoc b (c - d) d,
          ← Nat.add_assoc (a - b) b ((c - d) + d)]
    rw [rearrange, sub_add_cancel h1, sub_add_cancel h2]
  -- ((a-b)+(c-d)) + (b+d) - (b+d) = (a-b)+(c-d) by add_sub_cancel_right
  have h_cancel : ((a - b) + (c - d)) + (b + d) - (b + d) = (a - b) + (c - d) :=
    add_sub_cancel_right _ _
  -- Substitute h_eq into h_cancel
  rw [h_eq] at h_cancel
  exact h_cancel.symm

/-- ∅-axiom Nat helper: `X + Y + 1 = (X + 1) + (Y + 1) - 1`. -/
private theorem add_one_add_one_sub_one (X Y : Nat) :
    X + Y + 1 = (X + 1) + (Y + 1) - 1 := by
  have h : (X + 1) + (Y + 1) = (X + Y + 1) + 1 := by
    rw [Nat.add_assoc X 1 (Y + 1),
        Nat.add_comm 1 (Y + 1),
        ← Nat.add_assoc X (Y + 1) 1,
        ← Nat.add_assoc X Y 1]
  rw [h]
  exact (add_sub_cancel_right (X + Y + 1) 1).symm

/-- ★★★★★★★ ∅-axiom Keystone:
    `subNatNat a b + subNatNat c d = subNatNat (a+c) (b+d)`.
    Unifies all 4 Int.add cases via subNatNat representation;
    foundation for `add_assoc` and downstream ring identities. -/
theorem subNatNat_add_subNatNat (a b c d : Nat) :
    Int.subNatNat a b + Int.subNatNat c d = Int.subNatNat (a + c) (b + d) := by
  rcases Nat.lt_or_ge a b with hab | hab
  · rcases Nat.lt_or_ge c d with hcd | hcd
    · -- Case IV: a < b, c < d. Both negSucc.
      rw [subNatNat_of_lt hab, subNatNat_of_lt hcd]
      have hac : a + c < b + d := Nat.add_lt_add hab hcd
      rw [subNatNat_of_lt hac]
      show Int.negSucc ((b - a - 1) + (d - c - 1) + 1)
         = Int.negSucc ((b + d) - (a + c) - 1)
      congr 1
      have h_diff : (b + d) - (a + c) = (b - a) + (d - c) :=
        (nat_diff_add_diff (Nat.le_of_lt hab) (Nat.le_of_lt hcd)).symm
      rw [h_diff]
      have hba_pos : 1 ≤ b - a := sub_pos_of_lt hab
      have hdc_pos : 1 ≤ d - c := sub_pos_of_lt hcd
      have h_b_split : b - a = (b - a - 1) + 1 :=
        (Nat.sub_one_add_one_eq_of_pos hba_pos).symm
      have h_d_split : d - c = (d - c - 1) + 1 :=
        (Nat.sub_one_add_one_eq_of_pos hdc_pos).symm
      rw [h_b_split, h_d_split]
      exact add_one_add_one_sub_one _ _
    · -- Case III: a < b, d ≤ c. Mixed (negSucc + ofNat).
      rw [subNatNat_of_lt hab, subNatNat_of_le hcd]
      have hba_pos : 1 ≤ b - a := sub_pos_of_lt hab
      show Int.subNatNat (c - d) ((b - a - 1) + 1)
         = Int.subNatNat (a + c) (b + d)
      rw [Nat.sub_one_add_one_eq_of_pos hba_pos]
      have h1 : (c - d) + (a + d) = a + c := by
        rw [Nat.add_comm a d, ← Nat.add_assoc (c - d) d a,
            sub_add_cancel hcd, Nat.add_comm c a]
      have h2 : (b - a) + (a + d) = b + d := by
        rw [← Nat.add_assoc (b - a) a d, sub_add_cancel (Nat.le_of_lt hab)]
      rw [← h1, ← h2]
      exact (subNatNat_add_add (c - d) (b - a) (a + d)).symm
  · rcases Nat.lt_or_ge c d with hcd | hcd
    · -- Case II: b ≤ a, c < d. Mixed (ofNat + negSucc).
      rw [subNatNat_of_le hab, subNatNat_of_lt hcd]
      have hdc_pos : 1 ≤ d - c := sub_pos_of_lt hcd
      show Int.subNatNat (a - b) ((d - c - 1) + 1)
         = Int.subNatNat (a + c) (b + d)
      rw [Nat.sub_one_add_one_eq_of_pos hdc_pos]
      have h1 : (a - b) + (b + c) = a + c := by
        rw [← Nat.add_assoc (a - b) b c, sub_add_cancel hab]
      have h2 : (d - c) + (b + c) = b + d := by
        rw [Nat.add_comm b c, ← Nat.add_assoc (d - c) c b,
            sub_add_cancel (Nat.le_of_lt hcd), Nat.add_comm d b]
      rw [← h1, ← h2]
      exact (subNatNat_add_add (a - b) (d - c) (b + c)).symm
    · -- Case I: b ≤ a, d ≤ c. Both ofNat.
      rw [subNatNat_of_le hab, subNatNat_of_le hcd]
      have hac : b + d ≤ a + c := Nat.add_le_add hab hcd
      rw [subNatNat_of_le hac]
      show Int.ofNat ((a - b) + (c - d)) = Int.ofNat ((a + c) - (b + d))
      rw [nat_diff_add_diff hab hcd]

/-- ∅-axiom: every Int has a `subNatNat` representation. -/
theorem subNatNat_repr : ∀ (a : Int), ∃ p q, a = Int.subNatNat p q
  | .ofNat n   => ⟨n, 0,   (subNatNat_zero n).symm⟩
  | .negSucc n => ⟨0, n+1, (subNatNat_zero_succ n).symm⟩

/-- ★★★★★★★ ∅-axiom: `Int.add_assoc`. -/
theorem add_assoc (a b c : Int) : a + b + c = a + (b + c) := by
  obtain ⟨a1, a2, ha⟩ := subNatNat_repr a
  obtain ⟨b1, b2, hb⟩ := subNatNat_repr b
  obtain ⟨c1, c2, hc⟩ := subNatNat_repr c
  rw [ha, hb, hc,
      subNatNat_add_subNatNat, subNatNat_add_subNatNat,
      subNatNat_add_subNatNat, subNatNat_add_subNatNat,
      Nat.add_assoc, Nat.add_assoc]

/-- ∅-axiom: `negOfNat n = subNatNat 0 n`. -/
theorem negOfNat_eq_subNatNat (n : Nat) :
    Int.negOfNat n = Int.subNatNat 0 n := by
  cases n with
  | zero => rfl
  | succ k => rfl

/-- ∅-axiom: `subNatNat A B * ofNat γ = subNatNat (A*γ) (B*γ)`. -/
theorem subNatNat_mul_ofNat (a b c : Nat) :
    Int.subNatNat a b * Int.ofNat c = Int.subNatNat (a * c) (b * c) := by
  rcases Nat.lt_or_ge a b with hab | hab
  · -- a < b
    rw [subNatNat_of_lt hab]
    have hba_pos : 1 ≤ b - a := sub_pos_of_lt hab
    show Int.negOfNat (((b - a - 1) + 1) * c) = Int.subNatNat (a * c) (b * c)
    rw [Nat.sub_one_add_one_eq_of_pos hba_pos, negOfNat_eq_subNatNat,
        ← subNatNat_add_add 0 ((b - a) * c) (a * c), Nat.zero_add]
    congr 1
    rw [← E213.Tactic.NatHelper.add_mul, sub_add_cancel (Nat.le_of_lt hab)]
  · -- b ≤ a
    rw [subNatNat_of_le hab]
    show Int.ofNat ((a - b) * c) = Int.subNatNat (a * c) (b * c)
    have hac : b * c ≤ a * c := Nat.mul_le_mul_right c hab
    rw [subNatNat_of_le hac, Nat.mul_comm (a-b) c, mul_sub_distrib hab,
        Nat.mul_comm c a, Nat.mul_comm c b]

/-- ∅-axiom: `subNatNat A B * negSucc δ = subNatNat (B*(δ+1)) (A*(δ+1))`. -/
theorem subNatNat_mul_negSucc (a b d : Nat) :
    Int.subNatNat a b * Int.negSucc d
      = Int.subNatNat (b * (d + 1)) (a * (d + 1)) := by
  rcases Nat.lt_or_ge a b with hab | hab
  · -- a < b
    rw [subNatNat_of_lt hab]
    have hba_pos : 1 ≤ b - a := sub_pos_of_lt hab
    show Int.ofNat (((b - a - 1) + 1) * (d + 1))
       = Int.subNatNat (b * (d + 1)) (a * (d + 1))
    rw [Nat.sub_one_add_one_eq_of_pos hba_pos]
    have h : a * (d + 1) ≤ b * (d + 1) :=
      Nat.mul_le_mul_right (d + 1) (Nat.le_of_lt hab)
    rw [subNatNat_of_le h, Nat.mul_comm (b-a) (d+1), mul_sub_distrib (Nat.le_of_lt hab),
        Nat.mul_comm (d+1) b, Nat.mul_comm (d+1) a]
  · -- b ≤ a
    rw [subNatNat_of_le hab]
    show Int.negOfNat ((a - b) * (d + 1))
       = Int.subNatNat (b * (d + 1)) (a * (d + 1))
    rw [negOfNat_eq_subNatNat,
        ← subNatNat_add_add 0 ((a - b) * (d + 1)) (b * (d + 1)),
        Nat.zero_add]
    congr 1
    rw [← E213.Tactic.NatHelper.add_mul, sub_add_cancel hab]

/-- ★★★★★★★ ∅-axiom: `Int.add_mul`: `(a + b) * c = a * c + b * c`. -/
theorem add_mul (a b c : Int) : (a + b) * c = a * c + b * c := by
  obtain ⟨a1, a2, ha⟩ := subNatNat_repr a
  obtain ⟨b1, b2, hb⟩ := subNatNat_repr b
  rw [ha, hb, subNatNat_add_subNatNat]
  cases c with
  | ofNat γ =>
    rw [subNatNat_mul_ofNat, subNatNat_mul_ofNat, subNatNat_mul_ofNat,
        subNatNat_add_subNatNat,
        E213.Tactic.NatHelper.add_mul a1 b1 γ,
        E213.Tactic.NatHelper.add_mul a2 b2 γ]
  | negSucc δ =>
    rw [subNatNat_mul_negSucc, subNatNat_mul_negSucc, subNatNat_mul_negSucc,
        subNatNat_add_subNatNat,
        E213.Tactic.NatHelper.add_mul a2 b2 (δ + 1),
        E213.Tactic.NatHelper.add_mul a1 b1 (δ + 1)]

/-- ∅-axiom: `Int.mul_add`: `a * (b + c) = a*b + a*c`. -/
theorem mul_add (a b c : Int) : a * (b + c) = a * b + a * c := by
  rw [mul_comm a (b + c), add_mul, mul_comm b a, mul_comm c a]

/-- ∅-axiom Nat helper: `(p-q) + (q+r) = p+r` when `q ≤ p`. -/
private theorem nat_help_subadd1 {p q r : Nat} (h : q ≤ p) :
    (p - q) + (q + r) = p + r := by
  rw [← Nat.add_assoc (p - q) q r, sub_add_cancel h]

/-- ∅-axiom Nat helper: `(p-q) + (r+q) = r+p` when `q ≤ p`. -/
private theorem nat_help_subadd2 {p q r : Nat} (h : q ≤ p) :
    (p - q) + (r + q) = r + p := by
  rw [Nat.add_comm r q, nat_help_subadd1 h, Nat.add_comm p r]

/-- ★★★★★★★ ∅-axiom Multiplication keystone:
    `subNatNat a b * subNatNat c d = subNatNat (a*c + b*d) (a*d + b*c)`. -/
theorem subNatNat_mul_subNatNat (a b c d : Nat) :
    Int.subNatNat a b * Int.subNatNat c d
      = Int.subNatNat (a * c + b * d) (a * d + b * c) := by
  rcases Nat.lt_or_ge c d with hcd | hcd
  · -- c < d: subNatNat c d = negSucc (d-c-1)
    rw [subNatNat_of_lt hcd]
    have hdc_pos : 1 ≤ d - c := sub_pos_of_lt hcd
    rw [subNatNat_mul_negSucc]
    show Int.subNatNat (b * ((d - c - 1) + 1)) (a * ((d - c - 1) + 1))
       = Int.subNatNat (a * c + b * d) (a * d + b * c)
    rw [Nat.sub_one_add_one_eq_of_pos hdc_pos]
    rw [← subNatNat_add_add (b * (d - c)) (a * (d - c)) (a * c + b * c)]
    have hcd_le : c ≤ d := Nat.le_of_lt hcd
    have hbc_le : b * c ≤ b * d := Nat.mul_le_mul_left b hcd_le
    have hac_le : a * c ≤ a * d := Nat.mul_le_mul_left a hcd_le
    rw [mul_sub_distrib hcd_le, mul_sub_distrib hcd_le,
        nat_help_subadd2 hbc_le, nat_help_subadd1 hac_le]
  · -- d ≤ c: subNatNat c d = ofNat (c-d)
    rw [subNatNat_of_le hcd]
    rw [subNatNat_mul_ofNat]
    rw [← subNatNat_add_add (a * (c - d)) (b * (c - d)) (a * d + b * d)]
    have hbd_le : b * d ≤ b * c := Nat.mul_le_mul_left b hcd
    have had_le : a * d ≤ a * c := Nat.mul_le_mul_left a hcd
    rw [mul_sub_distrib hcd, mul_sub_distrib hcd,
        nat_help_subadd1 had_le, nat_help_subadd2 hbd_le]

/-- ★★★★★★★ ∅-axiom: `Int.mul_assoc`: `a * b * c = a * (b * c)`. -/
theorem mul_assoc (a b c : Int) : a * b * c = a * (b * c) := by
  obtain ⟨a1, a2, ha⟩ := subNatNat_repr a
  obtain ⟨b1, b2, hb⟩ := subNatNat_repr b
  rw [ha, hb]
  cases c with
  | ofNat γ =>
    rw [subNatNat_mul_subNatNat, subNatNat_mul_ofNat, subNatNat_mul_ofNat,
        subNatNat_mul_subNatNat,
        E213.Tactic.NatHelper.add_mul, E213.Tactic.NatHelper.add_mul,
        E213.Tactic.NatHelper.mul_assoc, E213.Tactic.NatHelper.mul_assoc,
        E213.Tactic.NatHelper.mul_assoc, E213.Tactic.NatHelper.mul_assoc]
  | negSucc δ =>
    rw [subNatNat_mul_subNatNat, subNatNat_mul_negSucc, subNatNat_mul_negSucc,
        subNatNat_mul_subNatNat,
        E213.Tactic.NatHelper.add_mul, E213.Tactic.NatHelper.add_mul,
        E213.Tactic.NatHelper.mul_assoc, E213.Tactic.NatHelper.mul_assoc,
        E213.Tactic.NatHelper.mul_assoc, E213.Tactic.NatHelper.mul_assoc]

/-- ∅-axiom: `Int.mul_left_comm`: `a * (b * c) = b * (a * c)`. -/
theorem mul_left_comm (a b c : Int) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a b, mul_assoc]

/-- ∅-axiom: `(x·y)·(z·w) = (x·z)·(y·w)` — the middle-swap shuffle. -/
theorem mul_mul_mul_comm (x y z w : Int) :
    (x * y) * (z * w) = (x * z) * (y * w) := by
  rw [mul_assoc x y (z * w), mul_left_comm y z w, ← mul_assoc x z (y * w)]

/-- ∅-axiom: `Int.zero_add` (Lean-core is propext). -/
theorem zero_add (a : Int) : 0 + a = a := by
  rw [add_comm, Int.add_zero]

/-- ∅-axiom: `a + -a = 0`. -/
theorem add_neg_cancel (a : Int) : a + -a = 0 := by
  rw [add_comm, add_left_neg]

/-- ∅-axiom: `Int.add_left_comm`: `a + (b + c) = b + (a + c)`. -/
theorem add_left_comm (a b c : Int) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a b, add_assoc]

/-- ∅-axiom: `Int.add_right_comm`: `a + b + c = a + c + b`. -/
theorem add_right_comm (a b c : Int) : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b c, ← add_assoc]

/-- ∅-axiom: `Int.mul_one`. -/
theorem mul_one (a : Int) : a * 1 = a := by
  rw [mul_comm]; exact Int.one_mul a

/-- `Int.mul_sub` — PURE replacement for Lean-core
    `Int.mul_sub` (which brings propext via Iff-chain derivation).
    Composed from `mul_add` + `mul_neg`. -/
theorem mul_sub (a b c : Int) : a * (b - c) = a * b - a * c := by
  show a * (b + -c) = a * b + -(a * c)
  rw [mul_add a b (-c), mul_neg]

/-- `Int.sub_mul` — PURE replacement for Lean-core `Int.sub_mul`. -/
theorem sub_mul (a b c : Int) : (a - b) * c = a * c - b * c := by
  show (a + -b) * c = a * c + -(b * c)
  rw [add_mul a (-b) c, neg_mul]

/-! ## Order / domain finishing helpers -/

/-- `0 ≤ N + N → 0 ≤ N` over `Int` (constructive halving).  `negSucc m
    + negSucc m` reduces to `negSucc (m + m + 1)`, which is never
    `Int.NonNeg`.  PURE. -/
theorem nonneg_of_add_self {N : Int} (h : 0 ≤ N + N) : 0 ≤ N := by
  cases N with
  | ofNat m => exact Int.ofNat_nonneg m
  | negSucc m =>
      exfalso
      have e : Int.negSucc m + Int.negSucc m = Int.negSucc (m + m + 1) := rfl
      rw [e] at h
      cases h

/-- Cross-product step identity for the `c₁ = 3, c₂ = -1` (d = 0)
    Pell recurrence: `b·(3q + (-1)p + 0) − (3b + (-1)a + 0)·q = aq − bp`.
    Explicit Int213 `rw`-chain (no `simp`, no `omega`).  PURE. -/
theorem cross_step_algebra (a b p q : Int) :
    b * (3 * q + (-1) * p + 0) - (3 * b + (-1) * a + 0) * q = a * q - b * p := by
  have hnp : ((-1 : Int) * p) = -p := by
    rw [neg_mul, Int.one_mul]
  have hna : ((-1 : Int) * a) = -a := by
    rw [neg_mul, Int.one_mul]
  rw [Int.add_zero, Int.add_zero, hnp, hna]
  rw [mul_add, add_mul]
  rw [mul_neg, neg_mul]
  rw [mul_left_comm b 3 q, mul_assoc 3 b q]
  rw [Int.sub_eq_add_neg, neg_add, Int.neg_neg]
  rw [add_assoc (3*(b*q)) (-(b*p)) (-(3*(b*q)) + a*q)]
  rw [add_left_comm (-(b*p)) (-(3*(b*q))) (a*q)]
  rw [← add_assoc (3*(b*q)) (-(3*(b*q))) (-(b*p) + a*q)]
  rw [add_neg_cancel, zero_add]
  rw [add_comm (-(b*p)) (a*q), ← Int.sub_eq_add_neg]

/-! ## Sign / zero kernel -/

/-- A nonzero `x` times `y` is zero ⟹ `y = 0` (`Int` has no zero
    divisors).  Decidable case split (no `propext` from the
    `mul_eq_zero` iff). -/
theorem int_eq_zero_of_mul_left {x y : Int} (hx : x ≠ 0) (h : x * y = 0) : y = 0 := by
  rcases mul_eq_zero h with hx0 | hy0
  · exact absurd hx0 hx
  · exact hy0

/-- A nonzero integer differs from its negation. -/
theorem int_ne_neg_self {x : Int} (h : x ≠ 0) : x ≠ -x := by
  match x with
  | Int.ofNat 0 => exact absurd rfl h
  | Int.ofNat (k + 1) => intro he; exact Int.noConfusion he
  | Int.negSucc k => intro he; exact Int.noConfusion he

/-- An integer equal to its own negation is zero. -/
theorem int_eq_zero_of_eq_neg {x : Int} (h : x = -x) : x = 0 := by
  have hxx : x + x = 0 := (congrArg (x + ·) h).trans (add_neg_cancel x)
  cases x with
  | ofNat m =>
    rw [show Int.ofNat m + Int.ofNat m = Int.ofNat (m + m) from rfl] at hxx
    have hm0 : m = 0 := Nat.eq_zero_of_add_eq_zero_right (Int.ofNat.inj hxx)
    subst hm0; rfl
  | negSucc m =>
    rw [show Int.negSucc m + Int.negSucc m = Int.negSucc (m + m + 1) from rfl] at hxx
    exact Int.noConfusion hxx

/-! ## Witness characterization — the order presentation of the difference-Lens

The pair `(a, b)` can name its difference two ways: by the equation
`a + x = b`, or by the sandwich `a + x < b + 1 ∧ b < a + x + 1`.  Over `ℕ`
the two presentations coincide (`eq_of_sandwich`), the witness is unique
(`witness_unique`), and the equation is solvable for **exactly one
orientation** of the pair: `subNatNat b a` reads out `ofNat x` precisely
when `x` witnesses `a + x = b` (`subNatNat_eq_ofNat_iff`), and `negSucc y`
precisely when the *swapped* equation `b + (y + 1) = a` is witnessed
(`subNatNat_eq_negSucc_iff`); the two sides are total (`witness_total`)
and exclusive (`witness_not_both`).  Sign = which orientation carries the
ℕ-witness — the order-side statement of the pair-swap `neg_subNatNat`.
The diagonal `(n, n)` is the boundary case: witnessed by `x = 0` on the
`ofNat` side only (`Int.subNatNat_self`).  Narrative:
`theory/essays/analysis/integers_as_difference_lens.md`. -/

/-- The sandwich pins the equation: `a + x < b + 1` and `b < a + x + 1`
    force `a + x = b`.  The strict-inequality pair is not a weaker
    presentation of the difference — over `ℕ` it is the same one. -/
theorem eq_of_sandwich {a b x : Nat}
    (h1 : a + x < b + 1) (h2 : b < a + x + 1) : a + x = b :=
  Nat.le_antisymm (Nat.le_of_lt_succ h1) (Nat.le_of_lt_succ h2)

/-- Witness uniqueness: `a + x = b` has at most one solution `x`. -/
theorem witness_unique {a b x y : Nat} (hx : a + x = b) (hy : a + y = b) :
    x = y :=
  add_left_cancel (hx.trans hy.symm)

/-- Witness reading, positive side: `subNatNat b a` reads out the natural
    `x` exactly when `x` witnesses `a + x = b`. -/
theorem subNatNat_eq_ofNat_iff (a b x : Nat) :
    Int.subNatNat b a = Int.ofNat x ↔ a + x = b := by
  constructor
  · intro h
    rcases Nat.lt_or_ge b a with hba | hba
    · rw [subNatNat_of_lt hba] at h
      exact Int.noConfusion h
    · rw [subNatNat_of_le hba] at h
      have hx : b - a = x := Int.ofNat.inj h
      rw [← hx]
      exact add_sub_of_le hba
  · intro h
    have h1 : Int.subNatNat (x + a) (0 + a) = Int.subNatNat x 0 :=
      subNatNat_add_add x 0 a
    rw [Nat.zero_add] at h1
    rw [← h, Nat.add_comm a x, h1, subNatNat_zero]

/-- Witness reading, negative side: `subNatNat b a` reads out `negSucc y`
    exactly when the *swapped* equation `b + (y + 1) = a` is witnessed.
    The unsolvability of `a + x = b` is not a failure of the pair — it is
    the solvability of its swap, read through `neg_subNatNat`. -/
theorem subNatNat_eq_negSucc_iff (a b y : Nat) :
    Int.subNatNat b a = Int.negSucc y ↔ b + (y + 1) = a := by
  constructor
  · intro h
    rcases Nat.lt_or_ge b a with hba | hba
    · rw [subNatNat_of_lt hba] at h
      have hk : a - b - 1 = y := Int.negSucc.inj h
      have h2 : (a - b - 1) + 1 = a - b :=
        Nat.sub_one_add_one_eq_of_pos (sub_pos_of_lt hba)
      rw [hk] at h2
      rw [h2]
      exact add_sub_of_le (Nat.le_of_lt hba)
    · rw [subNatNat_of_le hba] at h
      exact Int.noConfusion h
  · intro h
    have h1 : Int.subNatNat (0 + b) ((y + 1) + b) = Int.subNatNat 0 (y + 1) :=
      subNatNat_add_add 0 (y + 1) b
    rw [Nat.zero_add] at h1
    rw [← h, Nat.add_comm b (y + 1), h1, subNatNat_zero_succ]

/-- Witness totality: every oriented pair is witnessed from one side —
    `a + x = b` solvable, or the swap `b + (y + 1) = a` solvable. -/
theorem witness_total (a b : Nat) :
    (∃ x, a + x = b) ∨ (∃ y, b + (y + 1) = a) := by
  rcases Nat.lt_or_ge b a with hba | hba
  · exact Or.inr ⟨a - b - 1,
      (subNatNat_eq_negSucc_iff a b _).mp (subNatNat_of_lt hba)⟩
  · exact Or.inl ⟨b - a, add_sub_of_le hba⟩

/-- Witness exclusivity: no pair is witnessed from both orientations.
    Together with `witness_total`: sign is a readout, not a choice. -/
theorem witness_not_both {a b x y : Nat}
    (hx : a + x = b) (hy : b + (y + 1) = a) : False := by
  have h : a + (x + (y + 1)) = a := by
    rw [← Nat.add_assoc, hx]; exact hy
  have h0 : x + (y + 1) = 0 :=
    add_left_cancel (h.trans (Nat.add_zero a).symm)
  rw [← Nat.add_assoc] at h0
  have h1 : (x + y).succ = 0 := h0
  exact Nat.noConfusion h1

/-- The sandwich presentation reads out through the difference-Lens:
    the strict-inequality pair determines `subNatNat b a = ofNat x`. -/
theorem subNatNat_of_sandwich {a b x : Nat}
    (h1 : a + x < b + 1) (h2 : b < a + x + 1) :
    Int.subNatNat b a = Int.ofNat x :=
  (subNatNat_eq_ofNat_iff a b x).mpr (eq_of_sandwich h1 h2)

end E213.Meta.Int213
