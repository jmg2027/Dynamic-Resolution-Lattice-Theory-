import E213.Term.Tactic.Nat213

/-!
# Int213 — ∅-axiom Int arithmetic helpers

Lean-core `Int.add_comm`, `Int.neg_add` are proved via `simp`-heavy
tactics that pull in `propext`.  `Theory/Raw/Signed.lean` needs both
identities to make `Tree.fold_signed_swap` ∅-axiom; this file
provides 213-native term-mode replacements.

Strategy: case-split on the two Int constructors (`ofNat`,
`negSucc`), reduce via core Nat lemmas (`Nat.zero_add`,
`Nat.succ_add`, `Nat.zero_sub`, `Nat.succ_sub_succ_eq_sub`, all
∅-axiom), and recurse where needed (`neg_subNatNat`).  No `simp`,
no `omega`, no Mathlib.
-/

namespace E213.Theory.Internal.Int213

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

end E213.Theory.Internal.Int213

namespace E213.Theory.Internal.Int213

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

end E213.Theory.Internal.Int213

namespace E213.Theory.Internal.Int213

/-- ∅-axiom `Int.add_nonneg`: `0 ≤ a → 0 ≤ b → 0 ≤ a + b`.
    Replaces propext-bearing `Int.add_nonneg`. -/
theorem add_nonneg : ∀ {a b : Int}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
  | .ofNat m, .ofNat n, _, _ => by
    show (0 : Int) ≤ Int.ofNat (m + n); exact Int.ofNat_nonneg _
  | .ofNat _, .negSucc _, _, hb => by cases hb
  | .negSucc _, _, ha, _ => by cases ha

end E213.Theory.Internal.Int213

namespace E213.Theory.Internal.Int213

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

end E213.Theory.Internal.Int213

namespace E213.Theory.Internal.Int213

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

end E213.Theory.Internal.Int213

namespace E213.Theory.Internal.Int213

/-- ∅-axiom `Int.mul_nonneg`: `0 ≤ a → 0 ≤ b → 0 ≤ a * b`. -/
theorem mul_nonneg : ∀ {a b : Int}, 0 ≤ a → 0 ≤ b → 0 ≤ a * b
  | .ofNat m, .ofNat n, _, _ => by
    show (0 : Int) ≤ Int.ofNat (m * n); exact Int.ofNat_nonneg _
  | .ofNat _, .negSucc _, _, hb => by cases hb
  | .negSucc _, _, ha, _ => by cases ha

end E213.Theory.Internal.Int213

namespace E213.Theory.Internal.Int213

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

end E213.Theory.Internal.Int213

namespace E213.Theory.Internal.Int213

open E213.Tactic.Nat213 (sub_add_cancel add_sub_of_le add_sub_cancel_right)

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

end E213.Theory.Internal.Int213

namespace E213.Theory.Internal.Int213

/-- ∅-axiom: `subNatNat m 0 = ofNat m`. -/
theorem subNatNat_zero (m : Nat) : Int.subNatNat m 0 = Int.ofNat m := by
  show (match (0 - m : Nat) with
        | 0 => Int.ofNat (m - 0)
        | k+1 => Int.negSucc k) = Int.ofNat m
  rw [Nat.zero_sub]; rfl

/-- ∅-axiom: `subNatNat 0 (m+1) = negSucc m`. -/
theorem subNatNat_zero_succ (m : Nat) : Int.subNatNat 0 (m+1) = Int.negSucc m := rfl


end E213.Theory.Internal.Int213
