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
