/-!
# shared `Int` helpers

Two basic facts about integer self-multiplication used by every
quadratic-extension `Domain` module (ZIDomain, ZSqrt2Domain,
…).  Extracted here to remove duplication.

Both lemmas ∅-axiom — direct case-analysis on `Int` constructors
(no `omega`, no `Int.mul_nonneg`/`Int.mul_eq_zero` propext-bearing
core lemmas).
-/

namespace E213.Meta.Nat.IntHelpers

/-- ∅-axiom `Int.zero_mul`, inlined from `Meta.Int213.zero_mul`. -/
private theorem zero_mul : ∀ (a : Int), 0 * a = 0
  | .ofNat n => by
    show Int.ofNat (0 * n) = (0 : Int); rw [Nat.zero_mul]; rfl
  | .negSucc n => by
    show Int.negOfNat (0 * (n+1)) = (0 : Int); rw [Nat.zero_mul]; rfl

/-- `0 ≤ a*a` for any integer `a`.  ∅-axiom. -/
protected theorem mul_self_nonneg : ∀ (a : Int), 0 ≤ a * a
  | .ofNat n => by
    show (0 : Int) ≤ Int.ofNat (n * n)
    exact Int.ofNat_nonneg _
  | .negSucc n => by
    show (0 : Int) ≤ Int.ofNat ((n+1) * (n+1))
    exact Int.ofNat_nonneg _

/-- `a*a = 0 ↔ a = 0` for any integer `a`.  ∅-axiom. -/
protected theorem mul_self_eq_zero : ∀ {a : Int}, a * a = 0 ↔ a = 0 := by
  intro a
  refine ⟨?_, fun h => by rw [h, zero_mul]⟩
  intro h
  match a with
  | .ofNat n =>
    have h1 : Int.ofNat (n * n) = (0 : Int) := h
    have h2 : n * n = 0 := Int.ofNat.inj h1
    have h3 : n = 0 := by
      match n with
      | 0 => rfl
      | k+1 =>
        exfalso
        have h_ge_1 : (k+1) * (k+1) ≥ 1 :=
          calc 1 = 1 * 1 := rfl
            _ ≤ (k+1) * 1 := Nat.mul_le_mul_right 1 (Nat.succ_le_succ (Nat.zero_le _))
            _ ≤ (k+1) * (k+1) := Nat.mul_le_mul_left (k+1) (Nat.succ_le_succ (Nat.zero_le _))
        rw [h2] at h_ge_1
        exact absurd h_ge_1 (by decide)
    rw [h3]; rfl
  | .negSucc n =>
    exfalso
    have h1 : Int.ofNat ((n+1) * (n+1)) = (0 : Int) := h
    have h2 : (n+1) * (n+1) = 0 := Int.ofNat.inj h1
    have h_ge_1 : (n+1) * (n+1) ≥ 1 :=
      calc 1 = 1 * 1 := rfl
        _ ≤ (n+1) * 1 := Nat.mul_le_mul_right 1 (Nat.succ_le_succ (Nat.zero_le _))
        _ ≤ (n+1) * (n+1) := Nat.mul_le_mul_left (n+1) (Nat.succ_le_succ (Nat.zero_le _))
    rw [h2] at h_ge_1
    exact absurd h_ge_1 (by decide)

/-- ∅-axiom: `0 ≤ a` implies `a = Int.ofNat n` for some `n`.
    Direct match on `Int.NonNeg` constructor (only `ofNat` form). -/
protected theorem le_ofNat_of_nonneg {a : Int} (h : (0 : Int) ≤ a) :
    ∃ n : Nat, a = Int.ofNat n := by
  match a, h with
  | Int.ofNat n, _ => exact ⟨n, rfl⟩
  | Int.negSucc k, h => cases h

/-- ∅-axiom replacement for `Int.add_nonneg` (which leaks propext).
    Reduces to ofNat case via `le_ofNat_of_nonneg`. -/
protected theorem add_nonneg {a b : Int} (ha : (0 : Int) ≤ a) (hb : (0 : Int) ≤ b) :
    (0 : Int) ≤ a + b := by
  obtain ⟨m, hm⟩ := IntHelpers.le_ofNat_of_nonneg ha
  obtain ⟨n, hn⟩ := IntHelpers.le_ofNat_of_nonneg hb
  subst hm; subst hn
  show (0 : Int) ≤ Int.ofNat m + Int.ofNat n
  exact Int.ofNat_nonneg _

/-- ∅-axiom replacement for `Int.add_comm` (Lean-core leaks propext).
    Term-mode 4-case match on (a, b) ∈ {ofNat, negSucc}². -/
protected theorem add_comm : ∀ (a b : Int), a + b = b + a
  | Int.ofNat m, Int.ofNat n => by
      show Int.ofNat (m + n) = Int.ofNat (n + m)
      rw [Nat.add_comm]
  | Int.ofNat _, Int.negSucc _ => rfl
  | Int.negSucc _, Int.ofNat _ => rfl
  | Int.negSucc m, Int.negSucc n => by
      show Int.negSucc (m + n + 1) = Int.negSucc (n + m + 1)
      rw [Nat.add_comm m n]

end E213.Meta.Nat.IntHelpers
