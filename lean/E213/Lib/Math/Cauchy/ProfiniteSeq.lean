import E213.Lens.Instances.Cauchy
import E213.Lens.Instances.Leaves.ModNat
import E213.Lens.Cardinality.LensCardinality
import E213.Meta.Tactic.NatHelper
import E213.Meta.Tactic.Omega213

/-!
# ProfiniteSeq: Cauchy instance for the leavesModNat family

Mingu proposal (b): formal demonstration that a specific Cauchy
sequence for the leavesModNat family generates a structure analogous
to the **profinite ℤ̂ (= Ẑ)**.

## Core

A sequence xs with leaves(xs n) = factorial(n+1) is family-Cauchy
w.r.t. {leavesModNat m : m ≥ 2}.

For each m ≥ 2, n+1 ≥ m → factorial(n+1) ≡ 0 (mod m).
Therefore limit class = "0 mod m for all m" = profinite zero.

Intuitively corresponds to "infinity" in ℕ — the profinite 0 in the
Ẑ style.

## Significance

The 213 framework does not merely remain in finite combinatorics; it
also naturally generates **profinite (algebraic) limits**.

The iProdLens of the leavesModNat family is exactly the ℤ̂-like
profinite completion.  A concrete instance of Lens-as-completion.
-/

namespace E213.Lib.Math.Cauchy.ProfiniteSeq

open E213.Theory E213.Lens
open E213.Lens.Instances.Cauchy

/-- Local factorial (absent from Lean 4 core). -/
def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n

theorem factorial_pos (n : Nat) : factorial n ≥ 1 := by
  induction n with
  | zero => exact Nat.le_refl 1
  | succ k ih =>
      show 1 ≤ (k+1) * factorial k
      have h1 : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
      have h2 : k + 1 ≤ (k + 1) * factorial k := by
        have step : (k + 1) * 1 ≤ (k + 1) * factorial k :=
          Nat.mul_le_mul_left (k + 1) ih
        rw [Nat.mul_one] at step
        exact step
      exact Nat.le_trans h1 h2

/-- factorial n is divisible by every m ≤ n.  ∅-axiom via
    `E213.Tactic.NatHelper.mul_assoc` and core-pure `Nat.mul_comm`. -/
theorem factorial_dvd (m n : Nat) (h : 1 ≤ m) (hmn : m ≤ n) :
    m ∣ factorial n := by
  induction n with
  | zero => exact absurd (Nat.le_trans h hmn) (Nat.not_succ_le_zero 0)
  | succ k ih =>
      by_cases hkm : m ≤ k
      · have hdvd : m ∣ factorial k := ih hkm
        show m ∣ (k+1) * factorial k
        obtain ⟨q, hq⟩ := hdvd
        refine ⟨(k+1) * q, ?_⟩
        rw [hq, ← E213.Tactic.NatHelper.mul_assoc (k+1) m q,
            Nat.mul_comm (k+1) m, E213.Tactic.NatHelper.mul_assoc m (k+1) q]
      · have hmk1 : m = k + 1 :=
          Nat.le_antisymm hmn (Nat.lt_of_not_le hkm)
        show m ∣ (k+1) * factorial k
        rw [hmk1]
        exact ⟨factorial k, rfl⟩

end E213.Lib.Math.Cauchy.ProfiniteSeq

namespace E213.Lib.Math.Cauchy.ProfiniteSeq

open E213.Theory E213.Lens
open E213.Lens.Instances.Leaves.ModNat E213.Lens.Instances.Cauchy

/-- The factorial sequence is eventually 0 mod m (when n + 1 ≥ m).
    ∅-axiom via `E213.Tactic.NatHelper.mul_mod_right`. -/
theorem factorial_eventually_zero_mod (m : Nat) (hm : 1 ≤ m)
    (n : Nat) (hn : n + 1 ≥ m) : factorial (n + 1) % m = 0 := by
  obtain ⟨q, hq⟩ := factorial_dvd m (n + 1) hm hn
  rw [hq, E213.Tactic.NatHelper.mul_mod_right]

/-- **Cauchy w.r.t. leavesModNat m**: the factorial-leaves sequence
    is leavesModNat m Cauchy for each m ≥ 2.  ∅-axiom via 213-native
    `Nat.le_trans` and `Nat.le_succ_of_le` (no `omega`). -/
theorem factorial_seq_cauchy (xs : Nat → Raw)
    (hLeaves : ∀ n, Lens.leaves.view (xs n) = factorial (n + 1))
    (m : Nat) (hm : m ≥ 2) :
    LensCauchy (leavesModNat m) xs := by
  have h1m : 1 ≤ m := Nat.le_trans (by decide : (1 : Nat) ≤ 2) hm
  refine ⟨m, ?_⟩
  intro k l hk hl
  show (leavesModNat m).view (xs k) = (leavesModNat m).view (xs l)
  rw [leavesModNat_view_eq, leavesModNat_view_eq]
  rw [hLeaves k, hLeaves l]
  rw [factorial_eventually_zero_mod m h1m k (Nat.le_succ_of_le hk)]
  rw [factorial_eventually_zero_mod m h1m l (Nat.le_succ_of_le hl)]

/-- **Profinite limit**: the leavesModNat m limit of the
    factorial-leaves sequence is 0.  Corresponds exactly to the
    profinite zero of Ẑ.  ∅-axiom. -/
theorem factorial_seq_limit_zero (xs : Nat → Raw)
    (hLeaves : ∀ n, Lens.leaves.view (xs n) = factorial (n + 1))
    (m : Nat) (hm : m ≥ 2) :
    EventuallyClass (leavesModNat m) xs 0 := by
  have h1m : 1 ≤ m := Nat.le_trans (by decide : (1 : Nat) ≤ 2) hm
  refine ⟨m, ?_⟩
  intro n hn
  show (leavesModNat m).view (xs n) = 0
  rw [leavesModNat_view_eq, hLeaves n]
  exact factorial_eventually_zero_mod m h1m n (Nat.le_succ_of_le hn)

/-- **Family Cauchy** w.r.t. leavesModNat family ({m : m ≥ 2}). -/
def leavesModNatFamily : { m : Nat // m ≥ 2 } → (α : Type) × Lens α :=
  fun m => ⟨Nat, leavesModNat m.val⟩

/-- The factorial-leaves sequence is family-Cauchy w.r.t. the entire
    leavesModNat family.  Formal expression of profinite Cauchy. -/
theorem factorial_seq_familyCauchy (xs : Nat → Raw)
    (hLeaves : ∀ n, Lens.leaves.view (xs n) = factorial (n + 1)) :
    FamilyCauchy leavesModNatFamily xs := by
  intro ⟨m, hm⟩
  exact factorial_seq_cauchy xs hLeaves m hm

/-- **Profinite limit assignment**: the family-Cauchy limit of the
    factorial sequence is 0 for every m.  The 213 representation of
    the 0 element of Ẑ. -/
theorem factorial_seq_limit_all_zero (xs : Nat → Raw)
    (hLeaves : ∀ n, Lens.leaves.view (xs n) = factorial (n + 1))
    (la : LimitAssignment leavesModNatFamily xs)
    (m : Nat) (hm : m ≥ 2) :
    la.limit ⟨m, hm⟩ = (0 : Nat) := by
  have h0 : EventuallyClass (leavesModNat m) xs 0 :=
    factorial_seq_limit_zero xs hLeaves m hm
  have hL : EventuallyClass (leavesModNat m) xs (la.limit ⟨m, hm⟩) := by
    refine ⟨(la.data ⟨m, hm⟩).N, ?_⟩
    intro n hn
    exact limitClass_eq_tail (leavesModNat m) xs (la.data ⟨m, hm⟩) n hn
  exact eventually_class_unique (leavesModNat m) xs (la.limit ⟨m, hm⟩) 0 hL h0

end E213.Lib.Math.Cauchy.ProfiniteSeq
