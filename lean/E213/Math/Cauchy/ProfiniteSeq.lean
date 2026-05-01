import E213.Hypervisor.Lens.Research.Lens.Cauchy
import E213.Hypervisor.Lens.Research.Leaves.ModNat
import E213.Infinity.LensCardinality

/-!
# Research.ProfiniteSeq: Cauchy instance for the leavesModNat family

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

namespace E213.Math.Cauchy.ProfiniteSeq

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Research.LensCauchy

/-- Local factorial (absent from Lean 4 core). -/
def factorial : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * factorial n

theorem factorial_pos (n : Nat) : factorial n ≥ 1 := by
  induction n with
  | zero => decide
  | succ k ih =>
      show (k+1) * factorial k ≥ 1
      have := Nat.mul_le_mul_left (k+1) ih
      simp at this
      omega

/-- factorial n is divisible by every m ≤ n. -/
theorem factorial_dvd (m n : Nat) (h : 1 ≤ m) (hmn : m ≤ n) :
    m ∣ factorial n := by
  induction n with
  | zero => omega
  | succ k ih =>
      by_cases hkm : m ≤ k
      · have hdvd : m ∣ factorial k := ih hkm
        show m ∣ (k+1) * factorial k
        obtain ⟨q, hq⟩ := hdvd
        refine ⟨(k+1) * q, ?_⟩
        calc (k + 1) * factorial k = (k + 1) * (m * q) := by rw [hq]
          _ = m * ((k + 1) * q) := by
              rw [← Nat.mul_assoc]
              rw [Nat.mul_comm (k + 1) m]
              rw [Nat.mul_assoc]
      · have hmk1 : m = k + 1 := by omega
        show m ∣ (k+1) * factorial k
        rw [hmk1]
        exact ⟨factorial k, rfl⟩

end E213.Math.Cauchy.ProfiniteSeq

namespace E213.Math.Cauchy.ProfiniteSeq

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Research.LeavesModNat E213.Hypervisor.Lens.Research.LensCauchy

/-- The factorial sequence is eventually 0 mod m (when n + 1 ≥ m). -/
theorem factorial_eventually_zero_mod (m : Nat) (hm : 1 ≤ m)
    (n : Nat) (hn : n + 1 ≥ m) : factorial (n + 1) % m = 0 := by
  obtain ⟨q, hq⟩ := factorial_dvd m (n + 1) hm hn
  rw [hq, Nat.mul_mod_right]

/-- **Cauchy w.r.t. leavesModNat m**: the factorial-leaves sequence
    is leavesModNat m Cauchy for each m ≥ 2. -/
theorem factorial_seq_cauchy (xs : Nat → Raw)
    (hLeaves : ∀ n, Lens.leaves.view (xs n) = factorial (n + 1))
    (m : Nat) (hm : m ≥ 2) :
    LensCauchy (leavesModNat m) xs := by
  refine ⟨m, ?_⟩
  intro k l hk hl
  show (leavesModNat m).view (xs k) = (leavesModNat m).view (xs l)
  rw [leavesModNat_view_eq, leavesModNat_view_eq]
  rw [hLeaves k, hLeaves l]
  rw [factorial_eventually_zero_mod m (by omega) k (by omega)]
  rw [factorial_eventually_zero_mod m (by omega) l (by omega)]

/-- **Profinite limit**: the leavesModNat m limit of the
    factorial-leaves sequence is 0.  Corresponds exactly to the
    profinite zero of Ẑ. -/
theorem factorial_seq_limit_zero (xs : Nat → Raw)
    (hLeaves : ∀ n, Lens.leaves.view (xs n) = factorial (n + 1))
    (m : Nat) (hm : m ≥ 2) :
    EventuallyClass (leavesModNat m) xs 0 := by
  refine ⟨m, ?_⟩
  intro n hn
  show (leavesModNat m).view (xs n) = 0
  rw [leavesModNat_view_eq, hLeaves n]
  exact factorial_eventually_zero_mod m (by omega) n (by omega)

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

end E213.Math.Cauchy.ProfiniteSeq
