import E213.Hypervisor.Lens.Leaves.ModNat
import E213.Hypervisor.Lens.Instances.Cauchy
import E213.Math.Cauchy.ProfiniteSeq

/-!
# Padic: p-adic ℤ_p as Lens sub-family

p-adic integers ℤ_p as the inverse limit of ℤ/p^k, realized in
213 as a sub-family of `leavesModNat` (powers of a fixed base).

## Structure

`padicFamily p k = leavesModNat (p^(k+1))` for k : ℕ.

Index starts at p^1 (k = 0) so each modulus ≥ p ≥ 2.

- p prime: ℤ_p (standard p-adic integers).
- p general (≥ 2): tower of mod-p^k Lenses (= ℤ_p for prime
  factors of p via CRT).

## Results

1. `padic_family_cauchy`: factorial seq is Cauchy w.r.t. each
   level of the tower.
2. `padic_family_limit_zero`: factorial seq has limit 0 at each
   level.
3. `padic_tower_refines`: level k+1 refines level k (canonical
   projection ℤ/p^(k+2) → ℤ/p^(k+1)).
4. `padic_familyCauchy`: family-Cauchy w.r.t. the entire tower.
5. `padic_limit_all_zero`: limit assignment is identically 0
   — the p-adic zero of ℤ_p.

## Significance

ℤ_p is a heavy tool of standard number theory.  In the 213 framework
it is naturally realized using only the `leavesModNat` sub-family and
the `factorial` sequence.  A sub-tower of `ProfiniteSeq` (factorial
entire = Ẑ).

Together with CmpIndependence + Cauchy completeness, this extends the
"ZFC replacement" claim of Paper 1 into the number-theoretic limit
domain.

`#print axioms`: propext only — no Classical.choice.

## Changelog

- 2026-04-25: padicFamily + factorial-seq instance.  Formalization as
  a direct sub-tower of ProfiniteSeq.
-/

namespace E213.Math.Hyper.Padic

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Leaves.ModNat E213.Hypervisor.Lens.Instances.Cauchy
open E213.Math.Cauchy.ProfiniteSeq

end E213.Math.Hyper.Padic

namespace E213.Math.Hyper.Padic

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Leaves.ModNat E213.Hypervisor.Lens.Instances.Cauchy
open E213.Math.Cauchy.ProfiniteSeq

/-! ### Power lemmas (based on Lean 4 core) -/

private theorem pow_one_le (p : Nat) (hp : p ≥ 2) (k : Nat) :
    1 ≤ p^k := by
  induction k with
  | zero => show 1 ≤ 1; exact Nat.le_refl 1
  | succ n ih =>
      show 1 ≤ p^n * p
      calc 1 = 1 * 1 := rfl
        _ ≤ p^n * p := Nat.mul_le_mul ih (by omega)

private theorem pow_succ_ge_two (p : Nat) (hp : p ≥ 2) (k : Nat) :
    2 ≤ p^(k+1) := by
  show 2 ≤ p^k * p
  have h1 : 1 ≤ p^k := pow_one_le p hp k
  have h2 : 1 * p ≤ p^k * p := Nat.mul_le_mul_right p h1
  have h3 : 2 ≤ 1 * p := by rw [Nat.one_mul]; exact hp
  exact Nat.le_trans h3 h2

private theorem pow_succ_dvd (p : Nat) (k : Nat) :
    p^(k+1) ∣ p^(k+2) := by
  show p^(k+1) ∣ p^(k+1) * p
  exact ⟨p, rfl⟩

end E213.Math.Hyper.Padic

namespace E213.Math.Hyper.Padic

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Leaves.ModNat E213.Hypervisor.Lens.Instances.Cauchy
open E213.Math.Cauchy.ProfiniteSeq

/-! ### p-adic Lens family -/

/-- p-adic family: indexed by ℕ, level k = leavesModNat (p^(k+1)). -/
def padicFamily (p : Nat) : Nat → Lens Nat :=
  fun k => leavesModNat (p^(k+1))

/-- Sigma-form for `FamilyCauchy` / `LimitAssignment`. -/
def padicFamilySigma (p : Nat) : Nat → (α : Type) × Lens α :=
  fun k => ⟨Nat, padicFamily p k⟩

/-! ### Cauchy + limit results -/

/-- factorial seq is Cauchy w.r.t. each level of the p-adic tower. -/
theorem padic_family_cauchy (p : Nat) (hp : p ≥ 2)
    (xs : Nat → Raw)
    (hLeaves : ∀ n, Lens.leaves.view (xs n) = factorial (n + 1))
    (k : Nat) :
    LensCauchy (padicFamily p k) xs :=
  factorial_seq_cauchy xs hLeaves (p^(k+1)) (pow_succ_ge_two p hp k)

/-- factorial seq has limit 0 at level k. -/
theorem padic_family_limit_zero (p : Nat) (hp : p ≥ 2)
    (xs : Nat → Raw)
    (hLeaves : ∀ n, Lens.leaves.view (xs n) = factorial (n + 1))
    (k : Nat) :
    EventuallyClass (padicFamily p k) xs 0 :=
  factorial_seq_limit_zero xs hLeaves (p^(k+1)) (pow_succ_ge_two p hp k)

/-- p-adic tower projection: level k+1 refines level k.
    Canonical surjection ℤ/p^(k+2) ↠ ℤ/p^(k+1). -/
theorem padic_tower_refines (p : Nat) (k : Nat) :
    (padicFamily p (k+1)).refines (padicFamily p k) :=
  divides_refines (p^(k+2)) (p^(k+1)) (pow_succ_dvd p k)

end E213.Math.Hyper.Padic

namespace E213.Math.Hyper.Padic

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Leaves.ModNat E213.Hypervisor.Lens.Instances.Cauchy
open E213.Math.Cauchy.ProfiniteSeq

/-- Family-Cauchy w.r.t. the entire p-adic tower. -/
theorem padic_familyCauchy (p : Nat) (hp : p ≥ 2)
    (xs : Nat → Raw)
    (hLeaves : ∀ n, Lens.leaves.view (xs n) = factorial (n + 1)) :
    FamilyCauchy (padicFamilySigma p) xs := by
  intro k
  exact padic_family_cauchy p hp xs hLeaves k

/-- Limit assignment is identically 0 — the p-adic zero of ℤ_p. -/
theorem padic_limit_all_zero (p : Nat) (hp : p ≥ 2)
    (xs : Nat → Raw)
    (hLeaves : ∀ n, Lens.leaves.view (xs n) = factorial (n + 1))
    (la : LimitAssignment (padicFamilySigma p) xs)
    (k : Nat) :
    la.limit k = (0 : Nat) := by
  have h0 : EventuallyClass (padicFamily p k) xs 0 :=
    padic_family_limit_zero p hp xs hLeaves k
  have hL : EventuallyClass (padicFamily p k) xs (la.limit k) := by
    refine ⟨(la.data k).N, ?_⟩
    intro n hn
    exact limitClass_eq_tail (padicFamily p k) xs (la.data k) n hn
  exact eventually_class_unique (padicFamily p k) xs (la.limit k) 0 hL h0

end E213.Math.Hyper.Padic
