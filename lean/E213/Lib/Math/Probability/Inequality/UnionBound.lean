import E213.Lib.Math.NumberTheory.FactorialLcmIdentity

/-!
# Boole's inequality (the union bound) — 213-native, ∅-axiom

Finite sample space `{0,…,N−1}` with an (unnormalized) weight
`p : Nat → Nat`.  An event is a predicate `A : Nat → Bool`; its weighted
measure is `prob N p A := Σ_{ω<N} (A ω).toNat · p ω`.  For a family of
events `As : Nat → (Nat → Bool)`, the union of the first `m` events is
`unionB As m` (Bool, by recursion on `m`).

★★★ **Union bound** (`union_bound`):
    `prob N p (unionB As m) ≤ Σ_{i<m} prob N p (As i)`.

Method: pointwise indicator sub-additivity
`(unionB As m ω).toNat ≤ Σ_{i<m} (As i ω).toNat` (induction on `m`,
Bool `or` fact), multiplied by `p ω` and summed (`sumTo_le_sumTo`),
then `Σ_ω Σ_i ↦ Σ_i Σ_ω` (`sumTo_fubini`).

All declarations PURE (`#print axioms ⋯ → no axioms`).
-/

namespace E213.Lib.Math.Probability.Inequality.UnionBound

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_zero sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem (sumTo_congr)
open E213.Lib.Math.NumberTheory.LcmGrowthChebyshev (sumTo_le_sumTo)
open E213.Lib.Math.NumberTheory.FactorialLcmIdentity (sumTo_fubini)
open E213.Meta.Nat.PureNat (add_mul)

/-! ## §1 — definitions -/

/-- Weighted measure of an event: `Σ_{ω<N} (A ω).toNat · p ω`. -/
def prob (N : Nat) (p : Nat → Nat) (A : Nat → Bool) : Nat :=
  sumTo N (fun ω => (A ω).toNat * p ω)

/-- Bool union of the first `k` events: `unionB As k ω = ⋁_{i<k} As i ω`. -/
def unionB (As : Nat → (Nat → Bool)) : Nat → Nat → Bool
  | 0,     _ => false
  | k + 1, ω => As k ω || unionB As k ω

@[simp] theorem unionB_zero (As : Nat → (Nat → Bool)) (ω : Nat) :
    unionB As 0 ω = false := rfl

@[simp] theorem unionB_succ (As : Nat → (Nat → Bool)) (k ω : Nat) :
    unionB As (k + 1) ω = (As k ω || unionB As k ω) := rfl

/-! ## §2 — Bool `or` indicator sub-additivity (closed, axiom-clean) -/

/-- `(a || b).toNat ≤ a.toNat + b.toNat`.  Closed Bool fact. -/
theorem or_toNat_le (a b : Bool) : (a || b).toNat ≤ a.toNat + b.toNat := by
  cases a <;> cases b <;> decide

/-! ## §3 — pointwise indicator sub-additivity over the union -/

/-- **Indicator of a union ≤ sum of indicators**:
    `(unionB As m ω).toNat ≤ Σ_{i<m} (As i ω).toNat`.  Induction on `m`. -/
theorem unionB_toNat_le_sum (As : Nat → (Nat → Bool)) (ω : Nat) :
    ∀ m, (unionB As m ω).toNat ≤ sumTo m (fun i => (As i ω).toNat)
  | 0 => by rw [unionB_zero, sumTo_zero]; exact Nat.le_refl 0
  | m + 1 => by
      rw [unionB_succ, sumTo_succ]
      -- (As m ω || unionB As m ω).toNat
      --   ≤ (As m ω).toNat + (unionB As m ω).toNat        (or_toNat_le)
      --   ≤ (As m ω).toNat + Σ_{i<m} (As i ω).toNat        (IH)
      --   = Σ_{i<m} (As i ω).toNat + (As m ω).toNat        (comm)
      refine Nat.le_trans (or_toNat_le (As m ω) (unionB As m ω)) ?_
      rw [Nat.add_comm (sumTo m (fun i => (As i ω).toNat)) ((As m ω).toNat)]
      exact Nat.add_le_add_left (unionB_toNat_le_sum As ω m) _

/-! ## §4 — finite-sum distributivity / split helpers -/

/-- Distributivity of `· c` over a finite sum:
    `(Σ_{k<n} f k) · c = Σ_{k<n} (f k · c)`.  Induction on `n`. -/
theorem sumTo_mul_right :
    ∀ (n : Nat) (f : Nat → Nat) (c : Nat),
      sumTo n f * c = sumTo n (fun k => f k * c)
  | 0,     _, c => by rw [sumTo_zero, sumTo_zero, Nat.zero_mul]
  | n + 1, f, c => by
      rw [sumTo_succ, sumTo_succ, add_mul, sumTo_mul_right n f c]

/-- `Σ (f + g) = Σ f + Σ g` (pointwise add splits).  Induction on `n`. -/
theorem sumTo_add_split :
    ∀ (n : Nat) (f g : Nat → Nat),
      sumTo n (fun k => f k + g k) = sumTo n f + sumTo n g
  | 0,     _, _ => by rw [sumTo_zero, sumTo_zero, sumTo_zero]
  | n + 1, f, g => by
      rw [sumTo_succ, sumTo_succ, sumTo_succ, sumTo_add_split n f g]
      -- (Σf + Σg) + (f n + g n) = (Σf + f n) + (Σg + g n)
      -- AC rearrangement: a + b + (c + d) = (a + c) + (b + d).
      rw [Nat.add_assoc (sumTo n f) (sumTo n g) (f n + g n),
          Nat.add_left_comm (sumTo n g) (f n) (g n),
          ← Nat.add_assoc (sumTo n f) (f n) (sumTo n g + g n)]

/-! ## §5 — the union bound -/

/-- ★★★ **Boole's inequality / the union bound**:
    `P(⋃_{i<m} Aᵢ) ≤ Σ_{i<m} P(Aᵢ)`. -/
theorem union_bound (N : Nat) (p : Nat → Nat) (As : Nat → (Nat → Bool)) (m : Nat) :
    prob N p (unionB As m) ≤ sumTo m (fun i => prob N p (As i)) := by
  -- Step 1: multiply the pointwise indicator bound by `p ω`, sum over `ω<N`.
  have step1 :
      prob N p (unionB As m)
        ≤ sumTo N (fun ω => sumTo m (fun i => (As i ω).toNat) * p ω) := by
    apply sumTo_le_sumTo
    intro ω _
    exact Nat.mul_le_mul_right (p ω) (unionB_toNat_le_sum As ω m)
  -- Step 2: distribute `· p ω` inside the inner sum (pointwise, `sumTo_congr`):
  --   (Σ_{i<m} (As i ω).toNat) · p ω = Σ_{i<m} (As i ω).toNat · p ω.
  have distrib :
      sumTo N (fun ω => sumTo m (fun i => (As i ω).toNat) * p ω)
        = sumTo N (fun ω => sumTo m (fun i => (As i ω).toNat * p ω)) := by
    apply sumTo_congr
    intro ω _
    -- (Σ f) * c = Σ (f · c), via sumTo_congr after a finite-sum distributivity.
    exact sumTo_mul_right m (fun i => (As i ω).toNat) (p ω)
  -- Step 3: Fubini swap  Σ_ω Σ_i  =  Σ_i Σ_ω.
  have fub :
      sumTo N (fun ω => sumTo m (fun i => (As i ω).toNat * p ω))
        = sumTo m (fun i => sumTo N (fun ω => (As i ω).toNat * p ω)) :=
    sumTo_fubini (fun ω i => (As i ω).toNat * p ω) N m
  -- Step 4: the inner sum is exactly `prob N p (As i)`.
  have fold :
      sumTo m (fun i => sumTo N (fun ω => (As i ω).toNat * p ω))
        = sumTo m (fun i => prob N p (As i)) := by
    apply sumTo_congr
    intro i _
    rfl
  -- Chain.
  rw [distrib, fub, fold] at step1
  exact step1

/-! ## §6 — pairwise special case -/

/-- ★★ **Pairwise union bound**: `P(A ∪ B) ≤ P A + P B`.
    Proved directly via `or_toNat_le`, multiplied by `p` and summed. -/
theorem prob_union_two (N : Nat) (p : Nat → Nat) (A B : Nat → Bool) :
    prob N p (fun ω => A ω || B ω) ≤ prob N p A + prob N p B := by
  -- Pointwise:  (A ω || B ω).toNat · p ω ≤ (A ω).toNat · p ω + (B ω).toNat · p ω.
  have step1 :
      prob N p (fun ω => A ω || B ω)
        ≤ sumTo N (fun ω => (A ω).toNat * p ω + (B ω).toNat * p ω) := by
    apply sumTo_le_sumTo
    intro ω _
    calc (A ω || B ω).toNat * p ω
        ≤ ((A ω).toNat + (B ω).toNat) * p ω :=
          Nat.mul_le_mul_right (p ω) (or_toNat_le (A ω) (B ω))
      _ = (A ω).toNat * p ω + (B ω).toNat * p ω := add_mul _ _ _
  -- Split the sum of a pointwise sum into a sum of two sums.
  have split :
      sumTo N (fun ω => (A ω).toNat * p ω + (B ω).toNat * p ω)
        = prob N p A + prob N p B :=
    sumTo_add_split N (fun ω => (A ω).toNat * p ω) (fun ω => (B ω).toNat * p ω)
  rw [split] at step1
  exact step1

/-! ## §7 — concrete smokes (closed, axiom-clean) -/

/-- Smoke: `N=4`, weights `p ω = ω+1` (so `p = 1,2,3,4`).
    `A = {0,1}` (ω<2), `B = {1,2}` (1≤ω≤2).
    `A∪B = {0,1,2}` → `P = 1+2+3 = 6`; `P A = 1+2 = 3`, `P B = 2+3 = 5`.
    Bound: `6 ≤ 3 + 5 = 8`.  ✓ -/
theorem smoke_two :
    prob 4 (fun ω => ω + 1)
        (fun ω => (decide (ω < 2)) || (decide (1 ≤ ω && ω ≤ 2)))
      ≤ prob 4 (fun ω => ω + 1) (fun ω => decide (ω < 2))
        + prob 4 (fun ω => ω + 1) (fun ω => decide (1 ≤ ω && ω ≤ 2)) := by
  decide

/-- Smoke (general bound, `m = 3`): three events over `N = 5`, `p ω = 1`.
    `A₀ = {0}`, `A₁ = {1,2}`, `A₂ = {2,3,4}` (overlap at `2`).
    `⋃ = {0,1,2,3,4}` → `P(⋃) = 5`; `Σ P = 1 + 2 + 3 = 6`.  `5 ≤ 6`.  ✓ -/
theorem smoke_three :
    prob 5 (fun _ => 1)
        (unionB (fun i ω =>
          match i with
          | 0 => decide (ω = 0)
          | 1 => decide (ω = 1 || ω = 2)
          | _ => decide (ω = 2 || ω = 3 || ω = 4)) 3)
      ≤ sumTo 3 (fun i => prob 5 (fun _ => 1)
          (fun ω =>
            match i with
            | 0 => decide (ω = 0)
            | 1 => decide (ω = 1 || ω = 2)
            | _ => decide (ω = 2 || ω = 3 || ω = 4))) := by
  decide

/-- Smoke (disjoint equality): `A = {0,1}`, `B = {2,3}` over `N=4`, `p=1`.
    Disjoint → `P(A∪B) = P A + P B = 2 + 2 = 4` (equality, not strict). -/
theorem smoke_disjoint_eq :
    prob 4 (fun _ => 1) (fun ω => decide (ω < 2) || decide (2 ≤ ω && ω < 4))
      = prob 4 (fun _ => 1) (fun ω => decide (ω < 2))
        + prob 4 (fun _ => 1) (fun ω => decide (2 ≤ ω && ω < 4)) := by
  decide

end E213.Lib.Math.Probability.Inequality.UnionBound
