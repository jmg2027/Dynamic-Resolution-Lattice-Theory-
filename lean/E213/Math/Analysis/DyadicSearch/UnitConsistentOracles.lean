import E213.Math.Analysis.DyadicSearch.MinimalRootLens
import E213.Math.Analysis.DyadicSearch.DyadicTrajectory
import E213.Math.Analysis.DyadicSearch.ConsistentOracle
import E213.Math.Real213.Dyadic
import E213.Kernel.Tactic.Pow213

/-!
# Concrete `ConsistentOracle` instances on the unit bracket — Layer 3c

Demonstrates that the typed protocol `ConsistentOracle` is
non-vacuously inhabitable beyond the trivial collapsed case.

## Two concrete instances

  * `unitAlwaysTrue_ConsistentOracle : ConsistentOracle unitBracket`
    — `alwaysTrue` oracle steers always-left from `[0, 1]`; midCut
    converges to the leftmost point `0`.  Threshold `N(m, k) = k`.
  * `unitAlwaysFalse_ConsistentOracle : ConsistentOracle unitBracket`
    — `alwaysFalse` oracle steers always-right; midCut converges
    to the rightmost point `1`.  Same threshold.

Both proofs use the closed-form midCut formulas
(`alwaysTrue_unit_midCut`, `alwaysFalse_unit_midCut`) plus the
explicit modulus `N(m, k) = k` derived from `n + 1 ≤ 2^n`.

## Layer 3c — the architectural conclusion

For arbitrary `(LocallyDeterminedData f, BracketSignChange f db)`,
constructing a `ConsistentOracle db` requires a hypothesis about
the trajectory's commitment at unit precision — equivalent to
Bishop locatedness.  The `ConsistentOracle` typed protocol *is*
that hypothesis made into a positive datum: each `ConsistentOracle`
witness is a constructive certificate of the trajectory's
finite-resolution commitment.

The general-case construction is therefore not a closed theorem
but a **construction principle**: for specific f-classes (e.g.,
polynomial, or LDD f with a uniform modulus bound), `ConsistentOracle`
is constructible directly via closed-form analysis.  This file
delivers the cleanest non-trivial cases — the constant-direction
oracles on the dyadic-canonical starting bracket.
-/

namespace E213.Math.Analysis.DyadicSearch.UnitConsistentOracles

open E213.Firmware E213.Hypervisor
open E213.Math.Analysis.DyadicSearch.DyadicBracket
open E213.Math.Analysis.DyadicSearch.DyadicTrajectory
open E213.Math.Analysis.DyadicSearch.ConsistentOracle (ConsistentOracle)
open E213.Math.Real213.Dyadic (dyadicCut)

/-- `1 ≤ 2^n`.  Local clean proof; `Nat.one_le_two_pow` would
    pull `propext` via Lean-core inequality machinery. -/
private theorem one_le_two_pow_local : ∀ n, (1:Nat) ≤ 2^n
  | 0 => Nat.le_refl 1
  | k+1 => by
    have ih := one_le_two_pow_local k
    show 1 ≤ 2^k * 2
    calc 1 ≤ 2^k := ih
      _ = 2^k * 1 := (Nat.mul_one _).symm
      _ ≤ 2^k * 2 := Nat.mul_le_mul_left _ (by decide)

/-- `n + 1 ≤ 2^n`.  Pure structural Nat induction; ∅-axiom via
    `one_le_two_pow_local` (replacing `Nat.one_le_two_pow` which
    drags `propext`). -/
private theorem succ_le_two_pow : ∀ n, n + 1 ≤ 2^n
  | 0 => by decide
  | k + 1 => by
    have ih := succ_le_two_pow k
    have h2k : 1 ≤ 2^k := one_le_two_pow_local k
    calc k + 1 + 1 ≤ 2^k + 1 := Nat.add_le_add_right ih 1
      _ ≤ 2^k + 2^k := Nat.add_le_add_left h2k _
      _ = 2 * 2^k := (Nat.two_mul _).symm
      _ = 2^(k+1) := by rw [Nat.pow_succ, Nat.mul_comm]

/-- For `n ≥ k` and `m ≥ 1`, `k ≤ 2^(n+1) * m`.

Used to show the `decide(k ≤ 2^(n+1) * m)` test is `true` past the
explicit modulus `N(m, k) = k`.  Combines `succ_le_two_pow` (giving
`2^(n+1) ≥ n + 2 ≥ k`) with `Nat.le_mul_of_pos_right` (m ≥ 1). -/
private theorem k_le_two_pow_succ_mul (n k m : Nat)
    (hkn : k ≤ n) (hm : 1 ≤ m) : k ≤ 2^(n+1) * m := by
  have hpow : (n + 1) + 1 ≤ 2^(n+1) := succ_le_two_pow (n+1)
  have hkn2 : k ≤ n + 2 := Nat.le_trans hkn (Nat.le_add_right _ _)
  have hkpow : k ≤ 2^(n+1) := Nat.le_trans hkn2 hpow
  calc k ≤ 2^(n+1) := hkpow
    _ = 2^(n+1) * 1 := (Nat.mul_one _).symm
    _ ≤ 2^(n+1) * m := Nat.mul_le_mul_left _ hm

/-- **Layer 3c instance #1**: `alwaysTrue` ConsistentOracle on
    unitBracket.

The trajectory steers always-left from `[0, 1]`; midCut at depth `n`
is exactly `dyadicCut 1 (n+1)` (closed form
`alwaysTrue_unit_midCut`).  At a query `(m, k)`:
  * `m = 0`: midCut value reduces to `decide(k ≤ 0)`, independent
    of `n`.
  * `m ≥ 1`, `k = 0`: vacuously true.
  * `m ≥ 1`, `k ≥ 1`: past `n ≥ k`, `k ≤ 2^(n+1) * m` by
    `k_le_two_pow_succ_mul`, so `decide` is `true`.

Threshold function `N(m, k) = k` works uniformly. -/
def unitAlwaysTrue_ConsistentOracle : ConsistentOracle unitBracket where
  oracle := alwaysTrue
  thresholdN := fun _ k => k
  consistency := by
    intro m k n1 n2 hn1 hn2
    rw [alwaysTrue_unit_midCut n1, alwaysTrue_unit_midCut n2]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; rfl
    · have h1 : dyadicCut 1 (n1+1) m k = true := by
        show decide (1 * k ≤ 2^(n1+1) * m) = true
        apply decide_eq_true
        rw [Nat.one_mul]
        exact k_le_two_pow_succ_mul n1 k m hn1 hm
      have h2 : dyadicCut 1 (n2+1) m k = true := by
        show decide (1 * k ≤ 2^(n2+1) * m) = true
        apply decide_eq_true
        rw [Nat.one_mul]
        exact k_le_two_pow_succ_mul n2 k m hn2 hm
      rw [h1, h2]

/-- For `n ≥ k`, `k < 2^(n+1)`. -/
private theorem k_lt_two_pow_succ (n k : Nat) (hkn : k ≤ n) :
    k < 2^(n+1) := by
  have h1 : (n + 1) + 1 ≤ 2^(n+1) := succ_le_two_pow (n+1)
  have h2 : k + 1 ≤ n + 1 := Nat.add_le_add_right hkn 1
  have h3 : k + 1 ≤ n + 2 := Nat.le_trans h2 (Nat.le_succ _)
  exact Nat.lt_of_succ_le (Nat.le_trans h3 h1)

/-- For `m < k`, `k ≤ n`, the alwaysFalse closed-form midCut value
    `(2^(n+1) - 1) * k > 2^(n+1) * m`.  This is the "decide false"
    side of the alwaysFalse consistency proof. -/
private theorem alwaysFalse_decide_false_aux (n k m : Nat)
    (hkn : k ≤ n) (hlt : m < k) :
    ¬ (2^(n+1) - 1) * k ≤ 2^(n+1) * m := by
  intro habs
  -- Add k to both sides, simplify (2^(n+1) - 1)*k + k = 2^(n+1)*k.
  have hone : 1 ≤ 2^(n+1) := one_le_two_pow_local (n+1)
  have hcollect : (2^(n+1) - 1) * k + k = 2^(n+1) * k := by
    have h1 : ((2^(n+1) - 1) + 1) * k = (2^(n+1) - 1) * k + 1 * k :=
      E213.Tactic.Nat213.add_mul _ _ _
    rw [Nat.one_mul] at h1
    have h2 : 2^(n+1) - 1 + 1 = 2^(n+1) := E213.Tactic.Nat213.sub_add_cancel hone
    rw [h2] at h1
    exact h1.symm
  have hk_le : 2^(n+1) * k ≤ 2^(n+1) * m + k := by
    rw [← hcollect]
    exact Nat.add_le_add_right habs k
  -- Use m + 1 ≤ k.
  have hm1k : m + 1 ≤ k := hlt
  have hprod : 2^(n+1) * (m + 1) ≤ 2^(n+1) * k :=
    Nat.mul_le_mul_left _ hm1k
  have hcomb : 2^(n+1) * (m + 1) ≤ 2^(n+1) * m + k :=
    Nat.le_trans hprod hk_le
  have hexpand : 2^(n+1) * (m + 1) = 2^(n+1) * m + 2^(n+1) := by
    rw [Nat.mul_add, Nat.mul_one]
  rw [hexpand] at hcomb
  have hpow_le : 2^(n+1) ≤ k := E213.Tactic.Nat213.le_of_add_le_add_left hcomb
  exact absurd hpow_le (Nat.not_le_of_lt (k_lt_two_pow_succ n k hkn))

/-- For `k ≤ m`, the alwaysFalse closed-form value
    `(2^(n+1) - 1) * k ≤ 2^(n+1) * m`.  Holds *uniformly in n*
    (no threshold needed). -/
private theorem alwaysFalse_decide_true_aux (n k m : Nat) (hge : k ≤ m) :
    (2^(n+1) - 1) * k ≤ 2^(n+1) * m := by
  have h1 : (2^(n+1) - 1) * k ≤ (2^(n+1) - 1) * m :=
    Nat.mul_le_mul_left _ hge
  have h2 : (2^(n+1) - 1) * m ≤ 2^(n+1) * m :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  exact Nat.le_trans h1 h2

/-- **Layer 3c instance #2**: `alwaysFalse` ConsistentOracle on
    unitBracket.

The trajectory steers always-right; midCut at depth `n` is exactly
`dyadicCut (2^(n+1) - 1) (n+1)` (closed form
`alwaysFalse_unit_midCut`).  For `n ≥ k` the decide value commits
to `decide(k ≤ m)` (independent of `n`):
  * `k ≤ m`: true (uniformly via `alwaysFalse_decide_true_aux`).
  * `m < k`: false (past `n ≥ k` via `alwaysFalse_decide_false_aux`).

Same threshold function `N(m, k) = k`. -/
def unitAlwaysFalse_ConsistentOracle : ConsistentOracle unitBracket where
  oracle := alwaysFalse
  thresholdN := fun _ k => k
  consistency := by
    intro m k n1 n2 hn1 hn2
    rw [alwaysFalse_unit_midCut n1, alwaysFalse_unit_midCut n2]
    show decide ((2^(n1+1) - 1) * k ≤ 2^(n1+1) * m)
       = decide ((2^(n2+1) - 1) * k ≤ 2^(n2+1) * m)
    rcases Nat.lt_or_ge m k with hlt | hge
    · -- m < k: both sides decide to false (past n ≥ k)
      rw [decide_eq_false (alwaysFalse_decide_false_aux n1 k m hn1 hlt),
          decide_eq_false (alwaysFalse_decide_false_aux n2 k m hn2 hlt)]
    · -- k ≤ m: both sides decide to true (uniformly)
      rw [decide_eq_true (alwaysFalse_decide_true_aux n1 k m hge),
          decide_eq_true (alwaysFalse_decide_true_aux n2 k m hge)]

end E213.Math.Analysis.DyadicSearch.UnitConsistentOracles



