import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem

/-!
# Integer partition function `p(n)` via the parts-bounded DP (∅-axiom)

The integer partition function `p(n)` (OEIS A000041) counts the ways to write `n`
as a sum of positive integers, order-independent: `p(0..10) = 1,1,2,3,5,7,11,15,22,30,42`.

Defined through the standard two-term dynamic program over `P(n,k)` = "partitions of
`n` into parts each `≤ k`":

  `P(0, k) = 1`,  `P(n+1, 0) = 0`,  `P(n+1, k+1) = P(n+1, k) + [k+1 ≤ n+1]·P(n+1−(k+1), k+1)`

with `p(n) = P(n, n)`.  This stays entirely in `Nat` (no signs / pentagonal
alternation), the cleanest PURE route.

  * ★ `partN_succ` — the defining recurrence (general `n,k`).
  * `partition_table` — `p(0..10)`.

`partF` is fuel-based (`Nat.strongRecOn` fuel-irrelevance, the `motzkin`/`schroder`
pattern; the `cond (Nat.ble (k+1)(n+1))` guard prevents the Nat-underflow spurious
count).  Genuinely absent (the `partition` hits elsewhere are set partitions/Bollobás).
-/

namespace E213.Lib.Math.Combinatorics.PartitionNumbers

/-- Fuel-based parts-bounded partition count.  `partF f n k = P(n,k)` (partitions of
    `n` into parts `≤ k`) whenever `f ≥ n + k`.  Fuel decreases structurally on every
    recursive call (PURE).  The `cond (Nat.ble (k+1)(n+1))` guard is essential: an
    unguarded `P(n+1−(k+1), k+1)` underflows to `P(0,·)=1` when `k+1 > n+1`. -/
def partF : Nat → Nat → Nat → Nat
  | 0,     _,     _     => 0
  | _ + 1, 0,     _     => 1
  | _ + 1, _ + 1, 0     => 0
  | f + 1, n + 1, k + 1 =>
      partF f (n + 1) k
        + cond (Nat.ble (k + 1) (n + 1)) (partF f (n + 1 - (k + 1)) (k + 1)) 0

/-- Integer partition number `p(n) = P(n,n)`, fuel `= 2n+1 ≥ n + n + 1`. -/
def partition (n : Nat) : Nat := partF (n + n + 1) n n

/-- **Fuel irrelevance**: any two fuels strictly above `n + k` agree (strong induction
    on the fuel; the bound is strict since fuel-`0` returns `0` while `P(0,0)=1`). -/
theorem partF_eq :
    ∀ f n k g, n + k < f → n + k < g → partF f n k = partF g n k := by
  intro f
  induction f using Nat.strongRecOn with
  | ind f ih =>
    intro n k g hf hg
    match f, n, k, hf, hg with
    | f + 1, 0,     k,     _,  hg =>
      cases g with
      | zero => exact absurd hg (Nat.not_lt_zero _)
      | succ g => rfl
    | f + 1, n + 1, 0,     _,  hg =>
      cases g with
      | zero => exact absurd hg (Nat.not_lt_zero _)
      | succ g => rfl
    | f + 1, n + 1, k + 1, hf, hg =>
      cases g with
      | zero => exact absurd hg (fun h => Nat.not_lt_zero _ h)
      | succ g =>
        show partF f (n + 1) k
              + cond (Nat.ble (k + 1) (n + 1)) (partF f (n + 1 - (k + 1)) (k + 1)) 0
           = partF g (n + 1) k
              + cond (Nat.ble (k + 1) (n + 1)) (partF g (n + 1 - (k + 1)) (k + 1)) 0
        have hfle : (n + 1) + (k + 1) ≤ f := Nat.le_of_lt_succ hf
        have hgle : (n + 1) + (k + 1) ≤ g := Nat.le_of_lt_succ hg
        have hhead_f : (n + 1) + k < f :=
          Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hfle
        have hhead_g : (n + 1) + k < g :=
          Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hgle
        have hhead : partF f (n + 1) k = partF g (n + 1) k :=
          ih f (Nat.lt_succ_self f) (n + 1) k g hhead_f hhead_g
        have hsub_le : n + 1 - (k + 1) ≤ n := by
          rw [Nat.succ_sub_succ]; exact Nat.sub_le n k
        have htail_le : (n + 1 - (k + 1)) + (k + 1) ≤ n + (k + 1) :=
          Nat.add_le_add_right hsub_le (k + 1)
        have htail_lt : (n + 1 - (k + 1)) + (k + 1) < (n + 1) + (k + 1) :=
          Nat.lt_of_le_of_lt htail_le (Nat.add_lt_add_right (Nat.lt_succ_self n) (k + 1))
        have htail_f : (n + 1 - (k + 1)) + (k + 1) < f :=
          Nat.lt_of_lt_of_le htail_lt hfle
        have htail_g : (n + 1 - (k + 1)) + (k + 1) < g :=
          Nat.lt_of_lt_of_le htail_lt hgle
        have htail : partF f (n + 1 - (k + 1)) (k + 1)
                       = partF g (n + 1 - (k + 1)) (k + 1) :=
          ih f (Nat.lt_succ_self f) (n + 1 - (k + 1)) (k + 1) g htail_f htail_g
        rw [hhead, htail]

/-- `partF f n k = partN n k` whenever the fuel exceeds `n + k`. -/
theorem partF_eq_partN (f n k : Nat) (h : n + k < f) :
    partF f n k = partF (n + k + 1) n k :=
  partF_eq f n k (n + k + 1) h (Nat.lt_succ_self _)

/-- Parts-bounded partition count `P(n,k)` (partitions of `n` into parts each `≤ k`),
    with the canonical fuel `n + k + 1`. -/
def partN (n k : Nat) : Nat := partF (n + k + 1) n k

theorem partition_eq_partN (n : Nat) : partition n = partN n n := by
  show partF (n + n + 1) n n = partF (n + n + 1) n n
  rfl

theorem partN_zero (k : Nat) : partN 0 k = 1 := rfl
theorem partN_succ_zero (n : Nat) : partN (n + 1) 0 = 0 := rfl

/-- ★ **Defining recurrence** (general `n,k`):
    `P(n+1, k+1) = P(n+1, k) + [k+1 ≤ n+1]·P(n+1−(k+1), k+1)` (indicator
    `Nat.ble (k+1)(n+1)`; below the diagonal the second term is `0`). -/
theorem partN_succ (n k : Nat) :
    partN (n + 1) (k + 1)
      = partN (n + 1) k
        + cond (Nat.ble (k + 1) (n + 1))
            (partN (n + 1 - (k + 1)) (k + 1)) 0 := by
  show partF ((n + 1) + (k + 1) + 1) (n + 1) (k + 1)
      = partN (n + 1) k
        + cond (Nat.ble (k + 1) (n + 1))
            (partN (n + 1 - (k + 1)) (k + 1)) 0
  show partF ((n + 1) + k + 1) (n + 1) k
        + cond (Nat.ble (k + 1) (n + 1))
            (partF ((n + 1) + k + 1) (n + 1 - (k + 1)) (k + 1)) 0
      = partN (n + 1) k
        + cond (Nat.ble (k + 1) (n + 1))
            (partN (n + 1 - (k + 1)) (k + 1)) 0
  have hhead : partF ((n + 1) + k + 1) (n + 1) k = partN (n + 1) k := rfl
  have htail :
      partF ((n + 1) + k + 1) (n + 1 - (k + 1)) (k + 1)
        = partN (n + 1 - (k + 1)) (k + 1) := by
    apply partF_eq_partN
    have hsub_le : n + 1 - (k + 1) ≤ n := by
      rw [Nat.succ_sub_succ]; exact Nat.sub_le n k
    have h1 : (n + 1 - (k + 1)) + (k + 1) ≤ n + (k + 1) :=
      Nat.add_le_add_right hsub_le (k + 1)
    have heq : n + (k + 1) = n + 1 + k := by
      rw [Nat.add_succ, Nat.succ_add]
    have h2 : n + (k + 1) < (n + 1) + k + 1 := by
      rw [heq]; exact Nat.lt_succ_self _
    exact Nat.lt_of_le_of_lt h1 h2
  rw [hhead, htail]

theorem partition_zero : partition 0 = 1 := rfl

/-- **Value table** `p(0..10) = 1,1,2,3,5,7,11,15,22,30,42` (OEIS A000041). -/
theorem partition_table :
    partition 0 = 1 ∧ partition 1 = 1 ∧ partition 2 = 2 ∧ partition 3 = 3
    ∧ partition 4 = 5 ∧ partition 5 = 7 ∧ partition 6 = 11 ∧ partition 7 = 15
    ∧ partition 8 = 22 ∧ partition 9 = 30 ∧ partition 10 = 42 := by decide

/-- Off-diagonal `partN` smokes: `P(5,2)=3`, `P(6,3)=7`, `P(4,4)=5=p(4)`. -/
theorem partN_smoke :
    partN 5 2 = 3 ∧ partN 6 3 = 7 ∧ partN 4 4 = 5 ∧ partN 0 7 = 1
    ∧ partN 3 0 = 0 := by decide

end E213.Lib.Math.Combinatorics.PartitionNumbers
