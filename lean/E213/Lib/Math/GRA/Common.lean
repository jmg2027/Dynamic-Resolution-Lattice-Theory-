import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.Gcd213

/-!
# GRA Common — shared PURE Nat lemmas

The five Reading instances (Graph / Cohomology / Analysis / HoTT /
HigherAlgebra) plus the NumberTheory hub all reduce, at the
arithmetic core, to the same (2,3) arithmetic on `Nat`.  This
module hosts the PURE lemmas they share, so each Reading file is
a thin wrapper rather than five copies of the same omega proof.

All theorems here are STRICT 0-AXIOM (`#print axioms` empty).
No `Classical`, no Mathlib, no `propext`, no `Quot.sound`.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.GRA.Common

open E213.Tactic.NatHelper (sub_add_cancel cases_lt_three)
open E213.Meta.Nat.AddMod213 (div_add_mod)
open E213.Meta.Nat.NatDiv213 (add_div_right_pos add_mod_right_pos)
open E213.Meta.Nat.Gcd213 (gcd213_self gcd213_succ_self)

/-! ### §1 — Coprime witness (2, 3) -/

/-- `gcd213 2 3 = 1` — kernel-reducible (PURE).  Bypasses Lean-core
    `Nat.gcd`'s well-founded-recursion `propext` inheritance. -/
theorem coprime_2_3 : E213.Tactic.NatHelper.gcd213 2 3 = 1 := rfl

/-- `2 < 3`. -/
theorem two_lt_three : (2 : Nat) < 3 := Nat.lt_succ_of_le Nat.le.refl

/-! ### §2 — Reachability for (2, 3) -/

/-- Step lemma: `k+2 = 2a + 3b ⟹ (k+2)+2 = 2(a+1) + 3b`. -/
private theorem reach_step {k a b : Nat} (h : k + 2 = 2 * a + 3 * b) :
    (k + 2) + 2 = 2 * (a + 1) + 3 * b := by
  rw [h, Nat.mul_succ,
      Nat.add_assoc (2 * a) (3 * b) 2,
      Nat.add_assoc (2 * a) 2 (3 * b),
      Nat.add_comm (3 * b) 2]

/-- Offset reachability: every `k + 2` decomposes as `2a + 3b`. -/
theorem reach_offset : ∀ k : Nat, ∃ a b : Nat, k + 2 = 2 * a + 3 * b := fun k =>
  Nat.strongRecOn k
    (motive := fun k => ∃ a b : Nat, k + 2 = 2 * a + 3 * b)
    (fun k ih =>
      match k with
      | 0 => ⟨1, 0, rfl⟩
      | 1 => ⟨0, 1, rfl⟩
      | k + 2 =>
        have h : k < k + 2 := Nat.lt_succ_of_lt (Nat.lt_succ_of_le Nat.le.refl)
        let ⟨a, b, hk⟩ := ih k h
        ⟨a + 1, b, reach_step hk⟩)

/-- Universal reachability: every `n ≥ 2` decomposes as `2a + 3b`. -/
theorem reach_23 (n : Nat) (hn : n ≥ 2) :
    ∃ a b : Nat, n = 2 * a + 3 * b := by
  have hk : n = (n - 2) + 2 := (sub_add_cancel hn).symm
  rw [hk]
  exact reach_offset (n - 2)

/-! ### §3 — Depth = `⌈n/3⌉` arithmetic -/

/-- `(3 * k + 2) / 3 = k`. -/
private theorem div3_3k_2 (k : Nat) : (3 * k + 2) / 3 = k := by
  induction k with
  | zero => decide
  | succ k ih =>
    show (3 * k + 3 + 2) / 3 = k + 1
    have h1 : 3 * k + 3 + 2 = (3 * k + 2) + 3 := by
      rw [Nat.add_assoc, Nat.add_comm 3 2, ← Nat.add_assoc]
    rw [h1, add_div_right_pos (by decide), ih]

/-- `(3 * k + 3) / 3 = k + 1`. -/
private theorem div3_3k_3 (k : Nat) : (3 * k + 3) / 3 = k + 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    show (3 * (k + 1) + 3) / 3 = k + 1 + 1
    rw [Nat.mul_succ]
    show (3 * k + 3 + 3) / 3 = k + 1 + 1
    rw [add_div_right_pos (by decide), ih]

/-- `(3 * k + 1) / 3 = k`. -/
private theorem div3_3k_1 (k : Nat) : (3 * k + 1) / 3 = k := by
  induction k with
  | zero => decide
  | succ k ih =>
    show (3 * (k + 1) + 1) / 3 = k + 1
    rw [Nat.mul_succ]
    show (3 * k + 3 + 1) / 3 = k + 1
    have h1 : 3 * k + 3 + 1 = (3 * k + 1) + 3 := by
      rw [Nat.add_assoc, Nat.add_comm 3 1, ← Nat.add_assoc]
    rw [h1, add_div_right_pos (by decide), ih]

/-- `(3 * k + 4) / 3 = k + 1`. -/
private theorem div3_3k_4 (k : Nat) : (3 * k + 4) / 3 = k + 1 := by
  have heq : 3 * k + 4 = (3 * k + 1) + 3 := by rw [Nat.add_assoc]
  rw [heq, add_div_right_pos (by decide), div3_3k_1]

/-- `n / 3` value when `n % 3 = 0`: `n / 3 = n / 3` (tautology, used for case rfl). -/
private theorem div3_of_mod0 {n : Nat} (h : n % 3 = 0) :
    3 * (n / 3) = n := by
  have hbase : 3 * (n / 3) + n % 3 = n := div_add_mod n 3
  rw [h, Nat.add_zero] at hbase
  exact hbase

/-- When `n % 3 = 1`: `3 * (n/3) + 1 = n`. -/
private theorem split_mod1 {n : Nat} (h : n % 3 = 1) :
    3 * (n / 3) + 1 = n := by
  have hbase : 3 * (n / 3) + n % 3 = n := div_add_mod n 3
  rw [h] at hbase
  exact hbase

/-- When `n % 3 = 2`: `3 * (n/3) + 2 = n`. -/
private theorem split_mod2 {n : Nat} (h : n % 3 = 2) :
    3 * (n / 3) + 2 = n := by
  have hbase : 3 * (n / 3) + n % 3 = n := div_add_mod n 3
  rw [h] at hbase
  exact hbase

/-- Case-0 lemma: when `n % 3 = 0`, `(n + 2) / 3 = n / 3`. -/
private theorem depth_case0 (n : Nat) (h : n % 3 = 0) :
    (n + 2) / 3 = n / 3 := by
  have hn : 3 * (n / 3) = n := div3_of_mod0 h
  have heq : (3 * (n / 3) + 2) / 3 = n / 3 := div3_3k_2 (n / 3)
  rw [← heq]
  congr 1
  rw [hn]

/-- Case-1 lemma: when `n % 3 = 1`, `(n + 2) / 3 = n / 3 + 1`. -/
private theorem depth_case1 (n : Nat) (h : n % 3 = 1) :
    (n + 2) / 3 = n / 3 + 1 := by
  have hn : 3 * (n / 3) + 1 = n := split_mod1 h
  have heq : (3 * (n / 3) + 3) / 3 = n / 3 + 1 := div3_3k_3 (n / 3)
  rw [← heq]
  congr 1
  calc n + 2 = (3 * (n / 3) + 1) + 2 := by rw [hn]
    _ = 3 * (n / 3) + (1 + 2) := Nat.add_assoc _ _ _
    _ = 3 * (n / 3) + 3 := rfl

/-- Case-2 lemma: when `n % 3 = 2`, `(n + 2) / 3 = n / 3 + 1`. -/
private theorem depth_case2 (n : Nat) (h : n % 3 = 2) :
    (n + 2) / 3 = n / 3 + 1 := by
  have hn : 3 * (n / 3) + 2 = n := split_mod2 h
  have heq : (3 * (n / 3) + 4) / 3 = n / 3 + 1 := div3_3k_4 (n / 3)
  rw [← heq]
  congr 1
  calc n + 2 = (3 * (n / 3) + 2) + 2 := by rw [hn]
    _ = 3 * (n / 3) + (2 + 2) := Nat.add_assoc _ _ _
    _ = 3 * (n / 3) + 4 := rfl

/-- **Depth formula** (the central GRA identity):
    `(n + 2) / 3 = n / 3 + (if n % 3 = 0 then 0 else 1)`. -/
theorem depth_formula (n : Nat) :
    (n + 2) / 3 = n / 3 + (if n % 3 = 0 then 0 else 1) := by
  have hmod : n % 3 < 3 := Nat.mod_lt n (by decide)
  rcases cases_lt_three hmod with h0 | h1 | h2
  · rw [if_pos h0, Nat.add_zero]; exact depth_case0 n h0
  · have hne : n % 3 ≠ 0 := h1 ▸ (by decide : (1:Nat) ≠ 0)
    rw [if_neg hne]; exact depth_case1 n h1
  · have hne : n % 3 ≠ 0 := h2 ▸ (by decide : (2:Nat) ≠ 0)
    rw [if_neg hne]; exact depth_case2 n h2

/-- Greedy form: `(n + 2) / 3 = (n + 3 - 1) / 3`. -/
theorem greedy_form (n : Nat) : (n + 2) / 3 = (n + 3 - 1) / 3 := rfl

/-! ### §4 — Universal depth comparison `⌈n/3⌉ ≤ (n+1)/2` -/

/-- Step lemma: divide by 3 increases by 2 when shifted by 6. -/
private theorem div3_shift_6 (k : Nat) :
    (k + 6 + 2 + 2) / 3 = (k + 2 + 2) / 3 + 2 := by
  have heq : k + 6 + 2 + 2 = (k + 2 + 2) + 3 + 3 := by
    show k + 10 = k + 2 + 2 + 3 + 3
    rfl
  rw [heq, add_div_right_pos (by decide), add_div_right_pos (by decide)]

/-- Step lemma: divide by 2 increases by 3 when shifted by 6. -/
private theorem div2_shift_6 (k : Nat) :
    (k + 6 + 2 + 1) / 2 = (k + 2 + 1) / 2 + 3 := by
  have heq : k + 6 + 2 + 1 = (k + 2 + 1) + 2 + 2 + 2 := by
    show k + 9 = k + 2 + 1 + 2 + 2 + 2
    rfl
  rw [heq, add_div_right_pos (by decide),
      add_div_right_pos (by decide),
      add_div_right_pos (by decide)]

/-- Offset version of the depth comparison: for all `k`,
    `(k + 2 + 2) / 3 ≤ (k + 2 + 1) / 2`. -/
private theorem ceil3_le_ceil2_offset :
    ∀ k : Nat, (k + 2 + 2) / 3 ≤ (k + 2 + 1) / 2 := fun k =>
  Nat.strongRecOn k
    (motive := fun k => (k + 2 + 2) / 3 ≤ (k + 2 + 1) / 2)
    (fun k ih =>
      match k with
      | 0 => by decide
      | 1 => by decide
      | 2 => by decide
      | 3 => by decide
      | 4 => by decide
      | 5 => by decide
      | k + 6 => by
        show (k + 6 + 2 + 2) / 3 ≤ (k + 6 + 2 + 1) / 2
        have hk6 : k < k + 6 :=
          Nat.lt_of_lt_of_le (Nat.lt_succ_of_le Nat.le.refl)
            (Nat.add_le_add_left (by decide : (1:Nat) ≤ 6) k)
        have ih_k : (k + 2 + 2) / 3 ≤ (k + 2 + 1) / 2 := ih k hk6
        rw [div3_shift_6 k, div2_shift_6 k]
        exact Nat.add_le_add ih_k (by decide : (2:Nat) ≤ 3))

/-- For all `n ≥ 2`, `(n + 2) / 3 ≤ (n + 1) / 2`. -/
theorem ceil3_le_ceil2 (n : Nat) (hn : n ≥ 2) :
    (n + 2) / 3 ≤ (n + 1) / 2 := by
  have hk : n = (n - 2) + 2 := (sub_add_cancel hn).symm
  rw [hk]
  exact ceil3_le_ceil2_offset (n - 2)

end E213.Lib.Math.GRA.Common
