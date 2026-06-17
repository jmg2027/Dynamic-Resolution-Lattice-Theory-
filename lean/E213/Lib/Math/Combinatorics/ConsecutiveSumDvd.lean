import E213.Lib.Math.Combinatorics.Pigeonhole
import E213.Meta.Nat.AddMod213
import E213.Meta.Tactic.NatHelper

/-!
# Forcing-PURE vein-B: a consecutive run with sum ≡ 0 mod n (∅-axiom)

Classic pigeonhole on prefix sums: among any `n` naturals there is a
non-empty consecutive run `[i, j)` whose sum is a multiple of `n`.  The
`n+1` prefix residues `prefixSum a k % n` (`k = 0..n`) live in `Fin n`, so
`exists_collision_lt` on `Fin (n+1) → Fin n` RETURNS a colliding pair; the
gap between the two prefixes is the computed run, and the two congruent
prefixes force `(prefixSum a j - prefixSum a i) % n = 0`
(`AddMod213.mod_diff_eq_zero_of_le`).
-/

open E213.Lib.Math.Combinatorics.Pigeonhole (exists_collision_lt)
open E213.Meta.Nat.AddMod213 (mod_diff_eq_zero_of_le)

namespace E213.Lib.Math.Combinatorics.ConsecutiveSumDvd

/-- Extend a finite sequence `a : Fin n → Nat` to `Nat → Nat` (0 outside). -/
def ext {n : Nat} (a : Fin n → Nat) : Nat → Nat :=
  fun k => if h : k < n then a ⟨k, h⟩ else 0

/-- Prefix sum: `prefixSum a k = Σ_{t<k} a t` (over the extended sequence). -/
def prefixSum {n : Nat} (a : Fin n → Nat) : Nat → Nat
  | 0 => 0
  | k+1 => prefixSum a k + ext a k

/-- Consecutive-run sum over the half-open index range `[i, j)`. -/
def segSum {n : Nat} (a : Fin n → Nat) (i j : Nat) : Nat :=
  prefixSum a j - prefixSum a i

/-- One prefix step is non-decreasing. -/
theorem prefix_le_succ {n : Nat} (a : Fin n → Nat) (k : Nat) :
    prefixSum a k ≤ prefixSum a (k+1) := by
  show prefixSum a k ≤ prefixSum a k + ext a k
  exact Nat.le_add_right _ _

/-- Prefix sums are non-decreasing: `i ≤ j → prefixSum a i ≤ prefixSum a j`. -/
theorem prefix_mono {n : Nat} (a : Fin n → Nat) :
    ∀ {i j : Nat}, i ≤ j → prefixSum a i ≤ prefixSum a j := by
  intro i j hij
  induction j with
  | zero =>
      have hi0 : i = 0 := Nat.le_antisymm hij (Nat.zero_le _)
      rw [hi0]; exact Nat.le_refl _
  | succ k ih =>
      rcases Nat.lt_or_ge i (k+1) with hlt | hge
      · have hik : i ≤ k := Nat.le_of_lt_succ hlt
        exact Nat.le_trans (ih hik) (prefix_le_succ a k)
      · have hik : i = k+1 := Nat.le_antisymm hij hge
        rw [hik]; exact Nat.le_refl _

/-- `segSum` is the telescoping difference of prefixes (definitional). -/
theorem segSum_eq_sub {n : Nat} (a : Fin n → Nat) (i j : Nat) :
    segSum a i j = prefixSum a j - prefixSum a i := rfl

/-! ## The load-bearing mod fact (reused from `AddMod213`)

`mod_sub_eq_zero` : `b ≤ a → a % n = b % n → (a - b) % n = 0`.  This is
exactly `AddMod213.mod_diff_eq_zero_of_le` (`a ≤ b → a%n = b%n → (b-a)%n = 0`)
with the names swapped. -/

/-- `b ≤ a → a % n = b % n → (a - b) % n = 0`.  ∅-axiom (reuse). -/
theorem mod_sub_eq_zero {n : Nat} (hn : 0 < n) {a b : Nat}
    (hle : b ≤ a) (hmod : a % n = b % n) : (a - b) % n = 0 :=
  mod_diff_eq_zero_of_le hn hle hmod.symm

/-! ## The deliverable -/

/-- **Consecutive-run sum divisible by `n`.**  Among any `n` naturals there
    is a non-empty consecutive run `[i, j)` (with `0 ≤ i < j ≤ n`) whose sum
    is a multiple of `n`.  The run is the *computed* prefix-sum collision:
    `exists_collision_lt` returns two distinct prefix indices with equal
    residue mod `n`, and their gap telescopes to a run with sum ≡ 0. -/
theorem exists_consecutive_sum_dvd (n : Nat) (hn : 0 < n) (a : Fin n → Nat) :
    ∃ i j : Nat, i < j ∧ j ≤ n ∧ (segSum a i j) % n = 0 := by
  -- map each prefix index k = 0..n to its residue in Fin n
  let g : Fin (n + 1) → Fin n :=
    fun k => ⟨prefixSum a k.val % n, Nat.mod_lt _ hn⟩
  have hlt : n < n + 1 := Nat.lt_succ_self n
  obtain ⟨p, q, hpq, hg⟩ := exists_collision_lt hlt g
  -- equal residues
  have hres : prefixSum a p.val % n = prefixSum a q.val % n :=
    congrArg Fin.val hg
  have hvalne : p.val ≠ q.val := fun e => hpq (Fin.ext e)
  -- WLOG the smaller index is the run start
  rcases Nat.lt_or_ge p.val q.val with hpqlt | hpqge
  · -- p < q : run [p, q)
    refine ⟨p.val, q.val, hpqlt, Nat.le_of_lt_succ q.isLt, ?_⟩
    have hple : prefixSum a p.val ≤ prefixSum a q.val :=
      prefix_mono a (Nat.le_of_lt hpqlt)
    show (prefixSum a q.val - prefixSum a p.val) % n = 0
    exact mod_sub_eq_zero hn hple hres.symm
  · -- q ≤ p and p ≠ q ⟹ q < p : run [q, p)
    have hqplt : q.val < p.val := Nat.lt_of_le_of_ne hpqge (fun e => hvalne e.symm)
    refine ⟨q.val, p.val, hqplt, Nat.le_of_lt_succ p.isLt, ?_⟩
    have hqle : prefixSum a q.val ≤ prefixSum a p.val :=
      prefix_mono a (Nat.le_of_lt hqplt)
    show (prefixSum a p.val - prefixSum a q.val) % n = 0
    exact mod_sub_eq_zero hn hqle hres

/-! ## Smoke test (closed numerals)

`a = ![1, 2, 3]`, `n = 3`: the run `[2, 3)` sums to `3 ≡ 0 mod 3`
(also `[0, 3)` sums to `6 ≡ 0`).  Existence checked by the theorem; the
prefix sums are pinned by `rfl`. -/

def smoke : Fin 3 → Nat := fun i => i.val + 1   -- 1, 2, 3

-- prefix sums: 0, 1, 3, 6  (so run [2,3) = 6-3 = 3, run [0,3) = 6)
example : prefixSum smoke 3 = 6 := rfl
example : segSum smoke 2 3 = 3 := rfl
example : (segSum smoke 2 3) % 3 = 0 := rfl
example : (segSum smoke 0 3) % 3 = 0 := rfl

#print axioms exists_consecutive_sum_dvd
#print axioms mod_sub_eq_zero
#print axioms prefix_mono

end E213.Lib.Math.Combinatorics.ConsecutiveSumDvd
