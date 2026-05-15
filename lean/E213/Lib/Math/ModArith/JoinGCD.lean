import E213.Lib.Math.ModArith.JoinBezout
import E213.Lib.Math.ModArith.JoinEuclidean
import E213.Lens.Lattice
import E213.Meta.Nat.Gcd213

/-!
# ModJoinGCD: general join = gcd (arbitrary m, k ≥ 2)

Iterates `ModJoinEuclidean.euclidean_step` and
`ModJoinBezout.consecutive_refines_const` via strong induction to
establish, for arbitrary m, k ≥ 2:

    L_m.refines N ∧ L_k.refines N → L_{gcd213 m k}.refines N.

That is, **join = gcd** in the refines preorder holds throughout the
entire mod family (universal direction).

Recall: `LeavesModNat.gcd213_upper_bound` gives the opposite direction
(L_m, L_k are refined by L_gcd).  Together the two directions
establish **join semilattice structure = gcd213 lattice** for the
mod family.

Uses 213-native `gcd213` (∅-axiom) instead of Lean-core `Nat.gcd`
(propext via well-founded termination).
-/

namespace E213.Lib.Math.ModArith.JoinGCD

open E213.Theory E213.Lens
open E213.Lens.Instances.Leaves.ModNat E213.Lib.Math.ModArith.JoinBezout
open E213.Lib.Math.ModArith.JoinEuclidean
open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.Gcd213
  (gcd213_self gcd213_comm gcd213_sub_left gcd213_succ_self)

/-- Sorted auxiliary: `m ≥ k` assumed.  Strong induction on s = m + k.
    ∅-axiom (uses `gcd213_*` ecosystem). -/
private theorem join_refines_gcd_sorted {α : Type} (N : Lens α) :
    ∀ (s m k : Nat), m + k ≤ s → m ≥ k → m ≥ 2 → k ≥ 2 →
    (leavesModNat m).refines N → (leavesModNat k).refines N →
    (leavesModNat (gcd213 m k)).refines N := by
  intro s
  induction s with
  | zero =>
      intro m k hsum _ hm _ _ _
      -- m + k ≤ 0 → m = 0, but m ≥ 2.  Contradiction.
      exfalso
      have hm_le : m ≤ 0 := Nat.le_trans (Nat.le_add_right _ _) hsum
      have hm_zero : m = 0 := Nat.le_zero.mp hm_le
      rw [hm_zero] at hm
      exact absurd hm (by decide)
  | succ n ih =>
      intro m k hsum hmk hm hk hLm hLk
      by_cases heq : m = k
      · rw [heq, gcd213_self]; exact hLk
      · have hmgt : m > k := Nat.lt_of_le_of_ne hmk (Ne.symm heq)
        by_cases hd1 : m - k = 1
        · -- m - k = 1 → m = k + 1
          have hms : m = k + 1 := by
            have h_sub_add : (m - k) + k = m :=
              E213.Tactic.NatHelper.sub_add_cancel hmk
            rw [hd1, Nat.add_comm] at h_sub_add
            exact h_sub_add.symm
          have hconst := consecutive_refines_const N m k hk hms hLm hLk
          have hgcd1 : gcd213 m k = 1 := by
            rw [hms]; exact gcd213_succ_self k
          rw [hgcd1]
          intro r r' _
          exact hconst r r'
        · -- m - k ≠ 1 ∧ m > k → m - k ≥ 2
          have hd2 : m - k ≥ 2 := by
            match h_eq : m - k with
            | 0 =>
              exfalso
              exact absurd (Nat.le_of_sub_eq_zero h_eq) (Nat.not_le_of_lt hmgt)
            | 1 => exact absurd h_eq hd1
            | n+2 => exact Nat.le_add_left 2 n
          have hLmk : (leavesModNat (m - k)).refines N :=
            euclidean_step N m k hk hmgt hd2 hLm hLk
          -- IH bound: (m - k) + k ≤ n.  (m - k) + k = m, hsum: m + k ≤ n + 1.
          -- Need m ≤ n.  Since k ≥ 2, m + k ≤ n + 1 → m ≤ n - 1 ≤ n.
          have h_m_le_n : m ≤ n := by
            -- m + k ≤ n + 1 ∧ k ≥ 2 → m + 2 ≤ n + 1 → m ≤ n - 1 ≤ n
            have h1 : m + 2 ≤ m + k := Nat.add_le_add_left hk m
            have h2 : m + 2 ≤ n + 1 := Nat.le_trans h1 hsum
            -- m + 2 ≤ n + 1 → m + 1 ≤ n → m ≤ n
            have h3 : m + 1 ≤ n := Nat.le_of_succ_le_succ h2
            exact Nat.le_trans (Nat.le_succ m) h3
          have h_mk_sum : (m - k) + k ≤ n := by
            rw [E213.Tactic.NatHelper.sub_add_cancel hmk]
            exact h_m_le_n
          by_cases hmkge : m - k ≥ k
          · have hrec : (leavesModNat (gcd213 (m - k) k)).refines N :=
              ih (m - k) k h_mk_sum hmkge hd2 hk hLmk hLk
            rw [gcd213_sub_left m k hmk]
            exact hrec
          · have hklt : k > m - k := Nat.lt_of_not_le hmkge
            have h_km_sum : k + (m - k) ≤ n := by
              rw [Nat.add_comm]; exact h_mk_sum
            have hrec : (leavesModNat (gcd213 k (m - k))).refines N :=
              ih k (m - k) h_km_sum (Nat.le_of_lt hklt) hk hd2 hLk hLmk
            rw [gcd213_sub_left m k hmk, gcd213_comm]
            exact hrec

/-- **Join = gcd (main theorem)**: for arbitrary m, k ≥ 2,
    L_m.refines N ∧ L_k.refines N → L_{gcd213 m k}.refines N.

    ∅-axiom version using 213-native `gcd213`. -/
theorem join_refines_gcd {α : Type} (N : Lens α) (m k : Nat)
    (hm : m ≥ 2) (hk : k ≥ 2)
    (hLm : (leavesModNat m).refines N)
    (hLk : (leavesModNat k).refines N) :
    (leavesModNat (gcd213 m k)).refines N := by
  by_cases hmk : m ≥ k
  · exact join_refines_gcd_sorted N (m + k) m k (Nat.le_refl _) hmk hm hk hLm hLk
  · have hkm : k ≥ m := Nat.le_of_lt (Nat.lt_of_not_le hmk)
    rw [gcd213_comm]
    exact join_refines_gcd_sorted N (k + m) k m (Nat.le_refl _) hkm hk hm hLk hLm

end E213.Lib.Math.ModArith.JoinGCD

namespace E213.Lib.Math.ModArith.JoinGCD

open E213.Theory E213.Lens
open E213.Lens.Instances.Leaves.ModNat
open E213.Tactic.NatHelper (gcd213)

/-- **Sanity check**: L_4 + L_6 → L_2 is a special case of
    join_refines_gcd (gcd213 4 6 = 2). -/
example {α : Type} (N : Lens α)
    (hL4 : (leavesModNat 4).refines N)
    (hL6 : (leavesModNat 6).refines N) :
    (leavesModNat 2).refines N := by
  have := join_refines_gcd N 4 6 (by decide) (by decide) hL4 hL6
  have hgcd : gcd213 4 6 = 2 := rfl
  rw [hgcd] at this
  exact this

/-- **Sanity check**: L_2 + L_3 → N constant.  gcd213 2 3 = 1,
    L_1.refines N = N const. -/
example {α : Type} (N : Lens α)
    (hL2 : (leavesModNat 2).refines N)
    (hL3 : (leavesModNat 3).refines N) :
    ∀ r r' : Raw, N.view r = N.view r' := by
  have := join_refines_gcd N 2 3 (by decide) (by decide) hL2 hL3
  have hgcd : gcd213 2 3 = 1 := rfl
  rw [hgcd] at this
  intro r r'
  apply this r r'
  show (leavesModNat 1).view r = (leavesModNat 1).view r'
  rw [leavesModNat_view_eq, leavesModNat_view_eq, Nat.mod_one, Nat.mod_one]

end E213.Lib.Math.ModArith.JoinGCD

namespace E213.Lib.Math.ModArith.JoinGCD

open E213.Theory E213.Lens
open E213.Lens.Instances.Leaves.ModNat E213.Lens.Lattice.JoinEquiv
open E213.Tactic.NatHelper (gcd213)

/-- **JoinEquiv ⊆ L_gcd.equiv**: JoinEquiv L_m L_k is contained in
    the equivalence of L_gcd.  ∅-axiom version using `gcd213`. -/
theorem joinEquiv_subset_gcd (m k : Nat)
    (x y : Raw)
    (h : JoinEquiv (leavesModNat m) (leavesModNat k) x y) :
    (leavesModNat (gcd213 m k)).equiv x y := by
  have hsym : ∀ u v, (leavesModNat (gcd213 m k)).combine u v
                       = (leavesModNat (gcd213 m k)).combine v u := by
    intro u v
    show (u + v) % gcd213 m k = (v + u) % gcd213 m k
    rw [Nat.add_comm]
  have hLm_gcd : (leavesModNat m).refines (leavesModNat (gcd213 m k)) :=
    (gcd213_upper_bound m k).1
  have hLk_gcd : (leavesModNat k).refines (leavesModNat (gcd213 m k)) :=
    (gcd213_upper_bound m k).2
  exact JoinEquiv_is_least _ _ _ hsym hLm_gcd hLk_gcd x y h

end E213.Lib.Math.ModArith.JoinGCD
