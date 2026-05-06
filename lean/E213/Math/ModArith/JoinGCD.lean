import E213.Math.ModArith.JoinBezout
import E213.Math.ModArith.JoinEuclidean
import E213.Hypervisor.Lens.Lattice.JoinEquiv

/-!
# ModJoinGCD: general join = gcd (arbitrary m, k ≥ 2)

Iterates `ModJoinEuclidean.euclidean_step` and
`ModJoinBezout.consecutive_refines_const` via strong induction to
establish, for arbitrary m, k ≥ 2:

    L_m.refines N ∧ L_k.refines N → L_{gcd m k}.refines N.

That is, **join = gcd** in the refines preorder holds throughout the
entire mod family (universal direction).

Recall: `LeavesModNat.gcd_upper_bound` gives the opposite direction
(L_m, L_k are refined by L_gcd).  Together the two directions
establish **join semilattice structure = Nat.gcd lattice** for the
mod family.

## gcd = 1 case

When m, k are coprime (gcd = 1), we obtain L_1.refines N.
Since `leavesModNat 1` has view = 0 for every r, refines is
equivalent to "N constant."  Hence coprimality implies "N is constant."
-/

namespace E213.Math.ModArith.JoinGCD

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Leaves.ModNat E213.Math.ModArith.JoinBezout
open E213.Math.ModArith.JoinEuclidean

/-- gcd(m, k) = gcd(m - k, k) when k ≤ m. -/
private theorem gcd_sub_left (m k : Nat) (h : k ≤ m) :
    Nat.gcd m k = Nat.gcd (m - k) k := by
  have hexp : (m - k) + k = m := by omega
  calc Nat.gcd m k
      = Nat.gcd ((m - k) + k) k := by rw [hexp]
    _ = Nat.gcd k ((m - k) + k) := Nat.gcd_comm _ _
    _ = Nat.gcd (((m - k) + k) % k) k := Nat.gcd_rec _ _
    _ = Nat.gcd ((m - k) % k) k := by rw [Nat.add_mod_right]
    _ = Nat.gcd k (m - k) := (Nat.gcd_rec _ _).symm
    _ = Nat.gcd (m - k) k := Nat.gcd_comm _ _

/-- gcd(k+1, k) = 1 (for k ≥ 2). -/
private theorem gcd_succ_self (k : Nat) (hk : k ≥ 2) :
    Nat.gcd (k + 1) k = 1 := by
  rw [Nat.gcd_rec]
  have h1 : k % (k + 1) = k := Nat.mod_eq_of_lt (Nat.lt_succ_self k)
  rw [h1, Nat.gcd_rec]
  have h2 : (k + 1) % k = 1 := by
    rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (by omega)
  rw [h2, Nat.gcd_rec]
  rw [Nat.mod_one]
  rfl

end E213.Math.ModArith.JoinGCD

namespace E213.Math.ModArith.JoinGCD

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Leaves.ModNat E213.Math.ModArith.JoinBezout
open E213.Math.ModArith.JoinEuclidean

/-- Sorted auxiliary: `m ≥ k` assumed.  Strong induction on s = m + k. -/
private theorem join_refines_gcd_sorted {α : Type} (N : Lens α) :
    ∀ (s m k : Nat), m + k ≤ s → m ≥ k → m ≥ 2 → k ≥ 2 →
    (leavesModNat m).refines N → (leavesModNat k).refines N →
    (leavesModNat (Nat.gcd m k)).refines N := by
  intro s
  induction s with
  | zero =>
      intro m k _ _ hm _ _ _
      omega
  | succ n ih =>
      intro m k hsum _ hm hk hLm hLk
      by_cases heq : m = k
      · rw [heq, Nat.gcd_self]; exact hLk
      · have hmgt : m > k := by omega
        by_cases hd1 : m - k = 1
        · have hms : m = k + 1 := by omega
          have hconst := consecutive_refines_const N m k hk hms hLm hLk
          have hgcd1 : Nat.gcd m k = 1 := by
            rw [hms]; exact gcd_succ_self k hk
          rw [hgcd1]
          intro r r' _
          exact hconst r r'
        · have hd2 : m - k ≥ 2 := by omega
          have hLmk : (leavesModNat (m - k)).refines N :=
            euclidean_step N m k hk hmgt hd2 hLm hLk
          by_cases hmkge : m - k ≥ k
          · have hrec : (leavesModNat (Nat.gcd (m - k) k)).refines N :=
              ih (m - k) k (by omega) hmkge hd2 hk hLmk hLk
            rw [gcd_sub_left m k (by omega)]
            exact hrec
          · have hklt : k > m - k := Nat.lt_of_not_le hmkge
            have hrec : (leavesModNat (Nat.gcd k (m - k))).refines N :=
              ih k (m - k) (by omega) (by omega) hk hd2 hLk hLmk
            rw [gcd_sub_left m k (by omega), Nat.gcd_comm]
            exact hrec

/-- **Join = gcd (main theorem)**: for arbitrary m, k ≥ 2,
    L_m.refines N ∧ L_k.refines N → L_{gcd m k}.refines N.

    Two significances:
    - Combined with `LeavesModNat.gcd_upper_bound` (L_m, L_k are
      refined by L_gcd), gives the **least upper bound
      characterization** of the refines preorder (gcd is least).
    - When gcd = 1 (coprime), L_1.refines N = N constant.  Hence
      coprime + N refines both → N is constant. -/
theorem join_refines_gcd {α : Type} (N : Lens α) (m k : Nat)
    (hm : m ≥ 2) (hk : k ≥ 2)
    (hLm : (leavesModNat m).refines N)
    (hLk : (leavesModNat k).refines N) :
    (leavesModNat (Nat.gcd m k)).refines N := by
  by_cases hmk : m ≥ k
  · exact join_refines_gcd_sorted N (m + k) m k (Nat.le_refl _) hmk hm hk hLm hLk
  · have hkm : k ≥ m := Nat.le_of_lt (Nat.lt_of_not_le hmk)
    rw [Nat.gcd_comm]
    exact join_refines_gcd_sorted N (k + m) k m (Nat.le_refl _) hkm hk hm hLk hLm

end E213.Math.ModArith.JoinGCD

namespace E213.Math.ModArith.JoinGCD

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Leaves.ModNat

/-- **Sanity check**: L_4 + L_6 → L_2 is a special case of
    join_refines_gcd (gcd 4 6 = 2).  Consistent with the manual
    Bezout construction of
    `ModJoinExample.mod_4_6_refines_parity`. -/
example {α : Type} (N : Lens α)
    (hL4 : (leavesModNat 4).refines N)
    (hL6 : (leavesModNat 6).refines N) :
    (leavesModNat 2).refines N := by
  have := join_refines_gcd N 4 6 (by decide) (by decide) hL4 hL6
  have hgcd : Nat.gcd 4 6 = 2 := by decide
  rw [hgcd] at this
  exact this

/-- **Sanity check**: L_2 + L_3 → N constant is consistent with
    `ModJoinCoprime`.  gcd 2 3 = 1, L_1.refines N = N const. -/
example {α : Type} (N : Lens α)
    (hL2 : (leavesModNat 2).refines N)
    (hL3 : (leavesModNat 3).refines N) :
    ∀ r r' : Raw, N.view r = N.view r' := by
  have := join_refines_gcd N 2 3 (by decide) (by decide) hL2 hL3
  have hgcd : Nat.gcd 2 3 = 1 := by decide
  rw [hgcd] at this
  intro r r'
  apply this r r'
  show (leavesModNat 1).view r = (leavesModNat 1).view r'
  rw [leavesModNat_view_eq, leavesModNat_view_eq, Nat.mod_one, Nat.mod_one]

end E213.Math.ModArith.JoinGCD

namespace E213.Math.ModArith.JoinGCD

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Leaves.ModNat E213.Hypervisor.Lens.Lattice.JoinEquiv

/-- **JoinEquiv ⊆ L_gcd.equiv**: JoinEquiv L_m L_k is contained in
    the equivalence of L_gcd.  Direct consequence of
    `JoinEquiv_is_least` + `gcd_upper_bound`. -/
theorem joinEquiv_subset_gcd (m k : Nat)
    (x y : Raw)
    (h : JoinEquiv (leavesModNat m) (leavesModNat k) x y) :
    (leavesModNat (Nat.gcd m k)).equiv x y := by
  have hsym : ∀ u v, (leavesModNat (Nat.gcd m k)).combine u v
                       = (leavesModNat (Nat.gcd m k)).combine v u := by
    intro u v
    show (u + v) % Nat.gcd m k = (v + u) % Nat.gcd m k
    rw [Nat.add_comm]
  have hLm_gcd : (leavesModNat m).refines (leavesModNat (Nat.gcd m k)) :=
    (gcd_upper_bound m k).1
  have hLk_gcd : (leavesModNat k).refines (leavesModNat (Nat.gcd m k)) :=
    (gcd_upper_bound m k).2
  exact JoinEquiv_is_least _ _ _ hsym hLm_gcd hLk_gcd x y h

end E213.Math.ModArith.JoinGCD
