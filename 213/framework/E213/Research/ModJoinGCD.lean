import E213.Research.ModJoinBezout
import E213.Research.ModJoinEuclidean

/-!
# Research.ModJoinGCD: 일반 join = gcd (임의 m, k ≥ 2)

`ModJoinEuclidean.euclidean_step` + `ModJoinBezout.consecutive_refines_const`
를 strong induction 으로 iterate 해서 임의 m, k ≥ 2 에 대해

    L_m.refines N ∧ L_k.refines N → L_{gcd m k}.refines N.

즉 refines preorder 의 **join = gcd** 이 mod family 전체에서
확립 (universal direction).

Recall: `LeavesModNat.gcd_upper_bound` 은 반대 방향 (L_m,
L_k 가 L_gcd 를 refine).  두 방향 합쳐 mod family 의
**join semilattice 구조 = Nat.gcd lattice**.

## gcd = 1 case

m, k coprime (gcd = 1) 이면 L_1.refines N 을 얻음.
`leavesModNat 1` 은 모든 r 에 대해 view = 0 이므로 refines 가
"N constant" 와 동치.  따라서 coprime 은 "N 은 constant" 를 의미.
-/

namespace E213.Research.ModJoinGCD

open E213.Firmware E213.Hypervisor
open E213.Research.LeavesModNat E213.Research.ModJoinBezout
open E213.Research.ModJoinEuclidean

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

namespace E213.Research.ModJoinGCD

open E213.Firmware E213.Hypervisor
open E213.Research.LeavesModNat E213.Research.ModJoinBezout
open E213.Research.ModJoinEuclidean

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

/-- **Join = gcd (main theorem)**: 임의 m, k ≥ 2 에 대해
    L_m.refines N ∧ L_k.refines N → L_{gcd m k}.refines N.

    두 의의:
    - `LeavesModNat.gcd_upper_bound` (L_m, L_k 가 L_gcd 에 의해
      refine 됨) 와 합쳐, refines preorder 의 **least upper bound
      characterization** (gcd 이 least).
    - gcd = 1 (coprime) 이면 L_1.refines N = N constant.  따라서
      coprime + N 양쪽 refine → N 은 constant. -/
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

namespace E213.Research.ModJoinGCD

open E213.Firmware E213.Hypervisor
open E213.Research.LeavesModNat

/-- **Sanity check**: L_4 + L_6 → L_2 은 join_refines_gcd 의
    특수 경우 (gcd 4 6 = 2).  `ModJoinExample.mod_4_6_refines_parity`
    의 manual Bezout 구성과 일관. -/
example {α : Type} (N : Lens α)
    (hL4 : (leavesModNat 4).refines N)
    (hL6 : (leavesModNat 6).refines N) :
    (leavesModNat 2).refines N := by
  have := join_refines_gcd N 4 6 (by decide) (by decide) hL4 hL6
  have hgcd : Nat.gcd 4 6 = 2 := by decide
  rw [hgcd] at this
  exact this

/-- **Sanity check**: L_2 + L_3 → N constant 은
    `ModJoinCoprime` 와 일관.  gcd 2 3 = 1, L_1.refines N = N const. -/
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

end E213.Research.ModJoinGCD
