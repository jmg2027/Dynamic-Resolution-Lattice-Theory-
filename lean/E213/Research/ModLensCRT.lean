import E213.Research.LeavesModNat
import E213.Research.LensMeet

/-!
# Research.ModLensCRT: prodLens(L_2, L_3) ≈ L_6 (CRT in Lens form)

**정리**: `L_6` 와 `prodLens L_2 L_3` 는 refines-equivalent.

## 의의

Note 45 의 claim "prodLens L_m L_k ≈ L_{lcm(m,k)}" 의 concrete
case (m=2, k=3, lcm=6).  CRT 가 Lens lattice 구조로 실현됨.

두 meet 표현 (prodLens 와 L_lcm) 이 정확히 같은 kernel 을
주는 Lean witness.
-/

namespace E213.Research.ModLensCRT

open E213.Firmware E213.Hypervisor
open E213.Research.LeavesModNat E213.Research.LensMeet

/-- L_6 refines prodLens(L_2, L_3) — divides_refines + meet
    universal property 로 자동. -/
theorem L6_refines_prod :
    (leavesModNat 6).refines
      (prodLens (leavesModNat 2) (leavesModNat 3)) := by
  apply prodLens_is_meet
  · intro u v
    show (u + v) % 2 = (v + u) % 2
    rw [Nat.add_comm]
  · intro u v
    show (u + v) % 3 = (v + u) % 3
    rw [Nat.add_comm]
  · exact divides_refines 6 2 ⟨3, rfl⟩
  · exact divides_refines 6 3 ⟨2, rfl⟩

/-- prodLens(L_2, L_3) refines L_6 — CRT 방향.  two values with
    same mod 2 and same mod 3 have same mod 6. -/
theorem prod_refines_L6 :
    (prodLens (leavesModNat 2) (leavesModNat 3)).refines
      (leavesModNat 6) := by
  intro r r' hpair
  have hpair_view : (prodLens (leavesModNat 2) (leavesModNat 3)).view r
                      = (prodLens (leavesModNat 2) (leavesModNat 3)).view r' :=
    hpair
  have hview_r := prodLens_view (leavesModNat 2) (leavesModNat 3)
    (fun u v => by show (u + v) % 2 = (v + u) % 2; rw [Nat.add_comm])
    (fun u v => by show (u + v) % 3 = (v + u) % 3; rw [Nat.add_comm]) r
  have hview_r' := prodLens_view (leavesModNat 2) (leavesModNat 3)
    (fun u v => by show (u + v) % 2 = (v + u) % 2; rw [Nat.add_comm])
    (fun u v => by show (u + v) % 3 = (v + u) % 3; rw [Nat.add_comm]) r'
  rw [hview_r, hview_r'] at hpair_view
  rw [leavesModNat_view_eq 2, leavesModNat_view_eq 2,
      leavesModNat_view_eq 3, leavesModNat_view_eq 3] at hpair_view
  have h2 : Lens.leaves.view r % 2 = Lens.leaves.view r' % 2 :=
    congrArg Prod.fst hpair_view
  have h3 : Lens.leaves.view r % 3 = Lens.leaves.view r' % 3 :=
    congrArg Prod.snd hpair_view
  show (leavesModNat 6).view r = (leavesModNat 6).view r'
  rw [leavesModNat_view_eq 6, leavesModNat_view_eq 6]
  omega

end E213.Research.ModLensCRT
