import E213.Hypervisor.Lens.Leaves.ModNat
import E213.Hypervisor.Lens.Lattice.Meet

/-!
# ModLensCRT: prodLens(L_2, L_3) ≈ L_6 (CRT in Lens form)

**Theorem**: `L_6` and `prodLens L_2 L_3` are refines-equivalent.

## Significance

Concrete case (m=2, k=3, lcm=6) of the claim in Note 45:
"prodLens L_m L_k ≈ L_{lcm(m,k)}."  CRT is realized as a Lens
lattice structure.

A Lean witness that the two meet representations (prodLens and L_lcm)
yield exactly the same kernel.
-/

namespace E213.Math.ModArith.LensCRT

open E213.Firmware E213.Hypervisor
open E213.Hypervisor.Lens.Leaves.ModNat E213.Hypervisor.Lens.Lattice.Meet

/-- L_6 refines prodLens(L_2, L_3) — automatic from divides_refines
    + the meet universal property. -/
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

/-- prodLens(L_2, L_3) refines L_6 — the CRT direction.  Two values
    with the same mod 2 and mod 3 have the same mod 6. -/
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

end E213.Math.ModArith.LensCRT
