import E213.Lib.Math.NumberTheory.ModArith.LensCRT
import E213.Lib.Math.NumberTheory.ModArith.CRTReconstruction
import E213.Lens.Unified

/-!
# General coprime CRT as a cross-domain Lens-isomorphism (∅-axiom)

`ModArith.LensCRT` realizes CRT as a Lens kernel-coincidence in the concrete case
`L_6 ≈ prodLens(L_2, L_3)`.  This file lifts it to the **general coprime** statement:

> `prodLens (L_m) (L_k) ≈ L_{m·k}`   whenever `gcd(m,k) = 1`   (`leavesModNat_crt`).

i.e. the mod-`mk` reading and the `(mod-m, mod-k)` product reading are *one residue* — a
genuine cross-domain `LensIso` (equal kernel on `Raw`), the number-theoretic primacy-witness
(narrative: `theory/essays/synthesis/crt_is_a_cross_domain_lensiso.md`).  The CRT direction
(`prodLens ⊑ L_{mk}`) replaces the concrete 36-case enumeration by `crt_unique`; the meet
direction (`L_{mk} ⊑ prodLens`) is `divides_refines` (m, k ∣ mk) through `prodLens_is_meet`.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.LensCRTGeneral

open E213.Theory E213.Lens
open E213.Lens.Instances.Leaves.ModNat E213.Lens.Lattice.Meet
open E213.Lens.Unified (LensIso)
open E213.Lib.Math.NumberTheory.ModArith.CRTReconstruction (crt_unique)
open E213.Meta.Nat.AddMod213 (mod_mod_of_dvd)

/-- Combine-commutativity of `leavesModNat m` (used to compute `prodLens` views). -/
private theorem lmn_comm (m : Nat) : ∀ u v, (u + v) % m = (v + u) % m :=
  fun u v => by rw [Nat.add_comm]

/-- **Meet direction**: `L_{mk}` refines `prodLens(L_m, L_k)` — `m, k ∣ mk` via
    `divides_refines`, through the meet universal property. -/
theorem leavesModNat_refines_prod (m k : Nat) :
    (leavesModNat (m * k)).refines (prodLens (leavesModNat m) (leavesModNat k)) := by
  apply prodLens_is_meet
  · exact fun u v => by show (u + v) % m = (v + u) % m; rw [Nat.add_comm]
  · exact fun u v => by show (u + v) % k = (v + u) % k; rw [Nat.add_comm]
  · exact divides_refines (m * k) m ⟨k, rfl⟩
  · exact divides_refines (m * k) k ⟨m, by rw [Nat.mul_comm]⟩

/-- **CRT direction**: `prodLens(L_m, L_k)` refines `L_{mk}` for coprime `m, k` — two values
    agreeing mod `m` and mod `k` agree mod `mk` (`crt_unique`). -/
theorem prod_refines_leavesModNat (m k : Nat) (hm : 0 < m) (hk : 0 < k)
    (hco : E213.Tactic.NatHelper.gcd213 m k = 1) :
    (prodLens (leavesModNat m) (leavesModNat k)).refines (leavesModNat (m * k)) := by
  intro r r' hpair
  have hpair_view : (prodLens (leavesModNat m) (leavesModNat k)).view r
                      = (prodLens (leavesModNat m) (leavesModNat k)).view r' := hpair
  rw [prodLens_view (leavesModNat m) (leavesModNat k) (lmn_comm m) (lmn_comm k) r,
      prodLens_view (leavesModNat m) (leavesModNat k) (lmn_comm m) (lmn_comm k) r',
      leavesModNat_view_eq m, leavesModNat_view_eq m,
      leavesModNat_view_eq k, leavesModNat_view_eq k] at hpair_view
  have h_m : Lens.leaves.view r % m = Lens.leaves.view r' % m := congrArg Prod.fst hpair_view
  have h_k : Lens.leaves.view r % k = Lens.leaves.view r' % k := congrArg Prod.snd hpair_view
  show (leavesModNat (m * k)).view r = (leavesModNat (m * k)).view r'
  rw [leavesModNat_view_eq (m * k), leavesModNat_view_eq (m * k)]
  have hmk : 0 < m * k := Nat.mul_pos hm hk
  have hX : Lens.leaves.view r % (m * k) < m * k := Nat.mod_lt _ hmk
  have hY : Lens.leaves.view r' % (m * k) < m * k := Nat.mod_lt _ hmk
  have eXm : Lens.leaves.view r % (m * k) % m = Lens.leaves.view r % m :=
    mod_mod_of_dvd _ ⟨k, rfl⟩
  have eYm : Lens.leaves.view r' % (m * k) % m = Lens.leaves.view r' % m :=
    mod_mod_of_dvd _ ⟨k, rfl⟩
  have eXk : Lens.leaves.view r % (m * k) % k = Lens.leaves.view r % k :=
    mod_mod_of_dvd _ ⟨m, by rw [Nat.mul_comm]⟩
  have eYk : Lens.leaves.view r' % (m * k) % k = Lens.leaves.view r' % k :=
    mod_mod_of_dvd _ ⟨m, by rw [Nat.mul_comm]⟩
  have km : Lens.leaves.view r % (m * k) % m = Lens.leaves.view r' % (m * k) % m := by
    rw [eXm, eYm]; exact h_m
  have kk : Lens.leaves.view r % (m * k) % k = Lens.leaves.view r' % (m * k) % k := by
    rw [eXk, eYk]; exact h_k
  exact crt_unique hco hm hk hX hY km kk

/-- ★★★ **General coprime CRT as a cross-domain Lens-isomorphism.**  For `gcd(m,k) = 1`, the
    mod-`mk` reading and the `(mod-m, mod-k)` product reading have the *same kernel* on `Raw`:
    `L_{mk} ≈ prodLens(L_m, L_k)`.  The genuine number-theoretic primacy-witness, generalized
    from the concrete `L_6` to all coprime moduli. -/
theorem leavesModNat_crt (m k : Nat) (hm : 0 < m) (hk : 0 < k)
    (hco : E213.Tactic.NatHelper.gcd213 m k = 1) :
    LensIso (leavesModNat (m * k)) (prodLens (leavesModNat m) (leavesModNat k)) :=
  ⟨leavesModNat_refines_prod m k, prod_refines_leavesModNat m k hm hk hco⟩

end E213.Lib.Math.NumberTheory.ModArith.LensCRTGeneral
