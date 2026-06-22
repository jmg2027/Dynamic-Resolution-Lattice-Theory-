import E213.Lib.Math.NumberTheory.ModArith.LensCRT
import E213.Lib.Math.NumberTheory.Lcm213
import E213.Lens.Unified

/-!
# The Lens lattice meet is the lcm-modulus — `prodLens(L_m, L_k) ≈ L_{lcm(m,k)}` (∅-axiom)

The general lattice statement behind `LensCRTGeneral`: for *all* positive `m, k` (no coprimality),
the product reading `prodLens(L_m, L_k)` and the mod-`lcm(m,k)` reading have the **same kernel** on
`Raw`:

> `LensIso (leavesModNat (lcm m k)) (prodLens (leavesModNat m) (leavesModNat k))`
> (`leavesModNat_lcm`).

So the meet in the `leavesModNat` Lens-lattice is exactly the lcm-modulus Lens — the Lens
refinement lattice mirrors the divisibility lattice (`refines` = `∣`, meet = lcm). CRT
(`LensCRTGeneral`, coprime ⟹ `lcm = m·k`) is the special case. The CRT/uniqueness step generalizes
to `lcm_unique` (replace `coprime_mul_dvd` by the universal property `lcm_dvd`).
-/

namespace E213.Lib.Math.NumberTheory.ModArith.LensLcmMeet

open E213.Theory E213.Lens
open E213.Lens.Instances.Leaves.ModNat E213.Lens.Lattice.Meet
open E213.Lens.Unified (LensIso)
open E213.Lib.Math.NumberTheory.Lcm213 (lcm213 dvd_lcm_left dvd_lcm_right lcm_dvd lcm_pos)
open E213.Meta.Nat.Gcd213 (mod_eq_dvd_sub)
open E213.Meta.Nat.AddMod213 (mod_mod_of_dvd)

/-- **`lcm`-uniqueness** (the general-modulus analogue of `crt_unique`): two values below
    `lcm(m,k)` that agree mod `m` and mod `k` are equal — via the universal property `lcm_dvd`
    (every common multiple is a multiple of `lcm`), no coprimality needed. -/
theorem lcm_unique (m k : Nat) (hm : 0 < m) (hk : 0 < k) {x y : Nat}
    (hx : x < lcm213 m k) (hy : y < lcm213 m k) (ha : x % m = y % m) (hb : x % k = y % k) :
    x = y := by
  rcases Nat.le_total y x with hyx | hxy
  · have hdm : m ∣ (x - y) := mod_eq_dvd_sub x y m hm hyx ha
    have hdk : k ∣ (x - y) := mod_eq_dvd_sub x y k hk hyx hb
    have hdl : lcm213 m k ∣ (x - y) := lcm_dvd m k (x - y) hm hk hdm hdk
    have hlt : x - y < lcm213 m k := Nat.lt_of_le_of_lt (Nat.sub_le x y) hx
    obtain ⟨c, hc⟩ := hdl
    have hxy0 : x - y = 0 := by
      cases c with
      | zero => rw [hc, Nat.mul_zero]
      | succ c' =>
          exfalso
          have hge : lcm213 m k ≤ x - y := by
            rw [hc]
            calc lcm213 m k = lcm213 m k * 1 := (Nat.mul_one _).symm
              _ ≤ lcm213 m k * (c' + 1) :=
                  Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.zero_le c'))
          exact absurd hge (Nat.not_le.mpr hlt)
    exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hxy0) hyx
  · have hdm : m ∣ (y - x) := mod_eq_dvd_sub y x m hm hxy ha.symm
    have hdk : k ∣ (y - x) := mod_eq_dvd_sub y x k hk hxy hb.symm
    have hdl : lcm213 m k ∣ (y - x) := lcm_dvd m k (y - x) hm hk hdm hdk
    have hlt : y - x < lcm213 m k := Nat.lt_of_le_of_lt (Nat.sub_le y x) hy
    obtain ⟨c, hc⟩ := hdl
    have hyx0 : y - x = 0 := by
      cases c with
      | zero => rw [hc, Nat.mul_zero]
      | succ c' =>
          exfalso
          have hge : lcm213 m k ≤ y - x := by
            rw [hc]
            calc lcm213 m k = lcm213 m k * 1 := (Nat.mul_one _).symm
              _ ≤ lcm213 m k * (c' + 1) :=
                  Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.zero_le c'))
          exact absurd hge (Nat.not_le.mpr hlt)
    exact (Nat.le_antisymm (Nat.le_of_sub_eq_zero hyx0) hxy).symm

/-- **Meet direction**: `L_{lcm(m,k)}` refines `prodLens(L_m, L_k)` — `m, k ∣ lcm` via
    `divides_refines`, through the meet universal property. -/
theorem leavesModNat_refines_prod_lcm (m k : Nat) (hm : 0 < m) (hk : 0 < k) :
    (leavesModNat (lcm213 m k)).refines (prodLens (leavesModNat m) (leavesModNat k)) := by
  apply prodLens_is_meet
  · exact fun u v => by show (u + v) % m = (v + u) % m; rw [Nat.add_comm]
  · exact fun u v => by show (u + v) % k = (v + u) % k; rw [Nat.add_comm]
  · exact divides_refines (lcm213 m k) m (dvd_lcm_left m k hm)
  · exact divides_refines (lcm213 m k) k (dvd_lcm_right m k hk)

/-- **lcm direction**: `prodLens(L_m, L_k)` refines `L_{lcm(m,k)}` for all positive `m, k` — two
    values agreeing mod `m` and mod `k` agree mod `lcm(m,k)` (`lcm_unique`). -/
theorem prod_refines_leavesModNat_lcm (m k : Nat) (hm : 0 < m) (hk : 0 < k) :
    (prodLens (leavesModNat m) (leavesModNat k)).refines (leavesModNat (lcm213 m k)) := by
  intro r r' hpair
  have hpair_view : (prodLens (leavesModNat m) (leavesModNat k)).view r
                      = (prodLens (leavesModNat m) (leavesModNat k)).view r' := hpair
  rw [prodLens_view (leavesModNat m) (leavesModNat k)
        (fun u v => by show (u + v) % m = (v + u) % m; rw [Nat.add_comm])
        (fun u v => by show (u + v) % k = (v + u) % k; rw [Nat.add_comm]) r,
      prodLens_view (leavesModNat m) (leavesModNat k)
        (fun u v => by show (u + v) % m = (v + u) % m; rw [Nat.add_comm])
        (fun u v => by show (u + v) % k = (v + u) % k; rw [Nat.add_comm]) r',
      leavesModNat_view_eq m, leavesModNat_view_eq m,
      leavesModNat_view_eq k, leavesModNat_view_eq k] at hpair_view
  have h_m : Lens.leaves.view r % m = Lens.leaves.view r' % m := congrArg Prod.fst hpair_view
  have h_k : Lens.leaves.view r % k = Lens.leaves.view r' % k := congrArg Prod.snd hpair_view
  show (leavesModNat (lcm213 m k)).view r = (leavesModNat (lcm213 m k)).view r'
  rw [leavesModNat_view_eq (lcm213 m k), leavesModNat_view_eq (lcm213 m k)]
  have hl : 0 < lcm213 m k := lcm_pos m k hm hk
  have hX : Lens.leaves.view r % lcm213 m k < lcm213 m k := Nat.mod_lt _ hl
  have hY : Lens.leaves.view r' % lcm213 m k < lcm213 m k := Nat.mod_lt _ hl
  have eXm : Lens.leaves.view r % lcm213 m k % m = Lens.leaves.view r % m :=
    mod_mod_of_dvd _ (dvd_lcm_left m k hm)
  have eYm : Lens.leaves.view r' % lcm213 m k % m = Lens.leaves.view r' % m :=
    mod_mod_of_dvd _ (dvd_lcm_left m k hm)
  have eXk : Lens.leaves.view r % lcm213 m k % k = Lens.leaves.view r % k :=
    mod_mod_of_dvd _ (dvd_lcm_right m k hk)
  have eYk : Lens.leaves.view r' % lcm213 m k % k = Lens.leaves.view r' % k :=
    mod_mod_of_dvd _ (dvd_lcm_right m k hk)
  have km : Lens.leaves.view r % lcm213 m k % m = Lens.leaves.view r' % lcm213 m k % m := by
    rw [eXm, eYm]; exact h_m
  have kk : Lens.leaves.view r % lcm213 m k % k = Lens.leaves.view r' % lcm213 m k % k := by
    rw [eXk, eYk]; exact h_k
  exact lcm_unique m k hm hk hX hY km kk

/-- ★★★ **The Lens-lattice meet is the lcm-modulus.**  For all positive `m, k`,
    `L_{lcm(m,k)} ≈ prodLens(L_m, L_k)` (equal kernel on `Raw`): the `leavesModNat` refinement
    lattice mirrors the divisibility lattice (`refines` = `∣`, meet = lcm).  CRT
    (`LensCRTGeneral.leavesModNat_crt`) is the coprime special case (`lcm = m·k`). -/
theorem leavesModNat_lcm (m k : Nat) (hm : 0 < m) (hk : 0 < k) :
    LensIso (leavesModNat (lcm213 m k)) (prodLens (leavesModNat m) (leavesModNat k)) :=
  ⟨leavesModNat_refines_prod_lcm m k hm hk, prod_refines_leavesModNat_lcm m k hm hk⟩

end E213.Lib.Math.NumberTheory.ModArith.LensLcmMeet
