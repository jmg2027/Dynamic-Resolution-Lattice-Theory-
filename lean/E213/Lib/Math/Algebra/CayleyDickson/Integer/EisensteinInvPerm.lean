import E213.Lib.Math.NumberTheory.EulerTheorem
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.AddMod213

/-!
# The units-inversion permutation `t ↦ t⁻¹ mod p` (∅-axiom)

Multiplicative inversion permutes the totatives: for a prime `p`, the map `t ↦ (aInv t p) mod p`
(`aInv` = the Bezout inverse) is a **bijection of `totativeList p`** (an involution `t⁻¹⁻¹ = t`):

  `LPerm (totativeList p) (map (·⁻¹) (totativeList p))`   (`totativeList_inv_lperm`).

This is the inversion reindex the cubic Gauss sum's off-diagonal `C = −1` needs (`χ(j+1)χ̄(j) =
χ(1+j⁻¹)`, reindex `w = j⁻¹`).  Injective/surjective by modular cancellation (`cancel_unit`) + the
involution.  The sibling of `EisensteinRangeSum.rangeList_mul_lperm` for inversion, not multiplication.
∅-axiom.  (A3 route b.)
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinInvPerm

open E213.Lib.Math.NumberTheory.EulerTheorem
  (aInv aInv_spec aInv_coprime gcd_mod_left cancel_unit lperm_of_nodup_mem_iff
   totativeList nodup_totativeList totativeList_coprime totative_lt_n totativeList_pos totativeList_le)
open E213.Lib.Math.Combinatorics.Permutations (LPerm)
open E213.Tactic.List213 (nodup_map_of_inj mem_map_of_mem exists_of_mem_map)
open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.MulMod213 (mul_mod_right_pure)
open E213.Meta.Nat.AddMod213 (mod_mod)

/-- `(t · (aInv t p % p)) % p = 1 % p` for a unit `t`. -/
private theorem inv_val_spec {t p : Nat} (hp : 0 < p) (ht : gcd213 t p = 1) :
    (t * (aInv t p % p)) % p = 1 % p := by
  rw [← mul_mod_right_pure t (aInv t p) p]; exact aInv_spec hp ht

/-- `gcd (aInv t p % p) p = 1` for a unit `t`. -/
private theorem inv_coprime' {t p : Nat} (hp : 1 < p) (ht : gcd213 t p = 1) :
    gcd213 (aInv t p % p) p = 1 := by
  rw [gcd_mod_left (aInv t p) p (Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hp))]
  exact aInv_coprime hp ht

/-- The inverse stays a totative: `t ∈ totativeList p → (aInv t p % p) ∈ totativeList p`. -/
private theorem inv_mem {t p : Nat} (hp : 1 < p) (ht : t ∈ totativeList p) :
    (aInv t p % p) ∈ totativeList p := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hp)
  have hco : gcd213 (aInv t p % p) p = 1 := inv_coprime' hp (totativeList_coprime ht)
  have hpos : 1 ≤ aInv t p % p := by
    rcases Nat.eq_zero_or_pos (aInv t p % p) with h0 | h
    · exfalso
      have hs := inv_val_spec hppos (totativeList_coprime ht)
      rw [h0, Nat.mul_zero, Nat.mod_eq_of_lt hppos, Nat.mod_eq_of_lt hp] at hs
      exact absurd hs (by decide)
    · exact h
  exact E213.Lib.Math.NumberTheory.EulerTheorem.mem_totListUpto.mpr
    ⟨hpos, Nat.le_of_lt (Nat.mod_lt _ hppos), hco⟩

/-- ★★★ **The involution** — `((aInv t p % p)⁻¹) % p = t` for a unit `t < p`: inversion squared is the
    identity (`cancel_unit` on the two inverses of `t⁻¹`).  ∅-axiom. -/
private theorem inv_invol {t p : Nat} (hp : 1 < p) (ht : gcd213 t p = 1) (htlt : t < p) :
    aInv (aInv t p % p) p % p = t := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hp)
  -- w := aInv t p % p ;  both `t` and `aInv w p % p` are inverses of `w`
  have hw : gcd213 (aInv t p % p) p = 1 := inv_coprime' hp ht
  have h1 : ((aInv t p % p) * t) % p = 1 % p := by
    rw [Nat.mul_comm]; exact inv_val_spec hppos ht
  have h2 : ((aInv t p % p) * (aInv (aInv t p % p) p % p)) % p = 1 % p := inv_val_spec hppos hw
  have hcanc := cancel_unit hp hw (h2.trans h1.symm) htlt
  rwa [mod_mod] at hcanc

/-- ★★★★ **Inversion permutes the totatives** — `LPerm (totativeList p) (map (·⁻¹) (totativeList p))`
    for a prime `p` (`1 < p`).  Injective by `cancel_unit`, surjective by the involution `inv_invol`.
    The inversion reindex for the Gauss-sum off-diagonal `C = −1`.  ∅-axiom. -/
theorem totativeList_inv_lperm {p : Nat} (hp : 1 < p) :
    LPerm (totativeList p) ((totativeList p).map (fun t => aInv t p % p)) := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hp)
  have hinj : ∀ i, i ∈ totativeList p → ∀ j, j ∈ totativeList p →
      aInv i p % p = aInv j p % p → i = j := by
    intro i hi j hj he
    have hci := totativeList_coprime hi
    have hilt := totative_lt_n hp (totativeList_coprime hi) (totativeList_pos hi) (totativeList_le hi)
    have hjlt := totative_lt_n hp (totativeList_coprime hj) (totativeList_pos hj) (totativeList_le hj)
    have hw : gcd213 (aInv i p % p) p = 1 := inv_coprime' hp hci
    have hiw : ((aInv i p % p) * i) % p = 1 % p := by
      rw [Nat.mul_comm]; exact inv_val_spec hppos hci
    have hjw : ((aInv i p % p) * j) % p = 1 % p := by
      rw [he, Nat.mul_comm]; exact inv_val_spec hppos (totativeList_coprime hj)
    have := cancel_unit hp hw (hiw.trans hjw.symm) hjlt
    rwa [Nat.mod_eq_of_lt hilt] at this
  refine lperm_of_nodup_mem_iff (nodup_totativeList p)
    (nodup_map_of_inj hinj (nodup_totativeList p)) (fun y => ?_)
  constructor
  · intro hy
    have hylt := totative_lt_n hp (totativeList_coprime hy) (totativeList_pos hy) (totativeList_le hy)
    have hinvol : aInv (aInv y p % p) p % p = y := inv_invol hp (totativeList_coprime hy) hylt
    rw [← hinvol]
    exact mem_map_of_mem (fun t => aInv t p % p) (inv_mem hp hy)
  · intro hy
    obtain ⟨t, ht, rfl⟩ := exists_of_mem_map hy
    exact inv_mem hp ht

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinInvPerm
