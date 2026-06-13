import E213.Lib.Math.Algebra.Linalg213.InversionsAppend
import E213.Lib.Math.NumberTheory.ModArith.ZolotarevSign
import E213.Lib.Math.NumberTheory.ModArith.GaussLemma
import E213.Lib.Math.Algebra.Linalg213.PermMatrixDet

/-!
# ZolotarevMuBridge — `psign σ_a = (a/p)` for every prime (the μ-bridge)

Closes the converse of Zolotarev's lemma for **all** odd primes, completing
`ZolotarevConverse` (which handled `p ≡ 3 mod 4`).  Because `σ_a(p−x) = p − σ_a(x)`,
`mulPermMod a p` is in the block form `0 :: (fh ++ (revL fh).map (p−·))`
(`mulPermMod_block`), so by `psign_blockForm` + `altSign_crossInv_map_psub`,
`psign σ_a = altSign (diagCount p fh)`, and the diagonal count is Gauss's `μ`.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.ZolotarevMuBridge

open E213.Lib.Math.Algebra.Linalg213.Permutation (psign inversions ltCount iota map_lperm LPerm)
open E213.Lib.Math.Algebra.Linalg213.DetN (altSign altSign_add det)
open E213.Lib.Math.Algebra.Linalg213.PermGroup (getD_iota)
open E213.Lib.Math.Algebra.Linalg213.PermClosure (length_iota)
open E213.Lib.Math.Algebra.Linalg213.PermMatrixDet (permMatrix det_permMatrix)
open E213.Lib.Math.Algebra.Linalg213.ProdLperm (prodZ)
open E213.Lib.Math.Algebra.Linalg213.InversionsAppend
  (revL crossInv diagCount revL_getD revL_length
   psign_blockForm altSign_crossInv_map_psub sub_one_sub
   crossInv_lperm_right revL_lperm)
open E213.Lib.Math.NumberTheory.ModArith.ZolotarevSign
  (mulPermMod mulPermMod_getD mulPermMod_length mulPermMod_mem_perms)
open E213.Lib.Math.NumberTheory.ModArith.GaussLemma (seg seg_length sgFn gauss_qr)
open E213.Tactic.List213 (exists_of_mem_map)
open E213.Tactic.List213 (list_ext_getD getD_ge getD_map_ib length_map
   length_append getD_append_left getD_append_right)
open E213.Tactic.NatHelper
  (add_sub_of_le sub_add_cancel add_sub_cancel_right le_sub_of_add_le sub_le_sub_left)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Lib.Math.NumberTheory.FourSquareSeed (nat_prime_dvd_mul)
open E213.Meta.Nat.AddMod213 (add_mod_gen mod_self dvd_of_mod_eq_zero zero_mod)
open E213.Meta.Nat.MulMod213 (mul_mod_pure)

/-! ## §1 — the negation identity `(a·(p−x)) % p = p − (a·x) % p` -/

theorem neg_mul_mod (a p x : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hnpa : ¬ p ∣ a) (hx1 : 1 ≤ x) (hxp : x < p) :
    (a * (p - x)) % p = p - (a * x) % p := by
  have hppos : 0 < p := Nat.lt_trans Nat.zero_lt_one hp
  have hnpx : ¬ p ∣ x := fun h => absurd (le_of_dvd_pos p x hx1 h) (Nat.not_le.mpr hxp)
  have hpx1 : 1 ≤ p - x := le_sub_of_add_le (by rw [Nat.add_comm]; exact Nat.succ_le_of_lt hxp)
  have hpxp : p - x < p := Nat.sub_lt hppos hx1
  have hnppx : ¬ p ∣ (p - x) := fun h => absurd (le_of_dvd_pos p (p - x) hpx1 h) (Nat.not_le.mpr hpxp)
  have hr2_1 : 1 ≤ (a * x) % p :=
    Nat.pos_of_ne_zero (fun h0 => (nat_prime_dvd_mul p hp hpr a x (dvd_of_mod_eq_zero h0)).elim hnpa hnpx)
  have hr2_lt : (a * x) % p < p := Nat.mod_lt _ hppos
  have hr1_lt : (a * (p - x)) % p < p := Nat.mod_lt _ hppos
  have hkey : a * (p - x) + a * x = a * p := by
    rw [← Nat.mul_add, Nat.add_comm (p - x) x, add_sub_of_le (Nat.le_of_lt hxp)]
  have hap : (a * p) % p = 0 := by rw [mul_mod_pure a p p, mod_self, Nat.mul_zero, zero_mod]
  have hsum0 : ((a * (p - x)) % p + (a * x) % p) % p = 0 := by
    rw [← add_mod_gen (a * (p - x)) (a * x) p, hkey, hap]
  have hdvd : p ∣ ((a * (p - x)) % p + (a * x) % p) := dvd_of_mod_eq_zero hsum0
  have hs1 : 1 ≤ (a * (p - x)) % p + (a * x) % p := Nat.le_trans hr2_1 (Nat.le_add_left _ _)
  have hsp : p ≤ (a * (p - x)) % p + (a * x) % p := le_of_dvd_pos p _ hs1 hdvd
  have hs2p : (a * (p - x)) % p + (a * x) % p < p + p := Nat.add_lt_add hr1_lt hr2_lt
  have hsum : (a * (p - x)) % p + (a * x) % p = p := by
    obtain ⟨k, hk⟩ := hdvd
    rw [hk] at hsp hs2p ⊢
    have hk1 : 1 ≤ k := Nat.pos_of_ne_zero (fun h0 => by
      rw [h0, Nat.mul_zero] at hsp; exact absurd hsp (Nat.not_le.mpr hppos))
    have hk2 : k < 2 := by
      rcases Nat.lt_or_ge k 2 with h | h
      · exact h
      · exfalso
        have hge : p * 2 ≤ p * k := Nat.mul_le_mul_left p h
        rw [Nat.mul_comm p 2, Nat.two_mul] at hge
        exact absurd hs2p (Nat.not_lt.mpr hge)
    rw [Nat.le_antisymm (Nat.le_of_lt_succ hk2) hk1, Nat.mul_one]
  calc (a * (p - x)) % p
      = ((a * (p - x)) % p + (a * x) % p) - (a * x) % p := (add_sub_cancel_right _ _).symm
    _ = p - (a * x) % p := by rw [hsum]

/-! ## §2 — `σ_a`'s first half and the block decomposition -/

/-- The first half `[σ_a 1, …, σ_a m]` of `σ_a`. -/
def fhList (a p m : Nat) : List Nat := (seg m).map (fun x => (a * x) % p)

theorem fhList_length (a p m : Nat) : (fhList a p m).length = m := by
  rw [fhList, length_map, seg_length]

theorem seg_getD (m j : Nat) (hj : j < m) : (seg m).getD j 0 = j + 1 := by
  rw [seg, getD_map_ib (· + 1) 0 0 (iota m) j (by rw [length_iota]; exact hj), getD_iota m j hj]

theorem fhList_getD (a p m j : Nat) (hj : j < m) : (fhList a p m).getD j 0 = (a * (j + 1)) % p := by
  rw [fhList, getD_map_ib (fun x => (a * x) % p) 0 0 (seg m) j (by rw [seg_length]; exact hj),
      seg_getD m j hj]

/-- ★★★ **`σ_a` is in block form.**  `mulPermMod a p = 0 :: (fh ++ (revL fh).map (p−·))`,
    because `σ_a(p−x) = p − σ_a(x)` (`neg_mul_mod`). -/
theorem mulPermMod_block (a p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hnpa : ¬ p ∣ a) (h2m : 2 * m = p - 1) :
    mulPermMod a p = 0 :: (fhList a p m ++ (revL (fhList a p m)).map (fun w => p - w)) := by
  have hppos : 0 < p := Nat.lt_trans Nat.zero_lt_one hp
  have hpval : p = m + m + 1 := by
    have hh : m + m = p - 1 := by rw [← Nat.two_mul]; exact h2m
    rw [hh, sub_add_cancel (Nat.le_of_lt hp)]
  have hshlen : ((revL (fhList a p m)).map (fun w => p - w)).length = m := by
    rw [length_map, revL_length, fhList_length]
  refine list_ext_getD 0 ?_ ?_
  · rw [mulPermMod_length]
    show p = (fhList a p m ++ (revL (fhList a p m)).map (fun w => p - w)).length + 1
    rw [length_append, fhList_length, hshlen]; exact hpval
  · intro i
    rcases Nat.lt_or_ge i p with hi | hi
    · rw [mulPermMod_getD a p i hi]
      rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · subst hi0; show (a * 0) % p = 0; rw [Nat.mul_zero, zero_mod]
      · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, (Nat.succ_pred_eq_of_pos hipos).symm⟩
        show (a * (k + 1)) % p
           = (fhList a p m ++ (revL (fhList a p m)).map (fun w => p - w)).getD k 0
        rcases Nat.lt_or_ge k m with hk | hk
        · rw [getD_append_left 0 (fhList a p m) _ k (by rw [fhList_length]; exact hk),
              fhList_getD a p m k hk]
        · obtain ⟨j, rfl⟩ : ∃ j, k = m + j := ⟨k - m, (add_sub_of_le hk).symm⟩
          have hjm : j < m := by
            have hlt : m + j < m + m := by rw [hpval] at hi; exact Nat.lt_of_succ_lt_succ hi
            exact Nat.lt_of_add_lt_add_left hlt
          have hmj1 : 1 ≤ m - j := le_sub_of_add_le (by rw [Nat.add_comm]; exact Nat.succ_le_of_lt hjm)
          have hmjp : m - j < p := Nat.lt_of_le_of_lt (Nat.sub_le m j)
            (by rw [hpval]; exact Nat.lt_succ_of_le (Nat.le_add_right m m))
          have hm1j : m - 1 - j < m := Nat.lt_of_le_of_lt (Nat.sub_le (m - 1) j)
            (Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le j) hjm) Nat.zero_lt_one)
          have hidx1 : (m - 1 - j) + 1 = m - j := by rw [sub_one_sub, sub_add_cancel hmj1]
          have hsumeq : m + j + 1 + (m - j) = p := by
            rw [show m + j + 1 + (m - j) = (m + 1) + (j + (m - j)) from by ring_nat,
                add_sub_of_le (Nat.le_of_lt hjm), hpval]; ring_nat
          have hmj_eq : m + j + 1 = p - (m - j) := by rw [← hsumeq, add_sub_cancel_right]
          have hRHS : (fhList a p m ++ (revL (fhList a p m)).map (fun w => p - w)).getD (m + j) 0
                    = p - (a * (m - j)) % p := by
            have happ := getD_append_right 0 (fhList a p m)
              ((revL (fhList a p m)).map (fun w => p - w)) j
            rw [fhList_length] at happ
            rw [happ,
                getD_map_ib (fun w => p - w) 0 0 (revL (fhList a p m)) j
                  (by rw [revL_length, fhList_length]; exact hjm),
                revL_getD (fhList a p m) j (by rw [fhList_length]; exact hjm),
                fhList_length, fhList_getD a p m (m - 1 - j) hm1j, hidx1]
          rw [hRHS, hmj_eq, neg_mul_mod a p (m - j) hp hpr hnpa hmj1 hmjp]
    · rw [getD_ge 0 (by rw [mulPermMod_length]; exact hi),
          getD_ge 0 (show (0 :: (fhList a p m ++ (revL (fhList a p m)).map (fun w => p - w))).length ≤ i from by
            show (fhList a p m ++ (revL (fhList a p m)).map (fun w => p - w)).length + 1 ≤ i
            rw [length_append, fhList_length, hshlen, ← hpval]; exact hi)]

/-! ## §3 — the bridge `psign σ_a = altSign (diagCount p fh)` -/

theorem fhList_le (a p m : Nat) (hp : 0 < p) : ∀ y ∈ fhList a p m, y ≤ p := by
  intro y hy
  obtain ⟨x, _, hyx⟩ := exists_of_mem_map hy
  rw [← hyx]; exact Nat.le_of_lt (Nat.mod_lt _ hp)

/-- ★★★ **The bridge:** `psign σ_a = altSign (diagCount p fh)` (`fh = σ_a`'s first half).
    `psign_blockForm` reduces `psign σ_a` to the cross count; `altSign_crossInv_map_psub`
    (after `crossInv_lperm_right` drops the reversal) collapses it to the diagonal. -/
theorem psign_mulPermMod_eq_diag (a p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hnpa : ¬ p ∣ a) (h2m : 2 * m = p - 1) :
    psign (mulPermMod a p) = altSign (diagCount p (fhList a p m)) := by
  have hppos : 0 < p := Nat.lt_trans Nat.zero_lt_one hp
  have hle := fhList_le a p m hppos
  rw [mulPermMod_block a p m hp hpr hnpa h2m, psign_blockForm p (fhList a p m) hle,
      crossInv_lperm_right (fhList a p m)
        (map_lperm (fun w => p - w) (LPerm.symm (revL_lperm (fhList a p m))))]
  exact altSign_crossInv_map_psub p (fhList a p m) hle

/-! ## §4 — the diagonal count is Gauss's `μ`: `altSign (diagCount p fh) = ∏ sgFn` -/

/-- `p − y < y ↔ m < y` for `p = 2m+1`, `y ≤ p` (the upper-half test). -/
theorem pm_lt (p m y : Nat) (hpm : p = 2 * m + 1) (hy : y ≤ p) : (p - y < y) ↔ (m < y) := by
  constructor
  · intro h
    rcases Nat.lt_or_ge m y with hmy | hmy
    · exact hmy
    · exfalso
      have h1 : p - m ≤ p - y := sub_le_sub_left p hmy
      have h2 : p - m = m + 1 := by rw [hpm, show 2 * m + 1 = (m + 1) + m from by ring_nat, add_sub_cancel_right]
      have h1' : m + 1 ≤ p - y := by rw [h2] at h1; exact h1
      have hle : y ≤ p - y := Nat.le_trans hmy (Nat.le_trans (Nat.le_succ m) h1')
      exact absurd h (Nat.not_lt.mpr hle)
  · intro h
    have h1 : p - y ≤ p - (m + 1) := sub_le_sub_left p h
    have h2 : p - (m + 1) = m := by rw [hpm, show 2 * m + 1 = m + (m + 1) from by ring_nat, add_sub_cancel_right]
    have h1' : p - y ≤ m := by rw [h2] at h1; exact h1
    exact Nat.lt_of_le_of_lt h1' h

/-- `altSign` of the upper-half indicator is the Gauss sign. -/
theorem sgn_helper (p m y : Nat) (hpm : p = 2 * m + 1) (hy : y < p) :
    altSign (if p - y < y then 1 else 0) = (if y ≤ m then 1 else -1) := by
  rcases Nat.lt_or_ge m y with hym | hym
  · rw [if_pos ((pm_lt p m y hpm (Nat.le_of_lt hy)).mpr hym), if_neg (Nat.not_le.mpr hym)]; rfl
  · rw [if_neg (fun h => absurd ((pm_lt p m y hpm (Nat.le_of_lt hy)).mp h) (Nat.not_lt.mpr hym)),
        if_pos hym]; rfl

theorem altSign_diag_eq_prodSgn (a p m : Nat) (hpm : p = 2 * m + 1) (hp : 0 < p) :
    ∀ (L : List Nat), altSign (diagCount p (L.map (fun x => (a * x) % p)))
      = prodZ (L.map (sgFn a p m))
  | []     => rfl
  | x :: t => by
      show altSign ((if p - (a * x) % p < (a * x) % p then 1 else 0)
            + diagCount p (t.map (fun x => (a * x) % p)))
         = sgFn a p m x * prodZ (t.map (sgFn a p m))
      have hsgn : altSign (if p - (a * x) % p < (a * x) % p then 1 else 0) = sgFn a p m x :=
        sgn_helper p m ((a * x) % p) hpm (Nat.mod_lt _ hp)
      rw [altSign_add, altSign_diag_eq_prodSgn a p m hpm hp t, hsgn]

/-! ## §5 — full Zolotarev: `psign σ_a = (a/p)` for every prime -/

theorem psign_mulPermMod_eq_prodSgn (a p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hnpa : ¬ p ∣ a) (h2m : 2 * m = p - 1) :
    psign (mulPermMod a p) = prodZ ((seg m).map (sgFn a p m)) := by
  have hppos : 0 < p := Nat.lt_trans Nat.zero_lt_one hp
  have hpm : p = 2 * m + 1 := by rw [h2m, sub_add_cancel (Nat.le_of_lt hp)]
  rw [psign_mulPermMod_eq_diag a p m hp hpr hnpa h2m]
  show altSign (diagCount p ((seg m).map (fun x => (a * x) % p))) = prodZ ((seg m).map (sgFn a p m))
  exact altSign_diag_eq_prodSgn a p m hpm hppos (seg m)

/-- ★★★★★ **Zolotarev's lemma (full converse, every prime).**  `psign σ_a = (a/p)`:
    `psign (mulPermMod a p) = 1 ⟺ a` is a quadratic residue mod `p`.  The sign character of the
    multiply-by-`a` permutation is the Legendre symbol — closing the converse for **all** odd
    primes (subsuming `ZolotarevConverse.zolotarev_pmod4_three`). -/
theorem zolotarev_mu (a p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) (ha1 : 1 ≤ a) (halt : a < p) :
    psign (mulPermMod a p) = 1 ↔ (∃ z, 1 ≤ z ∧ z < p ∧ z ^ 2 % p = a) := by
  have hnpa : ¬ p ∣ a := fun h =>
    absurd (le_of_dvd_pos p a (Nat.lt_of_lt_of_le Nat.zero_lt_one ha1) h) (Nat.not_le.mpr halt)
  rw [psign_mulPermMod_eq_prodSgn a p m hp hpr hnpa h2m]
  exact (gauss_qr a p m hp hpr h2m hm1 ha1 halt).symm

/-- ★★★★★ **Zolotarev as a determinant (every prime).**  `det (permMatrix σ_a) = (a/p)`:
    `det = 1 ⟺ a` is a QR — closing the "one permutation, three readouts" triangle
    (inversions / determinant / Legendre) **universally**. -/
theorem det_permMatrix_mulPermMod (a p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) (ha1 : 1 ≤ a) (halt : a < p) :
    det p (permMatrix (mulPermMod a p)) = 1 ↔ (∃ z, 1 ≤ z ∧ z < p ∧ z ^ 2 % p = a) := by
  have hnpa : ¬ p ∣ a := fun h =>
    absurd (le_of_dvd_pos p a (Nat.lt_of_lt_of_le Nat.zero_lt_one ha1) h) (Nat.not_le.mpr halt)
  rw [det_permMatrix p (mulPermMod a p) (mulPermMod_mem_perms a p hp hpr hnpa)]
  exact zolotarev_mu a p m hp hpr h2m hm1 ha1 halt

end E213.Lib.Math.NumberTheory.ModArith.ZolotarevMuBridge
