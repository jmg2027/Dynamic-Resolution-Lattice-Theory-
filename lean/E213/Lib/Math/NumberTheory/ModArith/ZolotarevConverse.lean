import E213.Lib.Math.NumberTheory.ModArith.ZolotarevSign
import E213.Lib.Math.NumberTheory.ModArith.EulerFirstSupplement
import E213.Lib.Math.NumberTheory.ModArith.LegendreMultiplicative

/-!
# ZolotarevConverse — the sign character is the Legendre symbol on the `−1` axis

`ZolotarevSign` closes the **residue** side of Zolotarev's lemma: `QR(a) ⟹ psign σ_a = 1`
(`psign_mulPermMod_qr`).  The full identity `psign σ_a = (a/p)` for *every* unit needs the
**non-residue ⟹ odd-permutation** direction — that the sign character `a ↦ psign σ_a` is
*nontrivial*.

This file closes that direction on the **`a = −1` axis** (the `(−1/p)` corner of the
inversion-sign square), universally for every odd prime, and then leverages it through the
character homomorphism + Legendre-multiplicativity to close the **full converse for every
prime `p ≡ 3 (mod 4)`**.

The `σ_{-1}` permutation is the reversal `[0, p−1, p−2, …, 1]` (multiply-by-`(p−1)` ≡ negate).
Its inversion count is `tri₂(p−1) = (p−1)(p−2)/2`, whose parity is the parity of `m = (p−1)/2`,
so

  `psign σ_{-1} = (−1)^m`     (`psign_mulPermMod_negone`).

`(−1)^m = 1 ⟺ m` even `⟺ p ≡ 1 (mod 4) ⟺ −1` is a QR (`neg_one_qr_iff`), i.e.

  `psign σ_{-1} = 1 ⟺ (−1/p) = 1`     (`psign_mulPermMod_negone_qr`)

— the sign character agrees with the Legendre symbol at `−1`.  For `p ≡ 3 (mod 4)`, `−1` is a
non-residue with `psign σ_{-1} = −1`: the **nontriviality witness**.  Every non-residue `a` is
then `(QR)·(−1)`, so `psign σ_a = psign σ_{QR} · psign σ_{-1} = 1 · (−1) = −1 = (a/p)`
(`zolotarev_pmod4_three`).

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.ZolotarevConverse

open E213.Lib.Math.Algebra.Linalg213.Permutation (psign inversions ltCount)
open E213.Lib.Math.Algebra.Linalg213.DetN (altSign altSign_add)
open E213.Lib.Math.Algebra.Linalg213.PermSign (altSign_self ltCount_zero_of_all_ge)
open E213.Lib.Math.Algebra.Linalg213.Laplace (ltCount_all)
open E213.Lib.Math.NumberTheory.ModArith.ZolotarevSign
  (mulPermMod mulPermMod_length mulPermMod_getD psign_mulPermMod psign_mulPermMod_qr)
open E213.Tactic.List213 (list_ext_getD getD_ge)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure)
open E213.Tactic.NatHelper (add_mul_mod_self_pure add_sub_of_le add_sub_cancel_right sub_add_cancel)
open E213.Meta.Nat.AddMod213 (div_add_mod zero_mod)
open E213.Meta.Int213 (mul_one mul_assoc)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Lib.Math.NumberTheory.ModArith.EulerFirstSupplement (neg_one_qr_iff even_iff_pmod4)
open E213.Lib.Math.NumberTheory.ModArith.LegendreMultiplicative
  (legendre_mul qr_iff_pow_one pow_m_mod_cases)

/-! ## §0 — pure Nat helpers (propext-free replacements for tainted core lemmas) -/

/-- `p − (j+1) = p − 1 − j` for `j + 1 ≤ p` (propext-free `Nat.sub_sub`). -/
private theorem psub_succ (p j : Nat) (h : j + 1 ≤ p) : p - (j + 1) = p - 1 - j := by
  obtain ⟨s, rfl⟩ : ∃ s, p = (j + 1) + s := ⟨p - (j + 1), (add_sub_of_le h).symm⟩
  rw [Nat.add_comm (j + 1) s, add_sub_cancel_right, ← Nat.add_assoc s j 1,
      add_sub_cancel_right, add_sub_cancel_right]

/-- `k % 2 ∈ {0, 1}` (propext-free `Nat.mod_two_eq_zero_or_one`). -/
private theorem mod_two_cases (k : Nat) : k % 2 = 0 ∨ k % 2 = 1 := by
  rcases Nat.eq_zero_or_pos (k % 2) with h | h
  · exact Or.inl h
  · have h2 : k % 2 < Nat.succ 1 := Nat.mod_lt k (by decide)
    exact Or.inr (Nat.le_antisymm (Nat.le_of_lt_succ h2) h)

/-! ## §1 — the descending list `[n, n−1, …, 1]` and its inversion count -/

/-- `descFrom n = [n, n−1, …, 1]` (strictly descending, length `n`). -/
def descFrom : Nat → List Nat
  | 0     => []
  | n + 1 => (n + 1) :: descFrom n

theorem descFrom_length : ∀ n, (descFrom n).length = n
  | 0     => rfl
  | n + 1 => by show (descFrom n).length + 1 = n + 1; rw [descFrom_length n]

/-- Position readout: `(descFrom n).getD j = n − j` for `j < n`. -/
theorem descFrom_getD : ∀ (n j : Nat), j < n → (descFrom n).getD j 0 = n - j
  | 0,     j,     h => absurd h (Nat.not_lt_zero j)
  | n + 1, 0,     _ => rfl
  | n + 1, j + 1, h => by
      show (descFrom n).getD j 0 = (n + 1) - (j + 1)
      rw [descFrom_getD n j (Nat.lt_of_succ_lt_succ h), Nat.succ_sub_succ]

/-- Every entry of `descFrom n` is `≤ n`. -/
theorem mem_descFrom_le : ∀ {n v : Nat}, v ∈ descFrom n → v ≤ n
  | 0,     v, h => absurd h (List.not_mem_nil v)
  | n + 1, v, h => by
      cases h with
      | head        => exact Nat.le_refl _
      | tail _ htl  => exact Nat.le_succ_of_le (mem_descFrom_le htl)

/-- Triangular number `tri₂ n = (n−1) + (n−2) + ⋯ + 0 = n(n−1)/2` (recursive, division-free). -/
def tri2 : Nat → Nat
  | 0     => 0
  | n + 1 => n + tri2 n

/-- ★ **The descending list has `tri₂ n` inversions** — every pair is out of order, so the head
    contributes its whole tail length and the count telescopes. -/
theorem inversions_descFrom : ∀ n, inversions (descFrom n) = tri2 n
  | 0     => rfl
  | n + 1 => by
      show ltCount (n + 1) (descFrom n) + inversions (descFrom n) = n + tri2 n
      rw [ltCount_all (n + 1) (fun v hv => Nat.lt_succ_of_le (mem_descFrom_le hv)),
          descFrom_length, inversions_descFrom n]

/-! ## §2 — the parity of `tri₂(2m)` is the parity of `m` -/

/-- `tri₂(2m) + m = 2m²` (so `tri₂(2m) = 2m² − m`, the same parity as `m`). -/
theorem tri2_two_m : ∀ m, tri2 (2 * m) + m = 2 * (m * m)
  | 0     => rfl
  | m + 1 => by
      have ih : tri2 (2 * m) + m = 2 * (m * m) := tri2_two_m m
      have e1 : 2 * (m + 1) = (2 * m + 1) + 1 := by ring_nat
      have step : tri2 ((2 * m + 1) + 1) = (2 * m + 1) + tri2 (2 * m + 1) := rfl
      have step2 : tri2 (2 * m + 1) = (2 * m) + tri2 (2 * m) := rfl
      have expand : 2 * ((m + 1) * (m + 1)) = 2 * (m * m) + 4 * m + 2 := by ring_nat
      rw [e1, step, step2, expand, ← ih]
      ring_nat

/-- ★ **`altSign (tri₂(2m)) = altSign m`** — same parity (`tri₂(2m) + m = 2m²` is even). -/
theorem altSign_tri2_two_m (m : Nat) : altSign (tri2 (2 * m)) = altSign m := by
  have key : altSign (tri2 (2 * m)) * altSign m = 1 := by
    rw [← altSign_add, tri2_two_m m,
        show 2 * (m * m) = (m * m) + (m * m) from by ring_nat, altSign_add]
    exact altSign_self (m * m)
  calc altSign (tri2 (2 * m))
      = altSign (tri2 (2 * m)) * (altSign m * altSign m) := by rw [altSign_self m, mul_one]
    _ = (altSign (tri2 (2 * m)) * altSign m) * altSign m := by rw [mul_assoc]
    _ = 1 * altSign m := by rw [key]
    _ = altSign m := by rw [Int.one_mul]

/-! ## §3 — `σ_{-1}` is the reversal list, and `psign σ_{-1} = (−1)^m` -/

/-- `(p−1)·x ≡ p − x (mod p)` for a unit `1 ≤ x < p` (negation `≡ −x`). -/
theorem negmul_mod (p x : Nat) (hx1 : 1 ≤ x) (hxp : x < p) : ((p - 1) * x) % p = p - x := by
  have hxpos : 0 < x := hx1
  have hppos : 0 < p := Nat.lt_trans hxpos hxp
  have e : (p - 1) * x = (p - x) + (x - 1) * p := by
    obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, (Nat.succ_pred_eq_of_pos hx1).symm⟩
    obtain ⟨r, rfl⟩ : ∃ r, p = x' + 1 + r :=
      ⟨p - (x' + 1), (add_sub_of_le (Nat.le_of_lt hxp)).symm⟩
    have a1 : x' + 1 + r - 1 = x' + r := by rw [Nat.add_right_comm x' 1 r, add_sub_cancel_right]
    have a2 : x' + 1 + r - (x' + 1) = r := by rw [Nat.add_comm (x' + 1) r, add_sub_cancel_right]
    have a3 : x' + 1 - 1 = x' := add_sub_cancel_right x' 1
    rw [a1, a2, a3]
    ring_nat
  rw [e, add_mul_mod_self_pure (p - x) p (x - 1), Nat.mod_eq_of_lt (Nat.sub_lt hppos hxpos)]

/-- ★★ **`σ_{-1}` is the reversal** `[0, p−1, p−2, …, 1]`: multiply-by-`(p−1)` negates. -/
theorem mulPermMod_negone_eq (p : Nat) (hp : 1 < p) :
    mulPermMod (p - 1) p = 0 :: descFrom (p - 1) := by
  have hppos : 0 < p := Nat.lt_trans Nat.zero_lt_one hp
  refine list_ext_getD 0 ?_ ?_
  · rw [mulPermMod_length]
    show p = (descFrom (p - 1)).length + 1
    rw [descFrom_length]; exact (Nat.succ_pred_eq_of_pos hppos).symm
  · intro i
    rcases Nat.lt_or_ge i p with hi | hi
    · rw [mulPermMod_getD (p - 1) p i hi]
      rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · subst hi0
        show ((p - 1) * 0) % p = 0
        rw [Nat.mul_zero, zero_mod]
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, (Nat.succ_pred_eq_of_pos hipos).symm⟩
        rw [negmul_mod p (j + 1) (Nat.succ_le_succ (Nat.zero_le j)) hi]
        have hjlt : j < p - 1 := by
          have h := hi
          rw [show p = (p - 1) + 1 from (Nat.succ_pred_eq_of_pos hppos).symm] at h
          exact Nat.lt_of_succ_lt_succ h
        show p - (j + 1) = (descFrom (p - 1)).getD j 0
        rw [descFrom_getD (p - 1) j hjlt]
        exact psub_succ p j (Nat.le_of_lt hi)
    · rw [getD_ge 0 (by rw [mulPermMod_length]; exact hi),
          getD_ge 0 (show (0 :: descFrom (p - 1)).length ≤ i from by
            rw [List.length_cons, descFrom_length, sub_add_cancel (Nat.le_of_lt hp)]; exact hi)]

/-- ★★★ **`psign σ_{-1} = (−1)^m`** (`2m = p − 1`).  The reversal has `tri₂(p−1)` inversions,
    of parity `m`; the leading `0` contributes none. -/
theorem psign_mulPermMod_negone (p m : Nat) (hp : 1 < p) (h2m : 2 * m = p - 1) :
    psign (mulPermMod (p - 1) p) = altSign m := by
  rw [show psign (mulPermMod (p - 1) p) = altSign (inversions (mulPermMod (p - 1) p)) from rfl,
      mulPermMod_negone_eq p hp]
  show altSign (ltCount 0 (descFrom (p - 1)) + inversions (descFrom (p - 1))) = altSign m
  rw [ltCount_zero_of_all_ge 0 (descFrom (p - 1)) (fun v _ => Nat.zero_le v), Nat.zero_add,
      inversions_descFrom (p - 1), ← h2m]
  exact altSign_tri2_two_m m

/-! ## §4 — `altSign` parity readout -/

theorem altSign_add_two (k : Nat) : altSign (k + 2) = altSign k := by
  show -(-(altSign k)) = altSign k; rw [Int.neg_neg]

theorem altSign_two_mul : ∀ j, altSign (2 * j) = 1
  | 0     => rfl
  | j + 1 => by
      rw [show 2 * (j + 1) = 2 * j + 2 from by ring_nat, altSign_add_two]; exact altSign_two_mul j

theorem altSign_two_mul_add_one : ∀ j, altSign (2 * j + 1) = -1
  | 0     => rfl
  | j + 1 => by
      rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 from by ring_nat, altSign_add_two]
      exact altSign_two_mul_add_one j

/-- `altSign k = 1 ⟺ k` even. -/
theorem altSign_eq_one_iff_even (k : Nat) : altSign k = 1 ↔ k % 2 = 0 := by
  have hdm := div_add_mod k 2
  rcases mod_two_cases k with h | h
  · refine ⟨fun _ => h, fun _ => ?_⟩
    have hk2 : k = 2 * (k / 2) := by rw [h] at hdm; exact hdm.symm
    rw [hk2]; exact altSign_two_mul (k / 2)
  · have hk2 : k = 2 * (k / 2) + 1 := by rw [h] at hdm; exact hdm.symm
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · rw [hk2, altSign_two_mul_add_one] at hc; exact absurd hc (by decide)
    · exact absurd (hc.symm.trans h) (by decide)

/-- `altSign k = −1 ⟺ k` odd. -/
theorem altSign_eq_negone_iff_odd (k : Nat) : altSign k = -1 ↔ k % 2 = 1 := by
  have hdm := div_add_mod k 2
  rcases mod_two_cases k with h | h
  · have hk2 : k = 2 * (k / 2) := by rw [h] at hdm; exact hdm.symm
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · rw [hk2, altSign_two_mul] at hc; exact absurd hc (by decide)
    · exact absurd (hc.symm.trans h) (by decide)
  · refine ⟨fun _ => h, fun _ => ?_⟩
    have hk2 : k = 2 * (k / 2) + 1 := by rw [h] at hdm; exact hdm.symm
    rw [hk2]; exact altSign_two_mul_add_one (k / 2)

/-! ## §5 — Zolotarev on the `−1` axis: `psign σ_{-1}` matches `(−1/p)` -/

/-- ★★★★ **The `(−1/p)` corner of Zolotarev's lemma.**  For a prime `p`, `2m = p − 1`:
    `psign σ_{-1} = 1 ⟺ −1` is a quadratic residue mod `p` (`⟺ p ≡ 1 mod 4`).  The sign
    character agrees with the Legendre symbol at `−1`. -/
theorem psign_mulPermMod_negone_qr (p m : Nat) (hp : 1 < p)
    (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) :
    psign (mulPermMod (p - 1) p) = 1 ↔ (∃ x : Nat, 1 ≤ x ∧ x < p ∧ x ^ 2 % p = p - 1) := by
  have h1 : psign (mulPermMod (p - 1) p) = 1 ↔ m % 2 = 0 := by
    rw [psign_mulPermMod_negone p m hp h2m]; exact altSign_eq_one_iff_even m
  exact h1.trans ((even_iff_pmod4 p m hp h2m).trans (neg_one_qr_iff p m hp hpr h2m hm1).symm)

/-! ## §6 — the full converse for every prime `p ≡ 3 (mod 4)` -/

/-- `σ_a` depends only on `a mod p`. -/
theorem mulPermMod_mod (a p : Nat) (hp : 0 < p) :
    mulPermMod a p = mulPermMod (a % p) p := by
  refine list_ext_getD 0 (by rw [mulPermMod_length, mulPermMod_length]) (fun i => ?_)
  rcases Nat.lt_or_ge i p with hi | hi
  · rw [mulPermMod_getD a p i hi, mulPermMod_getD (a % p) p i hi, ← mul_mod_left_pure a i p]
  · rw [getD_ge 0 (by rw [mulPermMod_length]; exact hi),
        getD_ge 0 (by rw [mulPermMod_length]; exact hi)]

/-- The sign of a permutation value-list is `±1`. -/
theorem psign_pm (l : List Nat) : psign l = 1 ∨ psign l = -1 := by
  rcases mod_two_cases (inversions l) with h | h
  · exact Or.inl ((altSign_eq_one_iff_even (inversions l)).mpr h)
  · exact Or.inr ((altSign_eq_negone_iff_odd (inversions l)).mpr h)

/-- For `p ≡ 3 (mod 4)`, `−1` is a non-residue, so `psign σ_{-1} = −1` (`m` is odd). -/
theorem psign_negone_pmod4_three (p m : Nat) (hp : 1 < p) (h2m : 2 * m = p - 1)
    (hp4 : p % 4 = 3) : psign (mulPermMod (p - 1) p) = -1 := by
  rw [psign_mulPermMod_negone p m hp h2m]
  refine (altSign_eq_negone_iff_odd m).mpr ?_
  rcases mod_two_cases m with h | h
  · exact absurd ((even_iff_pmod4 p m hp h2m).mp h)
      (fun hc => absurd (hp4.symm.trans hc) (by decide))
  · exact h

/-- ★★★★★ **Non-residue ⟹ odd permutation** (the converse, `p ≡ 3 mod 4`).  For a non-residue
    unit `a`, `a·(−1)` is a residue (product of two non-residues), so by the character
    homomorphism `psign σ_a · psign σ_{-1} = psign σ_{a·(-1)} = 1`; with `psign σ_{-1} = −1`,
    `psign σ_a = −1`. -/
theorem psign_mulPermMod_nonresidue (p m a : Nat) (hp : 1 < p)
    (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m)
    (ha1 : 1 ≤ a) (halt : a < p) (hp4 : p % 4 = 3)
    (hnqr : ¬ ∃ z, 1 ≤ z ∧ z < p ∧ z ^ 2 % p = a) :
    psign (mulPermMod a p) = -1 := by
  have hppos : 0 < p := Nat.lt_trans Nat.zero_lt_one hp
  have hnpa : ¬ p ∣ a := fun h =>
    absurd (le_of_dvd_pos p a (Nat.lt_of_lt_of_le Nat.zero_lt_one ha1) h) (Nat.not_le.mpr halt)
  have hb1 : 1 ≤ p - 1 := h2m ▸ (Nat.le_trans hm1 (Nat.le_mul_of_pos_left m (by decide)))
  have hblt : p - 1 < p := Nat.sub_lt hppos Nat.zero_lt_one
  have hnpb : ¬ p ∣ (p - 1) := fun h =>
    absurd (le_of_dvd_pos p (p - 1) hb1 h) (Nat.not_le.mpr hblt)
  have hnqr_b : ¬ ∃ z, 1 ≤ z ∧ z < p ∧ z ^ 2 % p = p - 1 := fun hc =>
    absurd ((neg_one_qr_iff p m hp hpr h2m hm1).mp hc)
      (fun he => absurd (hp4.symm.trans he) (by decide))
  have hqab : ∃ z, 1 ≤ z ∧ z < p ∧ z ^ 2 % p = (a * (p - 1)) % p :=
    (legendre_mul p m a (p - 1) hp hpr h2m hm1 ha1 halt hb1 hblt).mpr (iff_of_false hnqr hnqr_b)
  have hps_ab : psign (mulPermMod (a * (p - 1)) p) = 1 := by
    rw [mulPermMod_mod (a * (p - 1)) p hppos]
    exact psign_mulPermMod_qr ((a * (p - 1)) % p) p hp hpr hqab
  have hhom := psign_mulPermMod a (p - 1) p hp hpr hnpa hnpb
  rw [hps_ab, psign_negone_pmod4_three p m hp h2m hp4] at hhom
  rcases psign_pm (mulPermMod a p) with hpa | hpa
  · rw [hpa] at hhom; exact absurd hhom (by decide)
  · exact hpa

/-- ★★★★★ **Zolotarev's lemma for `p ≡ 3 (mod 4)`.**  `psign σ_a = (a/p)` for every unit `a`:
    `psign σ_a = 1 ⟺ a` is a quadratic residue.  Residues map even (`psign_mulPermMod_qr`);
    non-residues map odd (`psign_mulPermMod_nonresidue`, via the `−1` nontriviality witness). -/
theorem zolotarev_pmod4_three (p m a : Nat) (hp : 1 < p)
    (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m)
    (ha1 : 1 ≤ a) (halt : a < p) (hp4 : p % 4 = 3) :
    psign (mulPermMod a p) = 1 ↔ (∃ z, 1 ≤ z ∧ z < p ∧ z ^ 2 % p = a) := by
  refine ⟨fun hps => ?_, fun hqr => psign_mulPermMod_qr a p hp hpr hqr⟩
  rcases pow_m_mod_cases p m a hp hpr h2m ha1 halt with hpow | hpow
  · exact (qr_iff_pow_one p m a hp hpr h2m hm1 ha1 halt).mpr hpow
  · have hpm1 : 2 ≤ p - 1 := by
      have h := Nat.mul_le_mul_left 2 hm1
      rw [Nat.mul_one, h2m] at h; exact h
    have hnqr : ¬ ∃ z, 1 ≤ z ∧ z < p ∧ z ^ 2 % p = a := fun hc => by
      have h1 := (qr_iff_pow_one p m a hp hpr h2m hm1 ha1 halt).mp hc
      rw [hpow] at h1
      exact absurd (h1 ▸ hpm1) (by decide)
    rw [psign_mulPermMod_nonresidue p m a hp hpr h2m hm1 ha1 halt hp4 hnqr] at hps
    exact absurd hps (by decide)

end E213.Lib.Math.NumberTheory.ModArith.ZolotarevConverse
