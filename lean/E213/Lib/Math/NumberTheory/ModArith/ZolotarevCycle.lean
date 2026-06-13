import E213.Lib.Math.NumberTheory.ModArith.Zolotarev
import E213.Lib.Math.NumberTheory.ModArith.ZolotarevReduction
import E213.Lib.Math.NumberTheory.ModArith.PrimitiveRoot

/-!
# ZolotarevCycle — the odd-cycle witness (brick 7), completing the full Zolotarev identity

A primitive root `g` has `psign (mulPerm g p) = −1`.  This is the single input that
`ZolotarevReduction.zolotarev_iff` needs: with it, `psign (mulPerm a p) = 1 ⟺ a` is a QR for **all**
units `a`.

`mulPerm g` (`v ↦ g·v mod p`) fixes `0` and is a single `(p−1)`-cycle on the units.  It is conjugate
to the **standard rotation** `S = [0, p−1, 1, 2, …, p−2]` (`S(0)=0`, `S(1)=p−1`, `S(i)=i−1` for
`2 ≤ i`) by the discrete-log list `τ(i) = g^(p−1−i) mod p` (`τ(0)=0`):
`composeList (mulPerm g) τ = composeList τ S` (both send `i ↦ g^(p−i)`-shaped values), so
`psign (mulPerm g)·psign τ = psign τ·psign S`, hence `psign (mulPerm g) = psign S` (a `±1` cancels).
`S` has exactly `p−2` inversions (`p−1` against the trailing block, the ascending tail sorted), so
`psign S = (−1)^(p−2) = −1` (`p` odd).

  * `asc` — the ascending block `[lo, lo+1, …, lo+n−1]`, with `inversions = 0`.
  * `S` / `cycS` — the standard rotation; `inversions_cycS = p−2`; ★★ `psign_cycS = −1`.

This file builds the inversion-count payoff (`psign S = −1`); the conjugation and final assembly
are `psign_mulPerm_primitive` / `zolotarev_full`.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.ZolotarevCycle

open E213.Lib.Math.Algebra.Linalg213.Permutation (iota perms psign inversions ltCount)
open E213.Lib.Math.Algebra.Linalg213.PermClosure (lt_of_mem_iota length_iota nodup_iota)
open E213.Lib.Math.Algebra.Linalg213.PermGroup (composeList getD_iota)
open E213.Lib.Math.Algebra.Linalg213.PermSign (psign_mul altSign_self)
open E213.Lib.Math.Algebra.Linalg213.DetN (altSign altSign_add)
open E213.Lib.Math.Algebra.Linalg213.DetMul (funcs nodup_imp_perm mem_tuples)
open E213.Lib.Math.Algebra.Linalg213.DetTranspose (nodup_map_restrict)
open E213.Lib.Math.Algebra.Linalg213.Laplace (mem_iota_of_lt)
open E213.Tactic.List213 (getD_ge getD_map_ib list_ext_getD exists_of_mem_map length_map)
open E213.Lib.Math.Algebra.Linalg213.PermGroup (composeList_getD composeList_length)
open E213.Lib.Math.NumberTheory.ModArith.Zolotarev
  (mulPerm mulPerm_getD mulPerm_mem_perms res_cancel mulPerm_length)
open E213.Lib.Math.NumberTheory.ModArith.MulOrder (ordModP fermat pow_split_eq ord_dvd)
open E213.Lib.Math.NumberTheory.ModArith.OrderPow (not_dvd_pow)
open E213.Lib.Math.NumberTheory.ModArith.PrimitiveRoot (exists_primitive_root)
open E213.Meta.Nat.MulMod213 (mul_mod_right_pure)
open E213.Meta.Nat.AddMod213 (div_add_mod dvd_of_mod_eq_zero)
open E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT (pow_add_pure)
open E213.Lib.Math.NumberTheory.ModArith.LegendreMultiplicative (qr_iff_pow_one)
open E213.Lib.Math.NumberTheory.ModArith.ZolotarevReduction (mul_neg_one_int zolotarev_iff)
open E213.Meta.Int213 (mul_one)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Tactic.NatHelper (add_sub_of_le sub_add_cancel add_sub_cancel_right add_left_cancel_pure)

/-! ## §1 — the ascending block and its inversion count -/

/-- The ascending block `[lo, lo+1, …, lo+n−1]`. -/
def asc (lo : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => lo :: asc (lo + 1) k

theorem asc_length (lo n : Nat) : (asc lo n).length = n := by
  induction n generalizing lo with
  | zero => rfl
  | succ k ih => show (lo :: asc (lo + 1) k).length = k + 1; rw [List.length_cons, ih]

theorem asc_getD (lo n i : Nat) (hi : i < n) : (asc lo n).getD i 0 = lo + i := by
  induction n generalizing lo i with
  | zero => exact absurd hi (Nat.not_lt_zero i)
  | succ k ih =>
    cases i with
    | zero => show (lo :: asc (lo + 1) k).getD 0 0 = lo + 0; rw [Nat.add_zero]; rfl
    | succ j =>
      show (lo :: asc (lo + 1) k).getD (j + 1) 0 = lo + (j + 1)
      rw [show (lo :: asc (lo + 1) k).getD (j + 1) 0 = (asc (lo + 1) k).getD j 0 from rfl,
          ih (lo + 1) j (Nat.lt_of_succ_lt_succ hi)]
      rw [Nat.add_assoc, Nat.add_comm 1 j]

/-- Nothing is `< 0`. -/
theorem ltCount_zero : ∀ L : List Nat, ltCount 0 L = 0
  | [] => rfl
  | y :: ys => by
    show (if y < 0 then 1 else 0) + ltCount 0 ys = 0
    rw [if_neg (Nat.not_lt_zero y), Nat.zero_add, ltCount_zero ys]

/-- If the threshold `c` is `≤ lo`, no element of `asc lo n` is `< c`. -/
theorem ltCount_asc_ge (c : Nat) : ∀ (n lo : Nat), c ≤ lo → ltCount c (asc lo n) = 0
  | 0, _, _ => rfl
  | k + 1, lo, h => by
    show (if lo < c then 1 else 0) + ltCount c (asc (lo + 1) k) = 0
    rw [if_neg (Nat.not_lt.mpr h), Nat.zero_add,
        ltCount_asc_ge c k (lo + 1) (Nat.le_trans h (Nat.le_succ lo))]

/-- If every element of `asc lo n` is `< c` (i.e. `lo + n ≤ c`), all `n` are counted. -/
theorem ltCount_asc_all (c : Nat) : ∀ (n lo : Nat), lo + n ≤ c → ltCount c (asc lo n) = n
  | 0, _, _ => rfl
  | k + 1, lo, h => by
    show (if lo < c then 1 else 0) + ltCount c (asc (lo + 1) k) = k + 1
    have hlo : lo < c := Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.succ_pos k)) h
    rw [if_pos hlo, ltCount_asc_all c k (lo + 1)
        (by rw [Nat.add_assoc, Nat.add_comm 1 k]; exact h)]
    rw [Nat.add_comm]

/-- An ascending block has no inversions. -/
theorem inversions_asc : ∀ (n lo : Nat), inversions (asc lo n) = 0
  | 0, _ => rfl
  | k + 1, lo => by
    show ltCount lo (asc (lo + 1) k) + inversions (asc (lo + 1) k) = 0
    rw [ltCount_asc_ge lo k (lo + 1) (Nat.le_succ lo), inversions_asc k (lo + 1)]

/-! ## §2 — the standard rotation `S = [0, p−1, 1, 2, …, p−2]` -/

/-- The value of the standard rotation at index `i`: `0 ↦ 0`, `1 ↦ p−1`, `i ↦ i−1` (`i ≥ 2`). -/
def sFun (p i : Nat) : Nat := if i = 0 then 0 else if i = 1 then p - 1 else i - 1

/-- The standard rotation as a value list over `iota p`. -/
def cycS (p : Nat) : List Nat := (iota p).map (sFun p)

theorem cycS_length (p : Nat) : (cycS p).length = p := by
  show ((iota p).map (sFun p)).length = p; rw [length_map, length_iota]

theorem cycS_getD (p i : Nat) (hi : i < p) : (cycS p).getD i 0 = sFun p i := by
  show ((iota p).map (sFun p)).getD i 0 = sFun p i
  rw [getD_map_ib (sFun p) 0 0 (iota p) i (by rw [length_iota]; exact hi), getD_iota p i hi]

/-- The explicit form of `S`: `0 :: (p−1) :: asc 1 (p−2)`. -/
theorem cycS_explicit (p : Nat) (hp : 2 ≤ p) :
    cycS p = 0 :: (p - 1) :: asc 1 (p - 2) := by
  obtain ⟨e, rfl⟩ : ∃ e, p = e + 2 := ⟨p - 2, by
    rw [Nat.add_comm (p - 2) 2]; exact (add_sub_of_le hp).symm⟩
  apply list_ext_getD 0
  · rw [cycS_length]
    show e + 2 = (0 :: (e + 2 - 1) :: asc 1 (e + 2 - 2)).length
    rw [List.length_cons, List.length_cons, asc_length, add_sub_cancel_right e 2]
  · intro i
    rcases Nat.lt_or_ge i (e + 2) with hi | hi
    · rw [cycS_getD (e + 2) i hi]
      cases i with
      | zero => rfl
      | succ j =>
        cases j with
        | zero => rfl
        | succ k =>
          show sFun (e + 2) (k + 2) = (asc 1 (e + 2 - 2)).getD k 0
          rw [add_sub_cancel_right e 2]
          have hk : k < e := Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi)
          rw [asc_getD 1 e k hk]
          show k + 1 = 1 + k
          exact Nat.add_comm k 1
    · rw [getD_ge 0 (by rw [cycS_length]; exact hi),
          getD_ge 0 (by
            show (0 :: (e + 2 - 1) :: asc 1 (e + 2 - 2)).length ≤ i
            rw [List.length_cons, List.length_cons, asc_length, add_sub_cancel_right e 2]
            exact hi)]

/-- The inversion count of the standard rotation is `p − 2`. -/
theorem inversions_cycS (p : Nat) (hp : 2 ≤ p) : inversions (cycS p) = p - 2 := by
  obtain ⟨e, rfl⟩ : ∃ e, p = e + 2 := ⟨p - 2, by
    rw [Nat.add_comm (p - 2) 2]; exact (add_sub_of_le hp).symm⟩
  rw [cycS_explicit (e + 2) hp, add_sub_cancel_right e 2]
  show ltCount 0 ((e + 2 - 1) :: asc 1 e) + inversions ((e + 2 - 1) :: asc 1 e) = e
  rw [ltCount_zero, Nat.zero_add]
  show ltCount (e + 2 - 1) (asc 1 e) + inversions (asc 1 e) = e
  rw [inversions_asc e 1, Nat.add_zero]
  exact ltCount_asc_all (e + 2 - 1) e 1 (Nat.le_of_eq (Nat.add_comm 1 e))

/-! ## §3 — the sign of the standard rotation is `−1` (for odd `p`) -/

/-- `altSign (2k + 1) = −1`. -/
theorem altSign_odd (k : Nat) : altSign (2 * k + 1) = -1 := by
  have h2k : altSign (2 * k) = 1 := by
    rw [show 2 * k = k + k from by rw [Nat.two_mul], altSign_add k k, altSign_self k]
  rw [show 2 * k + 1 = (2 * k) + 1 from rfl, altSign_add (2 * k) 1, h2k]
  show (1 : Int) * altSign 1 = -1
  rw [Int.one_mul]; rfl

/-- ★★ **The standard rotation is odd**: `psign (cycS p) = −1` for an odd prime-sized `p`
    (`2m = p − 1`, `m ≥ 1`).  Its `p − 2 = 2(m−1) + 1` inversions are odd. -/
theorem psign_cycS (p m : Nat) (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) (hp : 2 ≤ p) :
    psign (cycS p) = -1 := by
  obtain ⟨e, rfl⟩ : ∃ e, p = e + 2 := ⟨p - 2, by
    rw [Nat.add_comm (p - 2) 2]; exact (add_sub_of_le hp).symm⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, (sub_add_cancel hm1).symm⟩
  show altSign (inversions (cycS (e + 2))) = -1
  rw [inversions_cycS (e + 2) hp, add_sub_cancel_right e 2]
  rw [Nat.mul_succ] at h2m
  -- h2m : 2 * m' + 2 = e + 2 - 1  (defeq Nat.succ (2*m'+1) = Nat.succ e)
  have he : 2 * m' + 1 = e := Nat.succ.inj h2m
  rw [← he]
  exact altSign_odd m'

/-! ## §4 — `cycS` is a permutation -/

theorem sFun_zero (p : Nat) : sFun p 0 = 0 := rfl
theorem sFun_one (p : Nat) : sFun p 1 = p - 1 := rfl
theorem sFun_ss (p k : Nat) : sFun p (k + 2) = k + 1 := rfl

/-- Every value of `sFun p` is `< p` (on `[0, p)`). -/
theorem sFun_lt (p y : Nat) (hp : 1 < p) (hy : y < p) : sFun p y < p := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  rcases y with _ | _ | k
  · rw [sFun_zero]; exact hppos
  · rw [sFun_one]; exact Nat.sub_lt hppos Nat.zero_lt_one
  · rw [sFun_ss]; exact Nat.lt_trans (Nat.lt_succ_self (k + 1)) hy

/-- `sFun p` is injective on `[0, p)`. -/
theorem sFun_inj (p : Nat) (hp : 1 < p) :
    ∀ x, x ∈ iota p → ∀ y, y ∈ iota p → sFun p x = sFun p y → x = y := by
  have hp1 : 1 ≤ p - 1 := Nat.le_sub_one_of_lt hp
  intro x hx y hy heq
  have hxp : x < p := lt_of_mem_iota hx
  have hyp : y < p := lt_of_mem_iota hy
  rcases x with _ | _ | k
  · rcases y with _ | _ | j
    · rfl
    · rw [sFun_zero, sFun_one] at heq; exact absurd heq.symm (Nat.not_eq_zero_of_lt hp1)
    · rw [sFun_zero, sFun_ss] at heq; exact absurd heq.symm (Nat.not_eq_zero_of_lt (Nat.succ_pos j))
  · rcases y with _ | _ | j
    · rw [sFun_one, sFun_zero] at heq; exact absurd heq (Nat.not_eq_zero_of_lt hp1)
    · rfl
    · rw [sFun_one, sFun_ss] at heq
      have hj : j + 1 < p - 1 :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self (j + 1)) (Nat.le_sub_one_of_lt hyp)
      exact absurd heq (Nat.ne_of_gt hj)
  · rcases y with _ | _ | j
    · rw [sFun_ss, sFun_zero] at heq; exact absurd heq (Nat.not_eq_zero_of_lt (Nat.succ_pos k))
    · rw [sFun_ss, sFun_one] at heq
      have hk : k + 1 < p - 1 :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self (k + 1)) (Nat.le_sub_one_of_lt hxp)
      exact absurd heq.symm (Nat.ne_of_gt hk)
    · rw [sFun_ss, sFun_ss] at heq
      have hkj : k = j := Nat.succ.inj heq
      rw [hkj]

/-- ★ **`cycS p ∈ perms p`** — the standard rotation is a permutation of the residues. -/
theorem cycS_mem_perms (p : Nat) (hp : 1 < p) : cycS p ∈ perms p := by
  have hfuncs : cycS p ∈ funcs p := by
    have h := mem_tuples (iota p) (cycS p)
      (fun v hv => by
        obtain ⟨y, hy, hvy⟩ := exists_of_mem_map hv
        rw [← hvy]; exact mem_iota_of_lt (sFun_lt p y hp (lt_of_mem_iota hy)))
    rwa [cycS_length p] at h
  exact nodup_imp_perm p (cycS p) hfuncs (nodup_map_restrict (sFun_inj p hp) (nodup_iota p))

/-! ## §5 — the discrete-log conjugator `τ(i) = g^(p−1−i) mod p` (`τ(0)=0`) -/

/-- The discrete-log conjugator value: `0 ↦ 0`, `i ↦ g^(p−1−i) mod p`. -/
def tauFun (g p i : Nat) : Nat := if i = 0 then 0 else g ^ (p - 1 - i) % p

def tau (g p : Nat) : List Nat := (iota p).map (tauFun g p)

theorem tau_length (g p : Nat) : (tau g p).length = p := by
  show ((iota p).map (tauFun g p)).length = p; rw [length_map, length_iota]

theorem tau_getD (g p i : Nat) (hi : i < p) : (tau g p).getD i 0 = tauFun g p i := by
  show ((iota p).map (tauFun g p)).getD i 0 = tauFun g p i
  rw [getD_map_ib (tauFun g p) 0 0 (iota p) i (by rw [length_iota]; exact hi), getD_iota p i hi]

/-- `g ∤ p` (`g` a unit). -/
theorem not_dvd_g (g p : Nat) (hg0 : 0 < g) (hglt : g < p) : ¬ p ∣ g :=
  fun h => absurd (le_of_dvd_pos p g hg0 h) (Nat.not_le.mpr hglt)

/-- `g·(g^E mod p) mod p = g^(E+1) mod p`. -/
theorem g_mul_pow (g p E : Nat) : g * (g ^ E % p) % p = g ^ (E + 1) % p := by
  rw [← mul_mod_right_pure g (g ^ E) p, show g * g ^ E = g ^ (E + 1) from by
    rw [Nat.pow_succ]; exact Nat.mul_comm g (g ^ E)]

theorem tauFun_lt (g p i : Nat) (hp : 1 < p) : tauFun g p i < p := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  show (if i = 0 then 0 else g ^ (p - 1 - i) % p) < p
  by_cases hi : i = 0
  · rw [if_pos hi]; exact hppos
  · rw [if_neg hi]; exact Nat.mod_lt _ hppos

/-- A nonzero index gives a unit value: `1 ≤ tauFun g p i`. -/
theorem tauFun_pos (g p i : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hg0 : 0 < g) (hglt : g < p) (hi1 : 1 ≤ i) : 1 ≤ tauFun g p i := by
  have hi : ¬ i = 0 := fun h => absurd (h ▸ hi1) (by decide)
  show 1 ≤ (if i = 0 then 0 else g ^ (p - 1 - i) % p)
  rw [if_neg hi]
  rcases Nat.eq_zero_or_pos (g ^ (p - 1 - i) % p) with h0 | hpos
  · exact absurd (dvd_of_mod_eq_zero h0) (not_dvd_pow g p (p - 1 - i) hp hpr (not_dvd_g g p hg0 hglt))
  · exact hpos

/-- **Periodicity**: `g^i ≡ g^(i mod ord) (mod p)`. -/
theorem pow_period (g p i : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hg0 : 0 < g) (hglt : g < p) :
    g ^ i % p = g ^ (i % ordModP g p) % p := by
  have hdm := div_add_mod i (ordModP g p)
  have h := pow_split_eq g p hp hpr hg0 hglt (i / ordModP g p) (i % ordModP g p)
  rw [hdm] at h; exact h

/-- Discrete-log injectivity (ordered): `a ≤ b < ord`, `g^a ≡ g^b` ⟹ `a = b`. -/
theorem pow_inj_le (g p a b : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hg0 : 0 < g) (hglt : g < p) (hord : ordModP g p = p - 1)
    (hab : a ≤ b) (hb : b < p - 1) (heq : g ^ a % p = g ^ b % p) : a = b := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  have hba : a + (b - a) = b := add_sub_of_le hab
  have hpow : g ^ b = g ^ a * g ^ (b - a) := by rw [← pow_add_pure g a (b - a), hba]
  have h2 : (g ^ a * g ^ (b - a)) % p = g ^ a % p := by rw [← hpow]; exact heq.symm
  have hnpa : ¬ p ∣ g ^ a := not_dvd_pow g p a hp hpr (not_dvd_g g p hg0 hglt)
  have heq3 : (g ^ a * (g ^ (b - a) % p)) % p = (g ^ a * 1) % p := by
    rw [← mul_mod_right_pure (g ^ a) (g ^ (b - a)) p, h2, Nat.mul_one]
  have hX1 : 1 ≤ g ^ (b - a) % p := by
    rcases Nat.eq_zero_or_pos (g ^ (b - a) % p) with h0 | hpos
    · exact absurd (dvd_of_mod_eq_zero h0)
        (not_dvd_pow g p (b - a) hp hpr (not_dvd_g g p hg0 hglt))
    · exact hpos
  have hres : g ^ (b - a) % p = 1 :=
    res_cancel (g ^ a) p (g ^ (b - a) % p) 1 hp hpr hnpa (Nat.mod_lt _ hppos) hX1 heq3
  have hdvd : ordModP g p ∣ (b - a) := ord_dvd g p hp hpr hg0 hglt (b - a) hres
  rw [hord] at hdvd
  have hbalt : b - a < p - 1 := Nat.lt_of_le_of_lt (Nat.sub_le b a) hb
  rcases Nat.eq_zero_or_pos (b - a) with h0 | hpos
  · exact Nat.le_antisymm hab (Nat.le_of_sub_eq_zero h0)
  · exact absurd (le_of_dvd_pos (p - 1) (b - a) hpos hdvd) (Nat.not_le.mpr hbalt)

/-- Discrete-log injectivity: `a, b < ord`, `g^a ≡ g^b` ⟹ `a = b`. -/
theorem pow_inj_mod (g p a b : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hg0 : 0 < g) (hglt : g < p) (hord : ordModP g p = p - 1)
    (ha : a < p - 1) (hb : b < p - 1) (heq : g ^ a % p = g ^ b % p) : a = b := by
  rcases Nat.le_total a b with hab | hba
  · exact pow_inj_le g p a b hp hpr hg0 hglt hord hab hb heq
  · exact (pow_inj_le g p b a hp hpr hg0 hglt hord hba ha heq.symm).symm

/-! ## §6 — `τ` is a permutation -/

theorem tauFun_zero (g p : Nat) : tauFun g p 0 = 0 := rfl

theorem tauFun_succ (g p k : Nat) : tauFun g p (k + 1) = g ^ (p - 1 - (k + 1)) % p :=
  if_neg (Nat.not_eq_zero_of_lt (Nat.succ_pos k))

/-- Subtraction is injective below the cap: `x, y ≤ n`, `n − x = n − y` ⟹ `x = y`. -/
theorem sub_inj (n x y : Nat) (hx : x ≤ n) (hy : y ≤ n) (h : n - x = n - y) : x = y := by
  have hxx : (n - x) + x = n := sub_add_cancel hx
  have hyy : (n - y) + y = n := sub_add_cancel hy
  rw [h] at hxx
  exact add_left_cancel_pure (hxx.trans hyy.symm)

/-- `tauFun g p` is injective on `[0, p)`. -/
theorem tau_inj (g p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hg0 : 0 < g) (hglt : g < p) (hord : ordModP g p = p - 1) :
    ∀ x, x ∈ iota p → ∀ y, y ∈ iota p → tauFun g p x = tauFun g p y → x = y := by
  have hp1pos : 0 < p - 1 := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_sub_one_of_lt hp)
  intro x hx y hy heq
  have hxp : x < p := lt_of_mem_iota hx
  have hyp : y < p := lt_of_mem_iota hy
  rcases x with _ | k
  · rcases y with _ | j
    · rfl
    · rw [tauFun_zero] at heq
      exact absurd heq.symm
        (Nat.not_eq_zero_of_lt (tauFun_pos g p (j + 1) hp hpr hg0 hglt (Nat.succ_pos j)))
  · rcases y with _ | j
    · rw [tauFun_zero] at heq
      exact absurd heq
        (Nat.not_eq_zero_of_lt (tauFun_pos g p (k + 1) hp hpr hg0 hglt (Nat.succ_pos k)))
    · rw [tauFun_succ, tauFun_succ] at heq
      have hke : p - 1 - (k + 1) < p - 1 := Nat.sub_lt hp1pos (Nat.succ_pos k)
      have hje : p - 1 - (j + 1) < p - 1 := Nat.sub_lt hp1pos (Nat.succ_pos j)
      have hexp : p - 1 - (k + 1) = p - 1 - (j + 1) :=
        pow_inj_mod g p (p - 1 - (k + 1)) (p - 1 - (j + 1)) hp hpr hg0 hglt hord hke hje heq
      exact sub_inj (p - 1) (k + 1) (j + 1)
        (Nat.le_sub_one_of_lt hxp) (Nat.le_sub_one_of_lt hyp) hexp

/-- ★ **`τ g p ∈ perms p`** — the discrete-log list is a permutation of the residues. -/
theorem tau_mem_perms (g p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hg0 : 0 < g) (hglt : g < p) (hord : ordModP g p = p - 1) : tau g p ∈ perms p := by
  have hfuncs : tau g p ∈ funcs p := by
    have h := mem_tuples (iota p) (tau g p)
      (fun v hv => by
        obtain ⟨y, _, hvy⟩ := exists_of_mem_map hv
        rw [← hvy]; exact mem_iota_of_lt (tauFun_lt g p y hp))
    rwa [tau_length g p] at h
  exact nodup_imp_perm p (tau g p) hfuncs
    (nodup_map_restrict (tau_inj g p hp hpr hg0 hglt hord) (nodup_iota p))

/-! ## §7 — the conjugation `composeList (mulPerm g) τ = composeList τ (cycS)` -/

theorem tauFun_of_ne (g p i : Nat) (h : ¬ i = 0) : tauFun g p i = g ^ (p - 1 - i) % p := if_neg h

theorem tauFun_one (g p : Nat) : tauFun g p 1 = g ^ (p - 1 - 1) % p := rfl

/-- The exponent step: `(m − (k+2)) + 1 = m − (k+1)` (when `k+2 ≤ m`). -/
theorem exp_step (m k : Nat) (h : k + 2 ≤ m) : (m - (k + 2)) + 1 = m - (k + 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, m = (k + 2) + t := ⟨m - (k + 2), (add_sub_of_le h).symm⟩
  have l : (k + 2) + t - (k + 2) = t := by
    rw [Nat.add_comm (k + 2) t]; exact add_sub_cancel_right t (k + 2)
  have r : (k + 2) + t - (k + 1) = t + 1 := by
    rw [show (k + 2) + t = (t + 1) + (k + 1) from by ring_nat]
    exact add_sub_cancel_right (t + 1) (k + 1)
  rw [l, r]

/-- **The conjugation, pointwise**: `g·τ(i) ≡ τ(S(i)) (mod p)` for `i < p`. -/
theorem conj_pointwise (g p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hg0 : 0 < g) (hglt : g < p) (i : Nat) (hi : i < p) :
    g * tauFun g p i % p = tauFun g p (sFun p i) := by
  have hp2 : 2 ≤ p := hp
  rcases i with _ | _ | k
  · -- i = 0
    rw [tauFun_zero, Nat.mul_zero, sFun_zero, tauFun_zero]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp))
  · -- i = 1
    have hne : ¬ (p - 1) = 0 := Nat.not_eq_zero_of_lt (Nat.le_sub_one_of_lt hp)
    have eqA : (p - 1 - 1) + 1 = p - 1 := Nat.succ_pred_eq_of_pos (Nat.le_sub_one_of_lt hp)
    have hLHS : g * tauFun g p 1 % p = 1 := by
      rw [tauFun_one, g_mul_pow, eqA]
      exact fermat g p hp hpr hg0 hglt
    have hRHS : tauFun g p (sFun p 1) = 1 := by
      rw [sFun_one, tauFun_of_ne g p (p - 1) hne, Nat.sub_self, Nat.pow_zero]
      exact Nat.mod_eq_of_lt hp
    rw [hLHS, hRHS]
  · -- i = k + 2
    have hk2 : k + 2 ≤ p - 1 := Nat.le_sub_one_of_lt hi
    have hne1 : ¬ (k + 2 : Nat) = 0 := Nat.not_eq_zero_of_lt (Nat.succ_pos (k + 1))
    have hne2 : ¬ (k + 1 : Nat) = 0 := Nat.not_eq_zero_of_lt (Nat.succ_pos k)
    rw [tauFun_of_ne g p (k + 2) hne1, g_mul_pow, exp_step (p - 1) k hk2,
        sFun_ss, tauFun_of_ne g p (k + 1) hne2]

/-- **The conjugation identity**: `composeList (mulPerm g) τ = composeList τ (cycS)`. -/
theorem conj_eq (g p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hg0 : 0 < g) (hglt : g < p) (hord : ordModP g p = p - 1) :
    composeList (mulPerm g p) (tau g p) = composeList (tau g p) (cycS p) := by
  apply list_ext_getD 0
  · rw [composeList_length, composeList_length, tau_length, cycS_length]
  · intro i
    rcases Nat.lt_or_ge i p with hi | hi
    · rw [composeList_getD (mulPerm g p) (tau g p) i (by rw [tau_length]; exact hi),
          composeList_getD (tau g p) (cycS p) i (by rw [cycS_length]; exact hi),
          tau_getD g p i hi, cycS_getD p i hi,
          mulPerm_getD g p (tauFun g p i) (tauFun_lt g p i hp),
          tau_getD g p (sFun p i) (sFun_lt p i hp hi)]
      exact conj_pointwise g p hp hpr hg0 hglt i hi
    · rw [getD_ge 0 (by rw [composeList_length, tau_length]; exact hi),
          getD_ge 0 (by rw [composeList_length, cycS_length]; exact hi)]

/-! ## §8 — assembly: a primitive root's permutation is odd, and full Zolotarev -/

/-- `altSign n = ±1`. -/
theorem altSign_pm : ∀ n, altSign n = 1 ∨ altSign n = -1
  | 0 => Or.inl rfl
  | n + 1 => by
    show -(altSign n) = 1 ∨ -(altSign n) = -1
    rcases altSign_pm n with h | h
    · right; rw [h]
    · left; rw [h]; exact Int.neg_neg 1

/-- A permutation's sign is `±1`. -/
theorem psign_pm (l : List Nat) : psign l = 1 ∨ psign l = -1 := altSign_pm (inversions l)

/-- ★★★ **A primitive root's multiplication-permutation is odd**: `psign (mulPerm g p) = −1`.
    `mulPerm g` is conjugate to the standard rotation `cycS` (`conj_eq`), and `psign` is a class
    function (`psign_mul`, with the conjugator's sign squaring to `1`), so
    `psign (mulPerm g) = psign (cycS) = −1`. -/
theorem psign_mulPerm_primitive (g p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hg0 : 0 < g) (hglt : g < p) (hord : ordModP g p = p - 1)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) : psign (mulPerm g p) = -1 := by
  have hp2 : 2 ≤ p := hp
  have hmemG := mulPerm_mem_perms g p hp hpr (not_dvd_g g p hg0 hglt)
  have hmemT := tau_mem_perms g p hp hpr hg0 hglt hord
  have hmemC := cycS_mem_perms p hp
  have hpsi := congrArg psign (conj_eq g p hp hpr hg0 hglt hord)
  rw [psign_mul p (mulPerm g p) (tau g p) hmemG hmemT,
      psign_mul p (tau g p) (cycS p) hmemT hmemC,
      psign_cycS p m h2m hm1 hp2, mul_neg_one_int (psign (tau g p))] at hpsi
  -- hpsi : psign (mulPerm g p) * psign (tau g p) = -(psign (tau g p))
  rcases psign_pm (tau g p) with hT | hT
  · rw [hT, mul_one] at hpsi; exact hpsi
  · rw [hT, mul_neg_one_int, Int.neg_neg] at hpsi
    have hneg := congrArg Neg.neg hpsi
    rwa [Int.neg_neg] at hneg

/-- A primitive root is a quadratic **non**-residue: its order `p−1 = 2m` does not divide `m`. -/
theorem primitive_not_qr (g p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hg1 : 1 ≤ g) (hglt : g < p) (hord : ordModP g p = p - 1)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) :
    ¬ ∃ x, 1 ≤ x ∧ x < p ∧ x ^ 2 % p = g := by
  intro hqr
  have hpow : g ^ m % p = 1 := (qr_iff_pow_one p m g hp hpr h2m hm1 hg1 hglt).mp hqr
  have hdvd : ordModP g p ∣ m := ord_dvd g p hp hpr hg1 hglt m hpow
  rw [hord, ← h2m] at hdvd
  have hle : 2 * m ≤ m := le_of_dvd_pos (2 * m) m hm1 hdvd
  have hmm : m + m ≤ m := by rw [← Nat.two_mul]; exact hle
  exact absurd (Nat.le_trans (Nat.add_le_add_left hm1 m) hmm) (Nat.not_succ_le_self m)

/-- ★★★★★ **Full Zolotarev / Legendre–sign identity.**  For an odd prime `p` (`2m = p − 1`,
    `m ≥ 1`) and a unit `1 ≤ a < p`:  `psign (mulPerm a p) = 1 ⟺ a` is a quadratic residue mod `p`.
    The single odd witness is a primitive root `g` (`exists_primitive_root`): it is a non-residue
    (`primitive_not_qr`) whose permutation is odd (`psign_mulPerm_primitive`), so
    `ZolotarevReduction.zolotarev_iff` upgrades to all units. -/
theorem zolotarev_full (p m a : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) (ha1 : 1 ≤ a) (halt : a < p) :
    psign (mulPerm a p) = 1 ↔ ∃ x, 1 ≤ x ∧ x < p ∧ x ^ 2 % p = a := by
  obtain ⟨g, hg1, hgp, hord⟩ := exists_primitive_root p hp hpr
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  have hglt : g < p := Nat.lt_of_le_of_lt hgp (Nat.sub_lt hppos Nat.zero_lt_one)
  have hsign : psign (mulPerm g p) = -1 :=
    psign_mulPerm_primitive g p m hp hpr hg1 hglt hord h2m hm1
  have hnqr : ¬ ∃ x, 1 ≤ x ∧ x < p ∧ x ^ 2 % p = g :=
    primitive_not_qr g p m hp hpr hg1 hglt hord h2m hm1
  exact zolotarev_iff p m a g hp hpr h2m hm1 ha1 halt hg1 hglt hnqr hsign

end E213.Lib.Math.NumberTheory.ModArith.ZolotarevCycle
