import E213.Lib.Math.Algebra.Linalg213.Laplace
import E213.Lib.Math.Algebra.Linalg213.ProdCongr
import E213.Meta.Tactic.List213
import E213.Lib.Math.NumberTheory.FourSquareSeed
import E213.Lib.Math.NumberTheory.ModArith.EulerConverse
import E213.Lib.Math.NumberTheory.ModArith.LegendreMultiplicative
import E213.Lib.Math.NumberTheory.ModArith.NonFixedExists
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.Gcd213
import E213.Meta.Tactic.Pow213

/-!
# GaussLemma — Gauss's lemma (in progress)

Layer 2: the half-system `[1..m]` and the fold permutation.

`cntNodup_of_listNodup` bridges `List.Nodup` (Pairwise) to the count-based `Nodup` used by
`lperm_of_nodup_mem_iff`; `mem_of_card_le` is the pigeonhole (a `Nodup` sublist of equal-or-greater
length is a superset); `seg m = [1..m]` with its length / membership / `Nodup`.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.GaussLemma

open E213.Lib.Math.Algebra.Linalg213.Permutation (iota LPerm map_lperm)
open E213.Lib.Math.Algebra.Linalg213.PermClosure
  (cnt Nodup cnt_eq_zero_of_not_mem cnt_pos_mem cnt_pos_of_mem lt_of_mem_iota length_iota map_map')
open E213.Meta.Int213 (mul_one)
open E213.Lib.Math.Algebra.Linalg213.Laplace (lperm_of_nodup_mem_iff mem_iota_of_lt)
open E213.Tactic.List213
  (nodup_map_of_inj nodup_append nodup_length_le_of_subset mem_filter_of
   length_filter_lt_of_mem length_map exists_of_mem_map mem_map_of_mem)
open E213.Tactic.NatHelper
  (add_right_cancel_pure le_sub_of_add_le sub_add_cancel add_sub_cancel_right sub_le_sub_left
   mul_sub sub_sub_self)
open E213.Lib.Math.NumberTheory.FourSquareSeed (nat_prime_dvd_mul)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero add_mod_gen mod_self div_add_mod)
open E213.Meta.Nat.Gcd213 (mod_eq_dvd_sub)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Lib.Math.Algebra.Linalg213.ProdLperm (prodZ prodZ_lperm)
open E213.Lib.Math.Algebra.Linalg213.ProdCongr (prodZ_congr_map prodZ_map_mul prodZ_map_const_mul)
open E213.Lib.Math.NumberTheory.PolyRoot (int_euclid int_dvd_to_nat nat_dvd_to_int dvd_sub')
open E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT
  (dvd_sub_one_of_mod_one mod_one_of_dvd_sub_one one_le_pow')
open E213.Lib.Math.NumberTheory.ModArith.NonFixedExists (natCast_sub_one)
open E213.Lib.Math.NumberTheory.ModArith.EulerConverse (natCast_sub euler_criterion)
open E213.Lib.Math.NumberTheory.ModArith.NonFixedExists (natCast_mul natCast_pow)
open E213.Meta.Int213.PolyIntM (mul_zeroZ)
open E213.Meta.Int213.Order (sub_self_zero)
open E213.Lib.Math.NumberTheory.ModArith.LegendreMultiplicative (qr_iff_pow_one)

/-! ## §1 — bridges and the pigeonhole -/

/-- `List.Nodup` (Pairwise) ⟹ the count-based `Nodup` (`∀ a, cnt a L ≤ 1`). -/
theorem cntNodup_of_listNodup {α : Type} [DecidableEq α] : ∀ {L : List α}, L.Nodup → Nodup L
  | [], _ => fun q => Nat.zero_le _
  | a :: l, h => fun q => by
    cases h with
    | cons hal hl =>
      show (if a = q then 1 else 0) + cnt q l ≤ 1
      by_cases haq : a = q
      · have hanl : a ∉ l := fun ham => (hal a ham) rfl
        have hql : cnt q l = 0 := cnt_eq_zero_of_not_mem (haq ▸ hanl)
        rw [if_pos haq, hql]; exact Nat.le_refl 1
      · rw [if_neg haq, Nat.zero_add]; exact cntNodup_of_listNodup hl q

/-- **Pigeonhole.**  A `Nodup` list `L1 ⊆ L2` with `|L2| ≤ |L1|` is a superset: every `v ∈ L2`
    lies in `L1` (else `L1 ⊆ L2 ∖ {v}` is strictly shorter than `L2 ≤ L1`). -/
theorem mem_of_card_le {α : Type} [DecidableEq α] {L1 L2 : List α} (h1 : L1.Nodup)
    (hsub : ∀ x, x ∈ L1 → x ∈ L2) (hlen : L2.length ≤ L1.length) :
    ∀ v, v ∈ L2 → v ∈ L1 := by
  intro v hv
  cases Nat.eq_zero_or_pos (cnt v L1) with
  | inr hpos => exact cnt_pos_mem hpos
  | inl hzero =>
    exfalso
    have hvL1 : v ∉ L1 := fun hm => Nat.lt_irrefl 0 (hzero ▸ cnt_pos_of_mem hm)
    have hsub' : ∀ x, x ∈ L1 → x ∈ L2.filter (fun a => if a = v then false else true) := by
      intro x hx
      have hxv : x ≠ v := fun e => hvL1 (e ▸ hx)
      exact mem_filter_of (hsub x hx) (if_neg hxv)
    have hle : L1.length ≤ (L2.filter (fun a => if a = v then false else true)).length :=
      nodup_length_le_of_subset h1 hsub'
    have hlt : (L2.filter (fun a => if a = v then false else true)).length < L2.length :=
      length_filter_lt_of_mem hv (if_pos rfl)
    exact Nat.lt_irrefl L1.length (Nat.lt_of_le_of_lt hle (Nat.lt_of_lt_of_le hlt hlen))

/-! ## §2 — the half-system `seg m = [1, 2, …, m]` -/

/-- `[1, 2, …, m]`. -/
def seg (m : Nat) : List Nat := (iota m).map (· + 1)

theorem seg_length (m : Nat) : (seg m).length = m := by rw [seg, length_map, length_iota]

theorem mem_seg {m v : Nat} : v ∈ seg m ↔ 1 ≤ v ∧ v ≤ m := by
  constructor
  · intro h
    obtain ⟨x, hx, hxv⟩ := exists_of_mem_map h
    have hxm : x < m := lt_of_mem_iota hx
    rw [← hxv]
    exact ⟨Nat.succ_le_succ (Nat.zero_le x), Nat.succ_le_of_lt hxm⟩
  · intro ⟨hv1, hvm⟩
    obtain ⟨w, hw⟩ : ∃ w, v = w + 1 := ⟨v - 1, (Nat.succ_pred_eq_of_pos hv1).symm⟩
    have hwm : w < m := by rw [hw] at hvm; exact Nat.lt_of_succ_le hvm
    rw [seg, hw]
    exact mem_map_of_mem (· + 1) (mem_iota_of_lt hwm)

/-- `iota n` is `List.Nodup` (each new tail-element `n` is fresh). -/
theorem listNodup_iota : ∀ n, (iota n).Nodup
  | 0 => List.Pairwise.nil
  | n + 1 => by
    show (iota n ++ [n]).Nodup
    refine nodup_append (listNodup_iota n)
      (List.Pairwise.cons (fun b hb => absurd hb (List.not_mem_nil b)) List.Pairwise.nil) ?_
    intro a ha hm
    have han : a = n := by
      cases hm with
      | head => rfl
      | tail _ h => exact absurd h (List.not_mem_nil a)
    have hlt : a < n := lt_of_mem_iota ha
    rw [han] at hlt
    exact Nat.lt_irrefl n hlt

theorem seg_listNodup (m : Nat) : (seg m).Nodup :=
  nodup_map_of_inj (fun _ _ _ _ h => add_right_cancel_pure h) (listNodup_iota m)

/-! ## §3 — the fold `x ↦ ±(a·x mod p)` into `[1, m]` -/

/-- The least-absolute-residue magnitude of `a·x`: `r` if `r ≤ m`, else `p − r` (`r = a·x mod p`). -/
def fold (a p m x : Nat) : Nat :=
  if (a * x) % p ≤ m then (a * x) % p else p - (a * x) % p

theorem fold_eq (a p m x : Nat) :
    fold a p m x = if (a * x) % p ≤ m then (a * x) % p else p - (a * x) % p := rfl

/-- `p = 2m + 1` from `2m = p − 1` (`1 < p`). -/
private theorem p_eq (p m : Nat) (hp : 1 < p) (h2m : 2 * m = p - 1) : p = 2 * m + 1 := by
  have h := sub_add_cancel (Nat.le_of_lt hp); rw [← h2m] at h; exact h.symm

/-- `m < p` (since `p = 2m+1`). -/
private theorem m_lt_p (p m : Nat) (hp : 1 < p) (h2m : 2 * m = p - 1) : m < p := by
  rw [p_eq p m hp h2m]; exact Nat.lt_succ_of_le (Nat.le_mul_of_pos_left m (by decide))

/-- A unit residue `1 ≤ z < p` is coprime to a prime `p`. -/
private theorem not_dvd_unit (p z : Nat) (hz1 : 1 ≤ z) (hzp : z < p) : ¬ p ∣ z :=
  fun h => absurd (le_of_dvd_pos p z (Nat.lt_of_lt_of_le Nat.zero_lt_one hz1) h) (Nat.not_le.mpr hzp)

/-- `1 ≤ (a·x) % p` for units `a, x` (i.e. `p ∤ a·x`). -/
private theorem res_pos (a p x : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hnpa : ¬ p ∣ a) (hnpx : ¬ p ∣ x) : 1 ≤ (a * x) % p :=
  Nat.pos_of_ne_zero (fun h0 =>
    (nat_prime_dvd_mul p hp hpr a x (dvd_of_mod_eq_zero h0)).elim hnpa hnpx)

/-- ★ **The fold lands in `[1, m]`.** -/
theorem fold_mem (a p m x : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (ha1 : 1 ≤ a) (halt : a < p) (hx1 : 1 ≤ x) (hxm : x ≤ m) :
    1 ≤ fold a p m x ∧ fold a p m x ≤ m := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  have hmp : m < p := m_lt_p p m hp h2m
  have hxp : x < p := Nat.lt_of_le_of_lt hxm hmp
  have hnpa : ¬ p ∣ a := not_dvd_unit p a ha1 halt
  have hnpx : ¬ p ∣ x := not_dvd_unit p x hx1 hxp
  have hr1 : 1 ≤ (a * x) % p := res_pos a p x hp hpr hnpa hnpx
  have hrlt : (a * x) % p < p := Nat.mod_lt _ hppos
  rw [fold_eq]
  rcases Nat.lt_or_ge ((a * x) % p) (m + 1) with hc | hc
  · have hle : (a * x) % p ≤ m := Nat.le_of_lt_succ hc
    rw [if_pos hle]; exact ⟨hr1, hle⟩
  · have hnc : ¬ (a * x) % p ≤ m := fun h => Nat.not_succ_le_self m (Nat.le_trans hc h)
    rw [if_neg hnc]
    have hrgt : m + 1 ≤ (a * x) % p := hc
    have hsub : p - (m + 1) = m := by
      rw [p_eq p m hp h2m, show 2 * m + 1 = m + (m + 1) from by ring_nat, add_sub_cancel_right]
    refine ⟨le_sub_of_add_le (by rw [Nat.add_comm]; exact hrlt), ?_⟩
    calc p - (a * x) % p ≤ p - (m + 1) := sub_le_sub_left p hrgt
      _ = m := hsub

/-! ## §4 — the fold is injective on `[1, m]` -/

/-- `fold` in the low branch (goal-side `if`, so propext-clean). -/
private theorem fold_lo (a p m x : Nat) (h : (a * x) % p ≤ m) : fold a p m x = (a * x) % p := by
  rw [fold_eq, if_pos h]

/-- `fold` in the high branch. -/
private theorem fold_hi (a p m x : Nat) (h : ¬ (a * x) % p ≤ m) :
    fold a p m x = p - (a * x) % p := by rw [fold_eq, if_neg h]

/-- Cancellation: `a·x ≡ a·y (mod p)` with `y ≤ x < p` and `p ∤ a` ⟹ `x = y`. -/
private theorem res_cancel (a p x y : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hnpa : ¬ p ∣ a) (hxp : x < p) (hyx : y ≤ x) (heq : (a * x) % p = (a * y) % p) : x = y := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  have hle : a * y ≤ a * x := Nat.mul_le_mul_left a hyx
  have hdvd : p ∣ (a * x - a * y) := mod_eq_dvd_sub (a * x) (a * y) p hppos hle heq
  rw [(mul_sub a x y).symm] at hdvd
  have hdxy : p ∣ (x - y) :=
    (nat_prime_dvd_mul p hp hpr a (x - y) hdvd).elim (fun h => absurd h hnpa) id
  have hxylt : x - y < p := Nat.lt_of_le_of_lt (Nat.sub_le x y) hxp
  have hxy0 : x - y = 0 := by
    rcases Nat.eq_zero_or_pos (x - y) with h0 | hpos
    · exact h0
    · exact absurd (Nat.lt_of_le_of_lt (le_of_dvd_pos p (x - y) hpos hdxy) hxylt) (Nat.lt_irrefl p)
  exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hxy0) hyx

/-- Impossibility: `a·x mod p + a·y mod p = p` with `0 < x+y < p`, `p ∤ a`. -/
private theorem sum_imposs (a p x y : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hnpa : ¬ p ∣ a) (hxy1 : 1 ≤ x + y) (hxylt : x + y < p)
    (heq : (a * x) % p + (a * y) % p = p) : False := by
  have hmod : (a * x + a * y) % p = 0 := by rw [add_mod_gen (a * x) (a * y) p, heq, mod_self]
  have hdvd : p ∣ (a * x + a * y) := dvd_of_mod_eq_zero hmod
  rw [(Nat.mul_add a x y).symm] at hdvd
  have hdxy : p ∣ (x + y) :=
    (nat_prime_dvd_mul p hp hpr a (x + y) hdvd).elim (fun h => absurd h hnpa) id
  exact absurd (Nat.lt_of_le_of_lt (le_of_dvd_pos p (x + y) hxy1 hdxy) hxylt) (Nat.lt_irrefl p)

/-- ★ **The fold is injective on the half-system.** -/
theorem fold_inj (a p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (ha1 : 1 ≤ a) (halt : a < p) :
    ∀ x, x ∈ seg m → ∀ y, y ∈ seg m → fold a p m x = fold a p m y → x = y := by
  intro x hx y hy hfe
  obtain ⟨hx1, hxm⟩ := mem_seg.mp hx
  obtain ⟨hy1, hym⟩ := mem_seg.mp hy
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  have hmp : m < p := m_lt_p p m hp h2m
  have hxp : x < p := Nat.lt_of_le_of_lt hxm hmp
  have hyp : y < p := Nat.lt_of_le_of_lt hym hmp
  have hnpa : ¬ p ∣ a := not_dvd_unit p a ha1 halt
  have hrxlt : (a * x) % p < p := Nat.mod_lt _ hppos
  have hrylt : (a * y) % p < p := Nat.mod_lt _ hppos
  have hsum1 : 1 ≤ x + y := Nat.le_trans hx1 (Nat.le_add_right x y)
  have hsumlt : x + y < p := by
    have hle2 : x + y ≤ 2 * m := by
      calc x + y ≤ m + m := Nat.add_le_add hxm hym
        _ = 2 * m := (Nat.two_mul m).symm
    rw [p_eq p m hp h2m]; exact Nat.lt_succ_of_le hle2
  rcases Nat.lt_or_ge ((a * x) % p) (m + 1) with hcx | hcx <;>
    rcases Nat.lt_or_ge ((a * y) % p) (m + 1) with hcy | hcy
  · rw [fold_lo a p m x (Nat.le_of_lt_succ hcx), fold_lo a p m y (Nat.le_of_lt_succ hcy)] at hfe
    rcases Nat.lt_or_ge x y with hlt | hge
    · exact (res_cancel a p y x hp hpr hnpa hyp (Nat.le_of_lt hlt) hfe.symm).symm
    · exact res_cancel a p x y hp hpr hnpa hxp hge hfe
  · have hncy : ¬ (a * y) % p ≤ m := fun h => Nat.not_succ_le_self m (Nat.le_trans hcy h)
    rw [fold_lo a p m x (Nat.le_of_lt_succ hcx), fold_hi a p m y hncy] at hfe
    have hsum : (a * x) % p + (a * y) % p = p := by rw [hfe, sub_add_cancel (Nat.le_of_lt hrylt)]
    exact (sum_imposs a p x y hp hpr hnpa hsum1 hsumlt hsum).elim
  · have hncx : ¬ (a * x) % p ≤ m := fun h => Nat.not_succ_le_self m (Nat.le_trans hcx h)
    rw [fold_hi a p m x hncx, fold_lo a p m y (Nat.le_of_lt_succ hcy)] at hfe
    have hsum : (a * x) % p + (a * y) % p = p := by
      rw [← hfe, Nat.add_comm, sub_add_cancel (Nat.le_of_lt hrxlt)]
    exact (sum_imposs a p x y hp hpr hnpa hsum1 hsumlt hsum).elim
  · have hncx : ¬ (a * x) % p ≤ m := fun h => Nat.not_succ_le_self m (Nat.le_trans hcx h)
    have hncy : ¬ (a * y) % p ≤ m := fun h => Nat.not_succ_le_self m (Nat.le_trans hcy h)
    rw [fold_hi a p m x hncx, fold_hi a p m y hncy] at hfe
    have heqr : (a * x) % p = (a * y) % p := by
      have hx' : p - (p - (a * x) % p) = (a * x) % p := sub_sub_self (Nat.le_of_lt hrxlt)
      have hy' : p - (p - (a * y) % p) = (a * y) % p := sub_sub_self (Nat.le_of_lt hrylt)
      rw [← hx', ← hy', hfe]
    rcases Nat.lt_or_ge x y with hlt | hge
    · exact (res_cancel a p y x hp hpr hnpa hyp (Nat.le_of_lt hlt) heqr.symm).symm
    · exact res_cancel a p x y hp hpr hnpa hxp hge heqr

/-! ## §5 — the fold is a permutation of `[1, m]` -/

/-- ★★ **The fold permutes the half-system.**  `[fold a p m x : x ∈ [1..m]]` is an `LPerm` of
    `[1..m]`: it is `Nodup` (injective, `fold_inj`) and lands in `[1..m]` (`fold_mem`), hence by
    cardinality (`mem_of_card_le`) hits every element. -/
theorem fold_perm (a p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (ha1 : 1 ≤ a) (halt : a < p) :
    LPerm ((seg m).map (fold a p m)) (seg m) := by
  have hsub : ∀ q, q ∈ (seg m).map (fold a p m) → q ∈ seg m := by
    intro q hq
    obtain ⟨x, hx, hxq⟩ := exists_of_mem_map hq
    obtain ⟨hx1, hxm⟩ := mem_seg.mp hx
    rw [← hxq]
    exact mem_seg.mpr (fold_mem a p m x hp hpr h2m ha1 halt hx1 hxm)
  have hfnd : ((seg m).map (fold a p m)).Nodup :=
    nodup_map_of_inj (fold_inj a p m hp hpr h2m ha1 halt) (seg_listNodup m)
  have hlenEq : ((seg m).map (fold a p m)).length = (seg m).length := length_map (seg m) (fold a p m)
  have hmem : ∀ q, q ∈ (seg m).map (fold a p m) ↔ q ∈ seg m := fun q =>
    ⟨hsub q, mem_of_card_le hfnd hsub (Nat.le_of_eq hlenEq.symm) q⟩
  exact lperm_of_nodup_mem_iff (cntNodup_of_listNodup hfnd)
    (cntNodup_of_listNodup (seg_listNodup m)) hmem

/-! ## §6 — Layer 3 helpers (casts, prime ∤ product, product of `±1`) -/

/-- `p ∣ (↑n − ↑(n % p))` over `ℤ` (the residue is congruent to `n`). -/
private theorem int_dvd_cast_sub_mod (p n : Nat) :
    (p : Int) ∣ (((n : Nat) : Int) - (((n % p : Nat)) : Int)) := by
  have hle : n % p ≤ n := Nat.mod_le n p
  have hkey : n - n % p = p * (n / p) := by
    have h : p * (n / p) + n % p = n := div_add_mod n p
    have h2 : (p * (n / p) + n % p) - n % p = p * (n / p) := add_sub_cancel_right (p * (n / p)) (n % p)
    rw [h] at h2; exact h2
  rw [← natCast_sub n (n % p) hle, hkey, natCast_mul]
  exact ⟨(n / p : Nat), rfl⟩

/-- A prime `p` does not divide a `prodZ` of units (`int_euclid` induction). -/
private theorem not_dvd_prodZ (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) :
    ∀ (L : List Int), (∀ z, z ∈ L → ¬ (p : Int) ∣ z) → ¬ (p : Int) ∣ prodZ L
  | [], _ => by
    show ¬ (p : Int) ∣ (1 : Int)
    intro h
    have h1 : p ∣ (1 : Int).natAbs := int_dvd_to_nat p 1 h
    rw [Int.natAbs_one] at h1
    exact absurd (le_of_dvd_pos p 1 (by decide) h1) (Nat.not_le.mpr hp)
  | x :: xs, hne => by
    show ¬ (p : Int) ∣ (x * prodZ xs)
    intro h
    have hnx : ¬ (p : Int) ∣ x := hne x (List.Mem.head xs)
    have hnp : ¬ (p : Int) ∣ prodZ xs :=
      not_dvd_prodZ p hp hpr xs (fun z hz => hne z (List.Mem.tail x hz))
    exact hnp (int_euclid p hp hpr x (prodZ xs) h hnx)

/-- A `prodZ` of `±1`s is `±1`. -/
private theorem prodZ_pm : ∀ (L : List Int), (∀ z, z ∈ L → z = 1 ∨ z = -1) →
    prodZ L = 1 ∨ prodZ L = -1
  | [], _ => Or.inl rfl
  | x :: xs, hpm => by
    have hrec := prodZ_pm xs (fun z hz => hpm z (List.Mem.tail x hz))
    show x * prodZ xs = 1 ∨ x * prodZ xs = -1
    rcases hpm x (List.Mem.head xs) with hx | hx <;> rcases hrec with hq | hq <;> rw [hx, hq]
    · exact Or.inl (by ring_intZ)
    · exact Or.inr (by ring_intZ)
    · exact Or.inr (by ring_intZ)
    · exact Or.inl (by ring_intZ)

/-! ## §7 — Gauss's lemma -/

/-- Cast function (for the fold-value product). -/
private def castFn (n : Nat) : Int := (n : Int)

/-- The least-residue sign of `a·x`: `+1` if `(a·x) % p ≤ m`, else `−1`. -/
def sgFn (a p m x : Nat) : Int := if (a * x) % p ≤ m then (1 : Int) else -1

private theorem sgFn_lo (a p m x : Nat) (h : (a * x) % p ≤ m) : sgFn a p m x = 1 := by
  show (if (a * x) % p ≤ m then (1 : Int) else -1) = 1; rw [if_pos h]

private theorem sgFn_hi (a p m x : Nat) (h : ¬ (a * x) % p ≤ m) : sgFn a p m x = -1 := by
  show (if (a * x) % p ≤ m then (1 : Int) else -1) = -1; rw [if_neg h]

/-- ★★★★ **Gauss's lemma (core identity).**  `↑aᵐ ≡ ∏ₓ sign(a·x) (mod p)`, the sign product over
    the half-system `[1..m]`.  Via the residue/signed-fold congruences (`prodZ_congr_map`), the
    factoring `P_ax = ↑aᵐ·M`, `P_sf = P_sg·P_f`, `P_f = M` (`fold_perm`), and cancellation of the
    coprime `M = m!` (`not_dvd_prodZ` + `int_euclid`). -/
theorem gauss_core (a p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (ha1 : 1 ≤ a) (halt : a < p) :
    (p : Int) ∣ (((a ^ m : Nat)) : Int) - prodZ ((seg m).map (sgFn a p m)) := by
  have hmp : m < p := m_lt_p p m hp h2m
  -- congruence  ↑((a·x)%p) ≡ ↑a·↑x
  have hA : (p : Int) ∣ (prodZ ((seg m).map (fun x => (((a * x) % p : Nat) : Int)))
      - prodZ ((seg m).map (fun x => (a : Int) * castFn x))) :=
    prodZ_congr_map p _ _ (seg m) (fun x _ => by
      show (p : Int) ∣ ((((a * x) % p : Nat) : Int) - (a : Int) * castFn x)
      rw [show (a : Int) * castFn x = ((a * x : Nat) : Int) from (natCast_mul a x).symm]
      obtain ⟨c, hc⟩ := int_dvd_cast_sub_mod p (a * x)
      exact ⟨-c, by
        rw [show (((a * x) % p : Nat) : Int) - ((a * x : Nat) : Int)
              = -(((a * x : Nat) : Int) - ((a * x) % p : Nat)) from by ring_intZ, hc]
        ring_intZ⟩)
  -- congruence  ↑((a·x)%p) ≡ sign · ↑(fold)
  have hB : (p : Int) ∣ (prodZ ((seg m).map (fun x => (((a * x) % p : Nat) : Int)))
      - prodZ ((seg m).map (fun x => sgFn a p m x * castFn (fold a p m x)))) :=
    prodZ_congr_map p _ _ (seg m) (fun x _ => by
      show (p : Int) ∣ ((((a * x) % p : Nat) : Int) - sgFn a p m x * castFn (fold a p m x))
      rcases Nat.lt_or_ge ((a * x) % p) (m + 1) with hc | hc
      · have hle : (a * x) % p ≤ m := Nat.le_of_lt_succ hc
        rw [sgFn_lo a p m x hle,
            show fold a p m x = (a * x) % p from fold_lo a p m x hle]
        have hz : (((a * x) % p : Nat) : Int) - 1 * castFn ((a * x) % p) = 0 := by
          rw [show castFn ((a * x) % p) = (((a * x) % p : Nat) : Int) from rfl, Int.one_mul,
              sub_self_zero]
        rw [hz]; exact ⟨0, (mul_zeroZ (p : Int)).symm⟩
      · have hnle : ¬ (a * x) % p ≤ m := fun h => Nat.not_succ_le_self m (Nat.le_trans hc h)
        have hrlt : (a * x) % p < p := Nat.mod_lt _ (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp))
        rw [sgFn_hi a p m x hnle,
            show fold a p m x = p - (a * x) % p from fold_hi a p m x hnle]
        have hpv : (((a * x) % p : Nat) : Int) - (-1) * castFn (p - (a * x) % p) = (p : Int) := by
          rw [show castFn (p - (a * x) % p) = ((p - (a * x) % p : Nat) : Int) from rfl,
              natCast_sub p ((a * x) % p) (Nat.le_of_lt hrlt)]
          ring_intZ
        rw [hpv]; exact ⟨1, (mul_one (p : Int)).symm⟩)
  -- combine + factor + cancel
  have hC : (p : Int) ∣ (prodZ ((seg m).map (fun x => (a : Int) * castFn x))
      - prodZ ((seg m).map (fun x => sgFn a p m x * castFn (fold a p m x)))) := by
    have h := dvd_sub' hB hA
    have he : (prodZ ((seg m).map (fun x => (((a * x) % p : Nat) : Int)))
          - prodZ ((seg m).map (fun x => sgFn a p m x * castFn (fold a p m x))))
        - (prodZ ((seg m).map (fun x => (((a * x) % p : Nat) : Int)))
          - prodZ ((seg m).map (fun x => (a : Int) * castFn x)))
        = prodZ ((seg m).map (fun x => (a : Int) * castFn x))
          - prodZ ((seg m).map (fun x => sgFn a p m x * castFn (fold a p m x))) := by ring_intZ
    rwa [he] at h
  -- P_ax = ↑a^m · M
  have hD : prodZ ((seg m).map (fun x => (a : Int) * castFn x))
      = (a : Int) ^ m * prodZ ((seg m).map castFn) := by
    rw [prodZ_map_const_mul (a : Int) castFn (seg m), seg_length]
  -- P_sf = P_sg · P_f
  have hE : prodZ ((seg m).map (fun x => sgFn a p m x * castFn (fold a p m x)))
      = prodZ ((seg m).map (sgFn a p m)) * prodZ ((seg m).map (fun x => castFn (fold a p m x))) :=
    prodZ_map_mul (sgFn a p m) (fun x => castFn (fold a p m x)) (seg m)
  -- P_f = M
  have hF : prodZ ((seg m).map (fun x => castFn (fold a p m x))) = prodZ ((seg m).map castFn) := by
    rw [show (seg m).map (fun x => castFn (fold a p m x))
          = ((seg m).map (fold a p m)).map castFn from
        (map_map' (fold a p m) castFn (seg m)).symm]
    exact prodZ_lperm (map_lperm castFn (fold_perm a p m hp hpr h2m ha1 halt))
  -- ¬ p ∣ M
  have hnM : ¬ (p : Int) ∣ prodZ ((seg m).map castFn) :=
    not_dvd_prodZ p hp hpr ((seg m).map castFn) (fun z hz => by
      obtain ⟨x, hx, hxz⟩ := exists_of_mem_map hz
      obtain ⟨hx1, hxm⟩ := mem_seg.mp hx
      rw [← hxz, show castFn x = (x : Int) from rfl]
      intro hd
      have hpx : p ∣ x := by have := int_dvd_to_nat p (x : Int) hd; rwa [Int.natAbs_ofNat] at this
      exact not_dvd_unit p x hx1 (Nat.lt_of_le_of_lt hxm hmp) hpx)
  -- assemble:  p ∣ M·(↑a^m − P_sg),  cancel M
  have hfac : prodZ ((seg m).map (fun x => (a : Int) * castFn x))
        - prodZ ((seg m).map (fun x => sgFn a p m x * castFn (fold a p m x)))
      = prodZ ((seg m).map castFn) * ((((a ^ m : Nat)) : Int) - prodZ ((seg m).map (sgFn a p m))) := by
    rw [hD, hE, hF, natCast_pow a m]; ring_intZ
  rw [hfac] at hC
  exact int_euclid p hp hpr (prodZ ((seg m).map castFn))
    ((((a ^ m : Nat)) : Int) - prodZ ((seg m).map (sgFn a p m))) hC hnM

/-- ★★★★★ **Gauss's lemma.**  For a prime `p`, `2m = p − 1`, unit `1 ≤ a < p`:  `a` is a quadratic
    residue mod `p` **iff** the least-residue sign product `∏ₓ sgFn(a·x) = 1` (= `(−1)^μ`, `μ` =
    `#{x ∈ [1,m] : (a·x) mod p > m}`).  Euler's criterion (`QR ⟺ aᵐ ≡ 1`) composed with the core
    identity `aᵐ ≡ ∏signs` (`gauss_core`), the `±1`-valuedness (`prodZ_pm`), and `p ∤ 2`. -/
theorem gauss_qr (a p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) (ha1 : 1 ≤ a) (halt : a < p) :
    (∃ z : Nat, 1 ≤ z ∧ z < p ∧ z ^ 2 % p = a) ↔ prodZ ((seg m).map (sgFn a p m)) = 1 := by
  have hcore := gauss_core a p m hp hpr h2m ha1 halt
  have hpm := prodZ_pm ((seg m).map (sgFn a p m)) (fun z hz => by
    obtain ⟨x, _, hxz⟩ := exists_of_mem_map hz
    rw [← hxz]
    rcases Nat.lt_or_ge ((a * x) % p) (m + 1) with hc | hc
    · exact Or.inl (sgFn_lo a p m x (Nat.le_of_lt_succ hc))
    · exact Or.inr (sgFn_hi a p m x (fun h => Nat.not_succ_le_self m (Nat.le_trans hc h))))
  have hp3 : 3 ≤ p := by
    have h2 : 2 ≤ 2 * m := by have := Nat.mul_le_mul_left 2 hm1; rwa [Nat.mul_one] at this
    rw [p_eq p m hp h2m]; exact Nat.succ_le_succ h2
  have ham1 : 1 ≤ a ^ m := one_le_pow' a ha1 m
  have hbridge : a ^ m % p = 1 ↔ prodZ ((seg m).map (sgFn a p m)) = 1 := by
    constructor
    · intro hpow
      have hd1 : (p : Int) ∣ (((a ^ m : Nat)) : Int) - 1 := by
        have hn : p ∣ (a ^ m - 1) := dvd_sub_one_of_mod_one p (a ^ m) hpow
        have hh := nat_dvd_to_int p (((a ^ m - 1 : Nat)) : Int) (by rw [Int.natAbs_ofNat]; exact hn)
        rwa [natCast_sub_one (a ^ m) ham1] at hh
      have hdps : (p : Int) ∣ (prodZ ((seg m).map (sgFn a p m)) - 1) := by
        have h := dvd_sub' hd1 hcore
        have he : (((a ^ m : Nat)) : Int) - 1 - ((((a ^ m : Nat)) : Int)
              - prodZ ((seg m).map (sgFn a p m)))
            = prodZ ((seg m).map (sgFn a p m)) - 1 := by ring_intZ
        rwa [he] at h
      rcases hpm with h1 | h1
      · exact h1
      · exfalso
        rw [h1] at hdps
        have h2d : p ∣ ((-1 : Int) - 1).natAbs := int_dvd_to_nat p ((-1 : Int) - 1) hdps
        rw [show ((-1 : Int) - 1).natAbs = 2 from by decide] at h2d
        exact absurd (le_of_dvd_pos p 2 (by decide) h2d) (Nat.not_le.mpr hp3)
    · intro hps
      rw [hps] at hcore
      have hn : p ∣ (a ^ m - 1) := by
        have hh := int_dvd_to_nat p ((((a ^ m : Nat)) : Int) - 1) hcore
        rwa [show ((((a ^ m : Nat)) : Int) - 1).natAbs = a ^ m - 1 from by
          rw [← natCast_sub_one (a ^ m) ham1, Int.natAbs_ofNat]] at hh
      exact mod_one_of_dvd_sub_one p (a ^ m) hp ham1 hn
  exact (qr_iff_pow_one p m a hp hpr h2m hm1 ha1 halt).trans hbridge

end E213.Lib.Math.NumberTheory.ModArith.GaussLemma
