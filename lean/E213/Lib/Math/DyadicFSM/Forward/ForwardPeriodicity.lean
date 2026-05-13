import E213.Lib.Math.DyadicFSM.Tier.TierBridge
import E213.Lib.Math.Pigeonhole
import E213.Meta.Nat.EncodePair213

import E213.Lib.Math.DyadicFSM.Signature.Signature
/-!
# Forward direction (general): periodic bits ⇒ ev-periodic signature

Joint state (sig n, n mod p) ∈ Fin (5p); pigeonhole forces a
collision among 5p+1 steps.  Decidable.byContradiction (no
Classical) on Bool-valued `collisionTest` keeps everything at
≤ {propext, Quot.sound}.
-/

namespace E213.Lib.Math.DyadicFSM.Forward.ForwardPeriodicity

open E213.Lib.Math.Pigeonhole
open E213.Lib.Math.DyadicFSM.Signature.Signature (signature nextVertex)

/-- Bool-valued collision test (decidable, no Classical). -/
def collisionTest {N k : Nat} (g : Fin k → Fin N) (i j : Nat) : Bool :=
  if h_i : i < k then
    if h_j : j < k then (g ⟨i, h_i⟩).val == (g ⟨j, h_j⟩).val
    else false
  else false

/-- Constructive inner search: for fixed i, find j > i with
    collisionTest = true.  Σ-witness or proof of "no collision". -/
private def searchInner {N k : Nat} (g : Fin k → Fin N) (i : Nat) :
    (j : Nat) → PSum (Σ' j', i < j' ∧ j' < j ∧ collisionTest g i j' = true)
                     (∀ j', i < j' → j' < j → collisionTest g i j' = false)
  | 0 => PSum.inr (fun _ _ hj => absurd hj (Nat.not_lt_zero _))
  | j+1 =>
    match searchInner g i j with
    | PSum.inl ⟨j', hij, hjk, hcoll⟩ =>
      PSum.inl ⟨j', hij, Nat.lt_succ_of_lt hjk, hcoll⟩
    | PSum.inr hno =>
      if hgt : i < j then
        match h : collisionTest g i j with
        | true => PSum.inl ⟨j, hgt, Nat.lt_succ_self _, h⟩
        | false =>
          PSum.inr (fun j' hij hj' => by
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj') with hlt | heq
            · exact hno j' hij hlt
            · exact heq ▸ h)
      else
        PSum.inr (fun j' hij hj' => by
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj') with hlt | heq
          · exact hno j' hij hlt
          · exact absurd (heq ▸ hij) hgt)

/-- Constructive outer search: search across i for any inner collision. -/
private def searchOuter {N k : Nat} (g : Fin k → Fin N) :
    (i : Nat) → PSum (Σ' i' j, i' < i ∧ j < k ∧ i' < j ∧ collisionTest g i' j = true)
                     (∀ i', i' < i → ∀ j, i' < j → j < k → collisionTest g i' j = false)
  | 0 => PSum.inr (fun _ hi => absurd hi (Nat.not_lt_zero _))
  | i+1 =>
    match searchOuter g i with
    | PSum.inl ⟨i', j, hi'i, hjk, hij, hcoll⟩ =>
      PSum.inl ⟨i', j, Nat.lt_succ_of_lt hi'i, hjk, hij, hcoll⟩
    | PSum.inr hno =>
      match searchInner g i k with
      | PSum.inl ⟨j, hij, hjk, hcoll⟩ =>
        PSum.inl ⟨i, j, Nat.lt_succ_self _, hjk, hij, hcoll⟩
      | PSum.inr hno_inner =>
        PSum.inr (fun i' hi' j hij hjk => by
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi') with hlt | heq
          · exact hno i' hlt j hij hjk
          · exact heq ▸ hno_inner j (heq ▸ hij) hjk)

/-- Helper: g x = g y (Fin) → collisionTest g x.val y.val = true. -/
private theorem g_eq_imp_collTest {N k : Nat} (g : Fin k → Fin N)
    (x y : Fin k) (heq : g x = g y) :
    collisionTest g x.val y.val = true := by
  show (if h_i : x.val < k then
          if h_j : y.val < k then (g ⟨x.val, h_i⟩).val == (g ⟨y.val, h_j⟩).val
          else false
        else false) = true
  rw [dif_pos x.isLt, dif_pos y.isLt]
  have hx : (⟨x.val, x.isLt⟩ : Fin k) = x := Fin.ext rfl
  have hy : (⟨y.val, y.isLt⟩ : Fin k) = y := Fin.ext rfl
  rw [hx, hy, heq]
  exact decide_eq_true (Eq.refl _)

/-- Constructive pigeonhole — STRICT ∅-AXIOM via Σ-witness search.
    Replaces previous `Decidable.byContradiction` proof which leaked
    `propext + Quot.sound` from instance synthesis. -/
theorem pigeonhole_collision {N k : Nat} (h : N < k) (g : Fin k → Fin N) :
    ∃ i, i < k ∧ ∃ j, j < k ∧ i < j ∧ collisionTest g i j = true := by
  match searchOuter g k with
  | PSum.inl ⟨i, j, hik, hjk, hij, hcoll⟩ =>
    exact ⟨i, hik, j, hjk, hij, hcoll⟩
  | PSum.inr hno =>
    exfalso
    apply no_inj_lt h g
    intro x y hxy heq
    rcases Nat.lt_or_ge x.val y.val with hlt | hge
    · have hctf : collisionTest g x.val y.val = false :=
        hno x.val x.isLt y.val hlt y.isLt
      have hctt : collisionTest g x.val y.val = true :=
        g_eq_imp_collTest g x y heq
      exact Bool.noConfusion (hctt.symm.trans hctf)
    · rcases Nat.lt_or_eq_of_le hge with hgt | heq_idx
      · have hctf : collisionTest g y.val x.val = false :=
          hno y.val y.isLt x.val hgt x.isLt
        have hctt : collisionTest g y.val x.val = true :=
          g_eq_imp_collTest g y x heq.symm
        exact Bool.noConfusion (hctt.symm.trans hctf)
      · exact hxy (Fin.ext heq_idx.symm)

/-- bs periodic at multiple of p: bs (n + k*p) = bs n. -/
theorem bs_periodic_multiple (bs : Nat → Bool) (p : Nat)
    (hbs : ∀ n, bs (n + p) = bs n) :
    ∀ k n, bs (n + k * p) = bs n := by
  intro k
  induction k with
  | zero => intro n; show bs (n + 0 * p) = bs n; rw [Nat.zero_mul, Nat.add_zero]
  | succ k' ih =>
    intro n
    rw [Nat.succ_mul, ← Nat.add_assoc, hbs, ih]

/-- Joint state map: (signature, position in period) → Fin (5p). -/
def jointState (bs : Nat → Bool) (p : Nat) (hp : 0 < p)
    (k : Fin (5 * p + 1)) : Fin (5 * p) :=
  ⟨(signature bs k.val).val * p + k.val % p, by
    have h1 : (signature bs k.val).val < 5 := (signature bs k.val).isLt
    have h2 : k.val % p < p := Nat.mod_lt _ hp
    have h1' : (signature bs k.val).val ≤ 4 := Nat.lt_succ_iff.mp h1
    have h3 : (signature bs k.val).val * p ≤ 4 * p :=
      Nat.mul_le_mul_right p h1'
    calc (signature bs k.val).val * p + k.val % p
        < 4 * p + p := Nat.add_lt_add_of_le_of_lt h3 h2
      _ = (4 + 1) * p := (Nat.succ_mul 4 p).symm
      _ = 5 * p := rfl⟩

/-- Helper: collisionTest g i j = true ⇒ (g ⟨i,_⟩).val = (g ⟨j,_⟩).val. -/
theorem collTest_imp_val_eq {N k : Nat} (g : Fin k → Fin N)
    (i j : Nat) (hi : i < k) (hj : j < k)
    (h : collisionTest g i j = true) :
    (g ⟨i, hi⟩).val = (g ⟨j, hj⟩).val := by
  show (g ⟨i, hi⟩).val = (g ⟨j, hj⟩).val
  have hu : (if h_i : i < k then
              if h_j : j < k then (g ⟨i, h_i⟩).val == (g ⟨j, h_j⟩).val
              else false
            else false) = true := h
  rw [dif_pos hi, dif_pos hj] at hu
  exact of_decide_eq_true hu

/-- Subtraction-cancellation for the pigeon collision: if both sides are
    `s · p + r` with `r < p`, equality forces both `s` and `r` to match.
    This avoids `omega` (Quot.sound) and `Nat.add_mul_div_left` (propext). -/
theorem encode_inj {p : Nat} (hp : 0 < p)
    (a b r1 r2 : Nat) (h1 : r1 < p) (h2 : r2 < p)
    (heq : a * p + r1 = b * p + r2) : a = b ∧ r1 = r2 := by
  have ha : (a * p + r1) / p = a := E213.Meta.Nat.EncodePair213.encode_div hp a r1 h1
  have hb : (b * p + r2) / p = b := E213.Meta.Nat.EncodePair213.encode_div hp b r2 h2
  have hra : (a * p + r1) % p = r1 := E213.Meta.Nat.EncodePair213.encode_mod hp a r1 h1
  have hrb : (b * p + r2) % p = r2 := E213.Meta.Nat.EncodePair213.encode_mod hp b r2 h2
  exact ⟨ha.symm.trans (heq ▸ hb), hra.symm.trans (heq ▸ hrb)⟩

/-- ★ Joint state collision: ∃ i < j ≤ 5p with sig & mod equal.
    STRICT ∅-AXIOM via pigeonhole_collision + encode_inj. -/
theorem joint_state_collision (bs : Nat → Bool) (p : Nat) (hp : 0 < p) :
    ∃ i, i ≤ 5 * p ∧ ∃ j, j ≤ 5 * p ∧ i < j
      ∧ signature bs i = signature bs j
      ∧ i % p = j % p := by
  have hlt : 5 * p < 5 * p + 1 := Nat.lt_succ_self _
  obtain ⟨i, hi, j, hj, hij, hcoll⟩ :=
    pigeonhole_collision hlt (jointState bs p hp)
  have hi' : i ≤ 5 * p := Nat.lt_succ_iff.mp hi
  have hj' : j ≤ 5 * p := Nat.lt_succ_iff.mp hj
  have hval_eq : (jointState bs p hp ⟨i, hi⟩).val
                = (jointState bs p hp ⟨j, hj⟩).val :=
    collTest_imp_val_eq (jointState bs p hp) i j hi hj hcoll
  have hval : (signature bs i).val * p + i % p
              = (signature bs j).val * p + j % p := hval_eq
  have hmi : i % p < p := Nat.mod_lt _ hp
  have hmj : j % p < p := Nat.mod_lt _ hp
  obtain ⟨h_sig_val_eq, h_mod_eq⟩ :=
    encode_inj hp (signature bs i).val (signature bs j).val
      (i % p) (j % p) hmi hmj hval
  exact ⟨i, hi', j, hj', hij, Fin.ext h_sig_val_eq, h_mod_eq⟩

end E213.Lib.Math.DyadicFSM.Forward.ForwardPeriodicity
