import E213.Meta.Nat.PolyNatMTactic
import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.AddMod213

/-!
# Josephus problem (k = 2) closed form (∅-axiom)
-/

namespace E213.Lib.Math.Combinatorics.Josephus

open E213.Meta.Nat.NatDiv213
  (add_div_right_pos add_mod_right_pos mul_mod_self_pure mul_div_cancel_left_pure
   add_mul_div_left_pure div_le_self_pos two_cancel_lt)
open E213.Tactic.NatHelper (add_mul_mod_self_pure)

def jos0F : Nat → Nat → Nat
  | 0,     _         => 0
  | _ + 1, 0         => 0
  | _ + 1, 1         => 0
  | f + 1, (n + 2)   =>
      match (n + 2) % 2 with
      | 0     => 2 * jos0F f ((n + 2) / 2)
      | _ + 1 => 2 * jos0F f ((n + 2) / 2) + 2

def jos0 (n : Nat) : Nat := jos0F n n

def josephus (n : Nat) : Nat := jos0 n + 1

/-- `(n+2)/2 = n/2 + 1` (PURE). -/
theorem half_eq (n : Nat) : (n + 2) / 2 = n / 2 + 1 :=
  add_div_right_pos (by decide : 0 < 2) n

theorem half_le {f n : Nat} (h : n + 2 ≤ f + 1) : (n + 2) / 2 ≤ f := by
  have h2 : n / 2 ≤ n := div_le_self_pos n 2 (by decide)
  have h3 : n / 2 + 1 ≤ n + 1 := Nat.succ_le_succ h2
  have h4 : n + 1 ≤ f := Nat.le_of_succ_le_succ h
  rw [half_eq]; exact Nat.le_trans h3 h4

theorem half_lt (n : Nat) : (n + 2) / 2 < n + 2 := by
  have h2 : n / 2 ≤ n := div_le_self_pos n 2 (by decide)
  rw [half_eq]
  exact Nat.lt_succ_of_le (Nat.succ_le_succ h2)

theorem jos0F_eq : ∀ n f g, n ≤ f → n ≤ g → jos0F f n = jos0F g n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro f g hf hg
    match n, f, g, hf, hg with
    | 0,     f,     g,     _,  _  => cases f <;> cases g <;> rfl
    | 1,     f + 1, g + 1, _,  _  => rfl
    | n + 2, f + 1, g + 1, hf, hg =>
      have hrec : jos0F f ((n + 2) / 2) = jos0F g ((n + 2) / 2) :=
        ih ((n + 2) / 2) (half_lt n) f g (half_le hf) (half_le hg)
      show (match (n + 2) % 2 with
            | 0     => 2 * jos0F f ((n + 2) / 2)
            | _ + 1 => 2 * jos0F f ((n + 2) / 2) + 2)
         = (match (n + 2) % 2 with
            | 0     => 2 * jos0F g ((n + 2) / 2)
            | _ + 1 => 2 * jos0F g ((n + 2) / 2) + 2)
      cases (n + 2) % 2 with
      | zero   => rw [hrec]
      | succ m => rw [hrec]

/-- `jos0F f n = jos0 n` whenever `fuel ≥ n`. -/
theorem jos0F_eq_jos0 (f n : Nat) (h : n ≤ f) : jos0F f n = jos0 n :=
  jos0F_eq n f n h (Nat.le_refl n)

/-! ## Defining recurrences (0-indexed) -/

/-- ★★ even recurrence (`k ≥ 1`): `J'(2k) = 2·J'(k)`. -/
theorem jos0_two_mul {k : Nat} (hk : 1 ≤ k) : jos0 (2 * k) = 2 * jos0 k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos hk).symm⟩
  have he : 2 * (j + 1) = (2 * j) + 2 := by ring_nat
  have hpar : ((2 * j) + 2) % 2 = 0 := by
    rw [show (2 * j) + 2 = 2 * (j + 1) from by ring_nat]
    exact mul_mod_self_pure 2 (j + 1)
  have hhalf : ((2 * j) + 2) / 2 = j + 1 := by
    rw [show (2 * j) + 2 = 2 * (j + 1) from by ring_nat]
    exact mul_div_cancel_left_pure 2 (j + 1) (by decide)
  show jos0F (2 * (j + 1)) (2 * (j + 1)) = 2 * jos0 (j + 1)
  rw [he]
  have hfuel : (2 * j) + 2 = ((2 * j) + 1) + 1 := by ring_nat
  rw [hfuel]
  show (match (((2 * j) + 1) + 1) % 2 with
        | 0     => 2 * jos0F ((2 * j) + 1) ((((2 * j) + 1) + 1) / 2)
        | _ + 1 => 2 * jos0F ((2 * j) + 1) ((((2 * j) + 1) + 1) / 2) + 2)
       = 2 * jos0 (j + 1)
  rw [show ((2 * j) + 1) + 1 = (2 * j) + 2 from by ring_nat, hpar, hhalf]
  show 2 * jos0F ((2 * j) + 1) (j + 1) = 2 * jos0 (j + 1)
  have hle : j + 1 ≤ (2 * j) + 1 := by
    have hj : j ≤ 2 * j := by rw [Nat.two_mul]; exact Nat.le_add_left j j
    exact Nat.succ_le_succ hj
  rw [jos0F_eq_jos0 ((2 * j) + 1) (j + 1) hle]

/-- ★★ odd recurrence (`k ≥ 1`): `J'(2k+1) = 2·J'(k) + 2`. -/
theorem jos0_two_mul_add_one {k : Nat} (hk : 1 ≤ k) :
    jos0 (2 * k + 1) = 2 * jos0 k + 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos hk).symm⟩
  have hfe : 2 * (j + 1) + 1 = (((2 * j) + 2)) + 1 := by ring_nat
  have hpar : ((((2 * j) + 2)) + 1) % 2 = 1 := by
    rw [show (((2 * j) + 2)) + 1 = 1 + (j + 1) * 2 from by ring_nat,
        add_mul_mod_self_pure 1 2 (j + 1)]
  have hhalf : ((((2 * j) + 2)) + 1) / 2 = j + 1 := by
    rw [show (((2 * j) + 2)) + 1 = 1 + 2 * (j + 1) from by ring_nat,
        add_mul_div_left_pure 1 2 (j + 1) (by decide),
        show (1 : Nat) / 2 = 0 from rfl, Nat.zero_add]
  show jos0F (2 * (j + 1) + 1) (2 * (j + 1) + 1) = 2 * jos0 (j + 1) + 2
  rw [hfe]
  show (match (((((2 * j) + 2)) + 1) % 2) with
        | 0     => 2 * jos0F ((2 * j) + 2) (((((2 * j) + 2)) + 1) / 2)
        | _ + 1 => 2 * jos0F ((2 * j) + 2) (((((2 * j) + 2)) + 1) / 2) + 2)
       = 2 * jos0 (j + 1) + 2
  rw [hpar, hhalf]
  show 2 * jos0F ((2 * j) + 2) (j + 1) + 2 = 2 * jos0 (j + 1) + 2
  have hle : j + 1 ≤ (2 * j) + 2 := by
    have hj : j ≤ 2 * j := by rw [Nat.two_mul]; exact Nat.le_add_left j j
    exact Nat.le_trans (Nat.succ_le_succ hj) (Nat.le_succ _)
  rw [jos0F_eq_jos0 ((2 * j) + 2) (j + 1) hle]

/-! ## Parity split -/

/-- Every `L : Nat` is `2L'` or `2L'+1`. -/
theorem parity_split : ∀ L : Nat, (∃ L', L = 2 * L') ∨ (∃ L', L = 2 * L' + 1)
  | 0 => Or.inl ⟨0, rfl⟩
  | n + 1 => by
    rcases parity_split n with ⟨m, h⟩ | ⟨m, h⟩
    · exact Or.inr ⟨m, by rw [h]⟩
    · refine Or.inl ⟨m + 1, ?_⟩
      rw [h, Nat.mul_add, Nat.mul_one]

/-! ## Closed form -/

/-- `2^(m+1) = 2·2^m`. -/
theorem two_pow_succ (m : Nat) : (2 : Nat) ^ (m + 1) = 2 * 2 ^ m := by
  rw [Nat.pow_succ, Nat.mul_comm]

/-- `1 ≤ 2^m`. -/
theorem one_le_two_pow (m : Nat) : 1 ≤ (2 : Nat) ^ m := by
  induction m with
  | zero => decide
  | succ k ih =>
    rw [two_pow_succ]
    exact Nat.le_trans ih (Nat.le_mul_of_pos_left _ (by decide))

/-- ★★★ **0-indexed closed form**: `J'(2^m + L) = 2·L` for `L < 2^m`.
    Induction on `m`; inductive step splits on the parity of `L` and applies the
    even / odd recurrences. -/
theorem jos0_closed_form : ∀ (m L : Nat), L < 2 ^ m → jos0 (2 ^ m + L) = 2 * L := by
  intro m
  induction m with
  | zero =>
    intro L hL
    -- 2^0 = 1, L < 1 → L = 0
    have hL0 : L = 0 := Nat.le_zero.mp (Nat.le_of_lt_succ hL)
    rw [hL0]
    -- jos0 (1 + 0) = jos0 1 = 0 = 2*0
    show jos0 1 = 2 * 0
    rfl
  | succ m ih =>
    intro L hL
    -- 2^(m+1) = 2*2^m
    rw [two_pow_succ] at hL ⊢
    have hpos : 1 ≤ 2 ^ m := one_le_two_pow m
    rcases parity_split L with ⟨L', rfl⟩ | ⟨L', rfl⟩
    · -- L = 2*L'
      have hL' : L' < 2 ^ m := two_cancel_lt L' (2 ^ m) hL
      -- 2*2^m + 2*L' = 2*(2^m + L')
      have hcomb : 2 * 2 ^ m + 2 * L' = 2 * (2 ^ m + L') := by ring_nat
      rw [hcomb]
      have hk : 1 ≤ 2 ^ m + L' := Nat.le_trans hpos (Nat.le_add_right _ _)
      rw [jos0_two_mul hk, ih L' hL']
    · -- L = 2*L'+1
      have hL' : L' < 2 ^ m := by
        have h2 : 2 * L' < 2 * 2 ^ m := Nat.lt_of_succ_lt hL
        exact two_cancel_lt L' (2 ^ m) h2
      -- 2*2^m + (2*L'+1) = 2*(2^m + L') + 1
      have hcomb : 2 * 2 ^ m + (2 * L' + 1) = 2 * (2 ^ m + L') + 1 := by ring_nat
      rw [hcomb]
      have hk : 1 ≤ 2 ^ m + L' := Nat.le_trans hpos (Nat.le_add_right _ _)
      rw [jos0_two_mul_add_one hk, ih L' hL']
      ring_nat

/-- ★★★ **Josephus closed form** (1-indexed): writing `n = 2^m + L`, `0 ≤ L < 2^m`,
    the survivor is `J(2^m + L) = 2·L + 1`. -/
theorem josephus_closed_form (m L : Nat) (hL : L < 2 ^ m) :
    josephus (2 ^ m + L) = 2 * L + 1 := by
  show jos0 (2 ^ m + L) + 1 = 2 * L + 1
  rw [jos0_closed_form m L hL]

/-! ## 1-indexed defining recurrences (derived) -/

/-- 1-indexed even recurrence (`k ≥ 1`): `J(2k) = 2·J(k) − 1`, stated additively
    `J(2k) + 1 = 2·J(k)` to stay subtraction-free. -/
theorem josephus_two_mul {k : Nat} (hk : 1 ≤ k) :
    josephus (2 * k) + 1 = 2 * josephus k := by
  show (jos0 (2 * k) + 1) + 1 = 2 * (jos0 k + 1)
  rw [jos0_two_mul hk]; ring_nat

/-- 1-indexed odd recurrence (`k ≥ 1`): `J(2k+1) = 2·J(k) + 1`. -/
theorem josephus_two_mul_add_one {k : Nat} (hk : 1 ≤ k) :
    josephus (2 * k + 1) = 2 * josephus k + 1 := by
  show jos0 (2 * k + 1) + 1 = 2 * (jos0 k + 1) + 1
  rw [jos0_two_mul_add_one hk]; ring_nat

/-! ## Smoke tests (closed, axiom-clean `decide`) -/

/-- `J(1..10) = 1,1,3,1,3,5,7,1,3,5`. -/
theorem josephus_table :
    josephus 1 = 1 ∧ josephus 2 = 1 ∧ josephus 3 = 3 ∧ josephus 4 = 1
    ∧ josephus 5 = 3 ∧ josephus 6 = 5 ∧ josephus 7 = 7 ∧ josephus 8 = 1
    ∧ josephus 9 = 3 ∧ josephus 10 = 5 := by decide

/-- The classic case `n = 41 ⇒ survivor at seat 19`. -/
theorem josephus_41 : josephus 41 = 19 := by decide

/-- 0-indexed table `J'(1..10) = 0,0,2,0,2,4,6,0,2,4`. -/
theorem jos0_table :
    jos0 1 = 0 ∧ jos0 2 = 0 ∧ jos0 3 = 2 ∧ jos0 4 = 0
    ∧ jos0 5 = 2 ∧ jos0 6 = 4 ∧ jos0 7 = 6 ∧ jos0 8 = 0
    ∧ jos0 9 = 2 ∧ jos0 10 = 4 := by decide

end E213.Lib.Math.Combinatorics.Josephus
