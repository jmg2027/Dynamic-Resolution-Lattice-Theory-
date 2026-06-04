import E213.Meta.Nat.NatDiv213
import E213.Meta.Tactic.NatHelper

/-!
# 213-native `Nat.add_mod` (∅-axiom, Math layer)

Lean-core `Nat.add_mod` brings `propext`.  This ∅-axiom replacement
unblocks `sub_is_multiple_of_p` and the
`signature_eventually_periodic_of_periodic_bits` chain.
-/

namespace E213.Meta.Nat.AddMod213

open E213.Tactic.NatHelper (sub_add_cancel)
open E213.Meta.Nat.NatDiv213 (add_mod_right_pos)

/-- `(a + b) % n = (a % n + b) % n` when `0 < n`.  ∅-axiom via
    strong recursion on `a`. -/
theorem add_mod_left {n : Nat} (hn : 0 < n) :
    ∀ (a b : Nat), (a + b) % n = (a % n + b) % n := fun a b =>
  Nat.strongRecOn a (motive := fun a => (a + b) % n = (a % n + b) % n)
    fun a ih => by
      show (a + b) % n = (a % n + b) % n
      by_cases ha : a < n
      · rw [Nat.mod_eq_of_lt ha]
      · have hge : n ≤ a := Nat.le_of_not_lt ha
        have hsub_lt : a - n < a :=
          Nat.sub_lt (Nat.lt_of_lt_of_le hn hge) hn
        have ih' := ih (a - n) hsub_lt
        have hmod_a : a % n = (a - n) % n := Nat.mod_eq_sub_mod hge
        have hadd_eq : a + b = (a - n) + b + n := by
          rw [Nat.add_right_comm (a - n) b n, sub_add_cancel hge]
        rw [hadd_eq, add_mod_right_pos hn, ih', hmod_a]

/-- `a % n % n = a % n`.  ∅-axiom. -/
theorem mod_mod (a n : Nat) : a % n % n = a % n := by
  by_cases h : 0 < n
  · exact Nat.mod_eq_of_lt (Nat.mod_lt _ h)
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    subst hn0
    rw [Nat.mod_zero, Nat.mod_zero]

/-- `0 % a = 0`.  ∅-axiom. -/
theorem zero_mod (a : Nat) : 0 % a = 0 := by
  by_cases h : 0 < a
  · exact Nat.mod_eq_of_lt h
  · have : a = 0 := Nat.eq_zero_of_not_pos h
    subst this; rfl

/-- `(a % b + c) % b = (a + c) % b` when `0 < b`.  ∅-axiom. -/
theorem mod_add_mod {b : Nat} (hb : 0 < b) (a c : Nat) :
    (a % b + c) % b = (a + c) % b :=
  (add_mod_left hb a c).symm

/-- `(a + b) % n = (a % n + b % n) % n` when `0 < n`.  ∅-axiom. -/
theorem add_mod {n : Nat} (hn : 0 < n) (a b : Nat) :
    (a + b) % n = (a % n + b % n) % n := by
  rw [add_mod_left hn a b]
  rw [Nat.add_comm (a % n) b, add_mod_left hn b (a % n), Nat.add_comm]

/-- `(a + b) % n = (a % n + b % n) % n` for all `n` (incl. n = 0).
    ∅-axiom replacement for Lean-core `Nat.add_mod` (`[propext]`). -/
theorem add_mod_gen (a b n : Nat) :
    (a + b) % n = (a % n + b % n) % n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    show (a + b) % 0 = (a % 0 + b % 0) % 0
    rw [Nat.mod_zero a, Nat.mod_zero b]
  · exact add_mod hn a b

/-- `n % 2 = 0 ∨ n % 2 = 1`.  ∅-axiom replacement for
    `Nat.mod_two_eq_zero_or_one` (which leaks propext + Quot.sound).
    Direct match on `n % 2` with `Nat.mod_lt` bound. -/
theorem mod_two_zero_or_one (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 := by
  have hlt : n % 2 < 2 := Nat.mod_lt n (by decide)
  match h : n % 2 with
  | 0 => exact Or.inl rfl
  | 1 => exact Or.inr rfl
  | k+2 =>
      exfalso
      rw [h] at hlt
      exact Nat.lt_irrefl 2 (Nat.lt_of_le_of_lt (Nat.le_add_left 2 k) hlt)

/-- `b * (a / b) + a % b = a` for all `a b`.  ∅-axiom replacement
    for `Nat.div_add_mod` (which leaks propext). -/
theorem div_add_mod : ∀ (a b : Nat), b * (a / b) + a % b = a := fun a b =>
  Nat.strongRecOn a (motive := fun a => b * (a / b) + a % b = a)
    fun a ih => by
      show b * (a / b) + a % b = a
      by_cases hbound : 0 < b ∧ b ≤ a
      · have hsub_lt : a - b < a :=
          Nat.sub_lt (Nat.lt_of_lt_of_le hbound.1 hbound.2) hbound.1
        have ih' := ih (a - b) hsub_lt
        have hd : a / b = (a - b) / b + 1 := by
          rw [Nat.div_eq]; rw [if_pos hbound]
        have hm : a % b = (a - b) % b := by
          rw [Nat.mod_eq]; rw [if_pos hbound]
        rw [hd, hm, Nat.mul_add, Nat.mul_one]
        rw [Nat.add_right_comm, ih']
        exact sub_add_cancel hbound.2
      · by_cases hb : 0 < b
        · have ha : a < b :=
            Nat.lt_of_not_le (fun h => hbound ⟨hb, h⟩)
          have hd : a / b = 0 := Nat.div_eq_of_lt ha
          have hm : a % b = a := Nat.mod_eq_of_lt ha
          rw [hd, hm, Nat.mul_zero, Nat.zero_add]
        · have hb_eq : b = 0 := Nat.eq_zero_of_not_pos hb
          rw [hb_eq, Nat.zero_mul, Nat.zero_add]
          rw [Nat.mod_eq]
          rw [if_neg (fun h => absurd h.1 (Nat.lt_irrefl _))]

/-- `(k ∣ m) → n % m % k = n % k`.  ∅-axiom replacement for
    Lean-core `Nat.mod_mod_of_dvd` (`[propext]`).  Decomposes via
    `div_add_mod`, then uses `Nat213.mul_mod_right` to kill the
    multiple-of-k term.  Used by `Lens.Leaves.ModNat.divides_refines`. -/
theorem mod_mod_of_dvd (n : Nat) {m k : Nat} (h : k ∣ m) :
    n % m % k = n % k := by
  obtain ⟨q, hq⟩ := h
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hm : m = 0 := by rw [hq, Nat.zero_mul]
    subst hm
    rw [Nat.mod_zero, Nat.mod_zero]
  have h1 : n = m * (n / m) + n % m := (div_add_mod n m).symm
  have h2 : n % k = (m * (n / m) + n % m) % k := by rw [← h1]
  have h3 : m * (n / m) = k * (q * (n / m)) := by
    rw [hq, E213.Tactic.NatHelper.mul_assoc]
  have h4 : n % k = (k * (q * (n / m)) + n % m) % k := by rw [h2, h3]
  have hkdvd : (k * (q * (n / m))) % k = 0 :=
    E213.Tactic.NatHelper.mul_mod_right k _
  have h5 : (k * (q * (n / m)) + n % m) % k = (n % m) % k := by
    rw [add_mod hk, hkdvd, Nat.zero_add]
    exact mod_mod (n % m) k
  rw [h4, h5]

/-- `n % n = 0`.  ∅-axiom replacement for Lean-core `Nat.mod_self`
    (`[propext]`).  Via `Nat213.mul_mod_right n 1` + `Nat.mul_one`. -/
theorem mod_self (n : Nat) : n % n = 0 :=
  let h1 : n * 1 = n := Nat.mul_one n
  let h2 : n * 1 % n = 0 := E213.Tactic.NatHelper.mul_mod_right n 1
  let h3 : n * 1 % n = n % n := congrArg (· % n) h1
  h3.symm.trans h2

/-- `(n + a) % n = a % n`.  ∅-axiom replacement for Lean-core
    `Nat.add_mod_left` (`[propext]`).  Via `Nat213.add_self_mod_pure`
    after `Nat.add_comm`. -/
theorem add_mod_left_pure (n a : Nat) : (n + a) % n = a % n :=
  let h2 : (a + n) % n = a % n := E213.Tactic.NatHelper.add_self_mod_pure a n
  let h3 : (n + a) % n = (a + n) % n := congrArg (· % n) (Nat.add_comm n a)
  h3.trans h2

/-- `a % b = 0 → b ∣ a`.  ∅-axiom replacement for Lean-core
    `Nat.dvd_of_mod_eq_zero` (`[propext]`).  Via `div_add_mod` —
    if `a % b = 0` then `b * (a/b) + 0 = a`, so witness `a/b`. -/
theorem dvd_of_mod_eq_zero {a b : Nat} (h : a % b = 0) : b ∣ a :=
  let h1 : b * (a / b) + a % b = a := div_add_mod a b
  let h2 : b * (a / b) + 0 = a := h ▸ h1
  let h3 : b * (a / b) = a := (Nat.add_zero (b * (a / b))).symm.trans h2
  ⟨a / b, h3.symm⟩

/-- `a ≤ b ∧ a % n = b % n → (b - a) % n = 0`.  ∅-axiom — used by
    `Lib.Math.ModArith.JoinExample` for the "(view r' - view r) is
    divisible by 2" step in the mod_4_6 → L_2 chain.

    Proof: write `b = (b - a) + a`, take `% n`, decompose via
    `add_mod_gen`.  Then enumerate the residue `(b - a) % n` against
    `n` to pin it down to `0`. -/
theorem mod_diff_eq_zero_of_le {n : Nat} (hn : 0 < n) {a b : Nat}
    (hle : a ≤ b) (hmod : a % n = b % n) : (b - a) % n = 0 := by
  have hsum : b - a + a = b := E213.Tactic.NatHelper.sub_add_cancel hle
  have h1 : (b - a + a) % n = b % n := by rw [hsum]
  have h2 : (b - a + a) % n = ((b - a) % n + a % n) % n :=
    add_mod_gen (b - a) a n
  have h3 : ((b - a) % n + a % n) % n = a % n := by
    rw [← h2, h1, ← hmod]
  -- Let r := (b - a) % n.  Need r = 0.  Strategy: r < n by mod_lt,
  -- a % n < n; case split on r + a % n vs n.
  have hr_lt : (b - a) % n < n := Nat.mod_lt _ hn
  have hamod_lt : a % n < n := Nat.mod_lt _ hn
  by_cases hsumlt : (b - a) % n + a % n < n
  · -- Then ((b-a)%n + a%n) % n = (b-a)%n + a%n.  And it equals a%n.
    rw [Nat.mod_eq_of_lt hsumlt] at h3
    -- h3 : (b - a) % n + a % n = a % n.  Want (b-a)%n = 0.
    -- Rewrite as (b-a)%n + a%n = 0 + a%n, cancel.
    have h_cancel : (b - a) % n + a % n = 0 + a % n := by
      rw [Nat.zero_add]; exact h3
    exact E213.Tactic.NatHelper.add_right_cancel h_cancel
  · -- (b-a)%n + a%n ≥ n.  Then ((b-a)%n + a%n) % n = ((b-a)%n + a%n) - n.
    have hge : n ≤ (b - a) % n + a % n := Nat.le_of_not_lt hsumlt
    have hms : ((b - a) % n + a % n) % n = ((b - a) % n + a % n - n) % n :=
      Nat.mod_eq_sub_mod hge
    rw [hms] at h3
    -- (b-a)%n + a%n - n < n: prove via add_lt_add + sub_add_cancel.
    have h_add_lt : (b - a) % n + a % n < n + n :=
      Nat.add_lt_add hr_lt hamod_lt
    have h_sub_add_lt : (b - a) % n + a % n - n + n < n + n := by
      rw [sub_add_cancel hge]; exact h_add_lt
    have hsublt : (b - a) % n + a % n - n < n :=
      Nat.lt_of_add_lt_add_right h_sub_add_lt
    rw [Nat.mod_eq_of_lt hsublt] at h3
    -- h3 : (b - a) % n + a % n - n = a % n.  Derive contradiction.
    have hrec : (b - a) % n + a % n = a % n + n := by
      have h_add : (b - a) % n + a % n - n + n = a % n + n :=
        congrArg (· + n) h3
      rw [sub_add_cancel hge] at h_add
      exact h_add
    have hr_eq_n : (b - a) % n = n := by
      have h_swap : (b - a) % n + a % n = n + a % n := by
        rw [hrec, Nat.add_comm n (a % n)]
      exact E213.Tactic.NatHelper.add_right_cancel h_swap
    exact absurd hr_eq_n (Nat.ne_of_lt hr_lt)

/-- 213-native `Nat.max_comm` (Lean-core leaks propext via max_eq_left). -/
theorem max_comm (a b : Nat) : Nat.max a b = Nat.max b a := by
  rcases Nat.le_total a b with hab | hba
  · show (if a ≤ b then b else a) = (if b ≤ a then a else b)
    rw [if_pos hab]
    by_cases h : b ≤ a
    · rw [if_pos h]; exact Nat.le_antisymm h hab
    · rw [if_neg h]
  · show (if a ≤ b then b else a) = (if b ≤ a then a else b)
    rw [if_pos hba]
    by_cases h : a ≤ b
    · rw [if_pos h]; exact Nat.le_antisymm hba h
    · rw [if_neg h]

/-- ★ **Double mod-p negation**: `(p - (p - r) % p) % p = r` for
    `r < p`.  PURE.

    The "additive inverse is involutive in `F_p`" identity, in
    canonical-form (r < p) form.  Used in:
      · `Lib/Math/NumberTheory/ModArith/FP2Sqrt5` (private double_neg_mod)
      · `Lib/Math/NumberTheory/ModArith/FP2SqrtD`
      · `Lib/Math/NumberSystems/Padic/NegInvolution{,Digit1,Preserve}` (p-adic
        Zp.neg involution at digit-0 and beyond)

    Canonical Meta-layer home for the `double_neg_mod` family used
    by the consumers above. -/
theorem double_neg_mod_at (p r : Nat) (hp : 0 < p) (hr : r < p) :
    (p - (p - r) % p) % p = r := by
  by_cases h0 : r = 0
  · subst h0
    show (p - (p - 0) % p) % p = 0
    rw [Nat.sub_zero, mod_self, Nat.sub_zero, mod_self]
  · have h0_pos : 0 < r := Nat.pos_of_ne_zero h0
    have hpsub_lt : p - r < p := Nat.sub_lt hp h0_pos
    have h_psub_le : r ≤ p := Nat.le_of_lt hr
    rw [Nat.mod_eq_of_lt hpsub_lt]
    rw [E213.Tactic.NatHelper.sub_sub_self h_psub_le]
    rw [Nat.mod_eq_of_lt hr]

/-- **Division monotonicity** (positive divisor): `x ≤ y → x / c ≤ y / c`.
    ∅-axiom replacement for Lean-core `Nat.div_le_div_right` (propext).
    Proof: if `y/c < x/c` then `c*(x/c) ≥ c*(y/c)+c > c*(y/c)+y%c = y ≥ x`
    while `c*(x/c) ≤ x`, contradiction. -/
theorem div_le_div_right_pos (c : Nat) (hc : 0 < c) {x y : Nat} (h : x ≤ y) :
    x / c ≤ y / c := by
  rcases Nat.lt_or_ge (y / c) (x / c) with hlt | hge
  · exfalso
    have hstep : (y / c) + 1 ≤ x / c := hlt
    have hcmul : c * ((y / c) + 1) ≤ c * (x / c) := Nat.mul_le_mul_left c hstep
    -- c*(x/c) ≤ x  (from div_add_mod)
    have hx_ge : c * (x / c) ≤ x :=
      Nat.le_trans (Nat.le_add_right (c * (x / c)) (x % c))
        (Nat.le_of_eq (div_add_mod x c))
    have hy_eq : c * (y / c) + y % c = y := div_add_mod y c
    have hmod_lt : y % c < c := Nat.mod_lt y hc
    -- c*(y/c) + c ≤ c*(x/c) ≤ x ≤ y
    have hchain : c * (y / c) + c ≤ y := by
      have e : c * ((y / c) + 1) = c * (y / c) + c := by rw [Nat.mul_add, Nat.mul_one]
      rw [e] at hcmul
      exact Nat.le_trans hcmul (Nat.le_trans hx_ge h)
    -- y = c*(y/c) + y%c, so c ≤ y%c, contradicting y%c < c.
    have hbad : c * (y / c) + c ≤ c * (y / c) + y % c :=
      Nat.le_trans hchain (Nat.le_of_eq hy_eq.symm)
    have hcle : c ≤ y % c := E213.Tactic.NatHelper.le_of_add_le_add_left hbad
    exact Nat.lt_irrefl c (Nat.lt_of_le_of_lt hcle hmod_lt)
  · exact hge

end E213.Meta.Nat.AddMod213
