import E213.Term.Tactic.Nat213

/-!
# 213-native `gcd213` divisibility infrastructure (∅-axiom)

Builds the divisibility properties of `Nat213.gcd213` PURE — i.e.,
`gcd213 a b ∣ a` and `gcd213 a b ∣ b` for arbitrary `a, b : Nat`.

Lean-core `Nat.gcd_dvd_left/right` bring `propext` (well-founded
gcd termination); these ∅-axiom replacements unblock downstream
`ModNat.gcd_upper_bound`, `JoinGCD.joinEquiv_subset_gcd`, etc.

## Proof structure

Three layers:

  1. `mod_self_pos`        : `0 < a → a % a = 0`
  2. `g_dvd_b_via_mod`     : `g ∣ a ∧ g ∣ (b % a) → g ∣ b`
                              (fuel-induction on `b`, replaces
                               `Nat.div_add_mod` propext)
  3. `gcdFuel_dvd_both`    : `n ≥ Nat.max a b + a →
                              gcdFuel n a b ∣ a ∧ ∣ b`
                              (induction on fuel `n`, monovariant
                               `M(a, b) := max a b + a`)
  4. `gcd213_dvd_left/right` : derive at the actual `gcd213` fuel.

The monovariant `M(a, b) := max(a, b) + a` strictly decreases per
Euclidean step.  `gcd213` allocates `2 * (a + b) + 1` fuel which
is ≥ `M(a, b)` for all `a, b`.
-/

namespace E213.Lib.Math.NatHelpers.Gcd213

open E213.Tactic.Nat213
  (gcdFuel gcd213 sub_add_cancel le_max_left le_max_right)

/-- `0 < a → a % a = 0` via `(a - a) % a = 0 % a = 0`. -/
theorem mod_self_pos : ∀ a, 0 < a → a % a = 0
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | a'+1, _ => by
    rw [Nat.mod_eq_sub_mod (Nat.le_refl _), Nat.sub_self]; rfl

/-- `0 < a → m + 1 - a ≤ m`.  PURE replacement for the propext-leaking
    `Nat.sub_le_sub_left`-based derivation. -/
theorem succ_sub_le_self (m a : Nat) (ha : 0 < a) : m + 1 - a ≤ m := by
  match a with
  | 0 => exact absurd ha (Nat.lt_irrefl 0)
  | a'+1 =>
    show m + 1 - (a' + 1) ≤ m
    rw [Nat.succ_sub_succ_eq_sub]; exact Nat.sub_le m a'

end E213.Lib.Math.NatHelpers.Gcd213

namespace E213.Lib.Math.NatHelpers.Gcd213

open E213.Tactic.Nat213
  (gcdFuel gcd213 sub_add_cancel le_max_left le_max_right)

/-- ★★★ **Key sub-lemma**: `g ∣ a ∧ g ∣ (b % a) → g ∣ b`.

    Standard Euclidean fact, but Lean-core's proof goes via
    `Nat.div_add_mod` (propext).  This ∅-axiom version uses
    fuel-induction on `b` with case-split on `b < a` vs. `b ≥ a`
    + rewriting `b % a = (b - a) % a` for `b ≥ a`. -/
theorem g_dvd_b_via_mod : ∀ (fuel a b g : Nat), 0 < a → b ≤ fuel →
    g ∣ a → g ∣ (b % a) → g ∣ b
  | 0, _, b, _, _, hb, _, _ => by
    rw [Nat.le_zero.mp hb]; exact ⟨0, rfl⟩
  | k+1, a, b, g, hpos, hbfuel, hga, hgmod => by
    by_cases hba : b < a
    · rw [Nat.mod_eq_of_lt hba] at hgmod; exact hgmod
    · have hba' : a ≤ b := Nat.le_of_not_lt hba
      have hb_a_le : b - a ≤ k :=
        Nat.le_trans (Nat.sub_le_sub_right hbfuel a) (succ_sub_le_self k a hpos)
      rw [Nat.mod_eq_sub_mod hba'] at hgmod
      have h_dvd_sub : g ∣ (b - a) :=
        g_dvd_b_via_mod k a (b - a) g hpos hb_a_le hga hgmod
      obtain ⟨c1, hc1⟩ := hga
      obtain ⟨c2, hc2⟩ := h_dvd_sub
      refine ⟨c2 + c1, ?_⟩
      rw [← sub_add_cancel hba', hc2, hc1, Nat.mul_add]

end E213.Lib.Math.NatHelpers.Gcd213

namespace E213.Lib.Math.NatHelpers.Gcd213

open E213.Tactic.Nat213
  (gcdFuel gcd213 sub_add_cancel le_max_left le_max_right)

/-- ★★★★ **Fuel-bounded divisibility**: when `n ≥ Nat.max a b + a`,
    `gcdFuel n a b` divides both `a` and `b`.

    Proof: induction on `n`.  Inductive case uses
    `gcdFuel (k+1) (a'+1) b = gcdFuel k (b % (a'+1)) (a'+1)` step,
    applying IH on the inner state (whose monovariant is strictly
    smaller: `M_new = (a'+1) + b%(a'+1) ≤ 2a' + 1 < 2a' + 2 ≤ M_old`),
    then `g_dvd_b_via_mod` to lift `gcd ∣ a ∧ gcd ∣ (b%a)` to
    `gcd ∣ b`. -/
theorem gcdFuel_dvd_both : ∀ (n a b : Nat),
    n ≥ Nat.max a b + a →
    gcdFuel n a b ∣ a ∧ gcdFuel n a b ∣ b := by
  intro n
  induction n with
  | zero =>
    intro a b hbound
    have hmax_le : Nat.max a b ≤ 0 :=
      Nat.le_trans (Nat.le_add_right _ _) hbound
    have ha : a = 0 :=
      Nat.le_zero.mp (Nat.le_trans (le_max_left a b) hmax_le)
    have hb : b = 0 :=
      Nat.le_zero.mp (Nat.le_trans (le_max_right a b) hmax_le)
    subst ha; subst hb
    exact ⟨⟨0, rfl⟩, ⟨0, rfl⟩⟩
  | succ k ih =>
    intro a b hbound
    match a with
    | 0 =>
      show b ∣ 0 ∧ b ∣ b
      exact ⟨⟨0, rfl⟩, ⟨1, (Nat.mul_one _).symm⟩⟩
    | a'+1 =>
      show gcdFuel k (b % (a'+1)) (a'+1) ∣ (a'+1)
            ∧ gcdFuel k (b % (a'+1)) (a'+1) ∣ b
      have hmod_lt : b % (a'+1) < a'+1 := Nat.mod_lt b (Nat.zero_lt_succ a')
      have hmod_le_a' : b % (a'+1) ≤ a' := Nat.lt_succ_iff.mp hmod_lt
      have hmax_eq : Nat.max (b % (a'+1)) (a'+1) = a'+1 :=
        Nat.max_eq_right (Nat.le_of_lt hmod_lt)
      have hk_bound : k ≥ Nat.max (b % (a'+1)) (a'+1) + b % (a'+1) := by
        rw [hmax_eq]
        have h1 : (a'+1) + (a'+1) ≤ k + 1 := by
          exact Nat.le_trans
            (Nat.add_le_add_right (le_max_left (a'+1) b) (a'+1)) hbound
        have h2 : (a'+1) + (a'+1) = ((a'+1) + a') + 1 := rfl
        have h3 : ((a'+1) + a') + 1 ≤ k + 1 := h2 ▸ h1
        have h4 : (a'+1) + a' ≤ k := Nat.le_of_succ_le_succ h3
        exact Nat.le_trans (Nat.add_le_add_left hmod_le_a' _) h4
      have ih_result := ih (b % (a'+1)) (a'+1) hk_bound
      refine ⟨ih_result.2, ?_⟩
      exact g_dvd_b_via_mod b (a'+1) b _ (Nat.zero_lt_succ _) (Nat.le_refl b)
        ih_result.2 ih_result.1

end E213.Lib.Math.NatHelpers.Gcd213

namespace E213.Lib.Math.NatHelpers.Gcd213

open E213.Tactic.Nat213
  (gcdFuel gcd213 sub_add_cancel le_max_left le_max_right)

/-- Fuel sufficiency: `2 * (a + b) + 1 ≥ Nat.max a b + a`. -/
private theorem fuel_sufficient (a b : Nat) :
    2 * (a + b) + 1 ≥ Nat.max a b + a := by
  have h1 : Nat.max a b ≤ a + b := by
    show (if a ≤ b then b else a) ≤ a + b
    by_cases hab : a ≤ b
    · rw [if_pos hab]; exact Nat.le_add_left b a
    · rw [if_neg hab]; exact Nat.le_add_right a b
  have h2 : Nat.max a b + a ≤ (a + b) + a := Nat.add_le_add_right h1 a
  have h3 : (a + b) + a ≤ 2 * (a + b) := by
    rw [Nat.two_mul]
    exact Nat.add_le_add_left (Nat.le_add_right a b) (a + b)
  exact Nat.le_trans (Nat.le_trans h2 h3) (Nat.le_succ _)

/-- ★★★★★ **`gcd213 a b ∣ a`**: PURE replacement for
    Lean-core `Nat.gcd_dvd_left`.  -/
theorem gcd213_dvd_left (a b : Nat) : gcd213 a b ∣ a :=
  (gcdFuel_dvd_both (2 * (a + b) + 1) a b (fuel_sufficient a b)).1

/-- ★★★★★ **`gcd213 a b ∣ b`**: PURE replacement for
    Lean-core `Nat.gcd_dvd_right`. -/
theorem gcd213_dvd_right (a b : Nat) : gcd213 a b ∣ b :=
  (gcdFuel_dvd_both (2 * (a + b) + 1) a b (fuel_sufficient a b)).2

end E213.Lib.Math.NatHelpers.Gcd213

namespace E213.Lib.Math.NatHelpers.Gcd213

open E213.Tactic.Nat213
  (gcdFuel gcd213 sub_add_cancel add_sub_cancel_right
   le_max_left le_max_right)

/-! ## Auxiliary arithmetic for Bezout/antisymmetry -/

/-- `(a * b) * c = a * (b * c)` term-mode (∅-axiom).
    Lean-core `Nat.mul_assoc` brings `propext`. -/
theorem mul_assoc_213 : ∀ (a b c : Nat), (a * b) * c = a * (b * c)
  | _, _, 0 => rfl
  | a, b, c+1 =>
    let ih : (a * b) * c = a * (b * c) := mul_assoc_213 a b c
    let h1 : (a * b) * (c + 1) = (a * b) * c + a * b := Nat.mul_succ (a*b) c
    let h2 : a * (b * (c + 1)) = a * (b * c + b) := congrArg (a * ·) (Nat.mul_succ b c)
    let h3 : a * (b * c + b) = a * (b * c) + a * b := Nat.mul_add a (b*c) b
    h1.trans (ih ▸ (h2.trans h3).symm)

/-- `c1 ≤ c2 → d * c2 - d * c1 = d * (c2 - c1)`.  ∅-axiom. -/
theorem mul_sub_213 (d c1 c2 : Nat) (h : c1 ≤ c2) :
    d * c2 - d * c1 = d * (c2 - c1) := by
  have h1 : c2 - c1 + c1 = c2 := sub_add_cancel h
  have h2 : d * (c2 - c1 + c1) = d * c2 := by rw [h1]
  rw [Nat.left_distrib] at h2
  rw [← h2]
  exact add_sub_cancel_right (d * (c2 - c1)) (d * c1)

/-- `d ∣ a ∧ d ∣ b ∧ a ≤ b → d ∣ (b - a)`.  ∅-axiom. -/
theorem dvd_sub_213 (a b d : Nat) (hab : a ≤ b) (hda : d ∣ a) (hdb : d ∣ b) :
    d ∣ (b - a) := by
  obtain ⟨c1, hc1⟩ := hda
  obtain ⟨c2, hc2⟩ := hdb
  refine ⟨c2 - c1, ?_⟩
  rw [hc1, hc2]
  have hab' : d * c1 ≤ d * c2 := by rw [← hc1, ← hc2]; exact hab
  by_cases hd : d = 0
  · rw [hd, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul]
  · exact mul_sub_213 d c1 c2
      (Nat.le_of_mul_le_mul_left hab' (Nat.zero_lt_of_ne_zero hd))

end E213.Lib.Math.NatHelpers.Gcd213

namespace E213.Lib.Math.NatHelpers.Gcd213

open E213.Tactic.Nat213
  (gcdFuel gcd213 sub_add_cancel le_max_left le_max_right)

/-- `d ∣ a ∧ d ∣ b → d ∣ (b % a)` for `a > 0`.  ∅-axiom via fuel
    induction on `b`. -/
theorem dvd_mod_via_fuel : ∀ (fuel a b d : Nat), 0 < a → b ≤ fuel →
    d ∣ a → d ∣ b → d ∣ (b % a)
  | 0, a, b, d, _, hb, _, hdb => by
    have : b = 0 := Nat.le_zero.mp hb; subst this
    show d ∣ 0 % a
    exact ⟨0, rfl⟩
  | k+1, a, b, d, hpos, hbfuel, hda, hdb => by
    by_cases hba : b < a
    · rw [Nat.mod_eq_of_lt hba]; exact hdb
    · have hba' : a ≤ b := Nat.le_of_not_lt hba
      have hb_a_le : b - a ≤ k :=
        Nat.le_trans (Nat.sub_le_sub_right hbfuel a) (succ_sub_le_self k a hpos)
      rw [Nat.mod_eq_sub_mod hba']
      exact dvd_mod_via_fuel k a (b - a) d hpos hb_a_le hda
        (dvd_sub_213 a b d hba' hda hdb)

/-- ★★★★ **`gcdFuel` is the greatest common divisor**: any `d` that
    divides both `a` and `b` divides `gcdFuel n a b` (when fuel
    suffices). -/
theorem gcdFuel_greatest : ∀ (n a b d : Nat),
    n ≥ Nat.max a b + a →
    d ∣ a → d ∣ b → d ∣ gcdFuel n a b := by
  intro n
  induction n with
  | zero =>
    intro a b d hbound hda _
    have hmax_le : Nat.max a b ≤ 0 :=
      Nat.le_trans (Nat.le_add_right _ _) hbound
    have ha : a = 0 :=
      Nat.le_zero.mp (Nat.le_trans (le_max_left a b) hmax_le)
    subst ha
    show d ∣ 0
    exact ⟨0, rfl⟩
  | succ k ih =>
    intro a b d hbound hda hdb
    match a with
    | 0 => exact hdb
    | a'+1 =>
      show d ∣ gcdFuel k (b % (a'+1)) (a'+1)
      have hmod_lt : b % (a'+1) < a'+1 := Nat.mod_lt b (Nat.zero_lt_succ a')
      have hmod_le_a' : b % (a'+1) ≤ a' := Nat.lt_succ_iff.mp hmod_lt
      have hmax_eq : Nat.max (b % (a'+1)) (a'+1) = a'+1 :=
        Nat.max_eq_right (Nat.le_of_lt hmod_lt)
      have hk_bound : k ≥ Nat.max (b % (a'+1)) (a'+1) + b % (a'+1) := by
        rw [hmax_eq]
        have h1 : (a'+1) + (a'+1) ≤ k + 1 := by
          exact Nat.le_trans
            (Nat.add_le_add_right (le_max_left (a'+1) b) (a'+1)) hbound
        have h2 : (a'+1) + (a'+1) = ((a'+1) + a') + 1 := rfl
        have h3 : ((a'+1) + a') + 1 ≤ k + 1 := h2 ▸ h1
        have h4 : (a'+1) + a' ≤ k := Nat.le_of_succ_le_succ h3
        exact Nat.le_trans (Nat.add_le_add_left hmod_le_a' _) h4
      have hd_mod : d ∣ (b % (a'+1)) :=
        dvd_mod_via_fuel b (a'+1) b d (Nat.zero_lt_succ _) (Nat.le_refl b) hda hdb
      exact ih (b % (a'+1)) (a'+1) d hk_bound hd_mod hda

end E213.Lib.Math.NatHelpers.Gcd213

namespace E213.Lib.Math.NatHelpers.Gcd213

open E213.Tactic.Nat213 (gcdFuel gcd213)

private theorem fuel_sufficient' (a b : Nat) :
    2 * (a + b) + 1 ≥ Nat.max a b + a := by
  have h1 : Nat.max a b ≤ a + b := by
    show (if a ≤ b then b else a) ≤ a + b
    by_cases hab : a ≤ b
    · rw [if_pos hab]; exact Nat.le_add_left b a
    · rw [if_neg hab]; exact Nat.le_add_right a b
  have h2 : Nat.max a b + a ≤ (a + b) + a := Nat.add_le_add_right h1 a
  have h3 : (a + b) + a ≤ 2 * (a + b) := by
    rw [Nat.two_mul]
    exact Nat.add_le_add_left (Nat.le_add_right a b) (a + b)
  exact Nat.le_trans (Nat.le_trans h2 h3) (Nat.le_succ _)

/-- ★★★★★ **`gcd213` is the greatest common divisor**: any `d` that
    divides both `a` and `b` divides `gcd213 a b`.  ∅-axiom. -/
theorem gcd213_greatest (a b d : Nat) (hda : d ∣ a) (hdb : d ∣ b) :
    d ∣ gcd213 a b :=
  gcdFuel_greatest (2 * (a + b) + 1) a b d (fuel_sufficient' a b) hda hdb

/-- Helper: `c * d = 1 → c = 1` (Nat-only multiplicative unit). -/
theorem mul_eq_one_left : ∀ (c d : Nat), c * d = 1 → c = 1
  | 0, _, h => by rw [Nat.zero_mul] at h; exact absurd h (by decide)
  | 1, _, _ => rfl
  | c'+2, d, h => by
    cases d with
    | zero => rw [Nat.mul_zero] at h; exact absurd h (by decide)
    | succ d' =>
      have h_le : (1 : Nat) ≤ d' + 1 := Nat.succ_le_succ (Nat.zero_le _)
      have hh1 : (c' + 2) * 1 ≤ (c' + 2) * (d' + 1) :=
        Nat.mul_le_mul_left (c'+2) h_le
      rw [Nat.mul_one] at hh1
      have hh2 : c' + 2 ≤ 1 := h ▸ hh1
      exact absurd (Nat.le_of_succ_le_succ hh2) (Nat.not_succ_le_zero c')

/-- ★★★★ **`Nat.dvd_antisymm` ∅-axiom replacement**: `a ∣ b ∧ b ∣ a → a = b`. -/
theorem dvd_antisymm_213 (a b : Nat) (hab : a ∣ b) (hba : b ∣ a) : a = b := by
  obtain ⟨c1, hc1⟩ := hab
  obtain ⟨c2, hc2⟩ := hba
  by_cases ha : a = 0
  · subst ha; rw [Nat.zero_mul] at hc1; exact hc1.symm
  · rw [hc1, mul_assoc_213] at hc2
    have h2 : a * 1 = a * (c1 * c2) := by rw [Nat.mul_one]; exact hc2
    have hc12 : 1 = c1 * c2 :=
      Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_ne_zero ha) h2
    have hc1_eq : c1 = 1 := mul_eq_one_left c1 c2 hc12.symm
    rw [hc1, hc1_eq, Nat.mul_one]

/-- ★★★★★★ **`gcd213` is symmetric**: `gcd213 a b = gcd213 b a`. -/
theorem gcd213_comm (a b : Nat) : gcd213 a b = gcd213 b a := by
  apply dvd_antisymm_213
  · exact gcd213_greatest b a (gcd213 a b)
      (gcd213_dvd_right a b) (gcd213_dvd_left a b)
  · exact gcd213_greatest a b (gcd213 b a)
      (gcd213_dvd_right b a) (gcd213_dvd_left b a)

end E213.Lib.Math.NatHelpers.Gcd213

namespace E213.Lib.Math.NatHelpers.Gcd213

open E213.Tactic.Nat213 (gcd213)

/-- ★★★★★ **`gcd213 a a = a`**.  ∅-axiom. -/
theorem gcd213_self (a : Nat) : gcd213 a a = a := by
  apply dvd_antisymm_213
  · exact gcd213_dvd_left a a
  · exact gcd213_greatest a a a ⟨1, (Nat.mul_one _).symm⟩ ⟨1, (Nat.mul_one _).symm⟩

/-- ★★★★★ **Euclidean step**: `0 < a → gcd213 a b = gcd213 (b % a) a`.
    ∅-axiom. -/
theorem gcd213_rec (a b : Nat) (ha : 0 < a) : gcd213 a b = gcd213 (b % a) a := by
  apply dvd_antisymm_213
  · -- gcd213 a b ∣ gcd213 (b % a) a: gcd213 a b divides both a and (b % a)
    apply gcd213_greatest
    · exact dvd_mod_via_fuel b a b _ ha (Nat.le_refl b)
        (gcd213_dvd_left a b) (gcd213_dvd_right a b)
    · exact gcd213_dvd_left a b
  · -- gcd213 (b % a) a ∣ gcd213 a b: divides both a and b (the latter via g_dvd_b_via_mod)
    apply gcd213_greatest
    · exact gcd213_dvd_right (b % a) a
    · exact g_dvd_b_via_mod b a b _ ha (Nat.le_refl b)
        (gcd213_dvd_right (b % a) a) (gcd213_dvd_left (b % a) a)

end E213.Lib.Math.NatHelpers.Gcd213

namespace E213.Lib.Math.NatHelpers.Gcd213

open E213.Tactic.Nat213 (gcd213 sub_add_cancel)

/-- `g ∣ x ∧ g ∣ y → g ∣ (x + y)`.  ∅-axiom. -/
theorem dvd_add_213 (g x y : Nat) (hx : g ∣ x) (hy : g ∣ y) : g ∣ (x + y) := by
  obtain ⟨c1, hc1⟩ := hx
  obtain ⟨c2, hc2⟩ := hy
  exact ⟨c1 + c2, by rw [hc1, hc2, Nat.mul_add]⟩

/-- ★★★★★ **Subtraction step**: `k ≤ m → gcd213 m k = gcd213 (m - k) k`.
    ∅-axiom.  Standard proof via `dvd_antisymm` + `dvd_sub_213` +
    `dvd_add_213`. -/
theorem gcd213_sub_left (m k : Nat) (h : k ≤ m) :
    gcd213 m k = gcd213 (m - k) k := by
  apply dvd_antisymm_213
  · apply gcd213_greatest
    · exact dvd_sub_213 k m _ h (gcd213_dvd_right m k) (gcd213_dvd_left m k)
    · exact gcd213_dvd_right m k
  · apply gcd213_greatest
    · have h_sum : (m - k) + k = m := sub_add_cancel h
      have h1 : gcd213 (m - k) k ∣ ((m - k) + k) :=
        dvd_add_213 _ (m - k) k (gcd213_dvd_left (m - k) k)
          (gcd213_dvd_right (m - k) k)
      rw [h_sum] at h1
      exact h1
    · exact gcd213_dvd_right (m - k) k

end E213.Lib.Math.NatHelpers.Gcd213

namespace E213.Lib.Math.NatHelpers.Gcd213

open E213.Tactic.Nat213 (gcd213)

/-- `(k + 1) - k = 1` term-mode (∅-axiom).
    Lean-core `Nat.add_sub_cancel_left` brings `propext`. -/
theorem succ_sub_self_213 : ∀ (k : Nat), k + 1 - k = 1
  | 0 => rfl
  | k+1 => by
    show (k + 1) + 1 - (k + 1) = 1
    rw [Nat.succ_sub_succ_eq_sub]
    exact succ_sub_self_213 k

/-- ★★★★★ **`gcd213 1 k = 1`**.  ∅-axiom. -/
theorem gcd213_one_left (k : Nat) : gcd213 1 k = 1 := by
  apply dvd_antisymm_213
  · exact gcd213_dvd_left 1 k
  · exact ⟨gcd213 1 k, (Nat.one_mul _).symm⟩

/-- ★★★★★ **`gcd213 (k + 1) k = 1`**: consecutive integers are
    coprime.  ∅-axiom (uses `gcd213_sub_left` + `succ_sub_self_213`
    + `gcd213_one_left`). -/
theorem gcd213_succ_self (k : Nat) : gcd213 (k + 1) k = 1 := by
  rw [gcd213_sub_left (k+1) k (Nat.le_succ k)]
  rw [succ_sub_self_213 k]
  exact gcd213_one_left k

end E213.Lib.Math.NatHelpers.Gcd213
