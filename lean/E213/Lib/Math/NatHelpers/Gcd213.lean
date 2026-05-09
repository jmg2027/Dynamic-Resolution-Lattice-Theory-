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
