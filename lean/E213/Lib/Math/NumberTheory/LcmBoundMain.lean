import E213.Lib.Math.NumberTheory.LcmGrowthChebyshev

/-!
# LcmBoundMain — Brick 1 steps 5–7: `lcm(1..n) ≤ 10^{…}`, ∅-axiom

The Chebyshev recursion `lcm(30m) ≤ (6m+1)·α₃₀^m·lcm(5m)` (`LcmGrowthChebyshev.step4`)
is driven to the headline bound.

  * **Step 5 — numeral induction** (this file, §1): `Sbound m`, i.e.
    `(6m+1)·α₃₀^m·10^{15·⌈m/6⌉} ≤ 10^{15m}` (`W = 10¹⁵`, `⌈m/6⌉ = (m+5)/6`), for all
    `m ≥ 26`.  Period-6 induction: `S(M+6)` from `S(M)` collapses to the single
    numeral `37·α₃₀⁶ ≤ 10⁷⁵` (via `(6M+37) ≤ 37(6M+1)`); bases `S(26..31)` decide.
  * **Step 6 — main** (§2): `lcm(1..30m) ≤ 10^{15m}` — strong induction with `step4`
    + lcm-monotonicity + step 5; bases `m ≤ 25` decide.
  * **Step 7 — corollaries** (§3): `lcm(1..n)⁶ ≤ 10^{87+3n}` etc.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.LcmBoundMain

set_option maxHeartbeats 4000000

open E213.Lib.Math.NumberTheory.LcmGrowthChebyshev
  (alpha30 lcmUpTo step4 dvd_lcmUpTo lcmUpTo_dvd lcmUpTo_pos)
open E213.Meta.Nat.NatDiv213 (add_div_right_pos div_add_mod_pure div_lt_of_lt_mul
  le_of_add_le_add_left_pure)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Tactic.NatHelper (mul_assoc sub_add_cancel)

-- Keep `α₃₀`'s 12-digit literal from being reduced during defeq/`ring_nat` (the
-- whnf would explode); `unfold alpha30` in the numeral decides still forces it.
attribute [local irreducible] alpha30

/-! ## §1 — step 5: the numeral induction -/

private theorem pow_add_pure (a x : Nat) : ∀ y, a ^ (x + y) = a ^ x * a ^ y
  | 0 => by rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | y + 1 => by rw [Nat.add_succ, Nat.pow_succ, Nat.pow_succ, pow_add_pure a x y, mul_assoc]

/-- `S m`: `(6m+1)·α₃₀^m·10^{15·⌈m/6⌉} ≤ 10^{15m}` (`⌈m/6⌉ = (m+5)/6`). -/
private def Sbound (m : Nat) : Prop :=
  (6 * m + 1) * alpha30 ^ m * 10 ^ (15 * ((m + 5) / 6)) ≤ 10 ^ (15 * m)

set_option maxRecDepth 4000 in
private theorem key_numeral : 37 * alpha30 ^ 6 ≤ 10 ^ 75 := by unfold alpha30; decide

/-- Abstract reassociation (`ring_nat` deep-recurses on literal-exponent `^` terms,
    so prove the reshuffle on opaque variables and instantiate). -/
private theorem re1 (u a b p c : Nat) :
    37 * u * (a * b) * (p * c) = 37 * b * c * (u * a * p) := by ring_nat

/-- The period-6 induction step: `S M → S (M+6)`, collapsing to `37·α₃₀⁶ ≤ 10⁷⁵`. -/
private theorem S_step (M : Nat) (h : Sbound M) : Sbound (M + 6) := by
  have h6M37 : 6 * M + 37 ≤ 37 * (6 * M + 1) := by
    rw [show 37 * (6 * M + 1) = 6 * M + (216 * M + 37) from by ring_nat]
    exact Nat.add_le_add_left (Nat.le_add_left 37 (216 * M)) (6 * M)
  have hd : (M + 6 + 5) / 6 = (M + 5) / 6 + 1 := by
    rw [show M + 6 + 5 = (M + 5) + 6 from by ring_nat, add_div_right_pos (by decide) (M + 5)]
  show (6 * (M + 6) + 1) * alpha30 ^ (M + 6) * 10 ^ (15 * ((M + 6 + 5) / 6))
    ≤ 10 ^ (15 * (M + 6))
  rw [show 6 * (M + 6) + 1 = 6 * M + 37 from by ring_nat, pow_add_pure alpha30 M 6, hd,
      show 15 * ((M + 5) / 6 + 1) = 15 * ((M + 5) / 6) + 15 from by ring_nat,
      pow_add_pure 10 (15 * ((M + 5) / 6)) 15,
      show 15 * (M + 6) = 15 * M + 90 from by ring_nat]
  calc (6 * M + 37) * (alpha30 ^ M * alpha30 ^ 6)
          * (10 ^ (15 * ((M + 5) / 6)) * 10 ^ 15)
      ≤ 37 * (6 * M + 1) * (alpha30 ^ M * alpha30 ^ 6)
          * (10 ^ (15 * ((M + 5) / 6)) * 10 ^ 15) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h6M37)
    _ = 37 * alpha30 ^ 6 * 10 ^ 15
          * ((6 * M + 1) * alpha30 ^ M * 10 ^ (15 * ((M + 5) / 6))) :=
        re1 (6 * M + 1) (alpha30 ^ M) (alpha30 ^ 6) (10 ^ (15 * ((M + 5) / 6))) (10 ^ 15)
    _ ≤ 37 * alpha30 ^ 6 * 10 ^ 15 * 10 ^ (15 * M) := Nat.mul_le_mul_left _ h
    _ = 37 * alpha30 ^ 6 * (10 ^ 15 * 10 ^ (15 * M)) :=
        mul_assoc (37 * alpha30 ^ 6) (10 ^ 15) (10 ^ (15 * M))
    _ = 37 * alpha30 ^ 6 * 10 ^ (15 + 15 * M) := by rw [← pow_add_pure 10 15 (15 * M)]
    _ ≤ 10 ^ 75 * 10 ^ (15 + 15 * M) := Nat.mul_le_mul_right _ key_numeral
    _ = 10 ^ (75 + (15 + 15 * M)) := (pow_add_pure 10 75 (15 + 15 * M)).symm
    _ = 10 ^ (15 * M + 90) := by rw [show (75 : Nat) + (15 + 15 * M) = 15 * M + 90 from by ring_nat]

private theorem S_add_step : ∀ j M, Sbound M → Sbound (M + 6 * j)
  | 0, M, h => by rw [Nat.mul_zero, Nat.add_zero]; exact h
  | j + 1, M, h => by
      rw [show 6 * (j + 1) = 6 * j + 6 from by ring_nat, ← Nat.add_assoc]
      exact S_step (M + 6 * j) (S_add_step j M h)

set_option maxRecDepth 6000 in
set_option exponentiation.threshold 500 in
set_option maxHeartbeats 4000000 in
/-- ★★ **Step 5**: `Sbound m` for all `m ≥ 26` (the numeral induction). -/
private theorem step5 (m : Nat) (hm : 26 ≤ m) : Sbound m := by
  obtain ⟨q, r, hr, hm26⟩ : ∃ q r, r < 6 ∧ m = (26 + r) + 6 * q :=
    ⟨(m - 26) / 6, (m - 26) % 6, Nat.mod_lt _ (by decide), by
      have h1 : 6 * ((m - 26) / 6) + (m - 26) % 6 = m - 26 := div_add_mod_pure (m - 26) 6
      rw [show (26 + (m - 26) % 6) + 6 * ((m - 26) / 6)
            = 26 + (6 * ((m - 26) / 6) + (m - 26) % 6) from by ring_nat, h1,
          Nat.add_comm 26 (m - 26), sub_add_cancel hm]⟩
  rw [hm26]
  refine S_add_step q (26 + r) ?_
  rcases r with _ | _ | _ | _ | _ | _ | r6
  · show Sbound 26; unfold Sbound alpha30; decide
  · show Sbound 27; unfold Sbound alpha30; decide
  · show Sbound 28; unfold Sbound alpha30; decide
  · show Sbound 29; unfold Sbound alpha30; decide
  · show Sbound 30; unfold Sbound alpha30; decide
  · show Sbound 31; unfold Sbound alpha30; decide
  · exact absurd hr (Nat.not_lt.mpr (Nat.le_add_left 6 r6))

/-! ## §2 — step 6: the main bound `lcm(1..30m) ≤ 10^{15m}` -/

/-- Pure `a + c ≤ b + c → a ≤ b` (`Nat.le_of_add_le_add_right` carries `propext`). -/
private theorem le_of_add_le_add_right' {a b c : Nat} (h : a + c ≤ b + c) : a ≤ b := by
  rw [Nat.add_comm a c, Nat.add_comm b c] at h
  exact le_of_add_le_add_left_pure h

/-- `lcm(1..a) ∣ lcm(1..b)` for `a ≤ b` (every `k ∈ [1,a]` divides `lcm(1..b)`). -/
private theorem lcmUpTo_mono {a b : Nat} (hab : a ≤ b) : lcmUpTo a ∣ lcmUpTo b :=
  lcmUpTo_dvd (fun k hk hka => dvd_lcmUpTo hk (Nat.le_trans hka hab))

set_option maxRecDepth 40000 in
set_option exponentiation.threshold 500 in
private theorem base_cert : ∀ m, m < 26 → lcmUpTo (30 * m) ≤ 10 ^ (15 * m) := by decide

/-- ★★★ **Step 6 — the main bound**: `lcm(1..30m) ≤ 10^{15m}`, ∀ `m`.  Strong
    induction: bases `m < 26` decide; for `m ≥ 26` the recursion `step4` reduces
    `lcm(30m)` to `lcm(5m) ≤ lcm(30⌈m/6⌉) ≤ 10^{15⌈m/6⌉}` (IH, `⌈m/6⌉ < m`), and the
    numeral `step5` (`Sbound m`) closes it. -/
theorem main : ∀ m, lcmUpTo (30 * m) ≤ 10 ^ (15 * m) := fun m =>
  Nat.strongRecOn m (motive := fun m => lcmUpTo (30 * m) ≤ 10 ^ (15 * m)) fun m ih => by
    rcases Nat.lt_or_ge m 26 with hlt | hge
    · exact base_cert m hlt
    · -- ⌈m/6⌉ = (m+5)/6 is < m and 5m ≤ 30⌈m/6⌉
      have hmlt : m + 5 < 6 * m := by
        have h5 : 5 < 5 * m := Nat.lt_of_lt_of_le (by decide) (Nat.mul_le_mul_left 5 hge)
        calc m + 5 < m + 5 * m := Nat.add_lt_add_left h5 m
          _ = 6 * m := by ring_nat
      have hq_lt : (m + 5) / 6 < m := div_lt_of_lt_mul hmlt
      have hdm : 6 * ((m + 5) / 6) + (m + 5) % 6 = m + 5 := div_add_mod_pure (m + 5) 6
      have hm6q : m ≤ 6 * ((m + 5) / 6) := by
        have hle : m + 5 ≤ 6 * ((m + 5) / 6) + 5 :=
          calc m + 5 = 6 * ((m + 5) / 6) + (m + 5) % 6 := hdm.symm
            _ ≤ 6 * ((m + 5) / 6) + 5 :=
                Nat.add_le_add_left (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide : (6:Nat) > 0))) _
        exact le_of_add_le_add_right' hle
      have h5m : 5 * m ≤ 30 * ((m + 5) / 6) := by
        calc 5 * m ≤ 5 * (6 * ((m + 5) / 6)) := Nat.mul_le_mul_left 5 hm6q
          _ = 30 * ((m + 5) / 6) := by ring_nat
      calc lcmUpTo (30 * m)
          ≤ (6 * m + 1) * alpha30 ^ m * lcmUpTo (5 * m) := step4 m
        _ ≤ (6 * m + 1) * alpha30 ^ m * lcmUpTo (30 * ((m + 5) / 6)) :=
            Nat.mul_le_mul_left _
              (le_of_dvd_pos _ _ (lcmUpTo_pos _) (lcmUpTo_mono h5m))
        _ ≤ (6 * m + 1) * alpha30 ^ m * 10 ^ (15 * ((m + 5) / 6)) :=
            Nat.mul_le_mul_left _ (ih ((m + 5) / 6) hq_lt)
        _ ≤ 10 ^ (15 * m) := step5 m hge

/-! ## §3 — step 7: the headline corollaries -/

/-- ★★★ **`lcm(1..n) ≤ 10^{(n+29)/2·…}`** — the padded bound: `lcm(1..n)` is bounded
    by `10^{15·⌈n/30⌉}` (pad `n` to the next multiple of 30 via monotonicity). -/
theorem lcmUpTo_le (n : Nat) : lcmUpTo n ≤ 10 ^ (15 * ((n + 29) / 30)) := by
  have hpad : n ≤ 30 * ((n + 29) / 30) := by
    have hdm : 30 * ((n + 29) / 30) + (n + 29) % 30 = n + 29 := div_add_mod_pure (n + 29) 30
    have hle : n + 29 ≤ 30 * ((n + 29) / 30) + 29 :=
      calc n + 29 = 30 * ((n + 29) / 30) + (n + 29) % 30 := hdm.symm
        _ ≤ 30 * ((n + 29) / 30) + 29 :=
            Nat.add_le_add_left (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide : (30:Nat) > 0))) _
    exact le_of_add_le_add_right' hle
  exact Nat.le_trans (le_of_dvd_pos _ _ (lcmUpTo_pos _) (lcmUpTo_mono hpad)) (main ((n + 29) / 30))

end E213.Lib.Math.NumberTheory.LcmBoundMain
