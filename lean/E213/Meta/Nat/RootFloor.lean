import E213.Meta.Nat.PowBasic

/-!
# RootFloor — the integer `s`-th root, floor reading

`rootFloor s x` is the largest `r ≤ x` with `r^s ≤ x` — the `Nat`-native floor
reading of the `s`-th root.  Bounded descent (`rootFloorGo`), characterized by
the sandwich

    (rootFloor s x)^s ≤ x < (rootFloor s x + 1)^s        (1 ≤ s, 1 ≤ x)

(`rootFloor_pow_le` / `rootFloor_succ_pow_gt`), calibrated exactly on powers
(`rootFloor_pow : rootFloor s (k^s) = k`), monotone in the radicand
(`rootFloor_mono`).

Companion to `ModulusComposition.rootCeil` (the ceiling reading); this floor
reading is the probe schedule of the graded rate generator
(`Real213/RateModulus.graded_total_modulus`): probe denominator `k` is admitted
at schedule layer `k^s`, and `rootFloor s` is that schedule read back from the
layer index.

All zero-axiom.
-/

namespace E213.Meta.Nat.RootFloor

open E213.Meta.Nat.PowBasic (powBase_le powBase_lt one_le_pow self_le_pow one_pow_pure)

/-- Bounded descent: largest `r ≤ F` with `r^s ≤ x` (`0` if none). -/
def rootFloorGo (s x : Nat) : Nat → Nat
  | 0 => 0
  | r+1 => cond (decide ((r+1)^s ≤ x)) (r+1) (rootFloorGo s x r)

/-- The integer `s`-th root, floor reading: largest `r ≤ x` with `r^s ≤ x`. -/
def rootFloor (s x : Nat) : Nat := rootFloorGo s x x

theorem rootFloorGo_le (s x : Nat) : ∀ F, rootFloorGo s x F ≤ F
  | 0 => Nat.le_refl 0
  | F+1 => by
      show (cond (decide ((F+1)^s ≤ x)) (F+1) (rootFloorGo s x F)) ≤ F+1
      by_cases h : (F+1)^s ≤ x
      · rw [decide_eq_true h]; exact Nat.le_refl _
      · rw [decide_eq_false h]
        exact Nat.le_trans (rootFloorGo_le s x F) (Nat.le_succ F)

theorem le_rootFloorGo (s x r : Nat) (hr : r^s ≤ x) :
    ∀ F, r ≤ F → r ≤ rootFloorGo s x F
  | 0, hF => hF
  | F+1, hF => by
      show r ≤ cond (decide ((F+1)^s ≤ x)) (F+1) (rootFloorGo s x F)
      by_cases h : (F+1)^s ≤ x
      · rw [decide_eq_true h]; exact hF
      · rw [decide_eq_false h]
        have hrF : r ≤ F := by
          rcases Nat.lt_or_ge r (F+1) with h' | h'
          · exact Nat.le_of_lt_succ h'
          · exact absurd (Nat.le_trans (powBase_le h' s) hr) h
        exact le_rootFloorGo s x r hr F hrF

theorem rootFloorGo_pow_le (s x : Nat) :
    ∀ F, 1 ≤ rootFloorGo s x F → (rootFloorGo s x F)^s ≤ x
  | 0, h => absurd h (by intro hc; exact absurd hc (Nat.not_succ_le_zero 0))
  | F+1, h => by
      by_cases hc : (F+1)^s ≤ x
      · rw [show rootFloorGo s x (F+1) = F+1 from by
              show cond (decide ((F+1)^s ≤ x)) _ _ = _
              rw [decide_eq_true hc]; rfl]
        exact hc
      · rw [show rootFloorGo s x (F+1) = rootFloorGo s x F from by
              show cond (decide ((F+1)^s ≤ x)) _ _ = _
              rw [decide_eq_false hc]; rfl] at h ⊢
        exact rootFloorGo_pow_le s x F h

theorem rootFloor_le (s x : Nat) : rootFloor s x ≤ x := rootFloorGo_le s x x

theorem rootFloor_pos (s x : Nat) (hx : 1 ≤ x) : 1 ≤ rootFloor s x :=
  le_rootFloorGo s x 1 (by rw [one_pow_pure s]; exact hx) x hx

/-- Lower half of the sandwich: the root's power stays below the radicand. -/
theorem rootFloor_pow_le (s x : Nat) (h : 1 ≤ rootFloor s x) :
    (rootFloor s x)^s ≤ x :=
  rootFloorGo_pow_le s x x h

/-- Upper half of the sandwich: the next candidate's power exceeds the radicand. -/
theorem rootFloor_succ_pow_gt (s : Nat) (hs : 1 ≤ s) (x : Nat) :
    x < (rootFloor s x + 1)^s := by
  rcases Nat.lt_or_ge x ((rootFloor s x + 1)^s) with h | h
  · exact h
  · have hb : rootFloor s x + 1 ≤ x := Nat.le_trans (self_le_pow _ hs) h
    have hself : rootFloor s x + 1 ≤ rootFloor s x :=
      le_rootFloorGo s x (rootFloor s x + 1) h x hb
    exact absurd hself (Nat.not_succ_le_self _)

/-- Calibration: the floor root inverts an exact power. -/
theorem rootFloor_pow (s : Nat) (hs : 1 ≤ s) (k : Nat) : rootFloor s (k^s) = k := by
  have hk_le : k ≤ rootFloor s (k^s) :=
    le_rootFloorGo s (k^s) k (Nat.le_refl _) (k^s) (self_le_pow k hs)
  have hle : rootFloor s (k^s) ≤ k := by
    rcases Nat.lt_or_ge k (rootFloor s (k^s)) with h | h
    · have h1 : 1 ≤ rootFloor s (k^s) := Nat.lt_of_le_of_lt (Nat.zero_le k) h
      have h2 : (rootFloor s (k^s))^s ≤ k^s := rootFloor_pow_le s (k^s) h1
      exact absurd h2 (Nat.not_le.mpr (powBase_lt h hs))
    · exact h
  exact Nat.le_antisymm hle hk_le

/-- The floor root is monotone in the radicand. -/
theorem rootFloor_mono (s : Nat) {x y : Nat} (hxy : x ≤ y) :
    rootFloor s x ≤ rootFloor s y := by
  rcases Nat.lt_or_ge 0 (rootFloor s x) with hpos | hz
  · have hp : (rootFloor s x)^s ≤ y := Nat.le_trans (rootFloor_pow_le s x hpos) hxy
    have hb : rootFloor s x ≤ y := Nat.le_trans (rootFloor_le s x) hxy
    exact le_rootFloorGo s y (rootFloor s x) hp y hb
  · exact Nat.le_trans hz (Nat.zero_le _)

end E213.Meta.Nat.RootFloor
