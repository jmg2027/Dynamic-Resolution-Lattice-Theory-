import E213.Meta.Nat.PureNat

/-!
# Meta.Nat.FloorLog — the natural floor-logarithm `⌊log_p N⌋`

`floorLog p N` = the largest `f` with `pᶠ ≤ N` (a downward search mirroring
`Meta/Nat/Valuation.vpSearch`).  Its sandwich `p^{floorLog} ≤ N < p^{floorLog+1}`
(`floorLog_pow_le`, `lt_pow_floorLog_succ`) is the ∅-axiom inverse of `Nat.pow`:
where `pow` is the iterated-`×` exponential, `floorLog` is the depth count — the
finite skeleton under the continuous `ln`.

Generic `Nat` infrastructure (no primes, no lcm).  Consumers: the lcm-growth
Chebyshev brick (`Lib/Math/NumberTheory/LcmGrowthChebyshev`) and the
central-binomial Chebyshev count bound (`Lens/Number/Nat213/MultSystemValue`).

All ∅-axiom.
-/

namespace E213.Meta.Nat.FloorLog

open E213.Meta.Nat.PureNat (lt_two_pow)

/-! ### General-base power monotonicity (no `Nat.pow_lt_pow_right` in core) -/

/-- `k < pᵏ` for `p ≥ 2`. -/
theorem lt_pow_self {p : Nat} (hp : 2 ≤ p) (k : Nat) : k < p ^ k :=
  Nat.lt_of_lt_of_le (lt_two_pow k) (Nat.pow_le_pow_left hp k)

/-- `pᵃ < pᵃ⁺¹` for `p ≥ 2`. -/
theorem pow_lt_succ_self {p : Nat} (hp : 2 ≤ p) (a : Nat) : p ^ a < p ^ (a + 1) := by
  have hpa : 0 < p ^ a := Nat.pos_pow_of_pos a (Nat.lt_of_lt_of_le (by decide) hp)
  rw [Nat.pow_succ]
  calc p ^ a < p ^ a + p ^ a := Nat.lt_add_of_pos_right hpa
    _ = p ^ a * 2 := (Nat.mul_two (p ^ a)).symm
    _ ≤ p ^ a * p := Nat.mul_le_mul_left (p ^ a) hp

/-- `a < b → pᵃ < pᵇ` for `p ≥ 2`. -/
theorem pow_lt_pow_of_lt {p a b : Nat} (hp : 2 ≤ p) (h : a < b) : p ^ a < p ^ b :=
  Nat.lt_of_lt_of_le (pow_lt_succ_self hp a)
    (Nat.pow_le_pow_right (Nat.lt_of_lt_of_le (by decide) hp) (Nat.succ_le_of_lt h))

/-- `pᵃ < pᵇ → a < b` for `p ≥ 2`. -/
theorem lt_of_pow_lt_pow {p a b : Nat} (hp : 2 ≤ p) (h : p ^ a < p ^ b) : a < b := by
  rcases Nat.lt_or_ge a b with hlt | hge
  · exact hlt
  · exact absurd h (Nat.not_lt.mpr (Nat.pow_le_pow_right (Nat.lt_of_lt_of_le (by decide) hp) hge))

/-! ### The floor-log search -/

/-- Largest `f ≤ b` with `pᶠ ≤ N` (downward search; mirror of `vpSearch`). -/
def floorLogSearch (p N : Nat) : Nat → Nat
  | 0 => 0
  | f + 1 => if p ^ (f + 1) ≤ N then f + 1 else floorLogSearch p N f

/-- `floorLog p N` = largest `f` with `pᶠ ≤ N`. -/
def floorLog (p N : Nat) : Nat := floorLogSearch p N N

private theorem floorLogSearch_pow_le {p N : Nat} (hN : 1 ≤ N) :
    ∀ b, p ^ (floorLogSearch p N b) ≤ N
  | 0 => by show p ^ 0 ≤ N; rw [Nat.pow_zero]; exact hN
  | b + 1 => by
      show p ^ (floorLogSearch p N (b + 1)) ≤ N
      unfold floorLogSearch
      by_cases h : p ^ (b + 1) ≤ N
      · rw [if_pos h]; exact h
      · rw [if_neg h]; exact floorLogSearch_pow_le hN b

private theorem floorLogSearch_le (p N : Nat) : ∀ b, floorLogSearch p N b ≤ b
  | 0 => Nat.le_refl 0
  | b + 1 => by
      unfold floorLogSearch
      by_cases h : p ^ (b + 1) ≤ N
      · rw [if_pos h]; exact Nat.le_refl _
      · rw [if_neg h]; exact Nat.le_succ_of_le (floorLogSearch_le p N b)

private theorem floorLogSearch_ge {p N : Nat} :
    ∀ b f, f ≤ b → p ^ f ≤ N → f ≤ floorLogSearch p N b
  | 0,     f, hf, _    => hf
  | b + 1, f, hf, hpow => by
      unfold floorLogSearch
      by_cases h : p ^ (b + 1) ≤ N
      · rw [if_pos h]; exact hf
      · rw [if_neg h]
        have hfb : f ≤ b := by
          rcases Nat.lt_or_eq_of_le hf with hlt | heq
          · exact Nat.le_of_lt_succ hlt
          · exact absurd (heq ▸ hpow) h
        exact floorLogSearch_ge b f hfb hpow

/-- `p^{floorLog p N} ≤ N` (`N ≥ 1`). -/
theorem floorLog_pow_le {p N : Nat} (hN : 1 ≤ N) : p ^ (floorLog p N) ≤ N :=
  floorLogSearch_pow_le hN N

/-- `floorLog p N ≤ N`. -/
theorem floorLog_le {p N : Nat} : floorLog p N ≤ N := floorLogSearch_le p N N

/-- `pᶠ ≤ N → f ≤ floorLog p N` (`p ≥ 2`). -/
theorem floorLog_ge {p N f : Nat} (hp : 2 ≤ p) (hpow : p ^ f ≤ N) : f ≤ floorLog p N :=
  floorLogSearch_ge N f (Nat.le_of_lt (Nat.lt_of_lt_of_le (lt_pow_self hp f) hpow)) hpow

/-- The upper sandwich: `N < p^{floorLog p N + 1}` (`p ≥ 2`). -/
theorem lt_pow_floorLog_succ {p N : Nat} (hp : 2 ≤ p) : N < p ^ (floorLog p N + 1) := by
  rcases Nat.lt_or_ge N (p ^ (floorLog p N + 1)) with h | h
  · exact h
  · exact absurd (floorLog_ge hp h) (Nat.not_le.mpr (Nat.lt_succ_self _))

/-- The indicator bridge: `p^{e+1} ≤ N ↔ e < floorLog p N` (`p ≥ 2`, `N ≥ 1`). -/
theorem pow_le_iff_lt_floorLog {p N : Nat} (hp : 2 ≤ p) (hN : 1 ≤ N) (e : Nat) :
    p ^ (e + 1) ≤ N ↔ e < floorLog p N := by
  constructor
  · intro h
    exact Nat.lt_of_succ_lt_succ
      (lt_of_pow_lt_pow hp (Nat.lt_of_le_of_lt h (lt_pow_floorLog_succ hp)))
  · intro h
    exact Nat.le_trans
      (Nat.pow_le_pow_right (Nat.lt_of_lt_of_le (by decide) hp) h) (floorLog_pow_le hN)

end E213.Meta.Nat.FloorLog
