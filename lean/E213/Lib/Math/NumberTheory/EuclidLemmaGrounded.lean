import E213.Meta.Nat.SubBezout213
import E213.Lib.Math.NumberTheory.PrimeValuation

/-!
# Euclid's lemma, grounded — `prime_dvd_mul` via structural Bézout (∅-axiom)

The FTA-uniqueness key: `p` prime, `p ∣ a·b → p ∣ a ∨ p ∣ b`.  The repo already proves this
(`PrimeValuation.prime_dvd_mul`), but through `Gcd213.gcd213`, which uses **`Nat.mod`**
(`lt_wfRel = true`).  This file regrounds it onto the `Nat.mod`/`Nat.div`/`lt_wfRel`-free Bézout
(`SubBezout213.bezout_one_of_coprime`, from `subMod`) + prime coprimality
(`SubGcd213.gcd_eq_one_of_prime_not_dvd`):

  if `p ∤ a` then `gcd(p,a) = 1`, so `∃ x y, p·x = a·y + 1` (or the flipped sign).  Multiplying the
  Bézout identity by `b` and using `p ∣ a·b` gives `p·c₁ = p·c₂ + b`, whence `p ∣ b`.

No `Int`/signed integers (the sign is carried as a `Bool` flag in `egcd`), no `Nat.mod`, no
`Nat.div`, no `Nat.lt_wfRel`.  ∅-axiom.  This closes the last conceptual gap to a fully grounded FTA
*uniqueness* (`vp` multiplicativity on top is mechanical).
-/

namespace E213.Lib.Math.NumberTheory.EuclidLemmaGrounded

open E213.Meta.Nat.SubGcd213 (gcdW gcdW_dvd_left gcdW_dvd_right)
open E213.Meta.Nat.SubBezout213 (bezout_one_of_coprime)
open E213.Meta.Nat.SubMod213 (le_add_cancel_left)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)

/-! ## §1 — clean cancellation / divisibility helpers (no propext) -/

/-- Right-cancellation of `+`, propext-free (core `Nat.add_right_cancel` leaks propext).  Two `≤`s
    via the clean left-cancel `le_add_cancel_left` + antisymmetry. -/
private theorem add_right_cancel' {a b c : Nat} (h : a + c = b + c) : a = b := by
  apply Nat.le_antisymm
  · exact le_add_cancel_left c (by rw [Nat.add_comm c a, Nat.add_comm c b]; exact Nat.le_of_eq h)
  · exact le_add_cancel_left c (by rw [Nat.add_comm c a, Nat.add_comm c b]; exact Nat.le_of_eq h.symm)

/-- **Divisibility of the difference.**  From `p·c₁ = p·c₂ + b` with `0 < p`, `p ∣ b` — witness
    `c₁ - c₂` (valid since `p·c₂ ≤ p·c₁` cancels to `c₂ ≤ c₁`).  No Nat-subtraction leak (`subMod`-
    style `sub_add_cancel`), propext-free. -/
private theorem dvd_of_pmul_eq {p c1 c2 b : Nat} (hp : 0 < p) (h : p * c1 = p * c2 + b) : p ∣ b := by
  have hle0 : p * c2 ≤ p * c1 := by rw [h]; exact Nat.le_add_right (p * c2) b
  have hc2c1 : c2 ≤ c1 := Nat.le_of_mul_le_mul_left hle0 hp
  refine ⟨c1 - c2, ?_⟩
  apply add_right_cancel' (c := p * c2)
  rw [← Nat.mul_add, E213.Tactic.NatHelper.sub_add_cancel hc2c1, Nat.add_comm b (p * c2)]
  exact h.symm

/-- `a·y·b = p·(k·y)` from `a·b = p·k` (associativity/commutativity shuffle, propext-free). -/
private theorem mul_shuffle {a b y p k : Nat} (hk : a * b = p * k) : a * y * b = p * (k * y) := by
  calc a * y * b = a * (y * b) := E213.Tactic.NatHelper.mul_assoc a y b
    _ = a * (b * y) := by rw [Nat.mul_comm y b]
    _ = a * b * y := (E213.Tactic.NatHelper.mul_assoc a b y).symm
    _ = p * k * y := by rw [hk]
    _ = p * (k * y) := E213.Tactic.NatHelper.mul_assoc p k y

/-! ## §2 — Euclid's lemma -/

/-- ★★★ **Euclid's lemma, grounded.**  `p` prime, `p ∣ a·b → p ∣ a ∨ p ∣ b`.  If `p ∤ a` then
    `gcd(p,a)=1` (`gcd_eq_one_of_prime_not_dvd`), giving a structural Bézout witness
    (`bezout_one_of_coprime`); multiplying by `b` and folding in `p ∣ a·b` forces `p ∣ b`.  Bézout
    via `subMod` — no `Nat.mod`/`Nat.div`/`Nat.lt_wfRel`, no `Int`.  ∅-axiom. -/
theorem prime_dvd_mul {p a b : Nat} (hp : Prime213 p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  -- `gcd(p,a) ∣ p`, and `p` prime ⟹ `gcd(p,a) = 1` or `= p`.  Casing on *this* avoids the
  -- `Decidable (p ∣ a)` instance (which would drag in `Nat.mod`).
  rcases hp.2 (gcdW p a) (gcdW_dvd_left p a) with hcop | hgp
  case inr =>
    -- gcd(p,a) = p ⟹ p ∣ a
    exact Or.inl (hgp ▸ gcdW_dvd_right p a)
  case inl =>
    -- gcd(p,a) = 1 ⟹ Bézout ⟹ p ∣ b
    refine Or.inr ?_
    have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
    obtain ⟨k, hk⟩ := h                              -- a * b = p * k
    obtain ⟨x, y, hxy⟩ := bezout_one_of_coprime hcop -- p*x = a*y+1  ∨  a*y = p*x+1
    cases hxy with
    | inl hpx =>
      have e : p * (x * b) = p * (k * y) + b := by
        calc p * (x * b) = p * x * b := (E213.Tactic.NatHelper.mul_assoc p x b).symm
          _ = (a * y + 1) * b := by rw [hpx]
          _ = a * y * b + 1 * b := E213.Tactic.NatHelper.add_mul (a * y) 1 b
          _ = p * (k * y) + b := by rw [mul_shuffle hk, Nat.one_mul]
      exact dvd_of_pmul_eq hp0 e
    | inr hpx =>
      have e : p * (k * y) = p * (x * b) + b := by
        calc p * (k * y) = a * y * b := (mul_shuffle hk).symm
          _ = (p * x + 1) * b := by rw [hpx]
          _ = p * x * b + 1 * b := E213.Tactic.NatHelper.add_mul (p * x) 1 b
          _ = p * (x * b) + b := by rw [E213.Tactic.NatHelper.mul_assoc p x b, Nat.one_mul]
      exact dvd_of_pmul_eq hp0 e

end E213.Lib.Math.NumberTheory.EuclidLemmaGrounded
