import E213.Meta.Tactic.Pow213
import E213.Meta.Nat.PureNat
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.NatDiv213
import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.PolyNatMTactic

/-!
# Valuation — the `q`-adic valuation `vp q n` over `ℕ`, ∅-axiom

`vp q n` = the largest `k` with `qᵏ ∣ n` (a downward search, like `findOrd`).  The prime-power
infrastructure for the primitive-root marathon's brick 4b.  The search decides on `n % qᵏ = 0`
(structural `decEq`) — the `Decidable (· ∣ ·)` instance and the core `Nat` dvd/mod API both carry
`propext`, so all divisibility runs through the repo's pure helpers.

  * ★ `pow_vp_dvd` — `q^(vp q n) ∣ n`.
  * ★ `vp_ge` — `qᵏ ∣ n ⟹ k ≤ vp q n` (for `k ≤ n`).
  * ★★ `vp_not_dvd_succ` — `q^(vp q n + 1) ∤ n` (exactness, `q ≥ 2`, `n > 0`).
  * `le_vp_iff` — `qᵏ ∣ n ⟺ k ≤ vp q n`.

All ∅-axiom.
-/

namespace E213.Meta.Nat.Valuation

open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Meta.Nat.PureNat (lt_two_pow)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero div_add_mod)
open E213.Meta.Nat.NatDiv213 (mul_div_cancel_left_pure)
open E213.Tactic.NatHelper (add_left_cancel_pure)

/-! ## §0 — pure divisibility helpers (core `Nat.dvd_*` carry `propext`) -/

theorem drefl (a : Nat) : a ∣ a := ⟨1, (Nat.mul_one a).symm⟩

theorem dtrans {a b c : Nat} (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  obtain ⟨x, hx⟩ := h1; obtain ⟨y, hy⟩ := h2
  exact ⟨x * y, by rw [hy, hx]; ring_nat⟩

/-- `m ∣ n ⟹ n % m = 0` (`m > 0`).  ∅-axiom (core `Nat.mod_eq_zero_of_dvd` carries `propext`). -/
theorem mod_zero_of_dvd {m n : Nat} (hm : 0 < m) (h : m ∣ n) : n % m = 0 := by
  obtain ⟨c, hc⟩ := h
  rw [hc]
  have hd : m * (m * c / m) + (m * c) % m = m * c := div_add_mod (m * c) m
  rw [mul_div_cancel_left_pure m c hm] at hd
  have hd' : m * c + (m * c) % m = m * c + 0 := by rw [Nat.add_zero]; exact hd
  exact add_left_cancel_pure hd'

/-- `qᵏ ∣ q^(k+j)`. -/
theorem pow_dvd_add (q k : Nat) : ∀ j, q ^ k ∣ q ^ (k + j)
  | 0     => drefl _
  | j + 1 => by
    rw [show k + (j + 1) = (k + j) + 1 from rfl, Nat.pow_succ]
    exact dtrans (pow_dvd_add q k j) (Nat.dvd_mul_right _ _)

theorem pow_dvd_of_le (q : Nat) {k m : Nat} (h : k ≤ m) : q ^ k ∣ q ^ m := by
  obtain ⟨j, hj⟩ := Nat.le.dest h; rw [← hj]; exact pow_dvd_add q k j

/-! ## §1 — the search -/

/-- Downward search for the largest `k ≤ b` with `qᵏ ∣ n` (decides on `n % qᵏ = 0`). -/
def vpSearch (q n : Nat) : Nat → Nat
  | 0     => 0
  | k + 1 => if n % q ^ (k + 1) = 0 then k + 1 else vpSearch q n k

/-- The `q`-adic valuation of `n`: the largest `k` with `qᵏ ∣ n`. -/
def vp (q n : Nat) : Nat := vpSearch q n n

theorem vpSearch_dvd (q n : Nat) : ∀ b, q ^ (vpSearch q n b) ∣ n
  | 0     => ⟨n, (Nat.one_mul n).symm⟩
  | b + 1 => by
    show q ^ (vpSearch q n (b + 1)) ∣ n
    unfold vpSearch
    by_cases h : n % q ^ (b + 1) = 0
    · rw [if_pos h]; exact dvd_of_mod_eq_zero h
    · rw [if_neg h]; exact vpSearch_dvd q n b

theorem vpSearch_le (q n : Nat) : ∀ b, vpSearch q n b ≤ b
  | 0     => Nat.le_refl 0
  | b + 1 => by
    unfold vpSearch
    by_cases h : n % q ^ (b + 1) = 0
    · rw [if_pos h]; exact Nat.le_refl _
    · rw [if_neg h]; exact Nat.le_succ_of_le (vpSearch_le q n b)

theorem vpSearch_ge (q n : Nat) (hq : 2 ≤ q) :
    ∀ b k, k ≤ b → q ^ k ∣ n → k ≤ vpSearch q n b
  | 0,     k, hk, _ => Nat.le_trans hk (Nat.le_refl 0)
  | b + 1, k, hk, h => by
    unfold vpSearch
    by_cases hc : n % q ^ (b + 1) = 0
    · rw [if_pos hc]; exact hk
    · rw [if_neg hc]
      have hkb : k ≤ b := by
        rcases Nat.lt_or_eq_of_le hk with hlt | heq
        · exact Nat.le_of_lt_succ hlt
        · subst heq
          exact absurd (mod_zero_of_dvd
            (Nat.pos_pow_of_pos (b + 1) (Nat.lt_of_lt_of_le (by decide : (0:Nat) < 2) hq)) h) hc
      exact vpSearch_ge q n hq b k hkb h

/-! ## §2 — `vp` laws -/

theorem pow_vp_dvd (q n : Nat) : q ^ (vp q n) ∣ n := vpSearch_dvd q n n

theorem vp_ge (q n k : Nat) (hq : 2 ≤ q) (hk : k ≤ n) (h : q ^ k ∣ n) : k ≤ vp q n :=
  vpSearch_ge q n hq n k hk h

theorem vp_lt (q n : Nat) (hq : 2 ≤ q) (hn : 0 < n) : vp q n < n := by
  rcases Nat.lt_or_ge (vp q n) n with hlt | hge
  · exact hlt
  · exfalso
    have hvpe : vp q n = n := Nat.le_antisymm (vpSearch_le q n n) hge
    have hdvd : q ^ n ∣ n := by have hd := pow_vp_dvd q n; rwa [hvpe] at hd
    have hqn : n < q ^ n :=
      Nat.lt_of_lt_of_le (lt_two_pow n) (Nat.pow_le_pow_left hq n)
    exact absurd (le_of_dvd_pos (q ^ n) n hn hdvd) (Nat.not_le.mpr hqn)

theorem vp_not_dvd_succ (q n : Nat) (hq : 2 ≤ q) (hn : 0 < n) : ¬ q ^ (vp q n + 1) ∣ n := by
  intro h
  have hle : vp q n + 1 ≤ n := vp_lt q n hq hn
  exact absurd (vp_ge q n (vp q n + 1) hq hle h) (Nat.not_succ_le_self (vp q n))

theorem le_vp_iff (q n k : Nat) (hq : 2 ≤ q) (hn : 0 < n) : q ^ k ∣ n ↔ k ≤ vp q n := by
  constructor
  · intro h
    rcases Nat.lt_or_ge k n with hkn | hkn
    · exact vp_ge q n k hq (Nat.le_of_lt hkn) h
    · exfalso
      have hqk : n < q ^ k :=
        Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (lt_two_pow n) (Nat.pow_le_pow_left hq n))
          (Nat.pow_le_pow_right (Nat.le_trans (by decide) hq) hkn)
      exact absurd (le_of_dvd_pos (q ^ k) n hn h) (Nat.not_le.mpr hqk)
  · intro h
    exact dtrans (pow_dvd_of_le q h) (pow_vp_dvd q n)

end E213.Meta.Nat.Valuation
