import E213.Lib.Math.NumberTheory.ModArith.MulOrder
import E213.Meta.Tactic.Pow213

/-!
# MaxOrder — the maximum multiplicative order mod `p` (exponent-argument scaffolding)

Brick 4a of the primitive-root marathon: the maximum of `ordModP a p` over the units
`a ∈ [1, p−1]`.  The routine, reusable scaffolding of the exponent argument — the hard core
("every order divides `maxOrd`", via the coprime lcm decomposition) is brick 4b.

  * `maxOrd_ge` — every unit's order is `≤ maxOrd`.
  * ★★ `maxOrd_achieved` — `maxOrd` is `ordModP g p` for some unit `g ∈ [1, p−1]`.
  * `one_le_maxOrd`, `maxOrd_le_pred` — `1 ≤ maxOrd ≤ p − 1`.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.MaxOrder

open E213.Lib.Math.NumberTheory.ModArith.MulOrder (ordModP ord_pos ord_dvd_p_sub_one)
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-- Pure binary max (core `Nat.max` lemmas carry `propext`). -/
def nmax (a b : Nat) : Nat := if a ≤ b then b else a

theorem le_nmax_left (a b : Nat) : a ≤ nmax a b := by
  unfold nmax; by_cases h : a ≤ b
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact Nat.le_refl a

theorem le_nmax_right (a b : Nat) : b ≤ nmax a b := by
  unfold nmax; by_cases h : a ≤ b
  · rw [if_pos h]; exact Nat.le_refl b
  · rw [if_neg h]; exact Nat.le_of_lt (Nat.lt_of_not_le h)

theorem nmax_le {a b c : Nat} (ha : a ≤ c) (hb : b ≤ c) : nmax a b ≤ c := by
  unfold nmax; by_cases h : a ≤ b
  · rw [if_pos h]; exact hb
  · rw [if_neg h]; exact ha

/-- Max of `ordModP a p` over `a ∈ [1, n]`. -/
def maxOrdAux (p : Nat) : Nat → Nat
  | 0     => 0
  | a + 1 => nmax (ordModP (a + 1) p) (maxOrdAux p a)

/-- The maximum multiplicative order mod `p` (over the units `[1, p−1]`). -/
def maxOrd (p : Nat) : Nat := maxOrdAux p (p - 1)

/-- Every order with index `≤ n` is `≤ maxOrdAux p n`. -/
theorem maxOrdAux_ge (p : Nat) : ∀ (n a : Nat), 1 ≤ a → a ≤ n → ordModP a p ≤ maxOrdAux p n
  | 0,     _, _,   ha => absurd (Nat.le_trans (by assumption) ha) (by decide)
  | n + 1, a, ha1, ha => by
    rcases Nat.lt_or_eq_of_le ha with hlt | heq
    · exact Nat.le_trans (maxOrdAux_ge p n a ha1 (Nat.le_of_lt_succ hlt)) (le_nmax_right _ _)
    · rw [heq]; exact le_nmax_left _ _

/-- ★ **Every unit's order is `≤ maxOrd`.** -/
theorem maxOrd_ge (p a : Nat) (ha1 : 1 ≤ a) (ha : a ≤ p - 1) : ordModP a p ≤ maxOrd p :=
  maxOrdAux_ge p (p - 1) a ha1 ha

/-- `maxOrdAux p n` is achieved by some index in `[1, n]` (for `n ≥ 1`). -/
theorem maxOrdAux_achieved (p : Nat) : ∀ (n : Nat), 1 ≤ n →
    ∃ a, 1 ≤ a ∧ a ≤ n ∧ ordModP a p = maxOrdAux p n
  | 0,     h => absurd h (by decide)
  | n + 1, _ => by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- n = 0: maxOrdAux p 1 = max (ordModP 1 p) 0 = ordModP 1 p
      subst hn0
      refine ⟨1, Nat.le_refl _, Nat.le_refl _, ?_⟩
      show ordModP 1 p = nmax (ordModP 1 p) (maxOrdAux p 0)
      exact Nat.le_antisymm (le_nmax_left _ _)
        (nmax_le (Nat.le_refl _) (Nat.zero_le _))
    · -- n ≥ 1: max of ordModP (n+1) p and maxOrdAux p n
      obtain ⟨a, ha1, han, hae⟩ := maxOrdAux_achieved p n hnpos
      rcases Nat.le_total (ordModP (n + 1) p) (maxOrdAux p n) with hle | hge
      · -- the recursive max wins
        refine ⟨a, ha1, Nat.le_succ_of_le han, ?_⟩
        rw [hae]; show maxOrdAux p n = nmax (ordModP (n + 1) p) (maxOrdAux p n)
        exact Nat.le_antisymm (le_nmax_right _ _) (nmax_le hle (Nat.le_refl _))
      · -- ordModP (n+1) p wins
        refine ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), Nat.le_refl _, ?_⟩
        show ordModP (n + 1) p = nmax (ordModP (n + 1) p) (maxOrdAux p n)
        exact Nat.le_antisymm (le_nmax_left _ _) (nmax_le (Nat.le_refl _) hge)

/-- ★★ **`maxOrd` is achieved by some unit `g ∈ [1, p−1]`.** -/
theorem maxOrd_achieved (p : Nat) (hp : 1 < p) :
    ∃ g, 1 ≤ g ∧ g ≤ p - 1 ∧ ordModP g p = maxOrd p := by
  have hp1 : 1 ≤ p - 1 := E213.Tactic.NatHelper.le_sub_of_add_le hp
  exact maxOrdAux_achieved p (p - 1) hp1

/-- `1 ≤ maxOrd` (the achieved order is positive). -/
theorem one_le_maxOrd (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) :
    1 ≤ maxOrd p := by
  obtain ⟨g, hg1, hgp, hge⟩ := maxOrd_achieved p hp
  have hglt : g < p := Nat.lt_of_le_of_lt hgp (Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)) Nat.zero_lt_one)
  rw [← hge]; exact ord_pos g p hp hpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hg1) hglt

/-- `maxOrdAux p n ≤ p − 1` (every order divides `p − 1`). -/
theorem maxOrdAux_le_pred (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) :
    ∀ (n : Nat), n ≤ p - 1 → maxOrdAux p n ≤ p - 1
  | 0,     _ => Nat.zero_le _
  | n + 1, hn => by
    have hp1pos : 0 < p - 1 := E213.Tactic.NatHelper.le_sub_of_add_le hp
    have hnp : n + 1 ≤ p - 1 := hn
    have hglt : n + 1 < p := Nat.lt_of_le_of_lt hnp (Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)) Nat.zero_lt_one)
    have hord : ordModP (n + 1) p ≤ p - 1 :=
      le_of_dvd_pos (ordModP (n + 1) p) (p - 1) hp1pos
        (ord_dvd_p_sub_one (n + 1) p hp hpr (Nat.succ_pos n) hglt)
    show nmax (ordModP (n + 1) p) (maxOrdAux p n) ≤ p - 1
    exact nmax_le hord (maxOrdAux_le_pred p hp hpr n (Nat.le_trans (Nat.le_succ n) hn))

/-- `maxOrd ≤ p − 1`. -/
theorem maxOrd_le_pred (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) :
    maxOrd p ≤ p - 1 :=
  maxOrdAux_le_pred p hp hpr (p - 1) (Nat.le_refl _)

end E213.Lib.Math.NumberTheory.ModArith.MaxOrder
