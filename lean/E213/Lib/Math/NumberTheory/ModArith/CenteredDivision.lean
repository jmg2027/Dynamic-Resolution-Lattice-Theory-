import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.NatRing213
import E213.Meta.Int213.PolyIntMTactic

/-!
# CenteredDivision — the centered (balanced) integer division

The Euclidean descent in `ℤ[ω]` rounds each coordinate of `α·conj β` to the **nearest**
multiple of `N = ‖β‖²`.  The arithmetic underneath is the *centered* division of an integer
`A` by a positive modulus `N`: a quotient `q` and a remainder `r` with `A = qN + r` and
`2|r| ≤ N` (the remainder lies in `(−N/2, N/2]`), so `(2r)² ≤ N²` — exactly the hypothesis of
the Eisenstein covering bound.

  * ★★★ `centered_div_nat` — the nonnegative core: for `a : ℕ`, `N > 0`,
    `∃ q r : ℤ, a = qN + r ∧ 2|r| ≤ N`.
  * ★★★ `centered_div` — for every `A : ℤ`, `N > 0`, `∃ q r : ℤ, A = qN + r ∧ 2|r| ≤ N`
    (negative `A` by negation).
  * ★★ `centered_div_sq` — the squared form `4(r·r) ≤ (N:ℤ)·N` consumed by `covering_bound`.

Built from the pure Nat division `AddMod213.div_add_mod` + `Nat.mod_lt`, routing subtraction
through the pure `NatRing213` lemmas (the core `Nat.sub_add_cancel` / `Int.ofNat_sub` are
`propext`-dirty).  All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.CenteredDivision

open E213.Meta.Nat.AddMod213 (div_add_mod)
open E213.Meta.Nat.NatRing213 (nat_sub_add_cancel nat_add_sub_self_right)

/-! ## §1 — the nonnegative core -/

/-- Centered division for a natural-number dividend. -/
theorem centered_div_nat (a N : Nat) (hN : 0 < N) :
    ∃ q r : Int, (a : Int) = q * (N : Int) + r ∧ 2 * r.natAbs ≤ N := by
  have hdm : N * (a / N) + a % N = a := div_add_mod a N
  have hlt : a % N < N := Nat.mod_lt a hN
  have hmN : a % N ≤ N := Nat.le_of_lt hlt
  have hcast : (N : Int) * ((a / N : Nat) : Int) + ((a % N : Nat) : Int) = (a : Int) := by
    rw [← Int.ofNat_mul, ← Int.ofNat_add, hdm]
  rcases Nat.lt_or_ge (2 * (a % N)) N with hlt2 | hge2
  · -- keep the remainder
    refine ⟨((a / N : Nat) : Int), ((a % N : Nat) : Int), ?_, ?_⟩
    · rw [← hcast]; ring_intZ
    · rw [Int.natAbs_ofNat]; exact Nat.le_of_lt hlt2
  · -- center down: r = −(N − a%N)
    refine ⟨((a / N : Nat) : Int) + 1, -(((N - a % N : Nat) : Int)), ?_, ?_⟩
    · have hsac : ((N - a % N : Nat) : Int) + ((a % N : Nat) : Int) = (N : Int) := by
        rw [← Int.ofNat_add, nat_sub_add_cancel hmN]
      have hrw : ((N - a % N : Nat) : Int) = (N : Int) - ((a % N : Nat) : Int) := by
        rw [← hsac]; ring_intZ
      rw [← hcast, hrw]; ring_intZ
    · rw [Int.natAbs_neg, Int.natAbs_ofNat]
      -- 2 * (N − a%N) ≤ N
      have hk : N - a % N ≤ a % N := by
        have h2 : N ≤ a % N + a % N := by rw [← Nat.two_mul]; exact hge2
        have hs := Nat.sub_le_sub_right h2 (a % N)
        rwa [nat_add_sub_self_right] at hs
      calc 2 * (N - a % N)
          = (N - a % N) + (N - a % N) := Nat.two_mul _
        _ ≤ (N - a % N) + a % N := Nat.add_le_add_left hk _
        _ = N := nat_sub_add_cancel hmN

/-! ## §2 — the full integer statement -/

/-- ★★★ **Centered division.**  For every integer `A` and positive modulus `N`, there is a
    quotient `q` and remainder `r` with `A = qN + r` and `2|r| ≤ N`.  Nonnegative `A` is the
    core; negative `A` reduces by negating the nonnegative result. -/
theorem centered_div (A : Int) (N : Nat) (hN : 0 < N) :
    ∃ q r : Int, A = q * (N : Int) + r ∧ 2 * r.natAbs ≤ N := by
  cases A with
  | ofNat a =>
    exact centered_div_nat a N hN
  | negSucc a =>
    obtain ⟨q, r, heq, hb⟩ := centered_div_nat (a + 1) N hN
    refine ⟨-q, -r, ?_, ?_⟩
    · -- Int.negSucc a = -(a+1); negate the equation
      have hneg : (Int.negSucc a) = -((a + 1 : Nat) : Int) := rfl
      rw [hneg, heq]; ring_intZ
    · rw [Int.natAbs_neg]; exact hb

end E213.Lib.Math.NumberTheory.ModArith.CenteredDivision
