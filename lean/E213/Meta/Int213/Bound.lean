import E213.Meta.Int213.Core

/-!
# Meta.Int213.Bound — PURE Int bound / comparison helpers

Centralised propext-free Int helpers, specifically targeting
bound-style lemmas (≤, <, sq ≤ 1, etc.) that Lean-core handles via
propext-tainted iff machinery.

Key technique: direct `cases h` on `Int.NonNeg` (definitionally
unfolded from `Int.le`).  Since `Int.NonNeg` is an inductive Prop
whose single constructor `mk : ∀ n, NonNeg (ofNat n)` cannot match
`Int.negSucc k`, contradiction is detected automatically via Lean's
constructor injection — no propext needed.

This is the **Int-side companion** to `Meta/Tactic/NatHelper.lean`
and `Meta/Tactic/ListHelper.lean`.  Helpers here were promoted from:

  · `Lib/Math/CayleyDickson/Integer/ZOmegaUnits §5` (diophantine)

per G93 §C1 + G94 §1 centralisation.  Existing call sites remain
compatible via `@[reducible]` aliases in the original locations.

All theorems below are **PURE**.
-/

namespace E213.Meta.Int213

/-! ## §1.  Bounded-Nat lemmas via Int.NonNeg constructor inversion -/

/-- For any Nat n with `Int.ofNat n ≤ 1`, `n = 0 ∨ n = 1`.
    PURE via direct `cases` on the underlying `Int.NonNeg`. -/
theorem ofNat_int_le_one (n : Nat) (h : (Int.ofNat n : Int) ≤ 1) :
    n = 0 ∨ n = 1 := by
  match n with
  | 0 => left; rfl
  | 1 => right; rfl
  | _+2 =>
    exfalso
    cases h

/-! ## §2.  Int squared bound -/

/-- For Int x with `x * x ≤ 1`, `x ∈ {-1, 0, 1}`.

    PURE via case-split on Int constructors + `ofNat_int_le_one`.
    Foundation for diophantine bounds on quadratic number rings
    (Eisenstein, Gaussian, Hurwitz units).  Replaces Lean-core
    `Int.sq_le_one`-style chains that import propext via
    `Int.ofNat_le` iff. -/
theorem int_sq_le_one (x : Int) (h : x * x ≤ (1 : Int)) :
    x = -1 ∨ x = 0 ∨ x = 1 := by
  match x with
  | Int.ofNat n =>
    have h_nat : Int.ofNat (n * n) ≤ (1 : Int) := h
    rcases ofNat_int_le_one (n * n) h_nat with h_zero | h_one
    · have hn : n = 0 := by
        match n, h_zero with
        | 0, _ => rfl
        | k+1, hk =>
          exfalso
          have h_pos : 1 ≤ (k+1) * (k+1) := by
            have : 1 ≤ k+1 := Nat.succ_le_succ (Nat.zero_le k)
            exact Nat.mul_le_mul this this
          rw [hk] at h_pos
          exact absurd h_pos (by decide)
      rw [hn]; right; left; rfl
    · have hn : n = 1 := by
        match n, h_one with
        | 0, hk => exact absurd hk (by decide)
        | 1, _ => rfl
        | k+2, hk => exact absurd hk (by
            have : 4 ≤ (k+2) * (k+2) := by
              have : 2 ≤ k+2 := Nat.le_add_left _ _
              exact Nat.mul_le_mul this this
            exact absurd (Nat.le_trans this (Nat.le_of_eq hk)) (by decide))
      rw [hn]; right; right; rfl
  | Int.negSucc n =>
    have h_nat : Int.ofNat ((n+1) * (n+1)) ≤ (1 : Int) := h
    rcases ofNat_int_le_one ((n+1) * (n+1)) h_nat with h_zero | h_one
    · exfalso
      have h_pos : 1 ≤ (n+1) * (n+1) := by
        have : 1 ≤ n+1 := Nat.succ_le_succ (Nat.zero_le n)
        exact Nat.mul_le_mul this this
      rw [h_zero] at h_pos
      exact absurd h_pos (by decide)
    · have hn : n = 0 := by
        match n, h_one with
        | 0, _ => rfl
        | k+1, hk => exact absurd hk (by
            have : 4 ≤ (k+2) * (k+2) := by
              have : 2 ≤ k+2 := Nat.le_add_left _ _
              exact Nat.mul_le_mul this this
            exact absurd (Nat.le_trans this (Nat.le_of_eq hk)) (by decide))
      rw [hn]; left; rfl

end E213.Meta.Int213
