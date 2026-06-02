import E213.Lib.Physics.Simplex.Counts
import E213.Meta.Int213.Core
import E213.Meta.Tactic.NatHelper

/-!
# The disc-forcing obstruction: `√2` is not a matrix discriminant

The `E₈` seed is *forced* by the framework: `√5 = √(disc P)` where
`P = [[2,1],[1,1]]` has `disc P = trace² − 4·det = 9 − 4 = 5 = NS+NT`.  The
Eisenstein `E₆` seed `√(-3)` is likewise a discriminant (`disc = 1 − 4 =
-3`, the order-6 matrix).  Does the *same* mechanism force the `E₇` seed
`√2 = √NT`?

**No — and there is a sharp obstruction.**  An integer `2×2` matrix
discriminant is `t² − 4d`, and `t² ≡ 0` or `1 (mod 4)` for every integer
`t` (even ⇒ 0, odd ⇒ 1), so `t² − 4d ≡ 0` or `1 (mod 4)` — **never `2`**.
The seeds `5 ≡ 1` and `-3 ≡ 1` are attainable; the `E₇` seed `2 ≡ 2` is
**not** a discriminant.  So the disc-mechanism that anchors `E₈` (and
`E₆`) provably **cannot** reach `√2`: the octahedral rung is *not*
disc-forced.

The proof is `∅`-axiom and runs entirely through **parity** (the `mod 4`
statement realised constructively): write `t·t = ↑(|t|²)` (a `Nat`
square, `Int.natAbs_mul_self`); if `|t| = 2j` then `t·t = 4(j²)` and the
equation forces `4·(… ) = 2`; if `|t| = 2j+1` then `t·t = 4(j²+j)+1` and
it forces `4·(…) = 1`.  Both are impossible because `4·X = 2·(2·X)` and
`2·Y ≠ 1` for every integer `Y`.

This neither imports an exterior (`ℤ[√2]` is a 213-internal construction)
nor falsifies anything — it *sharpens* the privilege of `E₇`: its seed is
the atomic `√NT`, but unlike `E₈/E₆` it is not realised by the `P`-style
discriminant mechanism.  `E₇` is the genuine exception, with a proven
number-theoretic reason (`disc ≢ 2 (mod 4)`).
-/

namespace E213.Lib.Math.CayleyDickson.Tower.DiscForcingObstruction

open E213.Lib.Physics.Simplex.Counts
open E213.Meta.Int213

/-! ## Pure parity / non-divisibility kernel -/

/-- `2·k ≠ 1` over `Nat` (∅-axiom, structural). -/
theorem nat_two_mul_ne_one : ∀ k : Nat, 2 * k ≠ 1
  | 0     => fun h => Nat.noConfusion h
  | _ + 1 => fun h => Nat.noConfusion (Nat.succ.inj h)

/-- `2·Y ≠ 1` over `Int`: even `≠` odd.  `ofNat` reduces to the `Nat`
    fact; `negSucc` is negative so `noConfusion` settles it. -/
theorem int_two_mul_ne_one : ∀ Y : Int, 2 * Y ≠ 1
  | Int.ofNat n   => fun h =>
      nat_two_mul_ne_one n (Int.ofNat.inj ((Int.ofNat_mul 2 n).trans h))
  | Int.negSucc _ => fun h => Int.noConfusion h

/-- `4·X = 2·(2·X)` — factor out one `2`. -/
theorem four_mul_eq_two_mul (X : Int) : 4 * X = 2 * (2 * X) := by
  have h2 : (4 : Int) * X = 2 * 2 * X := rfl
  rw [h2, mul_assoc]

/-- **No integer is `4·X = 1`.**  `4·X = 2·(2·X) = 1` would make `2·(2X) =
    1`, impossible. -/
theorem four_mul_ne_one (X : Int) : 4 * X ≠ 1 := by
  intro h
  rw [four_mul_eq_two_mul] at h
  exact int_two_mul_ne_one (2 * X) h

/-- `a + 1 = 2 → a = 1` (∅-axiom, via `add_neg_cancel`). -/
theorem add_one_eq_two_imp {a : Int} (h : a + 1 = 2) : a = 1 := by
  have e : a + 1 + (-1) = 2 + (-1) := by rw [h]
  rw [add_assoc, show (1 : Int) + (-1) = 0 from by decide,
      show (2 : Int) + (-1) = 1 from by decide, add_comm, zero_add] at e
  exact e

/-- **No integer is `4·X = 2`.**  `4·X = 2·(2·X) = 2` would force `2·X =
    1`, impossible. -/
theorem four_mul_ne_two (X : Int) : 4 * X ≠ 2 := by
  intro h
  rw [four_mul_eq_two_mul] at h
  -- h : 2 * (2 * X) = 2
  have hz : 2 * (2 * X - 1) = 0 := by rw [mul_sub, h]; decide
  rcases mul_eq_zero hz with h2 | h2x
  · exact absurd h2 (by decide)
  · have step : 2 * X - 1 + 1 = 2 * X := sub_add_cancel_int (2 * X) 1
    rw [h2x, zero_add] at step
    exact int_two_mul_ne_one X step.symm

/-! ## Pure square parity in `Nat` -/

/-- Every `Nat` is even or odd (∅-axiom, structural recursion). -/
theorem nat_even_or_odd : ∀ n : Nat, (∃ k, n = 2 * k) ∨ (∃ k, n = 2 * k + 1)
  | 0     => Or.inl ⟨0, rfl⟩
  | n + 1 =>
      match nat_even_or_odd n with
      | Or.inl ⟨k, hk⟩ => Or.inr ⟨k, by rw [hk]⟩
      | Or.inr ⟨k, hk⟩ => Or.inl ⟨k + 1, by rw [hk, Nat.mul_succ]⟩

/-- `(2j+1)² = 4(j²+j)+1` (∅-axiom). -/
theorem odd_sq (j : Nat) : (2 * j + 1) * (2 * j + 1) = 4 * (j * j + j) + 1 := by
  rw [E213.Tactic.NatHelper.add_mul, Nat.mul_add, Nat.mul_add,
      E213.Tactic.NatHelper.mul_mul_mul_comm_213,
      Nat.one_mul, Nat.mul_one, Nat.mul_add,
      Nat.add_assoc (2 * 2 * (j * j)) (2 * j) (2 * j + 1 * 1),
      ← Nat.add_assoc (2 * j) (2 * j) (1 * 1),
      ← E213.Tactic.NatHelper.add_mul, ← Nat.add_assoc]

/-! ## The obstruction -/

/-- **No integer `2×2` matrix discriminant equals `2`.**  `t² = ↑|t|²`;
    parity of `|t|` forces `4·X = 2` (even) or `4·X = 1` (odd), both
    impossible.  Hence the `E₇` seed `√2` is not a `P`-style
    discriminant. -/
theorem two_not_a_discriminant (t d : Int) : t * t - 4 * d ≠ 2 := by
  intro h
  rw [← Int.natAbs_mul_self] at h
  rcases nat_even_or_odd t.natAbs with ⟨j, hj⟩ | ⟨j, hj⟩
  · -- |t| = 2j ⇒ t² = 4(j²) ⇒ 4·(↑(j²) − d) = 2
    rw [hj, show (2 * j) * (2 * j) = 4 * (j * j) from by
      rw [E213.Tactic.NatHelper.mul_mul_mul_comm_213]] at h
    refine four_mul_ne_two (↑(j * j) - d) ?_
    rw [mul_sub, show (4 : Int) * (↑(j * j)) = ↑(4 * (j * j)) from
      (Int.ofNat_mul 4 (j * j)).symm]
    exact h
  · -- |t| = 2j+1 ⇒ t² = 4(j²+j)+1 ⇒ 4·(↑(j²+j) − d) = 1
    rw [hj, odd_sq, Int.ofNat_add, Int.ofNat_mul] at h
    refine four_mul_ne_one (↑(j * j + j) - d) ?_
    -- h : ↑4 * ↑(j*j+j) + ↑1 - 4*d = 2
    rw [mul_sub]
    -- goal : 4 * ↑(j*j+j) - 4*d = 1
    apply add_one_eq_two_imp
    -- goal : 4 * ↑(j*j+j) - 4*d + 1 = 2
    rw [Int.sub_eq_add_neg, add_right_comm, ← Int.sub_eq_add_neg]
    exact h

/-- ★★ **The disc-forcing obstruction, located on the `5`-floor.**  The
    `E₈` and `E₆` seeds *are* discriminants (`disc P = 5 = NS+NT`,
    Eisenstein `disc = -3`); the `E₇` seed `NT = 2` is *not* — no
    `t² − 4d` equals `2`.  So the disc-mechanism forces `E₈` (and `E₆`)
    but provably misses `E₇`. -/
theorem disc_forcing_splits_at_E7 :
    -- E₈: disc P = 5 = NS+NT, a discriminant (t=3, d=1).
    ((3 : Int) ^ 2 - 4 * 1 = 5 ∧ (5 : Int) = (NS : Int) + NT)
    -- E₆: Eisenstein disc = -3 = -NS, a discriminant (t=1, d=1).
    ∧ ((1 : Int) ^ 2 - 4 * 1 = -3 ∧ (-3 : Int) = -(NS : Int))
    -- E₇: the seed NT = 2 is NOT a discriminant — the obstruction.
    ∧ ((NT : Int) = 2 ∧ ∀ t d : Int, t * t - 4 * d ≠ 2) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, two_not_a_discriminant⟩⟩

end E213.Lib.Math.CayleyDickson.Tower.DiscForcingObstruction
