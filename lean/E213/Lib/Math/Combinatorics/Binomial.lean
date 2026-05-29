import E213.Lib.Physics.Simplex.Counts

/-!
# Combinatorics — binomial coefficients (Pascal recursion)

Reuses `binom` from `Lib/Physics/Simplex/Counts.lean` (defined
for the Δⁿ⁻¹ cohomology setup).  Extends with Pascal-level
identities and the Vandermonde-2 split for `binom (a+b) 2`.

Atomic content:
  * `binom n 0 = 1`, `binom n 1 = n` (defeq-blocked at level 0
    for free `n`; case-split forces reduction).
  * Pascal step at level 2: `binom (n+1) 2 = n + binom n 2`.
  * Vandermonde-2: `binom (a+b) 2 = binom a 2 + binom b 2 + a·b`.
  * Pascal's row 5 values; small-n Pascal step.

All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.Binomial

open E213.Lib.Physics.Simplex.Counts (binom)

/-! ## Pascal-level identities -/

/-- `binom n 0 = 1` for any `n`.  Although the first pattern of
    `binom` reads `binom _ 0 = 1`, Lean does not eagerly reduce
    `binom n 0` when `n` is a free variable — case-splitting
    forces the reduction. -/
theorem binom_n_0 (n : Nat) : binom n 0 = 1 := by
  cases n <;> rfl

/-- `binom p m ≤ binom (p+1) m` — Pascal monotonicity in the
    first argument.  For `m = 0` both sides are `1` (via
    `binom_n_0`); for `m = succ k` the Pascal recursion gives
    `binom (p+1) (k+1) = binom p k + binom p (k+1)`, so
    `binom p (k+1) ≤ binom p k + binom p (k+1)` by
    `Nat.le_add_left`. -/
theorem binom_le_binom_succ (p m : Nat) :
    binom p m ≤ binom (p+1) m := by
  cases m with
  | zero => rw [binom_n_0 p, binom_n_0 (p+1)]; exact Nat.le_refl 1
  | succ k => exact Nat.le_add_left _ _

/-- `binom n 1 = n` by Nat-induction via Pascal recursion.  Used
    as the first ingredient in the Vandermonde-2 identity. -/
theorem binom_n_1 : ∀ n : Nat, binom n 1 = n
  | 0     => rfl
  | n + 1 => by
    show binom n 0 + binom n 1 = n + 1
    rw [binom_n_0 n, binom_n_1 n]
    exact Nat.add_comm 1 n

/-- Pascal step at level 2: `binom (n+1) 2 = n + binom n 2`.
    Combines the `binom` definition with `binom n 1 = n`. -/
theorem binom_succ_2 (n : Nat) : binom (n + 1) 2 = n + binom n 2 := by
  show binom n 1 + binom n 2 = n + binom n 2
  rw [binom_n_1]

/-! ## Vandermonde-2 -/

/-- Helper: reposition `b` from the second slot to the last slot
    in a left-associated 5-term `Nat` sum.  Internal to
    `binom_add_2`. -/
private theorem move_b_to_tail (a b X Y Z : Nat) :
    a + b + X + Y + Z = a + X + Y + Z + b := by
  rw [Nat.add_right_comm a b X,
      Nat.add_right_comm (a + X) b Y,
      Nat.add_right_comm (a + X + Y) b Z]

/-- Propext-free right distribution `(a + b) * c = a * c + b * c`.
    Re-derived from `Nat.mul_succ` + `Nat.add_assoc` +
    `Nat.add_right_comm` to avoid the `propext` dependency in
    `Nat.right_distrib`. -/
theorem add_mul_pure : ∀ (a b c : Nat), (a + b) * c = a * c + b * c
  | _, _, 0     => rfl
  | a, b, c + 1 => by
    show (a + b) * (c + 1) = a * (c + 1) + b * (c + 1)
    rw [Nat.mul_succ (a + b) c, Nat.mul_succ a c, Nat.mul_succ b c,
        add_mul_pure a b c]
    rw [← Nat.add_assoc (a * c + b * c) a b,
        ← Nat.add_assoc (a * c + a) (b * c) b,
        Nat.add_right_comm (a * c) (b * c) a]

/-- ★ **Vandermonde-2 identity**:
        `binom (a + b) 2 = binom a 2 + binom b 2 + a · b`.

    2-subsets of `a + b` split into intra-a (`binom a 2`),
    intra-b (`binom b 2`), and cross-ab (`a · b`).  Used by the
    mediant cohomology functor to decompose K_{a+c, *} S-pair
    counts; the same identity governs T-pairs. -/
theorem binom_add_2 : ∀ a b : Nat,
    binom (a + b) 2 = binom a 2 + binom b 2 + a * b
  | 0,     b => by
    show binom (0 + b) 2 = binom 0 2 + binom b 2 + 0 * b
    rw [Nat.zero_add, Nat.zero_mul, Nat.add_zero]
    show binom b 2 = 0 + binom b 2
    rw [Nat.zero_add]
  | a + 1, b => by
    have ih := binom_add_2 a b
    show binom (a + 1 + b) 2
        = binom (a + 1) 2 + binom b 2 + (a + 1) * b
    have h_assoc : a + 1 + b = (a + b) + 1 := Nat.add_right_comm a 1 b
    rw [h_assoc, binom_succ_2, ih, binom_succ_2, Nat.succ_mul]
    rw [← Nat.add_assoc (a + b) (binom a 2 + binom b 2) (a * b),
        ← Nat.add_assoc (a + b) (binom a 2) (binom b 2)]
    rw [← Nat.add_assoc (a + binom a 2 + binom b 2) (a * b) b]
    exact move_b_to_tail a b (binom a 2) (binom b 2) (a * b)

/-! ## Small-n concrete identities -/

/-- ★ Pascal's row 5: 1, 5, 10, 10, 5, 1 — the d=5 simplex
    grade dimensions for K_{3,2}^{(c=2)} ↪ Δ⁴.  Symmetric:
    C(5, k) = C(5, 5−k).  Row sum 2⁵ = 32. -/
theorem binom_5_row :
    binom 5 0 = 1 ∧ binom 5 1 = 5 ∧ binom 5 2 = 10
    ∧ binom 5 3 = 10 ∧ binom 5 4 = 5 ∧ binom 5 5 = 1
    ∧ binom 5 0 + binom 5 1 + binom 5 2
        + binom 5 3 + binom 5 4 + binom 5 5 = 32
    ∧ binom 5 6 = 0  -- vanishes above grade d
    := by decide

/-- ★ Atomic Pascal step at (5, 2): C(5, 2) = C(4, 1) + C(4, 2)
    = 4 + 6 = 10. -/
theorem pascal_5_2 : binom 5 2 = binom 4 1 + binom 4 2 := by decide

end E213.Lib.Math.Combinatorics.Binomial
