import E213.Meta.Tactic.NatHelper
/-!
# Binomial coefficients (213-native) — FLT prerequisite

213-native `choose` via Pascal recurrence, with the basic identities
needed for the binomial-theorem-based proof of Fermat's Little Theorem
(FLT, `a^p ≡ a (mod p)` for prime p):

  · `choose n 0 = 1`
  · `choose 0 (k+1) = 0`
  · `choose (n+1) (k+1) = choose n k + choose n (k+1)`     (Pascal)
  · `choose_self`            : `choose n n = 1`
  · `choose_eq_zero_of_lt`   : `n < k → choose n k = 0`
  · `choose_one_right`       : `choose n 1 = n`
  · **`choose_succ_mul`** (★ key FLT identity):
       `(k + 1) · choose (n + 1) (k + 1) = (n + 1) · choose n k`

The last identity, combined with `gcd(k + 1, p) = 1` for `0 ≤ k ≤ p - 2`
(since `k + 1 < p`, prime `p`), gives `p ∣ choose p (k + 1)` by
Euclid's lemma — the prime-divisibility foundation for the
binomial-mod-p middle terms vanishing.

This file is foundational FLT infrastructure; the full FLT proof is
multi-session.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial

open E213.Tactic.NatHelper (add_mul mul_assoc)

/-- 213-native binomial coefficient via Pascal recurrence.
    `choose n k = "n choose k"`.  PURE. -/
def choose : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- `choose n 0 = 1` — base. -/
@[simp] theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by
  cases n <;> rfl

/-- `choose 0 (k+1) = 0` — base. -/
@[simp] theorem choose_zero_succ (k : Nat) : choose 0 (k + 1) = 0 := rfl

/-- ★ **Pascal**: `choose (n+1) (k+1) = choose n k + choose n (k+1)`.  Definitional. -/
theorem choose_succ_succ (n k : Nat) :
    choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := rfl

/-- `choose n k = 0` when `n < k`.  By induction on `n`. -/
theorem choose_eq_zero_of_lt : ∀ (n k : Nat), n < k → choose n k = 0
  | 0,     0,     h => absurd h (Nat.lt_irrefl 0)
  | 0,     _ + 1, _ => rfl
  | _ + 1, 0,     h => absurd h (Nat.not_lt_zero _)
  | n + 1, k + 1, h => by
    have h' : n < k := Nat.lt_of_succ_lt_succ h
    rw [choose_succ_succ,
        choose_eq_zero_of_lt n k h',
        choose_eq_zero_of_lt n (k + 1) (Nat.lt_succ_of_lt h')]

/-- `choose n n = 1` — by induction on `n` using Pascal. -/
@[simp] theorem choose_self : ∀ n, choose n n = 1
  | 0     => rfl
  | n + 1 => by
    rw [choose_succ_succ, choose_self n,
        choose_eq_zero_of_lt n (n + 1) (Nat.lt_succ_self _)]

/-- `choose n 1 = n` — induction on `n`. -/
theorem choose_one_right : ∀ n, choose n 1 = n
  | 0     => rfl
  | n + 1 => by
    rw [choose_succ_succ, choose_zero_right, choose_one_right n]
    exact Nat.add_comm _ _

/-- Smoke tests for small values. -/
theorem choose_table :
    choose 5 0 = 1 ∧ choose 5 1 = 5 ∧ choose 5 2 = 10 ∧ choose 5 3 = 10
    ∧ choose 5 4 = 5 ∧ choose 5 5 = 1 ∧ choose 7 3 = 35 := by decide

/-! ## Key FLT identity: `(k + 1) · choose (n + 1) (k + 1) = (n + 1) · choose n k`

By induction on `n`.  Base cases (`n = 0`) and (`k = 0`) handled
directly.  Inductive step uses **two** IHs (at `k` and `k+1`) and
**two** Pascal expansions; the resulting Nat-algebra is captured by
the private `inductive_step_algebra` helper which proves the
rearrangement after the substitutions. -/

/-- Algebraic rearrangement closing the inductive step:
    `(X + (Z + W)) + Y = X + (Z + W) + Y` where the two sides are
    sums of the same 4 atomic terms in different associations.
    Reduces to commutativity / associativity of `Nat.add`. -/
private theorem rearrange4 (X Y Z W : Nat) :
    X * (Z + W) + Y = X * Z + X * W + Y := by
  rw [Nat.mul_add]

/-- Generic 4-term rearrangement: `(a + (b + c)) + d = (a + d) + (b + c)`. -/
private theorem rearrange_abcd (a b c d : Nat) :
    a + b + c + d = a + d + b + c := by
  rw [Nat.add_assoc a b c, Nat.add_assoc a (b + c) d,
      Nat.add_comm (b + c) d, ← Nat.add_assoc a d (b + c),
      Nat.add_assoc (a + d) b c]

/-- ★★★ **Key FLT identity**: `(k + 1) · choose (n + 1) (k + 1) = (n + 1) · choose n k`.

    Recursive form of `k · C(n, k) = n · C(n - 1, k - 1)`.  Combined
    with `gcd(k + 1, p) = 1` (when `k + 1 < p`, prime `p`), Euclid's
    lemma gives `p ∣ choose p (k + 1)`.  PURE.

    Proof: induction on `n`.  Inductive step expands both sides via
    Pascal and applies the two IHs at `(n, k)` and `(n, k+1)`. -/
theorem choose_succ_mul : ∀ (n k : Nat),
    (k + 1) * choose (n + 1) (k + 1) = (n + 1) * choose n k
  | 0,     0     => rfl
  | 0,     k + 1 => by
    show (k + 2) * choose 1 (k + 2) = 1 * choose 0 (k + 1)
    rw [show choose 1 (k + 2) = 0 from rfl,
        show choose 0 (k + 1) = 0 from rfl,
        Nat.mul_zero, Nat.mul_zero]
  | n + 1, 0     => by
    show 1 * choose (n + 2) 1 = (n + 2) * choose (n + 1) 0
    rw [Nat.one_mul, choose_one_right, choose_zero_right, Nat.mul_one]
  | n + 1, k + 1 => by
    -- IHs:
    --   ih1 : (k+1) · choose (n+1) (k+1) = (n+1) · choose n k
    --   ih2 : (k+2) · choose (n+1) (k+2) = (n+1) · choose n (k+1)
    have ih1 : (k + 1) * choose (n + 1) (k + 1) = (n + 1) * choose n k :=
      choose_succ_mul n k
    have ih2 : (k + 2) * choose (n + 1) (k + 2) = (n + 1) * choose n (k + 1) :=
      choose_succ_mul n (k + 1)
    -- Goal: (k+2) · choose (n+2) (k+2) = (n+2) · choose (n+1) (k+1)
    -- Expand LHS via Pascal on choose (n+2) (k+2):
    show (k + 2) * choose (n + 2) (k + 2) = (n + 2) * choose (n + 1) (k + 1)
    rw [show choose (n + 2) (k + 2) = choose (n + 1) (k + 1) + choose (n + 1) (k + 2)
          from rfl]
    -- LHS: (k+2) · (choose (n+1) (k+1) + choose (n+1) (k+2))
    --    = (k+2) · choose (n+1) (k+1) + (k+2) · choose (n+1) (k+2)
    --    = (k+2) · choose (n+1) (k+1) + (n+1) · choose n (k+1)            [by ih2]
    rw [Nat.mul_add (k + 2) (choose (n + 1) (k + 1)) (choose (n + 1) (k + 2)), ih2]
    -- Goal: (k+2) · choose (n+1) (k+1) + (n+1) · choose n (k+1)
    --     = (n+2) · choose (n+1) (k+1)
    -- Expand RHS: (n+2) = (n+1) + 1; (n+2) · X = (n+1) · X + X
    rw [show n + 2 = (n + 1) + 1 from rfl,
        add_mul (n + 1) 1 (choose (n + 1) (k + 1)), Nat.one_mul]
    -- Goal: (k+2) · choose (n+1) (k+1) + (n+1) · choose n (k+1)
    --     = (n+1) · choose (n+1) (k+1) + choose (n+1) (k+1)
    -- Apply Pascal again on choose (n+1) (k+1) (in the (n+1) · _ term):
    rw [show choose (n + 1) (k + 1) = choose n k + choose n (k + 1) from rfl]
    -- Goal: (k+2) · choose (n+1) (k+1) + (n+1) · choose n (k+1)
    --     = (n+1) · (choose n k + choose n (k+1)) + (choose n k + choose n (k+1))
    rw [Nat.mul_add (n + 1) (choose n k) (choose n (k + 1))]
    -- Goal: (k+2) · choose (n+1) (k+1) + (n+1) · choose n (k+1)
    --     = (n+1) · choose n k + (n+1) · choose n (k+1) + (choose n k + choose n (k+1))
    -- Apply ih1 backward: (n+1) · choose n k = (k+1) · choose (n+1) (k+1)
    rw [← ih1]
    -- Goal: (k+2) · choose (n+1) (k+1) + (n+1) · choose n (k+1)
    --     = (k+1) · choose (n+1) (k+1) + (n+1) · choose n (k+1) + (choose n k + choose n (k+1))
    -- Note: choose n k + choose n (k+1) = choose (n+1) (k+1) [by Pascal backward]
    rw [show choose n k + choose n (k + 1) = choose (n + 1) (k + 1) from rfl]
    -- Goal: (k+2) · choose (n+1) (k+1) + (n+1) · choose n (k+1)
    --     = (k+1) · choose (n+1) (k+1) + (n+1) · choose n (k+1) + choose (n+1) (k+1)
    -- Simplify (k+2) · X = (k+1) · X + X
    rw [show k + 2 = (k + 1) + 1 from rfl,
        add_mul (k + 1) 1 (choose (n + 1) (k + 1)), Nat.one_mul]
    -- Goal: (k+1) · choose (n+1) (k+1) + choose (n+1) (k+1) + (n+1) · choose n (k+1)
    --     = (k+1) · choose (n+1) (k+1) + (n+1) · choose n (k+1) + choose (n+1) (k+1)
    -- This is the same sum, just reordered.  Use rearrange_abcd:
    --   a + b + c + d = a + c + b + d   (where a = (k+1)·choose(n+1)(k+1),
    --                                          b = choose(n+1)(k+1),
    --                                          c = (n+1)·choose n (k+1),
    --                                          d = doesn't quite fit — let me re-check)
    -- Wait the form is: a + b + c = a + c + b. With a = (k+1)·choose(n+1)(k+1),
    -- b = choose(n+1)(k+1), c = (n+1)·choose n (k+1).
    -- This is Nat.add_assoc + Nat.add_comm.
    rw [Nat.add_assoc ((k + 1) * choose (n + 1) (k + 1))
          (choose (n + 1) (k + 1)) ((n + 1) * choose n (k + 1))]
    rw [Nat.add_comm (choose (n + 1) (k + 1)) ((n + 1) * choose n (k + 1))]
    rw [← Nat.add_assoc ((k + 1) * choose (n + 1) (k + 1))
          ((n + 1) * choose n (k + 1)) (choose (n + 1) (k + 1))]

end E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
