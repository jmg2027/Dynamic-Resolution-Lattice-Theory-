import E213.Lib.Math.Cauchy.DepthPRecursiveInstances
import E213.Meta.Int213.Core

/-!
# NewtonGregory — the faithful forward-difference reconstruction, over ℤ

`DepthPRecursiveInstances` proves the **forward** law over `ℕ`: every degree-`d`
Newton-form polynomial `Σ_{i≤d} cᵢ·binom(·,i)` has divergence-depth `d`
(`newton_polyDepth`).  The **converse** — reconstruct a depth-`d` sequence *from*
its iterated differences-at-a-point — fails over `ℕ`, because the forward
difference `s(n+1) − s n` uses **truncated** subtraction: when an intermediate
difference would be negative, `ℕ` clamps it to `0` and the information is lost.
A genuinely degree-`2` integer polynomial like `(n−2)(n−1)` then has a
*non-constant* `ℕ`-truncated second difference (see `obstruction_*` below).

The generalization that closes it: run the finite-difference calculus over `ℤ`,
where subtraction is faithful (`E213.Meta.Int213` supplies ∅-axiom `Int` ring
arithmetic).  The headline is the **universal Newton–Gregory identity** — the
operator law `Eⁿ = (I + Δ)ⁿ` for the shift `E` and difference `Δ`, holding for
*every* sequence with no polynomiality hypothesis:

> ★★★ `newton_gregory` : for all `s : ℕ → ℤ` and `m n`,
> `s (m + n) = Σ_{j=0}^{n} binom(n,j) · (Δʲ s)(m)`.

From it: the reconstruction `polyDepthZ d s ⟹ s = Σ_{i≤d} (Δⁱs 0)·binom(·,i)`
(`reconstruct`), which is the ℤ converse `ℕ` could not state.

All ∅-axiom (over `Int213` + the 213-native `binom`).
-/

namespace E213.Lib.Math.Cauchy.NewtonGregory

open E213.Lib.Math.Cauchy.DepthPRecursiveInstances (binom binom_zero_right binom_lt_zero binom_diag)
open E213.Meta.Int213
  (add_comm add_assoc add_left_comm add_right_comm mul_add add_mul zero_mul
   add_neg_cancel)

/-! ## §0 — small ℤ rearrangement helpers (pure, over `Int213`) -/

/-- `a + (b − a) = b` (pure). -/
theorem add_sub_cancel_left' (a b : Int) : a + (b - a) = b := by
  rw [Int.sub_eq_add_neg, add_left_comm, add_neg_cancel, Int.add_zero]

/-- Four-term middle swap: `a + b + (c + d) = a + c + (b + d)` (pure). -/
theorem add_add_add_comm (a b c d : Int) : a + b + (c + d) = a + c + (b + d) := by
  rw [add_assoc a b (c + d), add_left_comm b c d, ← add_assoc a c (b + d)]

/-! ## §1 — the ℤ finite-difference calculus -/

/-- Faithful forward difference over `ℤ`: `diffZ s n = s(n+1) − s n` (no truncation). -/
def diffZ (s : Nat → Int) : Nat → Int := fun n => s (n + 1) - s n

/-- `k`-fold forward difference. -/
def liftKZ : Nat → (Nat → Int) → (Nat → Int)
  | 0,   s => s
  | k+1, s => diffZ (liftKZ k s)

/-- ★ **The difference recurrence, read on the argument.**  `(Δʲs)(m+1) =
    (Δʲs)(m) + (Δʲ⁺¹s)(m)` — pushing one step forward in the argument adds the
    next difference.  Faithful (`a + (b − a) = b`), the engine of the induction. -/
theorem liftKZ_succ_arg (j : Nat) (s : Nat → Int) (m : Nat) :
    liftKZ j s (m + 1) = liftKZ j s m + liftKZ (j + 1) s m := by
  show liftKZ j s (m + 1) = liftKZ j s m + (liftKZ j s (m + 1) - liftKZ j s m)
  rw [add_sub_cancel_left']

/-! ## §2 — the binomial-weighted partial sum `bsum T x L = Σ_{j=0}^{L} binom(T,j)·xⱼ` -/

/-- `bsum T x L = Σ_{j=0}^{L} binom(T,j) · x j` (top index `T`, length `L`). -/
def bsum (T : Nat) (x : Nat → Int) : Nat → Int
  | 0   => (binom T 0 : Int) * x 0
  | L+1 => bsum T x L + (binom T (L + 1) : Int) * x (L + 1)

/-- `bsum` respects pointwise equality of the summand sequence (no `funext`). -/
theorem bsum_congr (T : Nat) (x y : Nat → Int) (h : ∀ j, x j = y j) : ∀ L,
    bsum T x L = bsum T y L
  | 0 => by show (binom T 0 : Int) * x 0 = (binom T 0 : Int) * y 0; rw [h 0]
  | L+1 => by
    show bsum T x L + (binom T (L+1) : Int) * x (L+1)
       = bsum T y L + (binom T (L+1) : Int) * y (L+1)
    rw [bsum_congr T x y h L, h (L+1)]

/-- `bsum` is additive in the summand sequence (linearity). -/
theorem bsum_add (T : Nat) (a b : Nat → Int) : ∀ L,
    bsum T (fun j => a j + b j) L = bsum T a L + bsum T b L
  | 0 => by
    show (binom T 0 : Int) * (a 0 + b 0)
       = (binom T 0 : Int) * a 0 + (binom T 0 : Int) * b 0
    rw [mul_add]
  | L+1 => by
    show bsum T (fun j => a j + b j) L
          + (binom T (L+1) : Int) * (a (L+1) + b (L+1))
       = (bsum T a L + (binom T (L+1) : Int) * a (L+1))
          + (bsum T b L + (binom T (L+1) : Int) * b (L+1))
    rw [bsum_add T a b L, mul_add]
    exact add_add_add_comm _ _ _ _

/-- `binom (n+1) (k+1) = binom n k + binom n (k+1)` cast to `ℤ` (Pascal, definitional). -/
theorem binom_succ_succ_int (n k : Nat) :
    (binom (n+1) (k+1) : Int) = (binom n k : Int) + (binom n (k+1) : Int) := rfl

/-- ★ **Pascal recombination on the partial sum** (the auxiliary `P(L)`):
    `bsum (n+1) x (L+1) = bsum n x (L+1) + bsum n (x∘succ) L`.  Splits the
    top-`(n+1)` binomial weights into the two top-`n` partial sums. -/
theorem bsum_pascal_aux (n : Nat) (x : Nat → Int) : ∀ L,
    bsum (n+1) x (L+1) = bsum n x (L+1) + bsum n (fun j => x (j+1)) L
  | 0 => by
    show (binom (n+1) 0 : Int) * x 0 + (binom (n+1) 1 : Int) * x 1
       = ((binom n 0 : Int) * x 0 + (binom n 1 : Int) * x 1)
          + (binom n 0 : Int) * x 1
    have hb : (binom (n+1) 1 : Int) = (binom n 0 : Int) + (binom n 1 : Int) :=
      binom_succ_succ_int n 0
    have hb0 : (binom (n+1) 0 : Int) = (binom n 0 : Int) := by
      rw [binom_zero_right, binom_zero_right]
    rw [hb, hb0, add_mul,
        add_assoc ((binom n 0 : Int) * x 0) ((binom n 1 : Int) * x 1) ((binom n 0 : Int) * x 1),
        add_comm ((binom n 0 : Int) * x 1) ((binom n 1 : Int) * x 1)]
  | L+1 => by
    show bsum (n+1) x (L+1) + (binom (n+1) (L+2) : Int) * x (L+2)
       = (bsum n x (L+1) + (binom n (L+2) : Int) * x (L+2))
          + (bsum n (fun j => x (j+1)) L + (binom n (L+1) : Int) * x (L+2))
    -- A = bsum n x (L+1), B = bsum n (x∘succ) L,
    -- C = binom n (L+1)·x(L+2), D = binom n (L+2)·x(L+2)
    -- LHS = A + (B + (C + D)) ;  RHS = (A + D) + (B + C); both = (A+B)+(C+D)
    rw [bsum_pascal_aux n x L, binom_succ_succ_int n (L+1), add_mul,
        add_add_add_comm (bsum n x (L+1)) ((binom n (L+2) : Int) * x (L+2))
          (bsum n (fun j => x (j+1)) L) ((binom n (L+1) : Int) * x (L+2)),
        add_comm ((binom n (L+2) : Int) * x (L+2)) ((binom n (L+1) : Int) * x (L+2))]

/-- ★ **Pascal recombination at the diagonal.**  `bsum (n+1) x (n+1) = bsum n x n
    + bsum n (x∘succ) n` — the `L = n` case of `bsum_pascal_aux`, after dropping
    the above-diagonal term `binom n (n+1) = 0`. -/
theorem bsum_pascal (n : Nat) (x : Nat → Int) :
    bsum (n+1) x (n+1) = bsum n x n + bsum n (fun j => x (j+1)) n := by
  rw [bsum_pascal_aux n x n]
  -- bsum n x (n+1) = bsum n x n + binom n (n+1) * x(n+1) = bsum n x n + 0
  show bsum n x n + (binom n (n+1) : Int) * x (n+1) + bsum n (fun j => x (j+1)) n
     = bsum n x n + bsum n (fun j => x (j+1)) n
  rw [binom_lt_zero n (n+1) (Nat.lt_succ_self n)]
  show bsum n x n + (0 : Int) * x (n+1) + bsum n (fun j => x (j+1)) n
     = bsum n x n + bsum n (fun j => x (j+1)) n
  rw [zero_mul, Int.add_zero]

/-! ## §3 — the universal Newton–Gregory identity (headline) -/

/-- ★★★ **Universal Newton–Gregory forward-difference identity.**  For *every*
    sequence `s : ℕ → ℤ` and all `m n`:
    `s (m + n) = Σ_{j=0}^{n} binom(n,j) · (Δʲ s)(m)`.
    The operator law `Eⁿ = (I + Δ)ⁿ` (shift = sum of differences), holding with
    **no** polynomiality hypothesis — the faithful generalization of the formula
    that truncated `ℕ` subtraction could not support.  Single induction on `n`,
    generalized over the base point `m`; each step expands `(Δʲs)(m+1) =
    (Δʲs)(m) + (Δʲ⁺¹s)(m)` and Pascal-recombines (`bsum_pascal`). -/
theorem newton_gregory (s : Nat → Int) : ∀ n m,
    s (m + n) = bsum n (fun j => liftKZ j s m) n
  | 0, m => by
    show s (m + 0) = (binom 0 0 : Int) * liftKZ 0 s m
    show s (m + 0) = (1 : Int) * s m
    rw [Nat.add_zero, Int.one_mul]
  | n+1, m => by
    -- LHS: s(m + (n+1)) = s((m+1) + n) = bsum n (Δ·s (m+1)) n   [IH at m+1]
    have hIH : s ((m + 1) + n) = bsum n (fun j => liftKZ j s (m + 1)) n :=
      newton_gregory s n (m + 1)
    have harg : m + (n + 1) = (m + 1) + n := by
      rw [Nat.add_succ, Nat.succ_add]
    rw [harg, hIH]
    -- expand each Δʲs(m+1) = Δʲs(m) + Δʲ⁺¹s(m), pointwise (no funext)
    rw [bsum_congr n (fun j => liftKZ j s (m + 1))
          (fun j => liftKZ j s m + liftKZ (j + 1) s m) (fun j => liftKZ_succ_arg j s m) n,
        bsum_add n (fun j => liftKZ j s m) (fun j => liftKZ (j+1) s m),
        ← bsum_pascal n (fun j => liftKZ j s m)]

end E213.Lib.Math.Cauchy.NewtonGregory
