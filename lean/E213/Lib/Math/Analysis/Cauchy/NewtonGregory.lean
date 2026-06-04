import E213.Lib.Math.Analysis.Cauchy.DepthPRecursiveInstances
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

namespace E213.Lib.Math.Analysis.Cauchy.NewtonGregory

open E213.Lib.Math.Analysis.Cauchy.DepthPRecursiveInstances (binom binom_zero_right binom_lt_zero binom_diag)
open E213.Meta.Int213
  (add_comm add_assoc add_left_comm add_right_comm mul_comm mul_add add_mul zero_mul
   add_neg_cancel mul_neg neg_mul neg_add mul_sub)

/-! ## §0 — small ℤ rearrangement helpers (pure, over `Int213`) -/

/-- `a + (b − a) = b` (pure). -/
theorem add_sub_cancel_left' (a b : Int) : a + (b - a) = b := by
  rw [Int.sub_eq_add_neg, add_left_comm, add_neg_cancel, Int.add_zero]

/-- `a · 0 = 0` (pure, via `mul_comm` + `zero_mul`). -/
theorem mul_zero' (a : Int) : a * 0 = 0 := by rw [mul_comm, zero_mul]

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

/-- Newton–Gregory at base point `0`: `s n = Σ_{j=0}^n binom(n,j) · (Δʲ s)(0)`. -/
theorem newton_gregory_zero (s : Nat → Int) (n : Nat) :
    s n = bsum n (fun j => liftKZ j s 0) n := by
  have h := newton_gregory s n 0
  rwa [Nat.zero_add] at h

/-! ## §4 — faithful divergence depth over ℤ, and the reconstruction (the converse) -/

/-- A `ℤ`-sequence is constant iff every value equals its value at `0`. -/
def isConstZ (s : Nat → Int) : Prop := ∀ n, s n = s 0

/-- Faithful divergence depth: `polyDepthZ d s` iff the `d`-th forward difference
    is constant.  Over `ℤ` (unlike `ℕ`) this is exactly "genuinely degree ≤ `d`". -/
def polyDepthZ (d : Nat) (s : Nat → Int) : Prop := isConstZ (liftKZ d s)

/-- `a − a = 0` (pure). -/
theorem sub_self_zero (a : Int) : a - a = 0 := by
  rw [Int.sub_eq_add_neg, add_neg_cancel]

/-- The forward difference of a constant `ℤ`-sequence is identically `0`. -/
theorem diffZ_isConstZ_zero {t : Nat → Int} (h : isConstZ t) : ∀ n, diffZ t n = 0 := by
  intro n; show t (n + 1) - t n = 0; rw [h (n + 1), h n, sub_self_zero]

/-- One step past the depth, the difference vanishes identically: `polyDepthZ d s ⟹
    Δ^{d+1}s ≡ 0`. -/
theorem liftKZ_succ_depth_zero {d : Nat} {s : Nat → Int} (h : polyDepthZ d s) :
    ∀ n, liftKZ (d + 1) s n = 0 := diffZ_isConstZ_zero h

/-- If `Δᵖs ≡ 0` then `Δ^{p+k}s ≡ 0` for every `k` (differencing zero stays zero). -/
theorem liftKZ_zero_extend {s : Nat → Int} {p : Nat} (h : ∀ n, liftKZ p s n = 0) :
    ∀ k n, liftKZ (p + k) s n = 0
  | 0,   n => by rw [Nat.add_zero]; exact h n
  | k+1, n => by
    have hk : ∀ n, liftKZ (p + k) s n = 0 := liftKZ_zero_extend h k
    show liftKZ (p + (k + 1)) s n = 0
    rw [Nat.add_succ]
    show diffZ (liftKZ (p + k) s) n = 0
    show liftKZ (p + k) s (n + 1) - liftKZ (p + k) s n = 0
    rw [hk (n + 1), hk n, sub_self_zero]

/-- ★ **Above the depth, every difference-at-a-point vanishes.**  `polyDepthZ d s ⟹
    Δʲs ≡ 0` for all `j > d` — the truncation of the Newton sum. -/
theorem liftKZ_high_zero {d : Nat} {s : Nat → Int} (h : polyDepthZ d s) :
    ∀ j, d < j → ∀ n, liftKZ j s n = 0 := by
  intro j hj n
  obtain ⟨k, hk⟩ := Nat.le.dest hj
  rw [← hk]
  exact liftKZ_zero_extend (liftKZ_succ_depth_zero h) k n

/-- ★ **Tail-truncation of `bsum`.**  If every term strictly above `A` (up to `B`)
    vanishes, the partial sum to `B` equals the partial sum to `A`.  Lets a Newton
    sum be retruncated to the exact degree. -/
theorem bsum_tail_eq (T : Nat) (y : Nat → Int) : ∀ (A B : Nat), A ≤ B →
    (∀ j, A < j → j ≤ B → (binom T j : Int) * y j = 0) → bsum T y B = bsum T y A
  | A, 0,   hAB, _  => by rw [Nat.le_zero.mp hAB]
  | A, B+1, hAB, hz => by
    rcases Nat.eq_or_lt_of_le hAB with heq | hlt
    · rw [heq]
    · have hAB' : A ≤ B := Nat.le_of_lt_succ hlt
      show bsum T y B + (binom T (B + 1) : Int) * y (B + 1) = bsum T y A
      rw [hz (B + 1) (Nat.lt_succ_of_le hAB') (Nat.le_refl _), Int.add_zero]
      exact bsum_tail_eq T y A B hAB' (fun j hj hjB => hz j hj (Nat.le_succ_of_le hjB))

/-- The Newton-form `ℤ`-polynomial `newtonZ c d n = Σ_{i=0}^{d} cᵢ · binom(n,i)`
    (the binomial / Pólya–Ostrowski basis). -/
def newtonZ (c : Nat → Int) (d n : Nat) : Int := bsum n c d

/-- ★★★ **Reconstruction — the ℤ converse that `ℕ` could not state.**  Every
    faithfully depth-`d` sequence is its own Newton series, truncated at `d`:
    `polyDepthZ d s ⟹ ∀ n, s n = Σ_{i=0}^{d} (Δⁱs)(0) · binom(n,i)`.  The
    coefficients are the iterated differences-at-`0` (the Pólya–Ostrowski
    coordinates); over `ℤ` no truncated subtraction corrupts them.  Closes
    HANDOFF Open Problem #4. -/
theorem reconstruct {d : Nat} {s : Nat → Int} (h : polyDepthZ d s) (n : Nat) :
    s n = newtonZ (fun i => liftKZ i s 0) d n := by
  show s n = bsum n (fun i => liftKZ i s 0) d
  rw [newton_gregory_zero s n]
  rcases Nat.le_total d n with hdn | hnd
  · -- d ≤ n: high terms vanish because Δʲs 0 = 0 for j > d
    exact bsum_tail_eq n (fun i => liftKZ i s 0) d n hdn
      (fun j hj _ => by
        show (binom n j : Int) * liftKZ j s 0 = 0
        rw [liftKZ_high_zero h j hj 0]; exact mul_zero' _)
  · -- n ≤ d: extra terms vanish because binom n j = 0 for j > n
    exact (bsum_tail_eq n (fun i => liftKZ i s 0) n d hnd
      (fun j hj _ => by
        show (binom n j : Int) * liftKZ j s 0 = 0
        rw [binom_lt_zero n j hj]; exact zero_mul _)).symm

/-! ## §5 — the inverse transform: `Δⁿ = (E − I)ⁿ` (the binomial-transform involution)

`newton_gregory` is the forward arrow `s ↦ (Δʲs)(0)` read back: `s = F (Δ·s 0)` where
`F` is the binomial transform `(F c) n = Σ binom(n,j) cⱼ`.  The matched inverse arrow
is `Δⁿ = (E − I)ⁿ` expanded:

> ★★★ `newton_gregory_inverse` : `(Δⁿ s)(m) = Σ_{j=0}^{n} (−1)^{n−j} binom(n,j) s(m+j)`.

Together they say the binomial transform and its sign-twisted partner are a matched
inverse pair (the "umbral inverse pair", Pólya–Ostrowski ⇄ monomial change of basis).
The two presentations — a sequence and its iterated differences-at-a-point — are one
object read in two bases, related by an involutive change of basis; this is a
fixed-point-*rich* (grounding) self-map, not a fixed-point-free oscillation.

The sign is handled without a second Pascal induction: on the effective range
`j ≤ n` (where `binom n j ≠ 0`), `(−1)^{n−j} = (−1)ⁿ·(−1)ʲ`, so the whole inverse sum
is `(−1)ⁿ · bsum n (fun j => (−1)ʲ·s(m+j)) n` and the existing `bsum_pascal` carries it. -/

/-- `(−1)^k` as a `ℤ`-valued sign. -/
def negPow : Nat → Int
  | 0   => 1
  | k+1 => -(negPow k)

theorem negPow_succ (k : Nat) : negPow (k + 1) = -(negPow k) := rfl

/-- `bsum` pulls a global sign out of the summand (`Σ binom·(−xⱼ) = −Σ binom·xⱼ`). -/
theorem bsum_neg (T : Nat) (x : Nat → Int) : ∀ L,
    bsum T (fun j => -(x j)) L = -(bsum T x L)
  | 0 => by
    show (binom T 0 : Int) * (-(x 0)) = -((binom T 0 : Int) * x 0)
    rw [mul_neg]
  | L+1 => by
    show bsum T (fun j => -(x j)) L + (binom T (L+1) : Int) * (-(x (L+1)))
       = -(bsum T x L + (binom T (L+1) : Int) * x (L+1))
    rw [bsum_neg T x L, mul_neg, neg_add]

/-- `−(a − b) = b − a` (pure). -/
theorem neg_sub' (a b : Int) : -(a - b) = b - a := by
  rw [Int.sub_eq_add_neg, neg_add, Int.neg_neg, Int.sub_eq_add_neg, add_comm]

/-- ★ **Signed Pascal step**, reusing the forward `bsum_pascal`.  For any `u`:
    `(−1)ⁿ·[ Σ binom(n,j)(−1)ʲ u(j+1) − Σ binom(n,j)(−1)ʲ u j ] =
     (−1)^{n+1}·Σ binom(n+1,j)(−1)ʲ u j`.  The bracket is exactly `−bsum(n+1)` of the
    signed sequence by `bsum_pascal` (the shifted column carries the extra `−1` from
    `(−1)^{j+1}`). -/
theorem inv_step (n : Nat) (u : Nat → Int) :
    negPow n * (bsum n (fun j => negPow j * u (j+1)) n
                - bsum n (fun j => negPow j * u j) n)
    = negPow (n+1) * bsum (n+1) (fun j => negPow j * u j) (n+1) := by
  -- W j = negPow j * u j ;  bsum_pascal: bsum (n+1) W (n+1) = bsum n W n + bsum n (W∘succ) n
  have hshift : bsum n (fun j => (fun i => negPow i * u i) (j+1)) n
              = -(bsum n (fun j => negPow j * u (j+1)) n) := by
    rw [← bsum_neg n (fun j => negPow j * u (j+1)) n]
    exact bsum_congr n _ _ (fun j => by
      show negPow (j+1) * u (j+1) = -(negPow j * u (j+1))
      rw [negPow_succ, neg_mul]) n
  rw [bsum_pascal n (fun j => negPow j * u j), hshift, negPow_succ, neg_mul,
      mul_add, mul_neg, ← Int.sub_eq_add_neg, neg_sub', mul_sub]

/-- ★★★ **Inverse Newton–Gregory: `Δⁿ = (E − I)ⁿ`.**  For every `s : ℕ → ℤ` and all
    `m n`: `(Δⁿ s)(m) = Σ_{j=0}^{n} (−1)^{n−j} binom(n,j) · s(m+j)`, written as
    `(−1)ⁿ · Σ_{j≤n} (−1)ʲ binom(n,j) s(m+j)`.  The matched inverse of `newton_gregory`
    — together they exhibit the binomial transform as a self-paired (involutive)
    change of basis. -/
theorem newton_gregory_inverse (s : Nat → Int) : ∀ n m,
    liftKZ n s m = negPow n * bsum n (fun j => negPow j * s (m + j)) n
  | 0, m => by
    show s m = negPow 0 * bsum 0 (fun j => negPow j * s (m + j)) 0
    show s m = (1 : Int) * ((binom 0 0 : Int) * (negPow 0 * s (m + 0)))
    rw [Nat.add_zero]
    show s m = (1 : Int) * ((1 : Int) * ((1 : Int) * s m))
    rw [Int.one_mul, Int.one_mul, Int.one_mul]
  | n+1, m => by
    show liftKZ n s (m + 1) - liftKZ n s m
       = negPow (n+1) * bsum (n+1) (fun j => negPow j * s (m + j)) (n+1)
    -- bridge s((m+1)+j) = s(m+(j+1)) inside the first sum, factor, then apply inv_step
    rw [newton_gregory_inverse s n (m + 1), newton_gregory_inverse s n m,
        bsum_congr n (fun j => negPow j * s (m + 1 + j))
          (fun j => negPow j * s (m + (j + 1)))
          (fun j => by
            show negPow j * s (m + 1 + j) = negPow j * s (m + (j + 1))
            rw [Nat.add_assoc m 1 j, Nat.add_comm 1 j]) n,
        ← mul_sub]
    exact inv_step n (fun j => s (m + j))

/-- ★★ **Round-trip `F ∘ G = id`.**  Reconstructing a sequence from its
    inverse-transform coefficients returns the sequence: combining the forward
    (`newton_gregory_zero`) and inverse (`newton_gregory_inverse`) arrows, the
    iterated differences-at-`0` are exactly the inverse-transform of `s`, and the
    forward transform inverts them.  The binomial transform is invertible over `ℤ`. -/
theorem binomial_transform_roundtrip (s : Nat → Int) (n : Nat) :
    s n = bsum n (fun j => liftKZ j s 0) n
      ∧ liftKZ n s 0 = negPow n * bsum n (fun j => negPow j * s j) n :=
  ⟨newton_gregory_zero s n, by
    have h := newton_gregory_inverse s n 0
    rw [bsum_congr n (fun j => negPow j * s (0 + j)) (fun j => negPow j * s j)
          (fun j => by
            show negPow j * s (0 + j) = negPow j * s j
            rw [Nat.zero_add]) n] at h
    exact h⟩

/-! ## §6 — the obstruction made precise: ℕ-`diff` and ℤ-`diff` are different Lenses

The genuine degree-2 sequence `(n−2)(n−1)` has nonneg values `2, 0, 0, 2, 6, 12, …`
(`vObs` below).  The **values** are identical in `ℕ` and `ℤ` — what differs is the
difference operator: the genuine first difference `s(1)−s(0) = −2` is faithful over
`ℤ` but **clamps to `0`** over `ℕ`'s truncated subtraction.  That single clamp
breaks constancy of the second difference, so `ℕ`-`polyDepth 2` fails while
`ℤ`-`polyDepthZ 2` holds.  ℕ-`diff` is not a *broken* ℤ-`diff`; it is a different
Lens, agreeing with ℤ-`diff` exactly on the monotone-difference cone (where no
clamp occurs).  ℤ is simply the readout group in which `Δ` closes under iteration. -/

open E213.Lib.Math.Analysis.Cauchy.DivergenceLadder (diff liftK isConst)
open E213.Lib.Math.Analysis.Cauchy.DepthPRecursive (polyDepth)

/-- The genuine nonneg values of `(n−2)(n−1)`: `2, 0, 0, 2, 6, 12, …`
    (`vObs (k+2) = k·(k+1)`). -/
def vObs : Nat → Nat
  | 0   => 2
  | 1   => 0
  | k+2 => k * (k + 1)

/-- The ℤ-faithful first difference clamps over `ℕ`: at `n=0` the genuine slope is
    `−2`, but `ℕ`-`diff` returns `0`.  The exact mechanism of the obstruction. -/
theorem obstruction_first_diff_clamp :
    diffZ (fun n => (vObs n : Int)) 0 = -2 ∧ diff vObs 0 = 0 := by decide

/-- ★ **ℕ-`polyDepth 2` FAILS on a genuine degree-2 sequence.**  The truncated
    second difference jumps `0, 2, 2, …` — `liftK 2 vObs 0 = 0` but
    `liftK 2 vObs 1 = 2` — so it is not constant.  (The single first-difference clamp
    of `obstruction_first_diff_clamp` is what corrupts it.) -/
theorem obstruction_nat : ¬ polyDepth 2 vObs := by
  intro h
  exact absurd (h 1) (by decide)

/-- ★ **ℤ-`polyDepthZ 2` holds at the divergence point.**  The faithful second
    difference is constant `2` exactly where the `ℕ` one jumped:
    `liftKZ 2 (↑vObs) 0 = 2 = liftKZ 2 (↑vObs) 1`.  The genuine degree-2 structure,
    visible once subtraction is faithful.  (`obstruction_nat` shows the `ℕ` Lens
    cannot see it.) -/
theorem obstruction_int_constant :
    liftKZ 2 (fun n => (vObs n : Int)) 0 = 2
      ∧ liftKZ 2 (fun n => (vObs n : Int)) 1 = 2 := by decide

/-! ## §7 — the polynomial growth bound (unblocks T4: Hurwitzian ⟹ poly-bounded)

A faithfully depth-`d` sequence grows at most polynomially:
`|s n| ≤ C·(n+1)^d` with the explicit constant `C = Σ_{i≤d} |Δⁱs(0)|` (the
Pólya–Ostrowski coefficient ℓ¹-norm).  Read off `reconstruct` + the triangle
inequality + `binom n i ≤ (n+1)ⁱ ≤ (n+1)^d`.  This is the ∅-axiom half of
"Hurwitzian (quasi-polynomial partial quotients) ⟹ partial quotients
polynomially bounded ⟹ irrationality measure μ = 2" (Pólya 1915 basis; the μ=2
step is classical, cited) — the general bridge `HANDOFF` flagged Newton–Gregory-
blocked over `ℕ`, now closed over `ℤ`. -/

/-- `(subNatNat m n).natAbs ≤ m + n` (pure; the `ℤ` triangle inequality kernel). -/
theorem natAbs_subNatNat_le (m n : Nat) : (Int.subNatNat m n).natAbs ≤ m + n := by
  unfold Int.subNatNat
  split
  · next => exact Nat.le_trans (Nat.sub_le m n) (Nat.le_add_right m n)
  · next k h =>
      show k + 1 ≤ m + n
      have hk : k + 1 ≤ n := by
        have hle := Nat.sub_le n m; rw [h] at hle; exact hle
      exact Nat.le_trans hk (Nat.le_add_left n m)

/-- ∅-axiom triangle inequality `|a + b| ≤ |a| + |b|` (core `Int.natAbs_add_le`
    pulls `propext`). -/
theorem natAbs_add_le (a b : Int) : (a + b).natAbs ≤ a.natAbs + b.natAbs := by
  cases a with
  | ofNat m => cases b with
    | ofNat n => exact Nat.le_refl _
    | negSucc n =>
      show (Int.subNatNat m (n+1)).natAbs ≤ m + (n+1)
      exact natAbs_subNatNat_le m (n+1)
  | negSucc m => cases b with
    | ofNat n =>
      show (Int.subNatNat n (m+1)).natAbs ≤ (m+1) + n
      exact Nat.le_trans (natAbs_subNatNat_le n (m+1)) (Nat.le_of_eq (Nat.add_comm n (m+1)))
    | negSucc n =>
      show (m + n + 1 + 1) ≤ m + 1 + (n + 1)
      exact Nat.le_of_eq (by rw [Nat.add_succ (m+1) n, Nat.add_right_comm m 1 n])

/-- `|negOfNat j| = j` (pure). -/
theorem natAbs_negOfNat (j : Nat) : (Int.negOfNat j).natAbs = j := by cases j <;> rfl

/-- `|↑k · a| = k · |a|` (pure; nonneg scalar). -/
theorem natAbs_ofNat_mul (k : Nat) (a : Int) : ((k : Int) * a).natAbs = k * a.natAbs := by
  show (Int.ofNat k * a).natAbs = k * a.natAbs
  cases a with
  | ofNat m => rfl
  | negSucc m =>
    show (Int.negOfNat (k * (m+1))).natAbs = k * (m+1)
    rw [natAbs_negOfNat]

/-- The binomial column is bounded by a power: `binom n i ≤ (n+1)ⁱ` (pure). -/
theorem binom_le_pow : ∀ (i n : Nat), binom n i ≤ (n + 1) ^ i
  | 0,   n => by rw [binom_zero_right]; exact Nat.le_refl _
  | i+1, n => by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      show binom n i + binom n (i+1) ≤ (n + 1 + 1) ^ (i+1)
      have hsum : binom n i + binom n (i+1) ≤ (n+1)^i + (n+1)^(i+1) :=
        Nat.add_le_add (binom_le_pow i n) ih
      have hfact : (n+1)^i + (n+1)^(i+1) = (n+1+1) * (n+1)^i := by
        rw [Nat.pow_succ, Nat.succ_mul, Nat.add_comm ((n+1)*(n+1)^i) ((n+1)^i),
            Nat.mul_comm ((n+1)^i) (n+1)]
      have hmul : (n+1+1) * (n+1)^i ≤ (n+1+1) * (n+1+1)^i :=
        Nat.mul_le_mul (Nat.le_refl _) (Nat.pow_le_pow_left (Nat.le_succ (n+1)) i)
      have hpow : (n+1+1) * (n+1+1)^i = (n+1+1)^(i+1) := by rw [Nat.pow_succ, Nat.mul_comm]
      exact Nat.le_trans hsum
        (Nat.le_trans (Nat.le_of_eq hfact) (Nat.le_trans hmul (Nat.le_of_eq hpow)))

/-- `1 ≤ (a+1)^d` (pure). -/
theorem one_le_succ_pow (a : Nat) : ∀ d, 1 ≤ (a + 1) ^ d
  | 0   => Nat.le_refl 1
  | d+1 => by
    rw [Nat.pow_succ]
    exact Nat.mul_le_mul (one_le_succ_pow a d) (Nat.le_add_left 1 a)

/-- The ℓ¹-norm of the Newton coefficients to degree `L`: `Σ_{i≤L} |cᵢ|`. -/
def absSum (c : Nat → Int) : Nat → Nat
  | 0   => (c 0).natAbs
  | L+1 => absSum c L + (c (L+1)).natAbs

/-- ★ **The Newton sum's ℓ∞ growth bound.**  `|bsum n c L| ≤ (n+1)^d · Σ_{i≤L}|cᵢ|`
    for `L ≤ d`: triangle inequality termwise, each `binom n i ≤ (n+1)^d`. -/
theorem bsum_abs_le (n d : Nat) (c : Nat → Int) : ∀ L, L ≤ d →
    (bsum n c L).natAbs ≤ (n + 1) ^ d * absSum c L
  | 0, _ => by
    show ((binom n 0 : Int) * c 0).natAbs ≤ (n + 1) ^ d * (c 0).natAbs
    rw [natAbs_ofNat_mul, binom_zero_right, Nat.one_mul]
    exact Nat.le_trans (Nat.le_of_eq (Nat.one_mul ((c 0).natAbs)).symm)
      (Nat.mul_le_mul (one_le_succ_pow n d) (Nat.le_refl _))
  | L+1, hL => by
    show (bsum n c L + (binom n (L+1) : Int) * c (L+1)).natAbs
       ≤ (n + 1) ^ d * (absSum c L + (c (L+1)).natAbs)
    have hLd : L + 1 ≤ d := hL
    have hbinom : binom n (L+1) ≤ (n + 1) ^ d :=
      Nat.le_trans (binom_le_pow (L+1) n)
        (Nat.pow_le_pow_right (Nat.le_add_left 1 n) hLd)
    calc (bsum n c L + (binom n (L+1) : Int) * c (L+1)).natAbs
        ≤ (bsum n c L).natAbs + ((binom n (L+1) : Int) * c (L+1)).natAbs :=
          natAbs_add_le _ _
      _ = (bsum n c L).natAbs + binom n (L+1) * (c (L+1)).natAbs := by rw [natAbs_ofNat_mul]
      _ ≤ (n + 1) ^ d * absSum c L + (n + 1) ^ d * (c (L+1)).natAbs :=
          Nat.add_le_add (bsum_abs_le n d c L (Nat.le_of_succ_le hLd))
            (Nat.mul_le_mul hbinom (Nat.le_refl _))
      _ = (n + 1) ^ d * (absSum c L + (c (L+1)).natAbs) := (Nat.mul_add _ _ _).symm

/-- ★★★ **Polynomial growth bound (unblocks T4).**  Every faithfully depth-`d`
    sequence grows at most polynomially: `|s n| ≤ C·(n+1)^d` with the explicit
    constant `C = Σ_{i≤d} |Δⁱs(0)|`.  The ∅-axiom half of "Hurwitzian ⟹
    polynomially-bounded partial quotients ⟹ μ = 2" (μ=2 step cited). -/
theorem poly_bound {d : Nat} {s : Nat → Int} (h : polyDepthZ d s) :
    ∃ C, ∀ n, (s n).natAbs ≤ C * (n + 1) ^ d := by
  refine ⟨absSum (fun i => liftKZ i s 0) d, fun n => ?_⟩
  rw [reconstruct h n]
  show (bsum n (fun i => liftKZ i s 0) d).natAbs
     ≤ absSum (fun i => liftKZ i s 0) d * (n + 1) ^ d
  rw [Nat.mul_comm (absSum (fun i => liftKZ i s 0) d) ((n + 1) ^ d)]
  exact bsum_abs_le n d (fun i => liftKZ i s 0) d (Nat.le_refl d)

end E213.Lib.Math.Analysis.Cauchy.NewtonGregory
