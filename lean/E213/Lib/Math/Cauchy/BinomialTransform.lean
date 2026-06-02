import E213.Lib.Math.Cauchy.NewtonGregory

/-!
# BinomialTransform — the self-inverse binomial transform and its fixed points

The sign-twisted binomial transform `T s n = Σ_{j≤n} (−1)ʲ binom(n,j) s(j)` is an
**involution** over `ℤ`:

> ★★★ `binomialT_involutive` : `T (T s) = s`.

and it is **fixed-point-rich** — for *every* `s`, the sequence `s + T s` is a fixed
point (`binomialT_fixed`).  This earns the "self-inverse Lens" reading of
Newton–Gregory (`seed/AXIOM/05_no_exterior.md` §5.2): the transform is a genuine
involutive *change of basis* with a large fixed set, i.e. **Nat-style** grounding
(a fixed point exists and the iteration settles), the *opposite* of the
fixed-point-free Bool-style liar oscillation `not ∘ not = id`.

The proof reuses `binomial_transform_roundtrip` (= `newton_gregory` + its inverse):
`T s n = (−1)ⁿ · (Δⁿ s)(0)`, and `(−1)ⁿ·(−1)ⁿ = 1` collapses the double transform
back onto the forward Newton identity.  All ∅-axiom.
-/

namespace E213.Lib.Math.Cauchy.BinomialTransform

open E213.Lib.Math.Cauchy.NewtonGregory
  (liftKZ bsum negPow negPow_succ bsum_add bsum_neg bsum_congr add_add_add_comm
   binomial_transform_roundtrip)
open E213.Meta.Int213 (add_comm mul_assoc mul_add neg_mul mul_neg neg_add add_neg_cancel)

/-- The self-inverse binomial transform `T s n = Σ_{j≤n} (−1)ʲ binom(n,j) s(j)`. -/
def binomialT (s : Nat → Int) (n : Nat) : Int := bsum n (fun j => negPow j * s j) n

/-- `(−1)ⁿ · (−1)ⁿ = 1`. -/
theorem negPow_sq_one : ∀ n, negPow n * negPow n = 1
  | 0   => rfl
  | n+1 => by rw [negPow_succ, neg_mul, mul_neg, Int.neg_neg, negPow_sq_one n]

/-- ★ `T s n = (−1)ⁿ · (Δⁿ s)(0)` — the transform reads off the iterated
    differences-at-`0`, signed.  (From `newton_gregory_inverse`, with the `(−1)ⁿ`
    pulled across via `negPow_sq_one`.) -/
theorem binomialT_eq (s : Nat → Int) (n : Nat) :
    binomialT s n = negPow n * liftKZ n s 0 := by
  show bsum n (fun j => negPow j * s j) n = negPow n * liftKZ n s 0
  rw [(binomial_transform_roundtrip s n).2, ← mul_assoc, negPow_sq_one, Int.one_mul]

/-- ★★★ **The binomial transform is an involution: `T (T s) = s`.**  A genuine
    self-inverse change of basis (Pólya–Ostrowski ⇄ monomial). -/
theorem binomialT_involutive (s : Nat → Int) (n : Nat) :
    binomialT (binomialT s) n = s n := by
  show bsum n (fun j => negPow j * binomialT s j) n = s n
  rw [bsum_congr n (fun j => negPow j * binomialT s j) (fun j => liftKZ j s 0)
        (fun j => by
          show negPow j * binomialT s j = liftKZ j s 0
          rw [binomialT_eq s j, ← mul_assoc, negPow_sq_one, Int.one_mul]) n]
  exact (binomial_transform_roundtrip s n).1.symm

/-- The transform is additive: `T (u + v) = T u + T v`. -/
theorem binomialT_add (u v : Nat → Int) (n : Nat) :
    binomialT (fun m => u m + v m) n = binomialT u n + binomialT v n := by
  show bsum n (fun j => negPow j * (u j + v j)) n
     = bsum n (fun j => negPow j * u j) n + bsum n (fun j => negPow j * v j) n
  rw [bsum_congr n (fun j => negPow j * (u j + v j))
        (fun j => negPow j * u j + negPow j * v j) (fun j => mul_add (negPow j) (u j) (v j)) n,
      bsum_add n (fun j => negPow j * u j) (fun j => negPow j * v j)]

/-- ★★ **The transform is fixed-point-rich (Nat-style, not Bool-style).**  For
    *every* `s`, the sequence `s + T s` is a fixed point of `T`: `T (s + T s) =
    s + T s`.  An involution with a large fixed set — grounding, the opposite of
    the fixed-point-free liar oscillation. -/
theorem binomialT_fixed (s : Nat → Int) (n : Nat) :
    binomialT (fun m => s m + binomialT s m) n = s n + binomialT s n := by
  rw [binomialT_add s (binomialT s) n, binomialT_involutive s n, add_comm]

/-- The transform negates: `T (−u) = −(T u)`. -/
theorem binomialT_neg (u : Nat → Int) (n : Nat) :
    binomialT (fun m => -(u m)) n = -(binomialT u n) := by
  show bsum n (fun j => negPow j * -(u j)) n = -(bsum n (fun j => negPow j * u j) n)
  rw [bsum_congr n (fun j => negPow j * -(u j)) (fun j => -(negPow j * u j))
        (fun j => mul_neg (negPow j) (u j)) n,
      bsum_neg n (fun j => negPow j * u j)]

/-- ★★ **The `−1` eigenspace.**  For every `s`, `s − T s` is an *anti*-fixed point:
    `T (s − T s) = −(s − T s)`.  Together with `binomialT_fixed` (the `+1`
    eigenspace) this is the full spectral picture: `T` has eigenvalues `±1` and both
    eigenspaces are large — a fixed-point-rich involution. -/
theorem binomialT_antifixed (s : Nat → Int) (n : Nat) :
    binomialT (fun m => s m + -(binomialT s m)) n = -(s n + -(binomialT s n)) := by
  rw [binomialT_add s (fun m => -(binomialT s m)) n, binomialT_neg (binomialT s) n,
      binomialT_involutive s n, neg_add, Int.neg_neg, add_comm]

/-- ★★ **The `±1` eigenspaces span (up to a factor 2).**  Pointwise
    `(s + T s) + (s − T s) = s + s = 2s`: every sequence's double is the sum of its
    `+1`-eigen part (`s + T s`) and `−1`-eigen part (`s − T s`).  Definitive
    fixed-point-richness — Nat-style, not the fixed-point-free Bool liar. -/
theorem binomialT_eigendecomp (s : Nat → Int) (n : Nat) :
    (s n + binomialT s n) + (s n + -(binomialT s n)) = s n + s n := by
  rw [add_add_add_comm (s n) (binomialT s n) (s n) (-(binomialT s n)),
      add_neg_cancel, Int.add_zero]

end E213.Lib.Math.Cauchy.BinomialTransform
