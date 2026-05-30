import E213.Lib.Math.Mobius213.Px.QFibIdentity
import E213.Lib.Math.Real213.PhiAsCut
import E213.Meta.Nat.PureNat
import E213.Lib.Math.NatRing

/-!
# FibCassiniNat — the Fibonacci convergents lie below φ (all-Nat, ∀ n)

The φ-convergent-below-φ fact in its native Nat form, avoiding the
propext-laden Int→Nat casts.  With `a := fib(2n+2)`, `b := fib(2n+1)` (the
consecutive Fibonacci pair that the Pell convergents `pellNum/pellDen` equal),
the Cassini-variant norm `a² + 1 = a·b + b²` holds for all n, and
`PhiAsCut.phiCut_false_of_norm` then reads each convergent as below φ.

All ∅-axiom: Lean-core `Nat.{add_mul, mul_assoc}` pull `propext`, so this uses
the repo's PURE replacements `Meta/Nat/PureNat.{add_mul, mul_assoc, even_sq}` and
`Lib/Math/NatRing.{two_mul_eq, three_mul_eq}`.
-/

namespace E213.Lib.Math.Real213.FibCassiniNat

open E213.Lib.Math.Mobius213.Px.FibonacciAtomicLock (fib)
open E213.Meta.Nat.PureNat (add_mul mul_assoc even_sq)
open E213.Lib.Math.NatRing (two_mul_eq three_mul_eq nat_add_left_cancel nat_sub_add_cancel nat_mul_assoc)

/-! ## Nat polynomial helpers (all PURE) -/

private theorem tt (x : Nat) : 2 * (2 * x) = 4 * x := (mul_assoc 2 2 x).symm
private theorem twox_x (x : Nat) : 2 * x + x = 3 * x := by
  rw [three_mul_eq, two_mul_eq]
private theorem c4 (x : Nat) : 3 * x + x = 4 * x := by
  rw [show (4 : Nat) = 3 + 1 from rfl, add_mul, Nat.one_mul]
private theorem c5' (x : Nat) : 4 * x + x = 5 * x := by
  rw [show (5 : Nat) = 4 + 1 from rfl, add_mul, Nat.one_mul]
private theorem c5 (x : Nat) : 3 * x + 2 * x = 5 * x := by
  rw [two_mul_eq, ← Nat.add_assoc, c4, c5']
private theorem c2 (x : Nat) : x + x = 2 * x := (two_mul_eq x).symm

private theorem eL (a b : Nat) :
    (2 * a + b) * (2 * a + b) = 4 * (a * a) + (4 * (a * b) + b * b) := by
  rw [add_mul, Nat.mul_add, Nat.mul_add, even_sq a, tt (a * a),
      show (2 * a) * b = 2 * (a * b) from mul_assoc 2 a b,
      show b * (2 * a) = 2 * (a * b) from by rw [Nat.mul_comm b (2 * a), mul_assoc],
      Nat.add_assoc (4 * (a * a)) (2 * (a * b)) (2 * (a * b) + b * b),
      ← Nat.add_assoc (2 * (a * b)) (2 * (a * b)) (b * b),
      show 2 * (a * b) + 2 * (a * b) = 4 * (a * b) from by rw [← Nat.two_mul, tt]]

private theorem eM (a b : Nat) :
    (2 * a + b) * (a + b) = 2 * (a * a) + (3 * (a * b) + b * b) := by
  rw [add_mul, Nat.mul_add, Nat.mul_add,
      show (2 * a) * a = 2 * (a * a) from mul_assoc 2 a a,
      show (2 * a) * b = 2 * (a * b) from mul_assoc 2 a b, Nat.mul_comm b a,
      Nat.add_assoc (2 * (a * a)) (2 * (a * b)) (a * b + b * b),
      ← Nat.add_assoc (2 * (a * b)) (a * b) (b * b), twox_x (a * b)]

private theorem eR (a b : Nat) :
    (a + b) * (a + b) = a * a + (2 * (a * b) + b * b) := by
  rw [add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm b a,
      Nat.add_assoc (a * a) (a * b) (a * b + b * b),
      ← Nat.add_assoc (a * b) (a * b) (b * b), ← Nat.two_mul (a * b)]

private theorem hR (a b : Nat) :
    (2 * (a * a) + (3 * (a * b) + b * b)) + (a * a + (2 * (a * b) + b * b))
    = (3 * (a * a) + (4 * (a * b) + b * b)) + (a * b + b * b) := by
  rw [show (2 * (a * a) + (3 * (a * b) + b * b)) + (a * a + (2 * (a * b) + b * b))
        = (2 * (a * a) + a * a) + ((3 * (a * b) + 2 * (a * b)) + (b * b + b * b)) from by
        rw [Nat.add_assoc, ← Nat.add_assoc (3 * (a * b) + b * b) (a * a) (2 * (a * b) + b * b),
            Nat.add_comm (3 * (a * b) + b * b) (a * a),
            Nat.add_assoc (a * a) (3 * (a * b) + b * b) (2 * (a * b) + b * b),
            ← Nat.add_assoc (2 * (a * a)) (a * a) _,
            Nat.add_assoc (3 * (a * b)) (b * b) (2 * (a * b) + b * b),
            ← Nat.add_assoc (b * b) (2 * (a * b)) (b * b),
            Nat.add_comm (b * b) (2 * (a * b)),
            Nat.add_assoc (2 * (a * b)) (b * b) (b * b),
            ← Nat.add_assoc (3 * (a * b)) (2 * (a * b)) (b * b + b * b)]]
  rw [twox_x (a * a), c5 (a * b), c2 (b * b)]
  rw [show (3 * (a * a) + (4 * (a * b) + b * b)) + (a * b + b * b)
        = 3 * (a * a) + ((4 * (a * b) + a * b) + (b * b + b * b)) from by
        rw [Nat.add_assoc, ← Nat.add_assoc (4 * (a * b) + b * b) (a * b) (b * b),
            Nat.add_assoc (4 * (a * b)) (b * b) (a * b), Nat.add_comm (b * b) (a * b),
            ← Nat.add_assoc (4 * (a * b)) (a * b) (b * b),
            Nat.add_assoc (4 * (a * b) + a * b) (b * b) (b * b)]]
  rw [c5' (a * b), c2 (b * b)]

/-- The Cassini-variant norm step: from the IH `a² + 1 = a·b + b²` derive the
    same at the doubled pair `(2a+b, a+b)`. -/
private theorem normstep (a b : Nat) (ih : a * a + 1 = a * b + b * b) :
    (2 * a + b) * (2 * a + b) + 1 = (2 * a + b) * (a + b) + (a + b) * (a + b) := by
  rw [eL, eM, eR]
  have hL : 4 * (a * a) + (4 * (a * b) + b * b) + 1
          = (3 * (a * a) + (4 * (a * b) + b * b)) + (a * a + 1) := by
    rw [show (4 : Nat) * (a * a) = 3 * (a * a) + a * a from by
          rw [show (4 : Nat) = 3 + 1 from rfl, add_mul, Nat.one_mul],
        Nat.add_assoc (3 * (a * a)) (a * a) (4 * (a * b) + b * b),
        Nat.add_comm (a * a) (4 * (a * b) + b * b),
        ← Nat.add_assoc (3 * (a * a)) (4 * (a * b) + b * b) (a * a),
        Nat.add_assoc (3 * (a * a) + (4 * (a * b) + b * b)) (a * a) 1]
  rw [hL, hR, ih]

/-! ## Fibonacci couplings (all PURE, from `fib_succ_succ` = rfl) -/

/-- `a := fib(2n+2)` satisfies `a_{n+1} = 2·a_n + b_n`. -/
private theorem aR (n : Nat) :
    fib (2 * n + 4) = 2 * fib (2 * n + 2) + fib (2 * n + 1) := by
  have e1 : fib (2 * n + 4) = fib (2 * n + 3) + fib (2 * n + 2) := rfl
  have e2 : fib (2 * n + 3) = fib (2 * n + 2) + fib (2 * n + 1) := rfl
  rw [e1, e2]
  calc fib (2 * n + 2) + fib (2 * n + 1) + fib (2 * n + 2)
      = fib (2 * n + 2) + fib (2 * n + 2) + fib (2 * n + 1) := by
        rw [Nat.add_assoc, Nat.add_comm (fib (2 * n + 1)) (fib (2 * n + 2)),
            ← Nat.add_assoc]
    _ = 2 * fib (2 * n + 2) + fib (2 * n + 1) := by rw [← Nat.two_mul]

/-- `b := fib(2n+1)` satisfies `b_{n+1} = a_n + b_n`. -/
private theorem bR (n : Nat) :
    fib (2 * n + 3) = fib (2 * n + 2) + fib (2 * n + 1) := rfl

/-! ## The Cassini norm ∀ n, and below-φ -/

/-- ★★ **Fibonacci Cassini norm, ∀ n**: `fib(2n+2)² + 1 = fib(2n+2)·fib(2n+1) +
    fib(2n+1)²`.  Induction with `normstep` over the fib couplings `aR`/`bR`.
    All ∅-axiom Nat. -/
theorem fib_cassini_norm (n : Nat) :
    fib (2 * n + 2) * fib (2 * n + 2) + 1
    = fib (2 * n + 2) * fib (2 * n + 1) + fib (2 * n + 1) * fib (2 * n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
    have ha : fib (2 * (k + 1) + 2) = 2 * fib (2 * k + 2) + fib (2 * k + 1) := by
      rw [show 2 * (k + 1) + 2 = 2 * k + 4 from by rw [Nat.mul_succ]]; exact aR k
    have hb : fib (2 * (k + 1) + 1) = fib (2 * k + 2) + fib (2 * k + 1) := by
      rw [show 2 * (k + 1) + 1 = 2 * k + 3 from by rw [Nat.mul_succ]]; exact bR k
    rw [ha, hb]
    exact normstep (fib (2 * k + 2)) (fib (2 * k + 1)) ih

/-! ## Below φ — the convergents read `false` under `phiCut` -/

/-- Convert the Cassini norm `a²+1 = a·b+b²` (with `b ≤ 2a`, so `p := 2a−b`
    satisfies `p+b = 2a`) into the `phiCut` norm form `p² + 4 = 5·b²`.  All
    additive (eliminating `a` via `2a = p+b`); PURE. -/
private theorem phiform (m k p : Nat) (hpk : p + k = 2 * m)
    (h : m * m + 1 = m * k + k * k) : p * p + 4 = 5 * (k * k) := by
  have e4mm : (2 * m) * (2 * m) = p * p + 2 * (p * k) + k * k := by
    rw [← hpk, add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm k p, ← Nat.add_assoc,
        Nat.add_assoc (p * p) (p * k) (p * k), ← Nat.two_mul (p * k)]
  have h22 : (2 * m) * (2 * m) = 4 * (m * m) := by rw [even_sq, ← mul_assoc]
  have e4mk : (2 * m) * k = p * k + k * k := by rw [← hpk, add_mul]
  have h4mk : 4 * (m * k) = 2 * ((2 * m) * k) := by
    rw [show (2 * m) * k = 2 * (m * k) from mul_assoc 2 m k, ← mul_assoc 2 2 (m * k)]
  have h4 : p * p + 2 * (p * k) + k * k + 4 = 2 * (p * k + k * k) + 4 * (k * k) := by
    rw [← e4mm, ← e4mk, h22,
        show (4 : Nat) * (m * m) + 4 = 4 * (m * m + 1) from by rw [Nat.mul_add, Nat.mul_one],
        h, Nat.mul_add, ← h4mk]
  rw [Nat.mul_add 2 (p * k) (k * k)] at h4
  have hL : p * p + 2 * (p * k) + k * k + 4 = 2 * (p * k) + (p * p + (k * k + 4)) := by
    rw [Nat.add_assoc (p * p) (2 * (p * k)) (k * k), Nat.add_assoc (p * p) (2 * (p * k) + k * k) 4,
        Nat.add_assoc (2 * (p * k)) (k * k) 4, Nat.add_comm (p * p) (2 * (p * k) + (k * k + 4)),
        Nat.add_assoc (2 * (p * k)) (k * k + 4) (p * p), Nat.add_comm (k * k + 4) (p * p),
        ← Nat.add_assoc (2 * (p * k)) (p * p) (k * k + 4)]
  have hR : 2 * (p * k) + 2 * (k * k) + 4 * (k * k) = 2 * (p * k) + (2 * (k * k) + 4 * (k * k)) :=
    Nat.add_assoc (2 * (p * k)) (2 * (k * k)) (4 * (k * k))
  rw [hL, hR] at h4
  have h5 : p * p + (k * k + 4) = 2 * (k * k) + 4 * (k * k) := nat_add_left_cancel h4
  rw [show 2 * (k * k) + 4 * (k * k) = (k * k) + 5 * (k * k) from by
        rw [show (2 : Nat) * (k * k) + 4 * (k * k) = 6 * (k * k) from by rw [← add_mul],
            show (k * k) + 5 * (k * k) = 6 * (k * k) from by
              rw [show (6 : Nat) = 1 + 5 from rfl, add_mul, Nat.one_mul]],
      show p * p + (k * k + 4) = (k * k) + (p * p + 4) from by
        rw [← Nat.add_assoc, Nat.add_comm (p * p) (k * k), Nat.add_assoc]] at h5
  exact nat_add_left_cancel h5

/-- `fib(2n+1) ≤ 2·fib(2n+2)` — Nat-subtraction faithfulness for the convergent
    (the denominator never exceeds twice the numerator). -/
private theorem den_le (n : Nat) : fib (2 * n + 1) ≤ 2 * fib (2 * n + 2) := by
  have hle : fib (2 * n + 1) ≤ fib (2 * n + 2) := by
    show fib (2 * n + 1) ≤ fib (2 * n + 1) + fib (2 * n)
    exact Nat.le_add_right _ _
  have h2 : fib (2 * n + 2) ≤ 2 * fib (2 * n + 2) := by
    have e : 2 * fib (2 * n + 2) = fib (2 * n + 2) + fib (2 * n + 2) := Nat.two_mul _
    rw [e]; exact Nat.le_add_right _ _
  exact Nat.le_trans hle h2

/-- ★★★ **Fibonacci convergents lie below φ, ∀ n** — `phiCut (fib(2n+2))
    (fib(2n+1)) = false` for every n.  The native-Nat form of "every Pell
    convergent is below φ" (`PhiCutConvergents.convergents_below_phi` had it only
    at layers 0..8 by `decide`).  Route: `fib_cassini_norm` (the Cassini norm
    ∀n) → `phiform` (norm → `(2a−b)²+4 = 5·b²`, with `den_le` giving the faithful
    Nat subtraction `p+b = 2a`) → `PhiAsCut.phiCut_false_of_norm`.  All ∅-axiom. -/
theorem fib_convergent_below_phi (n : Nat) :
    E213.Lib.Math.Real213.PhiAsCut.phiCut (fib (2 * n + 2)) (fib (2 * n + 1)) = false := by
  have hpk : (2 * fib (2 * n + 2) - fib (2 * n + 1)) + fib (2 * n + 1)
           = 2 * fib (2 * n + 2) :=
    E213.Lib.Math.NatRing.nat_sub_add_cancel (den_le n)
  have hform : (2 * fib (2 * n + 2) - fib (2 * n + 1)) * (2 * fib (2 * n + 2) - fib (2 * n + 1)) + 4
             = 5 * (fib (2 * n + 1) * fib (2 * n + 1)) :=
    phiform (fib (2 * n + 2)) (fib (2 * n + 1)) (2 * fib (2 * n + 2) - fib (2 * n + 1))
      hpk (fib_cassini_norm n)
  -- `phiCut_false_of_norm` wants `5 * k * k` (= `(5*k)*k`); `hform` has `5 * (k*k)`.
  rw [← mul_assoc 5 (fib (2 * n + 1)) (fib (2 * n + 1))] at hform
  exact E213.Lib.Math.Real213.PhiAsCut.phiCut_false_of_norm
    (fib (2 * n + 2)) (fib (2 * n + 1)) hform

/-! ## Toward the Cauchy-complete limit — consecutive-convergent cross-product

For the `CauchyCutSeq` limit construction (`Analysis/CauchyComplete`), the key
fact is that consecutive convergents differ by exactly `1` in cross-product
(equivalently `1/(den_n·den_{n+1})` in value), so they nest and the brackets
shrink.  Combined with `fib_convergent_below_phi` (all convergents below φ) and
monotone increase, this gives a constructible modulus for each rational target. -/

/-- Generic cross-product step: from the Cassini norm `A²+1 = A·B+B²`,
    `(2A+B)·B = A·(A+B) + 1` — i.e. the two consecutive convergents
    `A/B` and `(2A+B)/(A+B)` have cross-product difference exactly `1`. -/
theorem cross_gen (A B : Nat) (norm : A * A + 1 = A * B + B * B) :
    (2 * A + B) * B = A * (A + B) + 1 := by
  rw [add_mul, Nat.mul_add, show 2 * A * B = A * B + A * B from by rw [Nat.two_mul, add_mul]]
  rw [Nat.add_assoc (A * B) (A * B) (B * B), ← norm]
  rw [Nat.add_comm (A * B) (A * A + 1), Nat.add_assoc, Nat.add_comm 1 (A * B),
      ← Nat.add_assoc]

/-- **Consecutive-convergent cross-product = +1, ∀ n**:
    `fib(2n+4)·fib(2n+1) = fib(2n+2)·fib(2n+3) + 1`.  The Fibonacci form of
    "adjacent convergents differ by one unit" — the nesting/shrinking witness for
    the Cauchy limit.  From `fib_cassini_norm` via `cross_gen`. -/
theorem convergent_cross (n : Nat) :
    fib (2 * n + 4) * fib (2 * n + 1) = fib (2 * n + 2) * fib (2 * n + 3) + 1 := by
  have hA : fib (2 * n + 4) = 2 * fib (2 * n + 2) + fib (2 * n + 1) := by
    have e1 : fib (2 * n + 4) = fib (2 * n + 3) + fib (2 * n + 2) := rfl
    have e2 : fib (2 * n + 3) = fib (2 * n + 2) + fib (2 * n + 1) := rfl
    rw [e1, e2]
    calc fib (2 * n + 2) + fib (2 * n + 1) + fib (2 * n + 2)
        = fib (2 * n + 2) + fib (2 * n + 2) + fib (2 * n + 1) := by
          rw [Nat.add_assoc, Nat.add_comm (fib (2 * n + 1)) (fib (2 * n + 2)),
              ← Nat.add_assoc]
      _ = 2 * fib (2 * n + 2) + fib (2 * n + 1) := by rw [← Nat.two_mul]
  have hB : fib (2 * n + 3) = fib (2 * n + 2) + fib (2 * n + 1) := rfl
  rw [hA, hB]
  exact cross_gen (fib (2 * n + 2)) (fib (2 * n + 1)) (fib_cassini_norm n)

/-! ## Monotonicity, positivity, and the Cauchy (antitone) property

Toward `phiCut` as a `CauchyCutSeq` limit (`Analysis/CauchyComplete`): the cut
sequence `i ↦ pellConvergentCut i` is **antitone at every rational target**
(`cs_antitone`) — its Bool value flips `true → false` at most once as `i` grows,
because the convergents strictly increase (`conv_mono`).  An antitone Bool
sequence is automatically Cauchy, so the modulus exists; `fib_odd_pos` /
`fib_lb` (the Archimedean lower bound `n+1 ≤ fib(2n+1)`) give the positivity and
unboundedness the explicit modulus needs. -/

/-- Convergents strictly increase: `conv_n < conv_{n+1}` as cross-products.
    From `convergent_cross` (the difference is exactly `1`). -/
theorem conv_mono (n : Nat) :
    fib (2 * n + 2) * fib (2 * n + 3) < fib (2 * n + 4) * fib (2 * n + 1) := by
  rw [convergent_cross n]; exact Nat.lt_succ_self _

/-- `1 ≤ fib(2i+1)` — the denominators are positive (Nat-faithful cross-mult). -/
theorem fib_odd_pos (i : Nat) : 1 ≤ fib (2 * i + 1) := by
  induction i with
  | zero => decide
  | succ k ih =>
    show 1 ≤ fib (2 * k + 3)
    have h : fib (2 * k + 3) = fib (2 * k + 2) + fib (2 * k + 1) := rfl
    rw [h]; exact Nat.le_trans ih (Nat.le_add_left _ _)

/-- **Archimedean lower bound**: `n + 1 ≤ fib(2n+1)`.  The denominators grow at
    least linearly, so they exceed any bound — the convergents reach any rational
    target below φ in finitely many steps (constructible Cauchy modulus). -/
theorem fib_lb (n : Nat) : n + 1 ≤ fib (2 * n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
    have e : fib (2 * (k + 1) + 1) = fib (2 * k + 1) + fib (2 * k + 2) := by
      show fib (2 * k + 3) = fib (2 * k + 1) + fib (2 * k + 2)
      have h : fib (2 * k + 3) = fib (2 * k + 2) + fib (2 * k + 1) := rfl
      rw [h, Nat.add_comm]
    rw [e]
    have h1 : 1 ≤ fib (2 * k + 2) :=
      Nat.le_trans (fib_odd_pos k) (Nat.le_add_right _ _)
    calc k + 1 + 1 ≤ fib (2 * k + 1) + 1 := Nat.add_le_add_right ih 1
      _ ≤ fib (2 * k + 1) + fib (2 * k + 2) := Nat.add_le_add_left h1 _

/-- ★★ **Cauchy (antitone) property**: at every rational target `(m, k)`, the
    convergent cut value is antitone in the layer — `pellConvergentCut (i+1)`
    true implies `pellConvergentCut i` true (so the Bool flips at most once,
    `true → false`).  Stated on `fib`: `fib(2i+4)·k ≤ fib(2i+3)·m` (the layer
    `i+1` cut) implies `fib(2i+2)·k ≤ fib(2i+1)·m` (the layer `i` cut).  By
    `conv_mono` + positive cross-multiplication cancellation (`fib_odd_pos`). -/
theorem cs_antitone (i m k : Nat)
    (H : fib (2 * i + 4) * k ≤ fib (2 * i + 3) * m) :
    fib (2 * i + 2) * k ≤ fib (2 * i + 1) * m := by
  have hmono : fib (2 * i + 2) * fib (2 * i + 3) ≤ fib (2 * i + 4) * fib (2 * i + 1) :=
    Nat.le_of_lt (conv_mono i)
  have hpos : 0 < fib (2 * i + 3) := fib_odd_pos (i + 1)
  have key : fib (2 * i + 3) * (fib (2 * i + 2) * k)
           ≤ fib (2 * i + 3) * (fib (2 * i + 1) * m) := by
    calc fib (2 * i + 3) * (fib (2 * i + 2) * k)
        = (fib (2 * i + 2) * fib (2 * i + 3)) * k := by
          rw [← nat_mul_assoc, Nat.mul_comm (fib (2 * i + 3)) (fib (2 * i + 2))]
      _ ≤ (fib (2 * i + 4) * fib (2 * i + 1)) * k := Nat.mul_le_mul_right k hmono
      _ = fib (2 * i + 1) * (fib (2 * i + 4) * k) := by
          rw [Nat.mul_comm (fib (2 * i + 4)) (fib (2 * i + 1)), nat_mul_assoc]
      _ ≤ fib (2 * i + 1) * (fib (2 * i + 3) * m) := Nat.mul_le_mul_left _ H
      _ = fib (2 * i + 3) * (fib (2 * i + 1) * m) := by
          rw [← nat_mul_assoc, Nat.mul_comm (fib (2 * i + 1)) (fib (2 * i + 3)), nat_mul_assoc]
  exact Nat.le_of_mul_le_mul_left key hpos

end E213.Lib.Math.Real213.FibCassiniNat
