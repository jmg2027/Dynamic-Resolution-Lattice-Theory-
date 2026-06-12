import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChooseFactorial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
import E213.Lib.Math.NumberTheory.LcmGrowthChebyshev
import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.PolyNatMTactic

/-!
# AperyIntegrality — Brick 2 (Apéry integrality, ζ(3) input I1), ∅-axiom

The integrality `2·lcm(1..n)³·aₙ ∈ ℕ` of the reduced Apéry numerators, as pure
divisibility chains (no `ord_p`, no Legendre, no primes — the heart collapses to
exact cofactor equations).

  * **§1 — the trinomial double identity** (`aperyTrinomial`): in the
    subtraction-free additive parametrisation `n = m+a+b`, `k = m+b`,
    `C(n,k)·C(n+k,k)·C(k,m)² = C(n,m)·C(n+m,m)·C(n−m,k−m)·C(n+k,n+m)`.  Both sides
    clear to `(2m+a+2b)! / (a!·(m!)²·(b!)²)`.
  * **§2 — KeyDiv** (in progress): `m·C(k,m) ∣ lcm(1..k)`, via the finite-difference
    identity `Σⱼ(−1)ʲC(s,j)·Πᵢ≠ⱼ(m+i) = s!`.  Foundations here: the rising
    factorial `rprod`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.AperyIntegrality

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChooseFactorial (choose_mul_factorials choose_symm)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose_succ_mul)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial (factorial factorial_pos
  factorial_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose_succ_succ choose_zero_right
  choose_eq_zero_of_lt choose_self)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ sumTo_zero)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem (sumTo_split_first sumTo_congr
  sumTo_add_func sumTo_mul_left)
open E213.Meta.Nat.NatDiv213 (add_mod_right_pos div_add_mod_pure mul_witness_iff_mod_eq_zero)
open E213.Tactic.NatHelper (sub_add_cancel add_right_cancel add_sub_of_le add_sub_cancel_right
  mul_sub mul_left_cancel_pos)
open E213.Lib.Math.NumberTheory.LcmGrowthChebyshev (lcmUpTo dvd_lcmUpTo lcmUpTo_dvd)

/-! ## §0 — pure mod-2 parity (standard `Nat.{mod_two_eq_zero_or_one,add_mod}` are propext) -/

/-- `j % 2` is `0` or `1`. -/
theorem mod2_cases (j : Nat) : j % 2 = 0 ∨ j % 2 = 1 := by
  have h : j % 2 < 2 := Nat.mod_lt j (by decide)
  rcases Nat.lt_or_ge (j % 2) 1 with h0 | h1
  · exact Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ h0) (Nat.zero_le _))
  · exact Or.inr (Nat.le_antisymm (Nat.le_of_lt_succ h) h1)

/-- `(j+1) % 2 = 1 − j%2`, as `if`: flips parity. -/
theorem succ_mod2 : ∀ j, (j + 1) % 2 = if j % 2 = 0 then 1 else 0
  | 0 => by decide
  | 1 => by decide
  | j + 2 => by
      rw [show j + 2 + 1 = (j + 1) + 2 from by ring_nat, add_mod_right_pos (by decide) (j + 1),
          add_mod_right_pos (by decide) j]
      exact succ_mod2 j

/-! ## §1 — the trinomial double identity -/

/-- The left side cleared by `a!·(m!)²·(b!)²` telescopes to `(2m+a+2b)!`. -/
private theorem lhs_clear (m a b : Nat) :
    (choose (m + a + b) (m + b) * choose (2 * m + a + 2 * b) (m + b)
        * (choose (m + b) m * choose (m + b) m))
      * (factorial a * factorial m * factorial m * factorial b * factorial b)
    = factorial (2 * m + a + 2 * b) := by
  have id1 : choose (m + b) m * (factorial m * factorial b) = factorial (m + b) :=
    choose_mul_factorials m b
  have id2 : choose (m + a + b) (m + b) * (factorial (m + b) * factorial a)
      = factorial (m + a + b) := by
    have h := choose_mul_factorials (m + b) a
    rwa [show m + b + a = m + a + b from by ring_nat] at h
  have id3 : choose (2 * m + a + 2 * b) (m + b) * (factorial (m + b) * factorial (m + a + b))
      = factorial (2 * m + a + 2 * b) := by
    have h := choose_mul_factorials (m + b) (m + a + b)
    rwa [show m + b + (m + a + b) = 2 * m + a + 2 * b from by ring_nat] at h
  calc (choose (m + a + b) (m + b) * choose (2 * m + a + 2 * b) (m + b)
          * (choose (m + b) m * choose (m + b) m))
        * (factorial a * factorial m * factorial m * factorial b * factorial b)
      = choose (2 * m + a + 2 * b) (m + b) * (choose (m + a + b) (m + b)
          * (choose (m + b) m * (factorial m * factorial b))
          * (choose (m + b) m * (factorial m * factorial b)) * factorial a) := by ring_nat
    _ = choose (2 * m + a + 2 * b) (m + b)
          * (choose (m + a + b) (m + b) * factorial (m + b) * factorial (m + b) * factorial a) := by
        rw [id1]
    _ = choose (2 * m + a + 2 * b) (m + b)
          * (factorial (m + b) * (choose (m + a + b) (m + b) * (factorial (m + b) * factorial a))) := by
        ring_nat
    _ = choose (2 * m + a + 2 * b) (m + b) * (factorial (m + b) * factorial (m + a + b)) := by
        rw [id2]
    _ = factorial (2 * m + a + 2 * b) := id3

/-- The right side cleared by `a!·(m!)²·(b!)²` telescopes to `(2m+a+2b)!`. -/
private theorem rhs_clear (m a b : Nat) :
    (choose (m + a + b) m * choose (2 * m + a + b) m * choose (a + b) b
        * choose (2 * m + a + 2 * b) (2 * m + a + b))
      * (factorial a * factorial m * factorial m * factorial b * factorial b)
    = factorial (2 * m + a + 2 * b) := by
  have id1 : choose (a + b) b * (factorial b * factorial a) = factorial (a + b) := by
    have h := choose_mul_factorials b a
    rwa [show b + a = a + b from by ring_nat] at h
  have id2 : choose (m + a + b) m * (factorial m * factorial (a + b)) = factorial (m + a + b) := by
    have h := choose_mul_factorials m (a + b)
    rwa [show m + (a + b) = m + a + b from by ring_nat] at h
  have id3 : choose (2 * m + a + b) m * (factorial m * factorial (m + a + b))
      = factorial (2 * m + a + b) := by
    have h := choose_mul_factorials m (m + a + b)
    rwa [show m + (m + a + b) = 2 * m + a + b from by ring_nat] at h
  have id4 : choose (2 * m + a + 2 * b) (2 * m + a + b)
      * (factorial (2 * m + a + b) * factorial b) = factorial (2 * m + a + 2 * b) := by
    have h := choose_mul_factorials (2 * m + a + b) b
    rwa [show 2 * m + a + b + b = 2 * m + a + 2 * b from by ring_nat] at h
  calc (choose (m + a + b) m * choose (2 * m + a + b) m * choose (a + b) b
          * choose (2 * m + a + 2 * b) (2 * m + a + b))
        * (factorial a * factorial m * factorial m * factorial b * factorial b)
      = choose (m + a + b) m * choose (2 * m + a + b) m
          * choose (2 * m + a + 2 * b) (2 * m + a + b)
          * (choose (a + b) b * (factorial b * factorial a)) * factorial m * factorial m
          * factorial b := by ring_nat
    _ = choose (m + a + b) m * choose (2 * m + a + b) m
          * choose (2 * m + a + 2 * b) (2 * m + a + b)
          * factorial (a + b) * factorial m * factorial m * factorial b := by rw [id1]
    _ = choose (2 * m + a + b) m * choose (2 * m + a + 2 * b) (2 * m + a + b)
          * (choose (m + a + b) m * (factorial m * factorial (a + b))) * factorial m
          * factorial b := by ring_nat
    _ = choose (2 * m + a + b) m * choose (2 * m + a + 2 * b) (2 * m + a + b)
          * factorial (m + a + b) * factorial m * factorial b := by rw [id2]
    _ = choose (2 * m + a + 2 * b) (2 * m + a + b)
          * (choose (2 * m + a + b) m * (factorial m * factorial (m + a + b))) * factorial b := by
        ring_nat
    _ = choose (2 * m + a + 2 * b) (2 * m + a + b) * factorial (2 * m + a + b) * factorial b := by
        rw [id3]
    _ = choose (2 * m + a + 2 * b) (2 * m + a + b)
          * (factorial (2 * m + a + b) * factorial b) := by ring_nat
    _ = factorial (2 * m + a + 2 * b) := id4

/-- ★★★ **The trinomial double identity** (Brick 2 step 1), additive form
    `n = m+a+b`, `k = m+b`: `C(n,k)·C(n+k,k)·C(k,m)² = C(n,m)·C(n+m,m)·C(n−m,k−m)·
    C(n+k,n+m)`.  Both sides clear by `a!·(m!)²·(b!)²` to `(2m+a+2b)!`. -/
theorem aperyTrinomial (m a b : Nat) :
    choose (m + a + b) (m + b) * choose (2 * m + a + 2 * b) (m + b)
        * (choose (m + b) m * choose (m + b) m)
    = choose (m + a + b) m * choose (2 * m + a + b) m * choose (a + b) b
        * choose (2 * m + a + 2 * b) (2 * m + a + b) := by
  have hD : 0 < factorial a * factorial m * factorial m * factorial b * factorial b :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (factorial_pos a) (factorial_pos m))
      (factorial_pos m)) (factorial_pos b)) (factorial_pos b)
  exact Nat.eq_of_mul_eq_mul_right hD ((lhs_clear m a b).trans (rhs_clear m a b).symm)

/-! ## §2 — KeyDiv foundations: the rising factorial -/

/-- Rising factorial `(m)(m+1)···(m+len−1)`, `len` factors (`rprod m 0 = 1`). -/
def rprod (m : Nat) : Nat → Nat
  | 0 => 1
  | len + 1 => rprod m len * (m + len)

/-- Back factor: `rprod m (len+1) = rprod m len · (m+len)`. -/
theorem rprod_back (m len : Nat) : rprod m (len + 1) = rprod m len * (m + len) := rfl

/-- Front factor: `rprod m (len+1) = m · rprod (m+1) len`. -/
theorem rprod_front (m : Nat) : ∀ len, rprod m (len + 1) = m * rprod (m + 1) len
  | 0 => by show 1 * (m + 0) = m * 1; rw [Nat.one_mul, Nat.add_zero, Nat.mul_one]
  | len + 1 => by
      show rprod m (len + 1) * (m + (len + 1)) = m * (rprod (m + 1) len * (m + 1 + len))
      rw [rprod_front m len, show m + (len + 1) = m + 1 + len from by ring_nat]
      ring_nat

/-- `rprod 1 len = len!`. -/
theorem rprod_one (len : Nat) : rprod 1 len = factorial len := by
  induction len with
  | zero => rfl
  | succ len ih => rw [rprod_back, ih, factorial_succ, Nat.add_comm 1 len, Nat.mul_comm]

/-- `rprod m len > 0` when `m ≥ 1` (every factor `m+i ≥ 1`). -/
theorem rprod_pos {m : Nat} (hm : 1 ≤ m) : ∀ len, 0 < rprod m len
  | 0 => Nat.zero_lt_one
  | len + 1 => Nat.mul_pos (rprod_pos hm len) (Nat.le_trans hm (Nat.le_add_right m len))

/-- Pure `(s+1) − j = (s−j) + 1` for `j ≤ s` (`Nat.succ_sub` carries `propext`). -/
private theorem succ_sub_pure {s j : Nat} (hj : j ≤ s) : (s + 1) - j = (s - j) + 1 := by
  have e1 : ((s - j) + 1) + j = s + 1 := by rw [Nat.add_right_comm, sub_add_cancel hj]
  have e2 : ((s + 1) - j) + j = s + 1 := sub_add_cancel (Nat.le_succ_of_le hj)
  exact add_right_cancel (e2.trans e1.symm)

/-- The product `Π_{i∈[0,s], i≠j}(m+i)` (meaningful for `j ≤ s`). -/
def Qex (m s j : Nat) : Nat := rprod m j * rprod (m + j + 1) (s - j)

/-- Back recurrence: extending the range by `m+s+1`.  `Qex m (s+1) j = (m+s+1)·Qex m s j`
    for `j ≤ s` (the new factor `m+s+1` joins the product). -/
theorem Qex_back {s j : Nat} (hj : j ≤ s) (m : Nat) :
    Qex m (s + 1) j = (m + s + 1) * Qex m s j := by
  show rprod m j * rprod (m + j + 1) ((s + 1) - j)
    = (m + s + 1) * (rprod m j * rprod (m + j + 1) (s - j))
  rw [succ_sub_pure hj, rprod_back,
      show m + j + 1 + (s - j) = m + s + 1 from by
        rw [show m + j + 1 + (s - j) = (m + 1) + (j + (s - j)) from by ring_nat,
            Nat.add_comm j (s - j), sub_add_cancel hj]; ring_nat]
  ring_nat

/-- Front recurrence: peeling the first factor `m`.  `Qex m (s+1) (j+1) = m·Qex (m+1) s j`. -/
theorem Qex_front (m s j : Nat) : Qex m (s + 1) (j + 1) = m * Qex (m + 1) s j := by
  show rprod m (j + 1) * rprod (m + (j + 1) + 1) ((s + 1) - (j + 1))
    = m * (rprod (m + 1) j * rprod (m + 1 + j + 1) (s - j))
  rw [rprod_front m j, Nat.succ_sub_succ, show m + (j + 1) + 1 = m + 1 + j + 1 from by ring_nat]
  ring_nat

/-- Excluding the last index leaves the all-before product: `Qex m s s = rprod m s`. -/
theorem Qex_self (m s : Nat) : Qex m s s = rprod m s := by
  show rprod m s * rprod (m + s + 1) (s - s) = rprod m s
  rw [Nat.sub_self]; show rprod m s * 1 = rprod m s; rw [Nat.mul_one]

/-! ## §3 — the even/odd finite-difference sums -/

/-- Even-indexed part of the signed sum `Σⱼ(−1)ʲC(s,j)·Qex m s j`. -/
def fdPos (m s : Nat) : Nat :=
  sumTo (s + 1) (fun j => if j % 2 = 0 then choose s j * Qex m s j else 0)

/-- Odd-indexed part. -/
def fdNeg (m s : Nat) : Nat :=
  sumTo (s + 1) (fun j => if j % 2 = 1 then choose s j * Qex m s j else 0)

theorem fdPos_zero (m : Nat) : fdPos m 0 = 1 := by
  show sumTo 1 (fun j => if j % 2 = 0 then choose 0 j * Qex m 0 j else 0) = 1
  rw [sumTo_succ, sumTo_zero, Nat.zero_add]
  show (if (0 : Nat) % 2 = 0 then choose 0 0 * Qex m 0 0 else 0) = 1
  rw [if_pos (by decide), choose_zero_right, Qex_self, show rprod m 0 = 1 from rfl, Nat.mul_one]

theorem fdNeg_zero (m : Nat) : fdNeg m 0 = 0 := by
  show sumTo 1 (fun j => if j % 2 = 1 then choose 0 j * Qex m 0 j else 0) = 0
  rw [sumTo_succ, sumTo_zero, Nat.zero_add]
  show (if (0 : Nat) % 2 = 1 then choose 0 0 * Qex m 0 0 else 0) = 0
  rw [if_neg (by decide)]

/-- The crux pointwise split for `(P)`: the shifted even-term `g(j+1)` splits (via
    Pascal + `Qex_front` on `C(s,j)`, `Qex_back` on `C(s,j+1)`, parity flip) into the
    `m·fdNeg(m+1,·)` and `(m+s+1)·fdPos(m,·)` contributions. -/
private theorem term_split (m s j : Nat) :
    (if (j + 1) % 2 = 0 then choose (s + 1) (j + 1) * Qex m (s + 1) (j + 1) else 0)
    = m * (if j % 2 = 1 then choose s j * Qex (m + 1) s j else 0)
      + (m + s + 1) * (if (j + 1) % 2 = 0 then choose s (j + 1) * Qex m s (j + 1) else 0) := by
  rcases mod2_cases j with hj | hj
  · have h1 : (j + 1) % 2 = 1 := by rw [succ_mod2 j, if_pos hj]
    rw [if_neg (show ¬ (j + 1) % 2 = 0 from by rw [h1]; decide),
        if_neg (show ¬ j % 2 = 1 from by rw [hj]; decide),
        if_neg (show ¬ (j + 1) % 2 = 0 from by rw [h1]; decide),
        Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
  · have h1 : (j + 1) % 2 = 0 := by
      rw [succ_mod2 j, if_neg (show ¬ j % 2 = 0 from by rw [hj]; decide)]
    rw [if_pos h1, if_pos hj, if_pos h1, choose_succ_succ s j]
    rcases Nat.lt_or_ge s (j + 1) with hlt | hge
    · rw [choose_eq_zero_of_lt s (j + 1) hlt, Qex_front m s j, Nat.add_zero (choose s j),
          Nat.zero_mul (Qex m s (j + 1)), Nat.mul_zero (m + s + 1),
          Nat.add_zero (m * (choose s j * Qex (m + 1) s j))]
      ring_nat
    · have hfront : Qex m (s + 1) (j + 1) = m * Qex (m + 1) s j := Qex_front m s j
      have hback : Qex m (s + 1) (j + 1) = (m + s + 1) * Qex m s (j + 1) := Qex_back hge m
      rw [show m * (choose s j * Qex (m + 1) s j) = choose s j * (m * Qex (m + 1) s j) from by
            ring_nat,
          show (m + s + 1) * (choose s (j + 1) * Qex m s (j + 1))
            = choose s (j + 1) * ((m + s + 1) * Qex m s (j + 1)) from by ring_nat,
          ← hfront, ← hback]
      ring_nat

/-! ## §4 — the recurrence system (P)/(N) and the FD identity `fdPos = s! + fdNeg` -/

/-- The `j = s` term of the `B`-sum vanishes (`C(s,s+1) = 0`). -/
private theorem Bterm_top (m s : Nat) :
    (if (s + 1) % 2 = 0 then choose s (s + 1) * Qex m s (s + 1) else 0) = 0 := by
  rw [choose_eq_zero_of_lt s (s + 1) (Nat.lt_succ_self s), Nat.zero_mul]
  by_cases hc : (s + 1) % 2 = 0
  · rw [if_pos hc]
  · rw [if_neg hc]

/-- The additive closure `Qex m s 0 + Σⱼ[(j+1)%2=0]C(s,j+1)Qex m s(j+1) = fdPos m s`. -/
private theorem fdPos_closure (m s : Nat) :
    Qex m s 0 + sumTo (s + 1) (fun j => if (j + 1) % 2 = 0
        then choose s (j + 1) * Qex m s (j + 1) else 0) = fdPos m s := by
  show Qex m s 0 + sumTo (s + 1) (fun j => if (j + 1) % 2 = 0
      then choose s (j + 1) * Qex m s (j + 1) else 0)
    = sumTo (s + 1) (fun i => if i % 2 = 0 then choose s i * Qex m s i else 0)
  rw [sumTo_succ, Bterm_top m s, Nat.add_zero,
      sumTo_split_first s (fun i => if i % 2 = 0 then choose s i * Qex m s i else 0)]
  congr 1
  show Qex m s 0 = (if (0 : Nat) % 2 = 0 then choose s 0 * Qex m s 0 else 0)
  rw [if_pos (by decide), choose_zero_right, Nat.one_mul]

/-- ★★ **(P)**: `fdPos(m,s+1) = (m+s+1)·fdPos(m,s) + m·fdNeg(m+1,s)`. -/
theorem fdPos_succ (m s : Nat) :
    fdPos m (s + 1) = (m + s + 1) * fdPos m s + m * fdNeg (m + 1) s := by
  show sumTo (s + 2) (fun j => if j % 2 = 0 then choose (s + 1) j * Qex m (s + 1) j else 0)
    = (m + s + 1) * fdPos m s + m * fdNeg (m + 1) s
  rw [sumTo_split_first (s + 1)
        (fun j => if j % 2 = 0 then choose (s + 1) j * Qex m (s + 1) j else 0),
      show (if (0 : Nat) % 2 = 0 then choose (s + 1) 0 * Qex m (s + 1) 0 else 0)
        = (m + s + 1) * Qex m s 0 from by
          rw [if_pos (by decide), choose_zero_right, Nat.one_mul, Qex_back (Nat.zero_le s) m],
      sumTo_congr (s + 1) _
        (fun j => m * (if j % 2 = 1 then choose s j * Qex (m + 1) s j else 0)
          + (m + s + 1) * (if (j + 1) % 2 = 0 then choose s (j + 1) * Qex m s (j + 1) else 0))
        (fun j _ => term_split m s j),
      ← sumTo_add_func, ← sumTo_mul_left, ← sumTo_mul_left]
  show (m + s + 1) * Qex m s 0
      + (m * fdNeg (m + 1) s + (m + s + 1) * sumTo (s + 1) (fun j => if (j + 1) % 2 = 0
          then choose s (j + 1) * Qex m s (j + 1) else 0))
    = (m + s + 1) * fdPos m s + m * fdNeg (m + 1) s
  rw [← fdPos_closure m s]
  ring_nat

/-- The `j=s` top term vanishes for any condition (`C(s,s+1) = 0`). -/
private theorem choose_top_term (m s : Nat) (P : Prop) [Decidable P] :
    (if P then choose s (s + 1) * Qex m s (s + 1) else 0) = 0 := by
  rw [choose_eq_zero_of_lt s (s + 1) (Nat.lt_succ_self s), Nat.zero_mul]
  by_cases hc : P
  · rw [if_pos hc]
  · rw [if_neg hc]

/-- The `(N)` pointwise split (odd-indexed). -/
private theorem term_split_neg (m s j : Nat) :
    (if (j + 1) % 2 = 1 then choose (s + 1) (j + 1) * Qex m (s + 1) (j + 1) else 0)
    = m * (if j % 2 = 0 then choose s j * Qex (m + 1) s j else 0)
      + (m + s + 1) * (if (j + 1) % 2 = 1 then choose s (j + 1) * Qex m s (j + 1) else 0) := by
  rcases mod2_cases j with hj | hj
  · have h1 : (j + 1) % 2 = 1 := by rw [succ_mod2 j, if_pos hj]
    rw [if_pos h1, if_pos hj, if_pos h1, choose_succ_succ s j]
    rcases Nat.lt_or_ge s (j + 1) with hlt | hge
    · rw [choose_eq_zero_of_lt s (j + 1) hlt, Qex_front m s j, Nat.add_zero (choose s j),
          Nat.zero_mul (Qex m s (j + 1)), Nat.mul_zero (m + s + 1),
          Nat.add_zero (m * (choose s j * Qex (m + 1) s j))]
      ring_nat
    · have hfront : Qex m (s + 1) (j + 1) = m * Qex (m + 1) s j := Qex_front m s j
      have hback : Qex m (s + 1) (j + 1) = (m + s + 1) * Qex m s (j + 1) := Qex_back hge m
      rw [show m * (choose s j * Qex (m + 1) s j) = choose s j * (m * Qex (m + 1) s j) from by
            ring_nat,
          show (m + s + 1) * (choose s (j + 1) * Qex m s (j + 1))
            = choose s (j + 1) * ((m + s + 1) * Qex m s (j + 1)) from by ring_nat,
          ← hfront, ← hback]
      ring_nat
  · have h1 : (j + 1) % 2 = 0 := by
      rw [succ_mod2 j, if_neg (show ¬ j % 2 = 0 from by rw [hj]; decide)]
    rw [if_neg (show ¬ (j + 1) % 2 = 1 from by rw [h1]; decide),
        if_neg (show ¬ j % 2 = 0 from by rw [hj]; decide),
        if_neg (show ¬ (j + 1) % 2 = 1 from by rw [h1]; decide),
        Nat.mul_zero, Nat.mul_zero, Nat.add_zero]

/-- The `fdNeg` closure: `Σⱼ[(j+1)%2=1]C(s,j+1)Qex m s(j+1) = fdNeg m s` (no offset —
    `fdNeg`'s `j=0` term is `0`). -/
private theorem fdNeg_closure (m s : Nat) :
    sumTo (s + 1) (fun j => if (j + 1) % 2 = 1 then choose s (j + 1) * Qex m s (j + 1) else 0)
    = fdNeg m s := by
  show sumTo (s + 1) (fun j => if (j + 1) % 2 = 1 then choose s (j + 1) * Qex m s (j + 1) else 0)
    = sumTo (s + 1) (fun i => if i % 2 = 1 then choose s i * Qex m s i else 0)
  rw [sumTo_succ, choose_top_term m s ((s + 1) % 2 = 1), Nat.add_zero,
      sumTo_split_first s (fun i => if i % 2 = 1 then choose s i * Qex m s i else 0),
      show (if (0 : Nat) % 2 = 1 then choose s 0 * Qex m s 0 else 0) = 0 from by
        rw [if_neg (by decide)],
      Nat.zero_add]

/-- ★★ **(N)**: `fdNeg(m,s+1) = (m+s+1)·fdNeg(m,s) + m·fdPos(m+1,s)`. -/
theorem fdNeg_succ (m s : Nat) :
    fdNeg m (s + 1) = (m + s + 1) * fdNeg m s + m * fdPos (m + 1) s := by
  show sumTo (s + 2) (fun j => if j % 2 = 1 then choose (s + 1) j * Qex m (s + 1) j else 0)
    = (m + s + 1) * fdNeg m s + m * fdPos (m + 1) s
  rw [sumTo_split_first (s + 1)
        (fun j => if j % 2 = 1 then choose (s + 1) j * Qex m (s + 1) j else 0),
      show (if (0 : Nat) % 2 = 1 then choose (s + 1) 0 * Qex m (s + 1) 0 else 0) = 0 from by
        rw [if_neg (by decide)],
      Nat.zero_add,
      sumTo_congr (s + 1) _
        (fun j => m * (if j % 2 = 0 then choose s j * Qex (m + 1) s j else 0)
          + (m + s + 1) * (if (j + 1) % 2 = 1 then choose s (j + 1) * Qex m s (j + 1) else 0))
        (fun j _ => term_split_neg m s j),
      ← sumTo_add_func, ← sumTo_mul_left, ← sumTo_mul_left]
  show m * fdPos (m + 1) s
      + (m + s + 1) * sumTo (s + 1) (fun j => if (j + 1) % 2 = 1
          then choose s (j + 1) * Qex m s (j + 1) else 0)
    = (m + s + 1) * fdNeg m s + m * fdPos (m + 1) s
  rw [fdNeg_closure m s]
  ring_nat

/-- ★★★ **The finite-difference identity** (additive form): `fdPos m s = s! + fdNeg m s`,
    i.e. `Σⱼ(−1)ʲC(s,j)·Qex m s j = s!`.  Induction on `s` via `(P)/(N)`. -/
theorem fd_identity (m s : Nat) : fdPos m s = factorial s + fdNeg m s := by
  induction s generalizing m with
  | zero => rw [fdPos_zero, fdNeg_zero]; rfl
  | succ s ih =>
    rw [fdPos_succ, fdNeg_succ, ih m, ih (m + 1), factorial_succ]
    ring_nat

/-! ## §5 — KeyDiv: `m·C(k,m) ∣ lcm(1..k)`

The finite-difference identity, read as a divisibility, gives `m·C(k,m) ∣ lcm(1..k)`.
The bridge is the *product* identity `P(m,s) = s!·m·C(m+s,m) = rprod m (s+1)`: the
rising product `m(m+1)…(m+s)` equals `s!` times `m·C(m+s,m)`.  Every factor `(m+j)`
of the product divides `lcm(1..m+s)` (when `m+j ≤ k`), and the alternating sum
collapses to `s!·m·C(m+s,m)`, so the common refinement divides `lcm`. -/

/-- ★★ **Bridge identity**: `m · C(m+s, m) · s! = rprod m (s+1)`, i.e. the rising product
    `m(m+1)…(m+s)` equals `s!·m·C(m+s,m)`.  Induction on `s`; the step reduces to
    `(s+1)·C(m+s+1, s+1) = (m+s+1)·C(m+s, s)` (`choose_succ_mul`), with `choose_symm`
    converting the binomial lower indices. -/
theorem keydiv_prod (m s : Nat) :
    m * choose (m + s) m * factorial s = rprod m (s + 1) := by
  induction s with
  | zero =>
    show m * choose (m + 0) m * factorial 0 = rprod m 1
    rw [Nat.add_zero, choose_self m, show factorial 0 = 1 from rfl, Nat.mul_one,
        Nat.mul_one, rprod_back, show rprod m 0 = 1 from rfl, Nat.one_mul, Nat.add_zero]
  | succ s ih =>
    -- RHS: rprod m (s+2) = rprod m (s+1) * (m+s+1)
    rw [rprod_back, ← ih, factorial_succ]
    -- Goal: m * C(m+(s+1), m) * ((s+1)*s!) = (m * C(m+s, m) * s!) * (m+s+0+1)
    -- Reduce binomials by symmetry, then apply choose_succ_mul.
    have hkey : (s + 1) * choose (m + s + 1) (s + 1) = (m + s + 1) * choose (m + s) s :=
      choose_succ_mul (m + s) s
    have hsym1 : choose (m + (s + 1)) m = choose (m + s + 1) (s + 1) := by
      rw [choose_symm m (s + 1), Nat.add_succ]
    have hsym2 : choose (m + s) m = choose (m + s) s := choose_symm m s
    rw [hsym1, hsym2, Nat.add_succ m s]
    -- Now: m * C(m+s+1)(s+1) * ((s+1)*s!) = (m * C(m+s) s * s!) * (m+s+1)
    rw [show m * choose (m + s + 1) (s + 1) * ((s + 1) * factorial s)
          = m * factorial s * ((s + 1) * choose (m + s + 1) (s + 1)) from by ring_nat,
        hkey,
        show m * factorial s * ((m + s + 1) * choose (m + s) s)
          = m * choose (m + s) s * factorial s * (m + s + 1) from by ring_nat]

/-- Splitting the rising product at length `a`: `rprod m (a+b) = rprod m a · rprod (m+a) b`. -/
theorem rprod_split (m a : Nat) : ∀ b, rprod m (a + b) = rprod m a * rprod (m + a) b
  | 0 => by rw [Nat.add_zero, show rprod (m + a) 0 = 1 from rfl, Nat.mul_one]
  | b + 1 => by
    rw [show a + (b + 1) = (a + b) + 1 from rfl, rprod_back, rprod_split m a b,
        rprod_back (m + a) b]
    ring_nat

/-- `(m+j)·Qex m s j = rprod m (s+1)` for `j ≤ s` — the excluded factor `(m+j)` restored,
    rebuilding the full rising product `m(m+1)…(m+s)`. -/
theorem Qex_mul {m s j : Nat} (hj : j ≤ s) : (m + j) * Qex m s j = rprod m (s + 1) := by
  have hjs : j ≤ s + 1 := Nat.le_trans hj (Nat.le_succ s)
  have hsum : j + (s + 1 - j) = s + 1 := add_sub_of_le hjs
  unfold Qex
  rw [show rprod m (s + 1) = rprod m (j + (s + 1 - j)) from by rw [hsum],
      rprod_split m j (s + 1 - j), succ_sub_pure hj, rprod_front (m + j) (s - j)]
  ring_nat

/-- `a ∣ d → a·(d/a) = d`, ∅-axiom (the divisibility witness restored from the quotient). -/
private theorem dvd_mul_div {a d : Nat} (h : a ∣ d) : a * (d / a) = d := by
  rcases h with ⟨c, hc⟩
  have hmod : d % a = 0 := (mul_witness_iff_mod_eq_zero a d).mp ⟨c, hc.symm⟩
  have hdm := div_add_mod_pure d a
  rw [hmod, Nat.add_zero] at hdm
  exact hdm

/-- Even-indexed quotient sum `Σ_{even j} C(s,j)·(d/(m+j))`. -/
def LPos (m s d : Nat) : Nat :=
  sumTo (s + 1) (fun j => if j % 2 = 0 then choose s j * (d / (m + j)) else 0)

/-- Odd-indexed quotient sum `Σ_{odd j} C(s,j)·(d/(m+j))`. -/
def LNeg (m s d : Nat) : Nat :=
  sumTo (s + 1) (fun j => if j % 2 = 1 then choose s j * (d / (m + j)) else 0)

/-- Pointwise (even): `d·[C(s,j)·Qex] = rprod·[C(s,j)·(d/(m+j))]` for `j ≤ s`, `(m+j)∣d`. -/
private theorem dfd_term_pos {m s j d : Nat} (hj : j ≤ s) (hd : (m + j) ∣ d) :
    d * (if j % 2 = 0 then choose s j * Qex m s j else 0)
    = rprod m (s + 1) * (if j % 2 = 0 then choose s j * (d / (m + j)) else 0) := by
  rcases mod2_cases j with hpar | hpar
  · rw [if_pos hpar, if_pos hpar,
        show d * (choose s j * Qex m s j) = choose s j * (d * Qex m s j) from by ring_nat,
        show rprod m (s + 1) * (choose s j * (d / (m + j)))
          = choose s j * (rprod m (s + 1) * (d / (m + j))) from by ring_nat,
        show d * Qex m s j = (m + j) * (d / (m + j)) * Qex m s j from by rw [dvd_mul_div hd],
        show (m + j) * (d / (m + j)) * Qex m s j = (d / (m + j)) * ((m + j) * Qex m s j) from by
          ring_nat,
        Qex_mul hj]
    ring_nat
  · rw [if_neg (show ¬ j % 2 = 0 from by rw [hpar]; decide),
        if_neg (show ¬ j % 2 = 0 from by rw [hpar]; decide), Nat.mul_zero, Nat.mul_zero]

/-- Pointwise (odd): `d·[C(s,j)·Qex] = rprod·[C(s,j)·(d/(m+j))]` for `j ≤ s`, `(m+j)∣d`. -/
private theorem dfd_term_neg {m s j d : Nat} (hj : j ≤ s) (hd : (m + j) ∣ d) :
    d * (if j % 2 = 1 then choose s j * Qex m s j else 0)
    = rprod m (s + 1) * (if j % 2 = 1 then choose s j * (d / (m + j)) else 0) := by
  rcases mod2_cases j with hpar | hpar
  · rw [if_neg (show ¬ j % 2 = 1 from by rw [hpar]; decide),
        if_neg (show ¬ j % 2 = 1 from by rw [hpar]; decide), Nat.mul_zero, Nat.mul_zero]
  · rw [if_pos hpar, if_pos hpar,
        show d * (choose s j * Qex m s j) = choose s j * (d * Qex m s j) from by ring_nat,
        show rprod m (s + 1) * (choose s j * (d / (m + j)))
          = choose s j * (rprod m (s + 1) * (d / (m + j))) from by ring_nat,
        show d * Qex m s j = (m + j) * (d / (m + j)) * Qex m s j from by rw [dvd_mul_div hd],
        show (m + j) * (d / (m + j)) * Qex m s j = (d / (m + j)) * ((m + j) * Qex m s j) from by
          ring_nat,
        Qex_mul hj]
    ring_nat

/-- `d·fdPos m s = rprod m (s+1)·LPos m s d` when every `(m+j)` (`j ≤ s`) divides `d`. -/
theorem dfd_pos {m s d : Nat} (hd : ∀ j, j ≤ s → (m + j) ∣ d) :
    d * fdPos m s = rprod m (s + 1) * LPos m s d := by
  show d * sumTo (s + 1) (fun j => if j % 2 = 0 then choose s j * Qex m s j else 0)
    = rprod m (s + 1)
      * sumTo (s + 1) (fun j => if j % 2 = 0 then choose s j * (d / (m + j)) else 0)
  rw [sumTo_mul_left, sumTo_mul_left]
  exact sumTo_congr (s + 1) _ _
    (fun j hj => dfd_term_pos (Nat.le_of_lt_succ hj) (hd j (Nat.le_of_lt_succ hj)))

/-- `d·fdNeg m s = rprod m (s+1)·LNeg m s d` when every `(m+j)` (`j ≤ s`) divides `d`. -/
theorem dfd_neg {m s d : Nat} (hd : ∀ j, j ≤ s → (m + j) ∣ d) :
    d * fdNeg m s = rprod m (s + 1) * LNeg m s d := by
  show d * sumTo (s + 1) (fun j => if j % 2 = 1 then choose s j * Qex m s j else 0)
    = rprod m (s + 1)
      * sumTo (s + 1) (fun j => if j % 2 = 1 then choose s j * (d / (m + j)) else 0)
  rw [sumTo_mul_left, sumTo_mul_left]
  exact sumTo_congr (s + 1) _ _
    (fun j hj => dfd_term_neg (Nat.le_of_lt_succ hj) (hd j (Nat.le_of_lt_succ hj)))

/-- ★★★ **KeyDiv (generic)**: if every `(m+j)` for `j ≤ s` divides `d`, then
    `m·C(m+s, m) ∣ d`.  Proof: `fd_identity` (`fdPos = s! + fdNeg`) times `d`, with
    `dfd_pos`/`dfd_neg` and `keydiv_prod` (`rprod m (s+1) = m·C(m+s,m)·s!`), collapses
    after cancelling `s!` to `P·LPos = d + P·LNeg` (`P = m·C(m+s,m)`); so `d = P·(LPos−LNeg)`. -/
theorem keydiv_dvd {m s d : Nat} (hd : ∀ j, j ≤ s → (m + j) ∣ d) :
    m * choose (m + s) m ∣ d := by
  have hA : d * fdPos m s = rprod m (s + 1) * LPos m s d := dfd_pos hd
  have hB : d * fdNeg m s = rprod m (s + 1) * LNeg m s d := dfd_neg hd
  have hP : rprod m (s + 1) = m * choose (m + s) m * factorial s := (keydiv_prod m s).symm
  -- multiply fd_identity by d and substitute the two quotient-sum identities
  have e1 : d * fdPos m s = d * factorial s + d * fdNeg m s := by
    rw [fd_identity m s, Nat.mul_add]
  rw [hA, hB, hP] at e1
  -- e1 : (P·s!)·LPos = d·s! + (P·s!)·LNeg ;  cancel s! to get  P·LPos = d + P·LNeg
  have hcancel : m * choose (m + s) m * LPos m s d
               = d + m * choose (m + s) m * LNeg m s d := by
    apply mul_left_cancel_pos (factorial_pos s)
    calc factorial s * (m * choose (m + s) m * LPos m s d)
        = m * choose (m + s) m * factorial s * LPos m s d := by ring_nat
      _ = d * factorial s + m * choose (m + s) m * factorial s * LNeg m s d := e1
      _ = factorial s * (d + m * choose (m + s) m * LNeg m s d) := by ring_nat
  -- d = P·LPos − P·LNeg = P·(LPos − LNeg)
  refine ⟨LPos m s d - LNeg m s d, ?_⟩
  rw [mul_sub, hcancel, add_sub_cancel_right]

/-- **KeyDiv**: `m·C(k, m) ∣ lcm(1..k)` for `1 ≤ m ≤ k` — every `(m+j)` up to `k` divides
    `lcm(1..k)`, so the finite-difference common refinement does too. -/
theorem keydiv {m k : Nat} (hm : 1 ≤ m) (hmk : m ≤ k) :
    m * choose k m ∣ lcmUpTo k := by
  have hms : m + (k - m) = k := add_sub_of_le hmk
  have hd : ∀ j, j ≤ k - m → (m + j) ∣ lcmUpTo k := by
    intro j hj
    refine dvd_lcmUpTo (Nat.lt_of_lt_of_le hm (Nat.le_add_right m j)) ?_
    calc m + j ≤ m + (k - m) := Nat.add_le_add_left hj m
      _ = k := hms
  have hdvd := keydiv_dvd (m := m) (s := k - m) hd
  rw [hms] at hdvd
  exact hdvd

/-! ## §3 — the Heart (L2)

`m³·C(n,m)·C(n+m,m) ∣ d³·C(n,k)·C(n+k,k)` (additive form `n = m+a+b`, `k = m+b`).
Substitute `d = m·C(k,m)·Q` (KeyDiv quotient) into the cube and apply the trinomial
double identity to the resulting `C(k,m)²·C(n,k)·C(n+k,k)` factor: it collapses to
`C(n,m)·C(n+m,m)·C(n−m,k−m)·C(n+k,n+m)`, leaving the explicit integer witness
`Q³·C(k,m)·C(n−m,k−m)·C(n+k,n+m)`. -/

/-- `x³ = x·x·x`, ∅-axiom (keeps `ring_nat` off literal-exponent `^`). -/
private theorem cube (x : Nat) : x ^ 3 = x * x * x := by
  rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_one]

/-- ★★★ **The Heart (L2)**: `m³·C(n,m)·C(n+m,m) ∣ d³·C(n,k)·C(n+k,k)` whenever
    `m·C(k,m) ∣ d` (KeyDiv supplies this with `d = lcm(1..n)`).  Witness:
    `Q³·C(k,m)·C(n−m,k−m)·C(n+k,n+m)` with `Q = d/(m·C(k,m))`; the trinomial identity
    `aperyTrinomial` collapses the `C(k,m)²·C(n,k)·C(n+k,k)` block. -/
theorem heart {m a b d : Nat} (hQ : m * choose (m + b) m ∣ d) :
    m ^ 3 * (choose (m + a + b) m * choose (2 * m + a + b) m)
      ∣ d ^ 3 * (choose (m + a + b) (m + b) * choose (2 * m + a + 2 * b) (m + b)) := by
  rcases hQ with ⟨Q, hQd⟩    -- hQd : d = m * choose (m+b) m * Q
  refine ⟨Q ^ 3 * choose (m + b) m * choose (a + b) b
            * choose (2 * m + a + 2 * b) (2 * m + a + b), ?_⟩
  have hT := aperyTrinomial m a b
  rw [cube d, cube m, cube Q, hQd]
  calc (m * choose (m + b) m * Q) * (m * choose (m + b) m * Q) * (m * choose (m + b) m * Q)
          * (choose (m + a + b) (m + b) * choose (2 * m + a + 2 * b) (m + b))
      = m * m * m * (Q * Q * Q) * choose (m + b) m
          * (choose (m + a + b) (m + b) * choose (2 * m + a + 2 * b) (m + b)
             * (choose (m + b) m * choose (m + b) m)) := by ring_nat
    _ = m * m * m * (Q * Q * Q) * choose (m + b) m
          * (choose (m + a + b) m * choose (2 * m + a + b) m * choose (a + b) b
             * choose (2 * m + a + 2 * b) (2 * m + a + b)) := by rw [hT]
    _ = m * m * m * (choose (m + a + b) m * choose (2 * m + a + b) m)
          * (Q * Q * Q * choose (m + b) m * choose (a + b) b
             * choose (2 * m + a + 2 * b) (2 * m + a + b)) := by ring_nat

/-! ## §4 — assembly engines (per-term divisibilities)

The two divisibilities the ℚ-free assembly of `2·lcm³·aₙ` consumes term by term:
the harmonic part `Σ_j 1/j³` clears against `lcm³` (`cube_dvd_lcm_cube`), and the
Apéry kernel part `Σ_m (−1)^{m−1}/(2m³C(n,m)C(n+m,m))` clears via the Heart with
`d = lcm(1..n)` (`heart_lcm`, KeyDiv supplying the quotient). -/

/-- Harmonic clearing: `j³ ∣ lcm(1..n)³` for `1 ≤ j ≤ n`. -/
theorem cube_dvd_lcm_cube {j n : Nat} (hj : 1 ≤ j) (hjn : j ≤ n) :
    j ^ 3 ∣ lcmUpTo n ^ 3 := by
  rcases dvd_lcmUpTo hj hjn with ⟨c, hc⟩
  refine ⟨c ^ 3, ?_⟩
  rw [cube (lcmUpTo n), hc, cube j, cube c]
  ring_nat

/-- ★★ **The Heart, on `lcm(1..n)`** (KeyDiv-supplied quotient): for `1 ≤ m`,
    `m³·C(n,m)·C(n+m,m) ∣ lcm(1..n)³·C(n,k)·C(n+k,k)` (additive `n = m+a+b`, `k = m+b`).
    `m·C(k,m) ∣ lcm(1..k) ∣ lcm(1..n)` (KeyDiv + monotonicity) feeds `heart`. -/
theorem heart_lcm {m a b : Nat} (hm : 1 ≤ m) :
    m ^ 3 * (choose (m + a + b) m * choose (2 * m + a + b) m)
      ∣ lcmUpTo (m + a + b) ^ 3
        * (choose (m + a + b) (m + b) * choose (2 * m + a + 2 * b) (m + b)) := by
  have hkn : m + b ≤ m + a + b := by
    rw [show m + a + b = m + b + a from by ring_nat]
    exact Nat.le_add_right (m + b) a
  have hmono : lcmUpTo (m + b) ∣ lcmUpTo (m + a + b) :=
    lcmUpTo_dvd (fun j hj0 hjN => dvd_lcmUpTo hj0 (Nat.le_trans hjN hkn))
  have hQ : m * choose (m + b) m ∣ lcmUpTo (m + a + b) := by
    rcases keydiv hm (Nat.le_add_right m b) with ⟨u, hu⟩
    rcases hmono with ⟨v, hv⟩
    exact ⟨u * v, by rw [hv, hu]; ring_nat⟩
  exact heart hQ

end E213.Lib.Math.NumberTheory.AperyIntegrality
