import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChooseFactorial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
import E213.Meta.Nat.PolyNatMTactic

/-!
# AperyRecurrence — the binomial Apéry numbers `Bₙ = Σ_k C(n,k)²C(n+k,k)²`

The denominator Apéry numbers as an explicit binomial sum (manifestly `ℕ`).  The
**nucleus** of the ζ(3) program is the recurrence

  `(j+2)³·B(j+2) + (j+1)³·B(j) = aperyLead(j)·B(j+1)`,   `aperyLead j = 34j³+153j²+231j+117`

(subtraction-free additive form).  This is **Apéry's recurrence** = the WZ /
creative-telescoping identity; once proven, `zeta3Den n = (n!)³·B(n)` follows by
induction (seeds `B 0 = 1`, `B 1 = 5` match), closing the recurrence-divisibility
route to `zeta3HolonomicReal`.

**The WZ certificate is found + verified** (see `research-notes/frontiers/zeta3_wz`).
With `a n k = C(n,k)²C(n+k,k)²` and the cleared certificate
`Ĝ(j,k) = −4·k⁴·(2j+3)·(4j²+12j−2k²+3k+8)·C(j+2,k)²·C(j+k,k)²`, the verified
all-polynomial telescoping identity is

  `(j+1)²·(j+2)²·[(j+2)³·a(j+2,k) + (j+1)³·a(j,k) − aperyLead(j)·a(j+1,k)]
      = Ĝ(j,k+1) − Ĝ(j,k)`

(boundary `Ĝ(j,0)=0`, `Ĝ(j,k)=0` for `k>j+2`).  Summing over `k` telescopes to
`0`, giving the recurrence.  The Lean proof of this per-`k` identity (clear
binomials → `ring_nat`) + telescoping is the recorded mechanical frontier.

This file pins the *definition* and validates the recurrence on base layers.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.AperyRecurrence

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose choose_eq_zero_of_lt choose_succ_mul)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChooseFactorial (choose_mul_factorials)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial (factorial factorial_succ factorial_pos)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem (sumTo_congr sumTo_add_func
  sumTo_mul_left)
open E213.Tactic.NatHelper (add_sub_of_le add_left_cancel add_right_cancel mul_left_cancel_pos
  add_sub_cancel_right)

/-! ## Column recurrence (the binomial `W`-factoring building block) -/

/-- `a − b = 0` for `a ≤ b`, ∅-axiom (`Nat.sub_eq_zero_of_le` carries propext). -/
theorem nat_sub_eq_zero : ∀ {a b : Nat}, a ≤ b → a - b = 0
  | 0, b, _ => Nat.zero_sub b
  | _ + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | a + 1, b + 1, h => by
    rw [Nat.succ_sub_succ]; exact nat_sub_eq_zero (Nat.le_of_succ_le_succ h)

/-- `n + 1 − k = (n − k) + 1` for `k ≤ n`. -/
theorem succ_sub_of_le {n k : Nat} (h : k ≤ n) : n + 1 - k = (n - k) + 1 := by
  have e1 : k + (n + 1 - k) = n + 1 := add_sub_of_le (Nat.le_succ_of_le h)
  have e2 : k + ((n - k) + 1) = n + 1 := by rw [← Nat.add_assoc, add_sub_of_le h]
  exact add_left_cancel (e1.trans e2.symm)

/-- ★★ **Column recurrence**: `(n+1−k)·C(n+1,k) = (n+1)·C(n,k)` (the upper-index
    recurrence; all `k` in ℕ).  Clears via `choose_mul_factorials`; the
    `(n+1−k)·(n−k)! = (n+1−k)!` step makes the factorials cancel. -/
theorem colrec (n k : Nat) : (n + 1 - k) * choose (n + 1) k = (n + 1) * choose n k := by
  rcases Nat.lt_or_ge k (n + 1) with hklt | hkge
  · have hkn : k ≤ n := Nat.le_of_lt_succ hklt
    have hcf1 : choose (n + 1) k * (factorial k * factorial (n + 1 - k)) = factorial (n + 1) := by
      have h := choose_mul_factorials k (n + 1 - k)
      rwa [add_sub_of_le (Nat.le_succ_of_le hkn)] at h
    have hcf0 : choose n k * (factorial k * factorial (n - k)) = factorial n := by
      have h := choose_mul_factorials k (n - k)
      rwa [add_sub_of_le hkn] at h
    have hfs : factorial (n + 1 - k) = (n + 1 - k) * factorial (n - k) := by
      rw [succ_sub_of_le hkn, factorial_succ]
    apply mul_left_cancel_pos (Nat.mul_pos (factorial_pos k) (factorial_pos (n - k)))
    calc factorial k * factorial (n - k) * ((n + 1 - k) * choose (n + 1) k)
        = choose (n + 1) k * (factorial k * ((n + 1 - k) * factorial (n - k))) := by ring_nat
      _ = choose (n + 1) k * (factorial k * factorial (n + 1 - k)) := by rw [hfs]
      _ = factorial (n + 1) := hcf1
      _ = (n + 1) * factorial n := factorial_succ n
      _ = (n + 1) * (choose n k * (factorial k * factorial (n - k))) := by rw [hcf0]
      _ = factorial k * factorial (n - k) * ((n + 1) * choose n k) := by ring_nat
  · rw [choose_eq_zero_of_lt n k hkge, Nat.mul_zero,
        show n + 1 - k = 0 from nat_sub_eq_zero hkge, Nat.zero_mul]

/-- `(n − (k+1)) + 1 = n − k` for `k < n`. -/
theorem sub_succ_add_one {n k : Nat} (h : k < n) : (n - (k + 1)) + 1 = n - k := by
  have e1 : k + ((n - (k + 1)) + 1) = n := by
    rw [Nat.add_comm (n - (k + 1)) 1, ← Nat.add_assoc]
    exact add_sub_of_le h
  have e2 : k + (n - k) = n := add_sub_of_le (Nat.le_of_lt h)
  exact add_left_cancel (e1.trans e2.symm)

/-- ★★ **Lower-index recurrence**: `(k+1)·C(n,k+1) = (n−k)·C(n,k)` (all `k` in ℕ).
    Clears via `choose_mul_factorials`; the `(n−k)·(n−k−1)! = (n−k)!` step cancels. -/
theorem lowrec (n k : Nat) : (k + 1) * choose n (k + 1) = (n - k) * choose n k := by
  rcases Nat.lt_or_ge k n with hkn | hkge
  · have hcf1 : choose n (k + 1) * (factorial (k + 1) * factorial (n - (k + 1))) = factorial n := by
      have h := choose_mul_factorials (k + 1) (n - (k + 1))
      rwa [add_sub_of_le hkn] at h
    have hcf0 : choose n k * (factorial k * factorial (n - k)) = factorial n := by
      have h := choose_mul_factorials k (n - k)
      rwa [add_sub_of_le (Nat.le_of_lt hkn)] at h
    have hfk1 : factorial (k + 1) = (k + 1) * factorial k := factorial_succ k
    have hfnk : factorial (n - k) = (n - k) * factorial (n - (k + 1)) := by
      rw [← sub_succ_add_one hkn, factorial_succ, sub_succ_add_one hkn]
    apply mul_left_cancel_pos (Nat.mul_pos (factorial_pos k) (factorial_pos (n - (k + 1))))
    calc factorial k * factorial (n - (k + 1)) * ((k + 1) * choose n (k + 1))
        = choose n (k + 1) * (((k + 1) * factorial k) * factorial (n - (k + 1))) := by ring_nat
      _ = choose n (k + 1) * (factorial (k + 1) * factorial (n - (k + 1))) := by rw [← hfk1]
      _ = factorial n := hcf1
      _ = choose n k * (factorial k * factorial (n - k)) := hcf0.symm
      _ = choose n k * (factorial k * ((n - k) * factorial (n - (k + 1)))) := by rw [hfnk]
      _ = factorial k * factorial (n - (k + 1)) * ((n - k) * choose n k) := by ring_nat
  · rw [choose_eq_zero_of_lt n (k + 1) (Nat.lt_succ_of_le hkge), Nat.mul_zero,
        show n - k = 0 from nat_sub_eq_zero hkge, Nat.zero_mul]

/-! ## §contiguity — the `W`-factoring product identities (from `colrec`/`lowrec`)

`W = C(j+2,k)²·C(j+k,k)²` is the common factor.  These express each `a(n,k)` and
`Gmag` factor as `W · polynomial`, via the (squared) column/lower recurrences. -/

/-- `(j+1)(j+2)·C(j,k) = (j+1−k)(j+2−k)·C(j+2,k)` (raise the lower row twice). -/
theorem colA (j k : Nat) :
    (j + 1) * (j + 2) * choose j k = (j + 1 - k) * (j + 2 - k) * choose (j + 2) k := by
  have h1 : (j + 1 - k) * choose (j + 1) k = (j + 1) * choose j k := colrec j k
  have h2 : (j + 2 - k) * choose (j + 2) k = (j + 2) * choose (j + 1) k := colrec (j + 1) k
  calc (j + 1) * (j + 2) * choose j k
      = (j + 2) * ((j + 1) * choose j k) := by ring_nat
    _ = (j + 2) * ((j + 1 - k) * choose (j + 1) k) := by rw [← h1]
    _ = (j + 1 - k) * ((j + 2) * choose (j + 1) k) := by ring_nat
    _ = (j + 1 - k) * ((j + 2 - k) * choose (j + 2) k) := by rw [← h2]
    _ = (j + 1 - k) * (j + 2 - k) * choose (j + 2) k := by ring_nat

/-- `(j+2)·C(j+1,k) = (j+2−k)·C(j+2,k)`. -/
theorem colAB (j k : Nat) :
    (j + 2) * choose (j + 1) k = (j + 2 - k) * choose (j + 2) k :=
  (colrec (j + 1) k).symm

/-- `(j+1)·C(j+k+1,k) = (j+k+1)·C(j+k,k)` (raise the upper index once). -/
theorem colB (j k : Nat) :
    (j + 1) * choose (j + k + 1) k = (j + k + 1) * choose (j + k) k := by
  have h := colrec (j + k) k
  rw [show j + k + 1 - k = j + 1 from by
        rw [Nat.add_right_comm j k 1, add_sub_cancel_right (j + 1) k]] at h
  exact h

/-- `(j+2)·C(j+k+2,k) = (j+k+2)·C(j+k+1,k)`. -/
theorem colC1 (j k : Nat) :
    (j + 2) * choose (j + k + 2) k = (j + k + 2) * choose (j + k + 1) k := by
  have h := colrec (j + k + 1) k
  rw [show j + k + 1 + 1 - k = j + 2 from by
        rw [show j + k + 1 + 1 = j + 2 + k from by ring_nat, add_sub_cancel_right (j + 2) k]] at h
  exact h

/-- `(j+1)(j+2)·C(j+k+2,k) = (j+k+1)(j+k+2)·C(j+k,k)` (raise the upper index twice). -/
theorem colC (j k : Nat) :
    (j + 1) * (j + 2) * choose (j + k + 2) k = (j + k + 1) * (j + k + 2) * choose (j + k) k := by
  calc (j + 1) * (j + 2) * choose (j + k + 2) k
      = (j + 1) * ((j + 2) * choose (j + k + 2) k) := by ring_nat
    _ = (j + 1) * ((j + k + 2) * choose (j + k + 1) k) := by rw [colC1]
    _ = (j + k + 2) * ((j + 1) * choose (j + k + 1) k) := by ring_nat
    _ = (j + k + 2) * ((j + k + 1) * choose (j + k) k) := by rw [colB]
    _ = (j + k + 1) * (j + k + 2) * choose (j + k) k := by ring_nat

/-- `(k+1)·C(j+2,k+1) = (j+2−k)·C(j+2,k)` (lower-index step on row `j+2`). -/
theorem G1a (j k : Nat) :
    (k + 1) * choose (j + 2) (k + 1) = (j + 2 - k) * choose (j + 2) k :=
  lowrec (j + 2) k

/-- `(k+1)·C(j+k+1,k+1) = (j+k+1)·C(j+k,k)` (diagonal step). -/
theorem G1b (j k : Nat) :
    (k + 1) * choose (j + k + 1) (k + 1) = (j + k + 1) * choose (j + k) k :=
  choose_succ_mul (j + k) k

/-- The Apéry summand `C(n,k)²·C(n+k,k)²` (squares as explicit products). -/
def aperySummand (n k : Nat) : Nat :=
  choose n k * choose n k * (choose (n + k) k * choose (n + k) k)

/-- The common factor `W = C(j+2,k)²·C(j+k,k)²`. -/
def Wfac (j k : Nat) : Nat :=
  choose (j + 2) k * choose (j + 2) k * (choose (j + k) k * choose (j + k) k)

/-- `R0`: `a(j,k)·(j+1)²(j+2)² = W·(j+2−k)²(j+1−k)²`. -/
theorem R0 (j k : Nat) :
    aperySummand j k * ((j + 1) * (j + 1)) * ((j + 2) * (j + 2))
    = Wfac j k * ((j + 2 - k) * (j + 2 - k)) * ((j + 1 - k) * (j + 1 - k)) := by
  have hsq : ((j + 1) * (j + 2) * choose j k) * ((j + 1) * (j + 2) * choose j k)
           = ((j + 1 - k) * (j + 2 - k) * choose (j + 2) k)
               * ((j + 1 - k) * (j + 2 - k) * choose (j + 2) k) := by rw [colA]
  unfold aperySummand Wfac
  calc choose j k * choose j k * (choose (j + k) k * choose (j + k) k)
          * ((j + 1) * (j + 1)) * ((j + 2) * (j + 2))
      = ((j + 1) * (j + 2) * choose j k) * ((j + 1) * (j + 2) * choose j k)
          * (choose (j + k) k * choose (j + k) k) := by ring_nat
    _ = ((j + 1 - k) * (j + 2 - k) * choose (j + 2) k)
          * ((j + 1 - k) * (j + 2 - k) * choose (j + 2) k)
          * (choose (j + k) k * choose (j + k) k) := by rw [hsq]
    _ = choose (j + 2) k * choose (j + 2) k * (choose (j + k) k * choose (j + k) k)
          * ((j + 2 - k) * (j + 2 - k)) * ((j + 1 - k) * (j + 1 - k)) := by ring_nat

/-- `R1`: `a(j+1,k)·(j+1)²(j+2)² = W·(j+2−k)²(j+k+1)²`. -/
theorem R1 (j k : Nat) :
    aperySummand (j + 1) k * ((j + 1) * (j + 1)) * ((j + 2) * (j + 2))
    = Wfac j k * ((j + 2 - k) * (j + 2 - k)) * ((j + k + 1) * (j + k + 1)) := by
  have hsqAB : ((j + 2) * choose (j + 1) k) * ((j + 2) * choose (j + 1) k)
             = ((j + 2 - k) * choose (j + 2) k) * ((j + 2 - k) * choose (j + 2) k) := by rw [colAB]
  have hsqB : ((j + 1) * choose (j + k + 1) k) * ((j + 1) * choose (j + k + 1) k)
            = ((j + k + 1) * choose (j + k) k) * ((j + k + 1) * choose (j + k) k) := by rw [colB]
  unfold aperySummand Wfac
  rw [show j + 1 + k = j + k + 1 from by ring_nat]
  calc choose (j + 1) k * choose (j + 1) k
          * (choose (j + k + 1) k * choose (j + k + 1) k)
          * ((j + 1) * (j + 1)) * ((j + 2) * (j + 2))
      = ((j + 2) * choose (j + 1) k) * ((j + 2) * choose (j + 1) k)
          * (((j + 1) * choose (j + k + 1) k) * ((j + 1) * choose (j + k + 1) k)) := by ring_nat
    _ = ((j + 2 - k) * choose (j + 2) k) * ((j + 2 - k) * choose (j + 2) k)
          * (((j + k + 1) * choose (j + k) k) * ((j + k + 1) * choose (j + k) k)) := by
        rw [hsqAB, hsqB]
    _ = choose (j + 2) k * choose (j + 2) k * (choose (j + k) k * choose (j + k) k)
          * ((j + 2 - k) * (j + 2 - k)) * ((j + k + 1) * (j + k + 1)) := by ring_nat

/-- `R2`: `a(j+2,k)·(j+1)²(j+2)² = W·(j+k+1)²(j+k+2)²`. -/
theorem R2 (j k : Nat) :
    aperySummand (j + 2) k * ((j + 1) * (j + 1)) * ((j + 2) * (j + 2))
    = Wfac j k * ((j + k + 1) * (j + k + 1)) * ((j + k + 2) * (j + k + 2)) := by
  have hsqC : ((j + 1) * (j + 2) * choose (j + k + 2) k) * ((j + 1) * (j + 2) * choose (j + k + 2) k)
            = ((j + k + 1) * (j + k + 2) * choose (j + k) k)
                * ((j + k + 1) * (j + k + 2) * choose (j + k) k) := by rw [colC]
  unfold aperySummand Wfac
  rw [show j + 2 + k = j + k + 2 from by ring_nat]
  calc choose (j + 2) k * choose (j + 2) k
          * (choose (j + k + 2) k * choose (j + k + 2) k)
          * ((j + 1) * (j + 1)) * ((j + 2) * (j + 2))
      = choose (j + 2) k * choose (j + 2) k
          * (((j + 1) * (j + 2) * choose (j + k + 2) k) * ((j + 1) * (j + 2) * choose (j + k + 2) k)) := by
        ring_nat
    _ = choose (j + 2) k * choose (j + 2) k
          * (((j + k + 1) * (j + k + 2) * choose (j + k) k)
              * ((j + k + 1) * (j + k + 2) * choose (j + k) k)) := by rw [hsqC]
    _ = choose (j + 2) k * choose (j + 2) k * (choose (j + k) k * choose (j + k) k)
          * ((j + k + 1) * (j + k + 1)) * ((j + k + 2) * (j + k + 2)) := by ring_nat

/-- `Q(j,k) = 4j²+12j+3k+8 − 2k²` (the certificate's polynomial factor; `>0` in the
    summation range, ℕ-truncation safe outside it since `C(j+2,k)=0` there). -/
def Qpoly (j k : Nat) : Nat := 4 * j * j + 12 * j + 3 * k + 8 - 2 * (k * k)

/-- The cleared certificate magnitude `Gmag(j,k) = 4k⁴(2j+3)·Q(j,k)·W`. -/
def Gmag (j k : Nat) : Nat := 4 * (k * k * k * k) * (2 * j + 3) * Qpoly j k * Wfac j k

/-- `G1`: `Gmag(j,k+1) = 4(2j+3)·Q(j,k+1)·(j+2−k)²(j+k+1)²·W`. -/
theorem G1 (j k : Nat) :
    Gmag j (k + 1)
    = 4 * (2 * j + 3) * Qpoly j (k + 1)
        * ((j + 2 - k) * (j + 2 - k)) * ((j + k + 1) * (j + k + 1)) * Wfac j k := by
  have hsqa : ((k + 1) * choose (j + 2) (k + 1)) * ((k + 1) * choose (j + 2) (k + 1))
            = ((j + 2 - k) * choose (j + 2) k) * ((j + 2 - k) * choose (j + 2) k) := by rw [G1a]
  have hsqb : ((k + 1) * choose (j + k + 1) (k + 1)) * ((k + 1) * choose (j + k + 1) (k + 1))
            = ((j + k + 1) * choose (j + k) k) * ((j + k + 1) * choose (j + k) k) := by rw [G1b]
  unfold Gmag Wfac
  rw [show j + (k + 1) = j + k + 1 from by ring_nat]
  calc 4 * ((k + 1) * (k + 1) * (k + 1) * (k + 1)) * (2 * j + 3) * Qpoly j (k + 1)
          * (choose (j + 2) (k + 1) * choose (j + 2) (k + 1)
              * (choose (j + k + 1) (k + 1) * choose (j + k + 1) (k + 1)))
      = 4 * (2 * j + 3) * Qpoly j (k + 1)
          * (((k + 1) * choose (j + 2) (k + 1)) * ((k + 1) * choose (j + 2) (k + 1)))
          * (((k + 1) * choose (j + k + 1) (k + 1)) * ((k + 1) * choose (j + k + 1) (k + 1))) := by
        ring_nat
    _ = 4 * (2 * j + 3) * Qpoly j (k + 1)
          * (((j + 2 - k) * choose (j + 2) k) * ((j + 2 - k) * choose (j + 2) k))
          * (((j + k + 1) * choose (j + k) k) * ((j + k + 1) * choose (j + k) k)) := by
        rw [hsqa, hsqb]
    _ = 4 * (2 * j + 3) * Qpoly j (k + 1)
          * ((j + 2 - k) * (j + 2 - k)) * ((j + k + 1) * (j + k + 1))
          * (choose (j + 2) k * choose (j + 2) k * (choose (j + k) k * choose (j + k) k)) := by
        ring_nat

/-- `Qpoly` additive bridge: for `k ≤ j` (so the `−2k²` truncation resolves),
    `Q(j,k) = 4(j−k)²+8(j−k)k+12(j−k)+2k²+15k+8`. -/
theorem Qpoly_brk {j k : Nat} (h : k ≤ j) :
    Qpoly j k = 4 * ((j - k) * (j - k)) + 8 * ((j - k) * k) + 12 * (j - k) + 2 * (k * k)
      + 15 * k + 8 := by
  obtain ⟨d, hd⟩ : ∃ d, j = k + d := ⟨j - k, (add_sub_of_le h).symm⟩
  subst hd
  rw [show k + d - k = d from by rw [Nat.add_comm k d, add_sub_cancel_right]]
  unfold Qpoly
  rw [show 4 * (k + d) * (k + d) + 12 * (k + d) + 3 * k + 8
        = (4 * (d * d) + 8 * (d * k) + 12 * d + 2 * (k * k) + 15 * k + 8) + 2 * (k * k) from by
        ring_nat, add_sub_cancel_right]

/-- `Qpoly` additive bridge at `k+1`: for `k ≤ j`,
    `Q(j,k+1) = 4(j−k)²+8(j−k)k+12(j−k)+2k²+11k+9`. -/
theorem Qpoly_brk1 {j k : Nat} (h : k ≤ j) :
    Qpoly j (k + 1) = 4 * ((j - k) * (j - k)) + 8 * ((j - k) * k) + 12 * (j - k) + 2 * (k * k)
      + 11 * k + 9 := by
  obtain ⟨d, hd⟩ : ∃ d, j = k + d := ⟨j - k, (add_sub_of_le h).symm⟩
  subst hd
  rw [show k + d - k = d from by rw [Nat.add_comm k d, add_sub_cancel_right]]
  unfold Qpoly
  rw [show 4 * (k + d) * (k + d) + 12 * (k + d) + 3 * (k + 1) + 8
        = (4 * (d * d) + 8 * (d * k) + 12 * d + 2 * (k * k) + 11 * k + 9) + 2 * ((k + 1) * (k + 1))
        from by ring_nat, add_sub_cancel_right]

/-! ## Telescoping infrastructure (pure ℕ, no subtraction)

The WZ proof sums the cleared per-`k` identity over `k`; the certificate's
`Ĝ(j,k+1)`/`Ĝ(j,k)` terms then telescope.  The repo had no telescoping lemma —
this is the additive (subtraction-free) form `Σ_{k<n} g(k+1) + g 0 = Σ_{k<n} g k +
g n`, i.e. `Σ(g(k+1)−g(k)) = g(n)−g(0)` rearranged to stay in ℕ. -/

/-- Shift-telescoping in ℕ: `Σ_{k<n} g(k+1) + g 0 = Σ_{k<n} g k + g n`. -/
theorem sumTo_shift_eq (g : Nat → Nat) :
    ∀ n, sumTo n (fun k => g (k + 1)) + g 0 = sumTo n g + g n
  | 0 => rfl
  | n + 1 => by
    rw [sumTo_succ, sumTo_succ]
    show sumTo n (fun k => g (k + 1)) + g (n + 1) + g 0 = sumTo n g + g n + g (n + 1)
    rw [Nat.add_right_comm (sumTo n (fun k => g (k + 1))) (g (n + 1)) (g 0),
        sumTo_shift_eq g n]

/-- The denominator Apéry number `Bₙ = Σ_{k=0}^n C(n,k)²·C(n+k,k)²`. -/
def B (n : Nat) : Nat := sumTo (n + 1) (aperySummand n)

/-- `aperyLead j = 34j³+153j²+231j+117` — the leading Apéry polynomial (matches
    `DepthAperyCubic.aperyLead` as a polynomial in `j`). -/
def aperyLead (j : Nat) : Nat := 34 * j ^ 3 + 153 * j ^ 2 + 231 * j + 117

/-- `aperyLead` in `^`-free product form (for `ring_nat`). -/
theorem aperyLead_prod (j : Nat) :
    aperyLead j = 34 * (j * j * j) + 153 * (j * j) + 231 * j + 117 := by
  unfold aperyLead
  rw [show j ^ 3 = j * j * j from by rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_one],
      show j ^ 2 = j * j from by rw [Nat.pow_succ, Nat.pow_one]]

/-- Seeds: `B 0 = 1`, `B 1 = 5` (match `zeta3Den 0, zeta3Den 1`). -/
theorem B_zero : B 0 = 1 := by decide
theorem B_one : B 1 = 5 := by decide
theorem B_two : B 2 = 73 := by decide
theorem B_three : B 3 = 1445 := by decide

/-- The Apéry recurrence on base layers (validation of the nucleus statement).
    The general `∀ j` form is the WZ frontier. -/
theorem apery_recurrence_at0 :
    (0 + 2) ^ 3 * B (0 + 2) + (0 + 1) ^ 3 * B 0 = aperyLead 0 * B (0 + 1) := by decide
theorem apery_recurrence_at1 :
    (1 + 2) ^ 3 * B (1 + 2) + (1 + 1) ^ 3 * B 1 = aperyLead 1 * B (1 + 1) := by decide
theorem apery_recurrence_at2 :
    (2 + 2) ^ 3 * B (2 + 2) + (2 + 1) ^ 3 * B 2 = aperyLead 2 * B (2 + 1) := by decide

/-! ## §WZ — the reduced polynomial core of the WZ telescoping identity

The per-`k` WZ identity (see `research-notes/frontiers/zeta3_wz`), after expressing
every term as `W·(polynomial)` via the column recurrence `(n+1−k)·C(n+1,k) =
(n+1)·C(n,k)` (so `W = C(j+2,k)²·C(j+k,k)²` factors out), collapses to a single
polynomial identity in `(j,k)`.  In the additive parametrisation `j = k + d`
(`d = j−k`, the `aperyTrinomial` trick) it becomes a **subtraction-free ℕ
identity** — `j+2−k = d+2`, `j+1−k = d+1`, `j+k+1 = 2k+d+1`, etc. — closed by
`ring_nat`.  Coefficients: `Q(j,k) = 4j²+12j−2k²+3k+8 = 4d²+8dk+12d+2k²+15k+8`,
`Q(j,k+1) = 4d²+8dk+12d+2k²+11k+9`, `aperyLead(k+d) = 34(k+d)³+…`. -/

/-- ★★ **The reduced WZ polynomial identity** (the cleared certificate core), in the
    additive `j = k+d` form.  Verified ∅-axiom via `ring_nat`.  This is the
    mathematical heart of Apéry's recurrence; the remaining work is the binomial
    `W`-factoring (`colrec` + the contiguity relations) that reduces the per-`k`
    identity to this. -/
theorem reduced_wz_identity (k d : Nat) :
    (k + d + 2) * (k + d + 2) * (k + d + 2) * ((2 * k + d + 1) * (2 * k + d + 1))
        * ((2 * k + d + 2) * (2 * k + d + 2))
      + (k + d + 1) * (k + d + 1) * (k + d + 1) * ((d + 2) * (d + 2)) * ((d + 1) * (d + 1))
      + 4 * (2 * k + 2 * d + 3)
          * (4 * (d * d) + 8 * d * k + 12 * d + 2 * (k * k) + 11 * k + 9)
          * ((d + 2) * (d + 2)) * ((2 * k + d + 1) * (2 * k + d + 1))
    = (34 * ((k + d) * (k + d) * (k + d)) + 153 * ((k + d) * (k + d)) + 231 * (k + d) + 117)
          * ((d + 2) * (d + 2)) * ((2 * k + d + 1) * (2 * k + d + 1))
      + 4 * (k * k * k * k) * (2 * k + 2 * d + 3)
          * (4 * (d * d) + 8 * d * k + 12 * d + 2 * (k * k) + 15 * k + 8) := by
  ring_nat

/-- `Q(j,j+1) = 2j²+11j+9`. -/
theorem Qpoly_at_jp1 (j : Nat) : Qpoly j (j + 1) = 2 * j * j + 11 * j + 9 := by
  unfold Qpoly
  rw [show 4 * j * j + 12 * j + 3 * (j + 1) + 8 = (2 * j * j + 11 * j + 9) + 2 * ((j + 1) * (j + 1))
        from by ring_nat, add_sub_cancel_right]

/-- `Q(j,j+2) = 2j²+7j+6`. -/
theorem Qpoly_at_jp2 (j : Nat) : Qpoly j (j + 2) = 2 * j * j + 7 * j + 6 := by
  unfold Qpoly
  rw [show 4 * j * j + 12 * j + 3 * (j + 2) + 8 = (2 * j * j + 7 * j + 6) + 2 * ((j + 2) * (j + 2))
        from by ring_nat, add_sub_cancel_right]

/-- ★ **The reduced identity** `redLHS = redRHS` for `k ≤ j+2` — the polynomial core
    in the exact form the `W`-relations produce.  Cases: `k≤j` (bridge to
    `reduced_wz_identity` via `j=k+d`, `Qpoly_brk`, `aperyLead_prod`), `k=j+1`,
    `k=j+2` (subtractions resolve to `1`/`0`, `Qpoly` to `Qpoly_at_*`). -/
theorem redid_eq {j k : Nat} (h : k ≤ j + 2) :
    (j + 2) * (j + 2) * (j + 2) * ((j + k + 1) * (j + k + 1)) * ((j + k + 2) * (j + k + 2))
      + (j + 1) * (j + 1) * (j + 1) * ((j + 2 - k) * (j + 2 - k)) * ((j + 1 - k) * (j + 1 - k))
      + 4 * (2 * j + 3) * Qpoly j (k + 1) * ((j + 2 - k) * (j + 2 - k)) * ((j + k + 1) * (j + k + 1))
    = aperyLead j * ((j + 2 - k) * (j + 2 - k)) * ((j + k + 1) * (j + k + 1))
      + 4 * (k * k * k * k) * (2 * j + 3) * Qpoly j k := by
  rcases Nat.lt_or_ge k (j + 1) with hkj | hkge
  · -- k ≤ j
    have hkjle : k ≤ j := Nat.le_of_lt_succ hkj
    obtain ⟨d, hd⟩ : ∃ d, j = k + d := ⟨j - k, (add_sub_of_le hkjle).symm⟩
    subst hd
    rw [Qpoly_brk1 (Nat.le_add_right k d), Qpoly_brk (Nat.le_add_right k d), aperyLead_prod,
        show k + d + 2 - k = d + 2 from by
          rw [show k + d + 2 = (d + 2) + k from by ring_nat, add_sub_cancel_right],
        show k + d + 1 - k = d + 1 from by
          rw [show k + d + 1 = (d + 1) + k from by ring_nat, add_sub_cancel_right],
        show k + d - k = d from by rw [Nat.add_comm k d, add_sub_cancel_right]]
    ring_nat
  · -- j+1 ≤ k ≤ j+2 : k = j+1 or k = j+2
    rcases Nat.lt_or_ge k (j + 2) with hk2 | hk2ge
    · -- k = j+1
      have hk : k = j + 1 := Nat.le_antisymm (Nat.le_of_lt_succ hk2) hkge
      subst hk
      rw [show j + 1 + 1 = j + 2 from rfl, Qpoly_at_jp2, Qpoly_at_jp1, aperyLead_prod,
          show j + 2 - (j + 1) = 1 from by
            rw [show j + 2 = 1 + (j + 1) from by ring_nat, add_sub_cancel_right],
          show j + 1 - (j + 1) = 0 from nat_sub_eq_zero (Nat.le_refl _)]
      ring_nat
    · -- k = j+2
      have hk : k = j + 2 := Nat.le_antisymm h hk2ge
      subst hk
      rw [Qpoly_at_jp2,
          show j + 2 - (j + 2) = 0 from nat_sub_eq_zero (Nat.le_refl _),
          show j + 1 - (j + 2) = 0 from nat_sub_eq_zero (Nat.le_succ (j + 1))]
      simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add]
      ring_nat

/-- ★★★ **The per-`k` WZ identity** (the cleared telescoping summand, all-ℕ):
    `(j+1)²(j+2)²[(j+2)³a(j+2,k)+(j+1)³a(j,k)] + Gmag(j,k+1)
       = (j+1)²(j+2)²·aperyLead(j)·a(j+1,k) + Gmag(j,k)`.
    Both sides `= W · (reduced)` via `R0/R1/R2/G1`; then `redid_eq` (`k≤j+2`) or
    `W=0` (`k>j+2`). -/
theorem per_k (j k : Nat) :
    ((j + 1) * (j + 1)) * ((j + 2) * (j + 2))
        * (((j + 2) * (j + 2) * (j + 2)) * aperySummand (j + 2) k
            + ((j + 1) * (j + 1) * (j + 1)) * aperySummand j k)
      + Gmag j (k + 1)
    = ((j + 1) * (j + 1)) * ((j + 2) * (j + 2)) * aperyLead j * aperySummand (j + 1) k
      + Gmag j k := by
  have hL :
      ((j + 1) * (j + 1)) * ((j + 2) * (j + 2))
          * (((j + 2) * (j + 2) * (j + 2)) * aperySummand (j + 2) k
              + ((j + 1) * (j + 1) * (j + 1)) * aperySummand j k)
        + Gmag j (k + 1)
      = Wfac j k *
          ((j + 2) * (j + 2) * (j + 2) * ((j + k + 1) * (j + k + 1)) * ((j + k + 2) * (j + k + 2))
            + (j + 1) * (j + 1) * (j + 1) * ((j + 2 - k) * (j + 2 - k)) * ((j + 1 - k) * (j + 1 - k))
            + 4 * (2 * j + 3) * Qpoly j (k + 1) * ((j + 2 - k) * (j + 2 - k))
                * ((j + k + 1) * (j + k + 1))) := by
    calc ((j + 1) * (j + 1)) * ((j + 2) * (j + 2))
            * (((j + 2) * (j + 2) * (j + 2)) * aperySummand (j + 2) k
                + ((j + 1) * (j + 1) * (j + 1)) * aperySummand j k)
          + Gmag j (k + 1)
        = ((j + 2) * (j + 2) * (j + 2))
              * (aperySummand (j + 2) k * ((j + 1) * (j + 1)) * ((j + 2) * (j + 2)))
            + ((j + 1) * (j + 1) * (j + 1))
              * (aperySummand j k * ((j + 1) * (j + 1)) * ((j + 2) * (j + 2)))
            + Gmag j (k + 1) := by ring_nat
      _ = ((j + 2) * (j + 2) * (j + 2))
              * (Wfac j k * ((j + k + 1) * (j + k + 1)) * ((j + k + 2) * (j + k + 2)))
            + ((j + 1) * (j + 1) * (j + 1))
              * (Wfac j k * ((j + 2 - k) * (j + 2 - k)) * ((j + 1 - k) * (j + 1 - k)))
            + Gmag j (k + 1) := by rw [R2, R0]
      _ = ((j + 2) * (j + 2) * (j + 2))
              * (Wfac j k * ((j + k + 1) * (j + k + 1)) * ((j + k + 2) * (j + k + 2)))
            + ((j + 1) * (j + 1) * (j + 1))
              * (Wfac j k * ((j + 2 - k) * (j + 2 - k)) * ((j + 1 - k) * (j + 1 - k)))
            + 4 * (2 * j + 3) * Qpoly j (k + 1) * ((j + 2 - k) * (j + 2 - k))
                * ((j + k + 1) * (j + k + 1)) * Wfac j k := by rw [G1]
      _ = _ := by ring_nat
  have hR :
      ((j + 1) * (j + 1)) * ((j + 2) * (j + 2)) * aperyLead j * aperySummand (j + 1) k + Gmag j k
      = Wfac j k *
          (aperyLead j * ((j + 2 - k) * (j + 2 - k)) * ((j + k + 1) * (j + k + 1))
            + 4 * (k * k * k * k) * (2 * j + 3) * Qpoly j k) := by
    calc ((j + 1) * (j + 1)) * ((j + 2) * (j + 2)) * aperyLead j * aperySummand (j + 1) k + Gmag j k
        = aperyLead j * (aperySummand (j + 1) k * ((j + 1) * (j + 1)) * ((j + 2) * (j + 2)))
            + Gmag j k := by ring_nat
      _ = aperyLead j * (Wfac j k * ((j + 2 - k) * (j + 2 - k)) * ((j + k + 1) * (j + k + 1)))
            + Gmag j k := by rw [R1]
      _ = aperyLead j * (Wfac j k * ((j + 2 - k) * (j + 2 - k)) * ((j + k + 1) * (j + k + 1)))
            + 4 * (k * k * k * k) * (2 * j + 3) * Qpoly j k * Wfac j k := by
          rw [show Gmag j k = 4 * (k * k * k * k) * (2 * j + 3) * Qpoly j k * Wfac j k from rfl]
      _ = _ := by ring_nat
  rw [hL, hR]
  rcases Nat.lt_or_ge k (j + 2 + 1) with hle | hgt
  · rw [redid_eq (Nat.le_of_lt_succ hle)]
  · have hw : Wfac j k = 0 := by
      unfold Wfac
      rw [choose_eq_zero_of_lt (j + 2) k hgt, show (0 : Nat) * 0 = 0 from rfl, Nat.zero_mul]
    rw [hw, Nat.zero_mul, Nat.zero_mul]

/-! ## §recurrence — sum the per-`k` identity over `k`, telescope, cancel -/

/-- `a(n,k) = 0` for `k > n`. -/
theorem aperySummand_zero {n k : Nat} (h : n < k) : aperySummand n k = 0 := by
  unfold aperySummand
  rw [choose_eq_zero_of_lt n k h, show (0 : Nat) * 0 = 0 from rfl, Nat.zero_mul]

/-- `Gmag j 0 = 0` (the `k⁴` factor vanishes). -/
theorem Gmag_zero (j : Nat) : Gmag j 0 = 0 := by
  unfold Gmag
  rw [show 4 * (0 * 0 * 0 * 0) = 0 from rfl, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul]

/-- `Gmag j (j+3) = 0` (`Wfac` vanishes: `C(j+2,j+3)=0`). -/
theorem Gmag_top (j : Nat) : Gmag j (j + 3) = 0 := by
  unfold Gmag
  rw [show Wfac j (j + 3) = 0 from by
        unfold Wfac
        rw [choose_eq_zero_of_lt (j + 2) (j + 3) (Nat.lt_succ_self (j + 2)),
            show (0 : Nat) * 0 = 0 from rfl, Nat.zero_mul],
      Nat.mul_zero]

/-- Extend the `B(j)`-sum to upper bound `j+3` (tail `k∈{j+1,j+2}` vanishes). -/
theorem sumExt_j (j : Nat) : sumTo (j + 3) (aperySummand j) = B j := by
  show sumTo (j + 1 + 1 + 1) (aperySummand j) = sumTo (j + 1) (aperySummand j)
  rw [sumTo_succ, sumTo_succ, aperySummand_zero (Nat.lt_succ_self j),
      aperySummand_zero (Nat.lt_succ_of_lt (Nat.lt_succ_self j)), Nat.add_zero, Nat.add_zero]

/-- Extend the `B(j+1)`-sum to upper bound `j+3` (tail `k=j+2` vanishes). -/
theorem sumExt_j1 (j : Nat) : sumTo (j + 3) (aperySummand (j + 1)) = B (j + 1) := by
  show sumTo (j + 1 + 1 + 1) (aperySummand (j + 1)) = sumTo (j + 1 + 1) (aperySummand (j + 1))
  rw [sumTo_succ, aperySummand_zero (Nat.lt_succ_self (j + 1)), Nat.add_zero]

/-- `B(j+2)`-sum already has upper bound `j+3`. -/
theorem sumExt_j2 (j : Nat) : sumTo (j + 3) (aperySummand (j + 2)) = B (j + 2) := rfl

/-- ★★★ **Apéry's recurrence** for the binomial sums `Bₙ`:
    `(j+2)³·B(j+2) + (j+1)³·B(j) = aperyLead(j)·B(j+1)`.  Sum `per_k` over `k<j+3`:
    the `Gmag` terms telescope (`sumTo_shift_eq`, boundaries `0`); the `a`-sums
    extend to `B`; cancel `(j+1)²(j+2)²`. -/
theorem apery_recurrence (j : Nat) :
    (j + 2) * (j + 2) * (j + 2) * B (j + 2) + (j + 1) * (j + 1) * (j + 1) * B j
      = aperyLead j * B (j + 1) := by
  -- the Gmag telescoping sums are equal
  have hSQ : sumTo (j + 3) (fun k => Gmag j (k + 1)) = sumTo (j + 3) (Gmag j) := by
    have h := sumTo_shift_eq (Gmag j) (j + 3)
    rw [Gmag_zero, Gmag_top, Nat.add_zero, Nat.add_zero] at h
    exact h
  -- LHS sum of per_k (keep C = (j+1)²(j+2)² factored out)
  have hF : sumTo (j + 3) (fun k =>
        ((j + 1) * (j + 1)) * ((j + 2) * (j + 2))
            * (((j + 2) * (j + 2) * (j + 2)) * aperySummand (j + 2) k
                + ((j + 1) * (j + 1) * (j + 1)) * aperySummand j k)
          + Gmag j (k + 1))
      = ((j + 1) * (j + 1)) * ((j + 2) * (j + 2))
          * ((j + 2) * (j + 2) * (j + 2) * B (j + 2) + (j + 1) * (j + 1) * (j + 1) * B j)
        + sumTo (j + 3) (fun k => Gmag j (k + 1)) := by
    rw [← sumTo_add_func (j + 3)
          (fun k => ((j + 1) * (j + 1)) * ((j + 2) * (j + 2))
            * (((j + 2) * (j + 2) * (j + 2)) * aperySummand (j + 2) k
                + ((j + 1) * (j + 1) * (j + 1)) * aperySummand j k))
          (fun k => Gmag j (k + 1)),
        ← sumTo_mul_left (((j + 1) * (j + 1)) * ((j + 2) * (j + 2))) (j + 3)
          (fun k => ((j + 2) * (j + 2) * (j + 2)) * aperySummand (j + 2) k
            + ((j + 1) * (j + 1) * (j + 1)) * aperySummand j k),
        ← sumTo_add_func (j + 3)
          (fun k => ((j + 2) * (j + 2) * (j + 2)) * aperySummand (j + 2) k)
          (fun k => ((j + 1) * (j + 1) * (j + 1)) * aperySummand j k),
        ← sumTo_mul_left ((j + 2) * (j + 2) * (j + 2)) (j + 3) (aperySummand (j + 2)),
        ← sumTo_mul_left ((j + 1) * (j + 1) * (j + 1)) (j + 3) (aperySummand j),
        sumExt_j2, sumExt_j]
  -- RHS sum of per_k (E = C·aperyLead j factored as the multiplier)
  have hG : sumTo (j + 3) (fun k =>
        ((j + 1) * (j + 1)) * ((j + 2) * (j + 2)) * aperyLead j * aperySummand (j + 1) k
          + Gmag j k)
      = ((j + 1) * (j + 1)) * ((j + 2) * (j + 2)) * aperyLead j * B (j + 1)
        + sumTo (j + 3) (Gmag j) := by
    rw [← sumTo_add_func (j + 3)
          (fun k => ((j + 1) * (j + 1)) * ((j + 2) * (j + 2)) * aperyLead j * aperySummand (j + 1) k)
          (fun k => Gmag j k),
        ← sumTo_mul_left (((j + 1) * (j + 1)) * ((j + 2) * (j + 2)) * aperyLead j) (j + 3)
          (aperySummand (j + 1)),
        sumExt_j1]
  -- combine
  have hcong : sumTo (j + 3) (fun k =>
        ((j + 1) * (j + 1)) * ((j + 2) * (j + 2))
            * (((j + 2) * (j + 2) * (j + 2)) * aperySummand (j + 2) k
                + ((j + 1) * (j + 1) * (j + 1)) * aperySummand j k)
          + Gmag j (k + 1))
      = sumTo (j + 3) (fun k =>
        ((j + 1) * (j + 1)) * ((j + 2) * (j + 2)) * aperyLead j * aperySummand (j + 1) k
          + Gmag j k) :=
    sumTo_congr (j + 3) _ _ (fun k _ => per_k j k)
  rw [hF, hG, hSQ] at hcong
  have summed := add_right_cancel hcong
  have hC : 0 < ((j + 1) * (j + 1)) * ((j + 2) * (j + 2)) :=
    Nat.mul_pos (Nat.mul_pos (Nat.succ_pos j) (Nat.succ_pos j))
      (Nat.mul_pos (Nat.succ_pos (j + 1)) (Nat.succ_pos (j + 1)))
  apply mul_left_cancel_pos hC
  rw [summed]
  ring_nat

end E213.Lib.Math.NumberTheory.AperyRecurrence
