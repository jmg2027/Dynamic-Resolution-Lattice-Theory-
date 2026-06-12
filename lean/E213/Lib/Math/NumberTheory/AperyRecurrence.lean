import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChooseFactorial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Meta.Nat.PolyNatMTactic

/-!
# AperyRecurrence — the binomial Apéry numbers `Bₙ = Σ_k C(n,k)²C(n+k,k)²`

The denominator Apéry numbers as an explicit binomial sum (manifestly `ℕ`).  The
**nucleus** of the ζ(3) program (see `research-notes/frontiers/zeta3_blueprint.md`,
"THE NUCLEUS") is the recurrence

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
open E213.Tactic.NatHelper (add_sub_of_le add_left_cancel mul_left_cancel_pos add_sub_cancel_right)

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

/-- The Apéry summand `C(n,k)²·C(n+k,k)²` (squares as explicit products). -/
def aperySummand (n k : Nat) : Nat :=
  choose n k * choose n k * (choose (n + k) k * choose (n + k) k)

/-- The denominator Apéry number `Bₙ = Σ_{k=0}^n C(n,k)²·C(n+k,k)²`. -/
def B (n : Nat) : Nat := sumTo (n + 1) (aperySummand n)

/-- `aperyLead j = 34j³+153j²+231j+117` — the leading Apéry polynomial (matches
    `DepthAperyCubic.aperyLead` as a polynomial in `j`). -/
def aperyLead (j : Nat) : Nat := 34 * j ^ 3 + 153 * j ^ 2 + 231 * j + 117

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

end E213.Lib.Math.NumberTheory.AperyRecurrence
