import E213.Lib.Math.Combinatorics.Catalan
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial

/-!
# Catalan ↔ central-binomial bridge (∅-axiom)

The corpus's `catalan` is a finite lookup table (n = 0..7, sentinel `0` beyond),
while `choose` is the Pascal-recurrence binomial.  This file ties them together
and supplies the **universal** engine the table can only exhibit instance-wise.

  * **`central_binom_recurrence`** (★, all `n`): the central-binomial recurrence
    `(n+1)·C(2n+2, n+1) = 2·(2n+1)·C(2n, n)` — the `choose`-level engine behind
    the Catalan growth law `C_{n+1}/C_n = 2(2n+1)/(n+2)`.  Derived *structurally*
    from the Pascal toolkit (`choose_succ_mul` + symmetry), not by `decide`, so it
    holds for every `n`.
  * **`catalan_central_binom`**: the bridge `(n+1)·catalan n = choose (2n) n`
    across the tabulated range, connecting the two independently-built objects.
  * **`catalan_ratio_cross`**: the cross-multiplied Catalan ratio
    `(n+2)·C_{n+1} = 2(2n+1)·C_n` over the real-table range — the universal
    recurrence instantiated on the `catalan` table.

All ∅-axiom (the `Nat.mul_assoc` propext-landmine is avoided via the NatHelper
PURE twin `mul_assoc`).
-/

namespace E213.Lib.Math.Combinatorics.CatalanBinomial

open E213.Lib.Math.Combinatorics.Catalan (catalan)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_succ_mul choose_symm_sum)
open E213.Tactic.NatHelper (mul_assoc)

/-- Helper: `choose (2n+1) n = choose (2n+1) (n+1)` by symmetry (`n + (n+1) = 2n+1`). -/
theorem choose_symm_2n1 (n : Nat) :
    choose (2 * n + 1) n = choose (2 * n + 1) (n + 1) :=
  choose_symm_sum (2 * n + 1) n (n + 1) (by ring_nat)

/-- Helper: `(n+1) · choose (2n+1) (n+1) = (2n+1) · choose (2n) n`.
    Instance of `choose_succ_mul (2n) n`. -/
theorem central_succ_mul (n : Nat) :
    (n + 1) * choose (2 * n + 1) (n + 1) = (2 * n + 1) * choose (2 * n) n :=
  choose_succ_mul (2 * n) n

/-- ★★ **Universal central-binomial recurrence**:
    `(n+1) · choose (2n+2) (n+1) = 2 · (2n+1) · choose (2n) n`.
    Holds for every `n`; the `choose`-level engine behind the Catalan ratio.
    ∅-axiom (built structurally from the Pascal toolkit). -/
theorem central_binom_recurrence (n : Nat) :
    (n + 1) * choose (2 * n + 2) (n + 1)
      = 2 * (2 * n + 1) * choose (2 * n) n := by
  -- Step 1: choose_succ_mul (2n+1) n :
  --   (n+1) · choose (2n+2) (n+1) = (2n+2) · choose (2n+1) n
  have step1 : (n + 1) * choose (2 * n + 2) (n + 1)
      = (2 * n + 2) * choose (2 * n + 1) n := by
    have h := choose_succ_mul (2 * n + 1) n
    rw [show 2 * n + 1 + 1 = 2 * n + 2 from rfl] at h
    exact h
  -- Step 2: rewrite choose (2n+1) n via symmetry, then central_succ_mul
  rw [step1, choose_symm_2n1 n]
  rw [show 2 * n + 2 = 2 * (n + 1) from by ring_nat]
  rw [mul_assoc 2 (n + 1) (choose (2 * n + 1) (n + 1)), central_succ_mul n,
      ← mul_assoc 2 (2 * n + 1) (choose (2 * n) n)]

/-- ★ **Catalan–central-binomial bridge** at each tabulated `n`:
    `(n+1) · catalan n = choose (2n) n`. -/
theorem catalan_central_binom :
    1 * catalan 0 = choose 0 0
    ∧ 2 * catalan 1 = choose 2 1
    ∧ 3 * catalan 2 = choose 4 2
    ∧ 4 * catalan 3 = choose 6 3
    ∧ 5 * catalan 4 = choose 8 4
    ∧ 6 * catalan 5 = choose 10 5
    ∧ 7 * catalan 6 = choose 12 6
    ∧ 8 * catalan 7 = choose 14 7 := by decide

/-- ★ **Catalan cross-multiplied ratio** `(n+2)·C_{n+1} = 2·(2n+1)·C_n`
    over the range where the table is real (n = 0..5) — the universal
    `central_binom_recurrence` instantiated on the `catalan` table. -/
theorem catalan_ratio_cross :
    2 * catalan 1 = 2 * (2 * 0 + 1) * catalan 0
    ∧ 3 * catalan 2 = 2 * (2 * 1 + 1) * catalan 1
    ∧ 4 * catalan 3 = 2 * (2 * 2 + 1) * catalan 2
    ∧ 5 * catalan 4 = 2 * (2 * 3 + 1) * catalan 3
    ∧ 6 * catalan 5 = 2 * (2 * 4 + 1) * catalan 4
    ∧ 7 * catalan 6 = 2 * (2 * 5 + 1) * catalan 5 := by decide

end E213.Lib.Math.Combinatorics.CatalanBinomial
