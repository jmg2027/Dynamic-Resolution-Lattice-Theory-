import E213.Lib.Math.Cohomology.Cup.InvAlphaEMDecomp

/-!
# AssignmentUniqueness — how far arithmetic forces the 1/α_em layer map

`DEGREES_OF_FREEDOM_LEDGER.md` Layer 1 marks the base-formula
coefficients `derived + assignment`: each *value* is a product of the
forced atoms `(NS, NT, c, d) = (3, 2, 2, 5)` (proven PURE in
`InvAlphaEMDecomp`), but *which* atom-product indexes *which* physical
layer is a separate question.

This file proves the **honest boundary** of what arithmetic alone
settles:

  · **Settled (forced by unique factorisation).** The prime-exponent
    vector of each coefficient is unique within a bounded monomial box —
    there is no second monomial `3^a · 2^p · 5^e` in the box equal to it.
    So the coefficient values are not arbitrary integers; they are the
    unique factor combinations.

  · **NOT settled (residual DoF, made precise).** Because `NT = c = 2`,
    the power of `2` in any coefficient cannot be attributed to `NT`
    versus `c` by arithmetic — there are exactly 3 ways to split a `2²`
    between them. The full layer-assignment (the `c`-multiplicity reading
    that distinguishes α_em from α_2) needs the cohomology
    (`c3_chain`), not this file.

This is the integrity-preserving result: it tightens the ledger's
`assignment` rows where arithmetic genuinely tightens them, and names
the exact place it does not — rather than overclaiming a `decide`
closure (which would itself be the fudge §7.2 forbids).

All theorems PURE (Bool-`decide` over finite `List.range` boxes).
-/

namespace E213.Lib.Physics.AlphaEM.AssignmentUniqueness

/-! ## §1 — the forced atoms (values from the §2 forcing chain) -/

def NS : Nat := 3
def NT : Nat := 2
def c  : Nat := 2
def d  : Nat := 5

/-! ## §2 — representation uniqueness within a monomial box

`reprCount target` counts monomials `3^a · 2^p · 5^e` with
`a, p, e ≤ 3` whose value equals `target`.  A count of `1` means the
coefficient's factor combination is unique in the box (no competing
atom-product gives the same integer). -/

def reprCount (target : Nat) : Nat :=
  (List.range 4).foldl (fun acc a =>
    (List.range 4).foldl (fun acc2 p =>
      (List.range 4).foldl (fun acc3 e =>
        acc3 + (if 3 ^ a * 2 ^ p * 5 ^ e == target then 1 else 0))
        acc2) acc) 0

/-- `60 = 3·2²·5` is the **unique** monomial in the box. -/
theorem repr_60_unique : reprCount 60 = 1 := by decide

/-- `30 = 3·2·5` is the **unique** monomial in the box. -/
theorem repr_30_unique : reprCount 30 = 1 := by decide

/-- `25 = 5²` is the **unique** monomial in the box. -/
theorem repr_25_unique : reprCount 25 = 1 := by decide

/-- `45 = 3²·5` is the **unique** monomial in the box. -/
theorem repr_45_unique : reprCount 45 = 1 := by decide

/-- The four leading coefficients each have a unique box-representation. -/
theorem leading_coeffs_unique :
    reprCount 60 = 1 ∧ reprCount 30 = 1
    ∧ reprCount 25 = 1 ∧ reprCount 45 = 1 := by decide

/-! ## §3 — the residual: the `NT = c` degeneracy

Arithmetic fixes the *power of 2* in each coefficient but cannot say how
much of it is `NT` and how much is `c`, because the two atoms share the
value `2`.  This is the precise location of the Layer-1 `assignment` DoF. -/

/-- `NT` and `c` have the same forced value — the source of the
    degeneracy. -/
theorem nt_eq_c : NT = c := rfl

/-- `twoPowerSplits` counts the ways to write `2² = 2^b · 2^(2-b)` as an
    `NT`-power times a `c`-power.  Arithmetic admits **3** — the split is
    not forced. -/
def twoPowerSplits : Nat :=
  (List.range 3).foldl (fun acc b =>
    acc + (if 2 ^ b * 2 ^ (2 - b) == 4 then 1 else 0)) 0

theorem two_power_splits_three : twoPowerSplits = 3 := by decide

/-- The `60 = c·NS·NT·d` reading (`b_c = b_NT = 1`) is one of the three
    arithmetically-equal splits; selecting it is the cohomology's job
    (`60/30 = c`, the multiplicity factor), not arithmetic's. -/
theorem sixty_split_not_forced :
    NS * NT * c * d = 60 ∧ NS * NT * NT * d = 60 ∧ NS * c * c * d = 60 := by
  decide

/-! ## §4 — master statement

What arithmetic forces (the values, uniquely) and what it leaves to the
cohomology (the NT/c attribution). -/

/-- **Honest boundary capstone.**  The leading coefficient *values* are
    uniquely the stated factor combinations (no other box-monomial
    matches); the *NT-vs-c attribution* is arithmetically free (3 splits
    of each `2²`), so the layer-assignment is settled by arithmetic only
    up to the `NT = c` degeneracy. -/
theorem assignment_arithmetic_boundary :
    -- values forced (unique factorisation in the box)
    (reprCount 60 = 1 ∧ reprCount 30 = 1
      ∧ reprCount 25 = 1 ∧ reprCount 45 = 1)
    -- attribution NOT forced (NT = c shares value 2)
    ∧ NT = c ∧ twoPowerSplits = 3 := by
  decide

end E213.Lib.Physics.AlphaEM.AssignmentUniqueness
