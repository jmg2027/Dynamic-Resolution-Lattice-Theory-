import E213.Lib.Math.Combinatorics.Binomial
import E213.Lib.Math.Cohomology.Fractal.ConfigCount
/-!
# Graded Ring ↔ configCount bridge (cross-axis)

Two **independent** counting structures both descend from the
atomic constants `(NS, NT, d) = (3, 2, 5)`:

  (A) Graded ring side (cup-ring, paradigm-domain shared):
      `paradigm_coeffs ∈ CoeffSeq` is the coefficient sequence of
      `(1 + x)^d` (Pascal row d).  Row sum is `2^d`.

  (B) Tensor-power / configuration side (fractal hierarchy):
      `configCountD d n = d^(d^n)`.  Level 0 = `d`, level 1 = `d^d`,
      level 2 = `d^(d²)`.  This is a parametric family; no level is
      privileged.

This file makes the bridge explicit at the Lean level: both
quantities are decidable functions of `d`, and at `d = 5` they
take the values:

  · `2^d = 32` (paradigm row sum)
  · `d^d = 3125 = configCount 1`
  · `2^(2d) = 1024` (paradigm self-cup row sum)
  · `d^(d²) = 5^25 = configCount 2` (a bare arithmetic value)

The two structures are commensurate but **orthogonal**: graded-ring
sums count *subsets* (binary 0/1 per atom); tensor-power counts
count *d-labellings* per position.  Both arise from the same atomic
`d`, but neither reduces to the other.

The honest reading: the two are not identified, but are
**simultaneously decidable** functions of d.

All declarations PURE.
-/

namespace E213.Lib.Math.Foundations.GradedRingConfigCountBridge

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Fractal.ConfigCount
  (configCount configCountD configCount_zero configCount_one
   configCount_two configCount_two_pow)

/-- Paradigm-row coefficient sequence at level 0: the Pascal row 5
    `(binom 5 g)_g` truncated past `g = 5`.  Coincides with the
    `paradigm_coeffs` of `ParadigmDomainGradedRing`. -/
def paradigm_coeffs (g : Nat) : Nat :=
  if g ≤ 5 then binom 5 g else 0

/-- The level-0 row sum, computed inline so we don't depend on the
    (currently mis-imported) `ParadigmDomainGradedRing.paradigm_cup_sum`. -/
def paradigm_row_sum : Nat :=
  paradigm_coeffs 0 + paradigm_coeffs 1 + paradigm_coeffs 2
    + paradigm_coeffs 3 + paradigm_coeffs 4 + paradigm_coeffs 5

/-! ## §1 — Common atomic dimension

Both structures are parametric in `d : Nat` and specialise at
the 213 atomic value `d = 5`. -/

/-- The atomic dimension shared by both counting structures. -/
def d_atomic : Nat := 5

/-- Smoke: `d_atomic = 5`. -/
theorem d_atomic_eq_five : d_atomic = 5 := rfl

/-! ## §2 — Graded-ring side row sums

The paradigm coefficient sequence at level 0 has row sum `2^d`
(= 32 at `d = 5`); at level 1 (self-cup) it has row sum `2^(2d)`
(= 1024 at `d = 5`). -/

/-- Smoke: `paradigm_row_sum = 32 = 2^d`. -/
theorem paradigm_row_sum_eq_two_pow_d :
    paradigm_row_sum = 2 ^ d_atomic := by decide

theorem paradigm_row_sum_eq_32 : paradigm_row_sum = 32 := by decide

/-- Self-convolution row sum for `(1+x)^5 · (1+x)^5 = (1+x)^10`:
    sum = `2^10 = 1024`.  Computed inline via Pascal row 10. -/
def paradigm_self_cup_row_sum : Nat :=
  binom 10 0 + binom 10 1 + binom 10 2 + binom 10 3 + binom 10 4
    + binom 10 5 + binom 10 6 + binom 10 7 + binom 10 8 + binom 10 9
    + binom 10 10

/-- Smoke: self-cup row sum = `2^(2d)`. -/
theorem paradigm_self_cup_eq_two_pow_2d :
    paradigm_self_cup_row_sum = 2 ^ (2 * d_atomic) := by decide

theorem paradigm_self_cup_eq_1024 :
    paradigm_self_cup_row_sum = 1024 := by decide

/-! ## §3 — Tensor-power / configCount side

The configuration count at level `n` is `d^(d^n)`.  At `d = 5`,
level 2 evaluates to `5^25` (a bare arithmetic value; no level
is privileged). -/

/-- Level-0 config count: `d = 5`. -/
theorem configCount_level_0 : configCount 0 = d_atomic := by decide

/-- Level-1 config count: `d^d = 5^5 = 3125`. -/
theorem configCount_level_1 : configCount 1 = d_atomic ^ d_atomic := by decide

/-- Level-2 config count: `d^(d²) = 5^25`. -/
theorem configCount_level_2 :
    configCount 2 = d_atomic ^ (d_atomic * d_atomic) := by decide

/-! ## §4 — Numerical witnesses

Concrete values at `d = 5`. -/

theorem configCount_0_value : configCount 0 = 5 := configCount_zero
theorem configCount_1_value : configCount 1 = 3125 := configCount_one
theorem configCount_2_value :
    configCount 2 = 298023223876953125 := configCount_two

/-! ## §5 — Capstone: simultaneous decidability

The two structures are **independent** but **simultaneously
decidable** in `d`.  Each takes a well-defined value at every
`d ≥ 1`; specialising at `d = 5` yields the named DRLT constants
(32, 1024, 5, 3125, 5^25). -/

/-- ★★★★★ **Graded-ring × configCount bridge** at `d = 5`.

    Bundles: the four named numerical readings (graded-ring level-0
    and level-1 row sums, configCount level-0 / level-1 / level-2),
    plus the exponent-formula correspondences (`2^d`, `2^(2d)`,
    `d^d`, `d^(d²)`).  Both structures arise from the same atomic
    `d`, so they are jointly decidable; `5^25` is a bare value, not
    a resolution.

    Reading: this is *not* an identification of the two — they
    count different things (subsets vs labellings).  It is the
    explicit cross-axis statement that the cup-ring's
    `(1+x)^d`-style sums and the fractal hierarchy's `d^(d^n)`-style
    counts are simultaneous downstream consequences of the same
    atomic `d`. -/
theorem graded_ring_nu_bridge_capstone :
    -- Graded-ring side (cup-ring sums)
    paradigm_row_sum = 32
    ∧ paradigm_row_sum = 2 ^ d_atomic
    ∧ paradigm_self_cup_row_sum = 1024
    ∧ paradigm_self_cup_row_sum = 2 ^ (2 * d_atomic)
    -- ConfigCount side (tensor-power family)
    ∧ configCount 0 = d_atomic
    ∧ configCount 1 = d_atomic ^ d_atomic
    ∧ configCount 1 = 3125
    ∧ configCount 2 = d_atomic ^ (d_atomic * d_atomic)
    ∧ configCount 2 = 298023223876953125 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.Foundations.GradedRingConfigCountBridge
