import E213.Lib.Physics.Foundations.DrltZeroParameters
import E213.Lib.Physics.AlphaEM.ChannelCohomologyLoss

/-!
# Atomic Constants Uniqueness (G35-C2 step 1)

213's atomic 4-tuple (NS, NT, c, d) = (3, 2, 2, 5) is conjectured
to be the **unique** integer solution to a small set of self-
consistency equations derivable from 213-Algebra alone, without
external input.

This file encodes the constraints discovered in the AlphaEM
session work and verifies (3, 2, 2, 5) satisfies all of them,
plus shows no nearby alternatives do.

## Independent constraints

  **C2a (Cohomology loss → 1/α_3 identification)**:
    `c · m · n = m² + m + n − 2`
    From `dim H¹(K_{m,n}^{(c)}) = m² − 1` (= adjoint SU(m) rank).
    For NT=2: c = (m+1)/2, so m odd.  Family: (1,2,1), (3,2,2),
    (5,2,3), ...  Infinite at NT=2.

  **C2b (Adjoint product identity)**:
    `(m² − 1)(n² − 1) = (m+n)² − 1`
    i.e. dim adj SU(m) · dim adj SU(n) = dim adj SU(d).
    Heavy constraint: among (m, n) ≤ 10 only (3, 2) and (2, 3)
    (symmetric pair) satisfy.

  **C2c (Atomic dim sum)**:  d = m + n.
    Definitional.

  **Combined**: C2a + C2b + C2c picks **(3, 2, 2, 5)** essentially
  uniquely (up to the (m, n) swap which is a labelling choice).

STRICT ∅-AXIOM (decide on Nat identities + bounded search).
-/

namespace E213.Lib.Physics.Foundations.AtomicConstantsUnique

open E213.Lib.Physics.Simplex.Counts (NS NT d)

end E213.Lib.Physics.Foundations.AtomicConstantsUnique

namespace E213.Lib.Physics.Foundations.AtomicConstantsUnique

open E213.Lib.Physics.Simplex.Counts (NS NT d)

/-! ## §1 — Three independent atomic constraints

  Each constraint is a Bool predicate over candidate (m, n, c).
  213 atomic constants must satisfy all three. -/

/-- C2a: cohomology loss constraint.
    `c · m · n = m² + m + n − 2`. -/
def constraint_C2a (m n c : Nat) : Bool :=
  c * m * n == m * m + m + n - 2

/-- C2b: adjoint product identity.
    `(m² − 1) · (n² − 1) = (m + n)² − 1`. -/
def constraint_C2b (m n : Nat) : Bool :=
  (m * m - 1) * (n * n - 1) == (m + n) * (m + n) - 1

/-- C2c: atomic dim definition (always trivially holds for D = m+n). -/
def constraint_C2c (m n D : Nat) : Bool :=
  D == m + n

/-- Combined check: 213's (NS, NT, c, d) satisfies all three. -/
def constraints_all (m n c D : Nat) : Bool :=
  constraint_C2a m n c && constraint_C2b m n && constraint_C2c m n D

/-! ## §2 — 213 satisfies all constraints -/

/-- 213 (NS=3, NT=2, c=2, d=5) satisfies C2a. -/
theorem c2a_213 : constraint_C2a NS NT 2 = true := by decide

/-- 213 satisfies C2b: (NS²−1)(NT²−1) = d²−1, i.e. 8·3 = 24. -/
theorem c2b_213 : constraint_C2b NS NT = true := by decide

/-- 213 satisfies C2c: d = NS + NT. -/
theorem c2c_213 : constraint_C2c NS NT d = true := by decide

/-- ★★★★★ 213 atomic constants satisfy all three constraints. -/
theorem atomic_constants_satisfy : constraints_all NS NT 2 d = true := by decide

end E213.Lib.Physics.Foundations.AtomicConstantsUnique

namespace E213.Lib.Physics.Foundations.AtomicConstantsUnique

/-! ## §3 — Bounded uniqueness (search through small candidates)

  Verify 213 is essentially unique among small (m, n, c) ≤ 10. -/

/-- Bounded constraint search: for all (m, n, c, D) in [1..bound]⁴
    with c ≥ 2 (non-trivial multiplicity), is (m, n, c) = (3, 2, 2)
    the unique solution to all three constraints? -/
def is_unique_to_213 (bound : Nat) : Bool :=
  -- 213 itself satisfies
  constraints_all 3 2 2 5
  -- All other (m, n, c) ≤ bound with m ≥ 2, n ≥ 2, c ≥ 2 do
  -- NOT satisfy (excluding m=0/n=0 trivial cases and (2,3,2) swap).
  && (List.range bound).all (fun m =>
       (List.range bound).all (fun n =>
         (List.range bound).all (fun c =>
           if m < 2 || n < 2 || c < 2 then true
           else if m = 3 && n = 2 && c = 2 then true
           else if m = 2 && n = 3 && c = 2 then true
           else constraints_all m n c (m + n) == false)))

/-- ★★★★★ 213 is unique within search bound 7. -/
theorem unique_within_bound_7 : is_unique_to_213 7 = true := by decide

/-! ## §4 — Master atomic uniqueness theorem -/

open E213.Lib.Physics.Simplex.Counts (NS NT d)

/-- ★★★★★ Atomic Constants Uniqueness Master (C2 step 1).
    STRICT ∅-AXIOM.

    Three independent constraints derivable from 213-Algebra:
      C2a: c · NS · NT = NS² + NS + NT − 2  (cohomology loss)
      C2b: (NS² − 1)(NT² − 1) = (NS + NT)² − 1  (adjoint product)
      C2c: d = NS + NT  (atomic dim sum)

    213 (NS=3, NT=2, c=2, d=5) is the unique solution within
    bounded search (m, n, c) < 7 (excluding the symmetric
    (m, n)-swap which is a labelling choice).

    Full ∀ (m, n, c) ∈ ℕ³ uniqueness remains open beyond search
    bound — but the bounded uniqueness is strong empirical
    evidence. -/
theorem atomic_constants_unique_master :
    -- 213 satisfies all three
    constraint_C2a NS NT 2 = true
    ∧ constraint_C2b NS NT = true
    ∧ constraint_C2c NS NT d = true
    ∧ constraints_all NS NT 2 d = true
    -- 213 is unique within bounded search
    ∧ is_unique_to_213 7 = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Physics.Foundations.AtomicConstantsUnique
