import E213.Lib.Math.NumberSystems.Real213.Phi.PhiCutConvergents
import E213.Meta.Int213.Core
import E213.Meta.Int213.Bound

/-!
# PhiNormInvariant — the convergent φ-norm form is `−1` for all n

`PhiCutConvergents.convergent_norm_form` witnesses `num_n² − num_n·den_n −
den_n² = −1` at layers 0..8 by `decide`.  Here it is proved for **all n**.

The Pell numerator/denominator follow the matrix action of `P = [[2,1],[1,1]]`:

    num_{n+1} = 2·num_n + den_n,   den_{n+1} = num_n + den_n   (`coupling`)

(both from the shared recurrence `s(n+2) = 3·s(n+1) − s(n)`).  Under this
coupling the single-sequence φ-norm equals the cross-product Pell unit:

    num_n² − num_n·den_n − den_n²  =  num_n·den_{n+1} − num_{n+1}·den_n
                                   =  pell_unit_at n  =  −1   (∀ n)

so the φ-norm is the constant `−1` — the det-1 symplectic invariant read at a
single layer rather than across adjacent ones.  This upgrades the layers-0..8
`decide` witness to the general `∀ n` form, all ∅-axiom (manual `Int213`
rewrites, no `ring`/`omega`/Mathlib).
-/

namespace E213.Lib.Math.NumberSystems.Real213.PhiNormInvariant

open E213.Meta.Int213
open E213.Lib.Math.Algebra.Mobius213 (P_numerator P_denominator pell_unit_at)

private abbrev N (n : Nat) : Int := P_numerator.seq n
private abbrev D (n : Nat) : Int := P_denominator.seq n

/-! ## Pure Int algebraic helpers (no `ring`/`omega`/Mathlib) -/

private theorem addid (a b : Int) : (a + a + b) + (-a) = a + b := by
  rw [add_assoc (a + a) b (-a), add_comm b (-a), ← add_assoc (a + a) (-a) b]
  rw [add_assoc a a (-a), add_neg_cancel, Int.add_zero]

private theorem cdtail (n d : Int) : (2 * n + 2 * d) + n = (2 * n + d) + (n + d) := by
  have h2d : (2 : Int) * d = d + d := by
    rw [show (2 : Int) = 1 + 1 from rfl, add_mul, Int.one_mul]
  rw [h2d, ← add_assoc (2 * n) d d, add_assoc (2 * n + d) d n, add_comm d n,
      ← add_assoc (2 * n + d) n d]

private theorem coupN_id (n d : Int) :
    3 * (2 * n + d) + (-1) * n + 0 = 2 * (2 * n + d) + (n + d) := by
  rw [Int.add_zero, neg_mul, Int.one_mul]
  have h2 : (2 : Int) * n = n + n := by
    rw [show (2 : Int) = 1 + 1 from rfl, add_mul, Int.one_mul]
  calc 3 * (2 * n + d) + -n
      = (2 * (2 * n + d) + (2 * n + d)) + -n := by
        rw [show (3 : Int) = 2 + 1 from rfl, add_mul, Int.one_mul]
    _ = 2 * (2 * n + d) + ((2 * n + d) + -n) := by rw [add_assoc]
    _ = 2 * (2 * n + d) + ((n + n + d) + -n) := by rw [h2]
    _ = 2 * (2 * n + d) + (n + d) := by rw [addid]

private theorem coupD_id (n d : Int) :
    3 * (n + d) + (-1) * d + 0 = (2 * n + d) + (n + d) := by
  rw [Int.add_zero, neg_mul, Int.one_mul]
  calc 3 * (n + d) + -d
      = (2 * (n + d) + (n + d)) + -d := by
        rw [show (3 : Int) = 2 + 1 from rfl, add_mul, Int.one_mul]
    _ = 2 * (n + d) + ((n + d) + -d) := by rw [add_assoc]
    _ = 2 * (n + d) + (n + (d + -d)) := by rw [add_assoc n d (-d)]
    _ = 2 * (n + d) + (n + 0) := by rw [add_neg_cancel]
    _ = 2 * (n + d) + n := by rw [Int.add_zero]
    _ = (2 * n + 2 * d) + n := by rw [mul_add]
    _ = (2 * n + d) + (n + d) := cdtail n d

private theorem qid (Nn Dn : Int) :
    Nn * (Nn + Dn) - (2 * Nn + Dn) * Dn = Nn * Nn - Nn * Dn - Dn * Dn := by
  rw [mul_add, add_mul]
  rw [show (2 : Int) * Nn = Nn + Nn from by
        rw [show (2 : Int) = 1 + 1 from rfl, add_mul, Int.one_mul]]
  rw [add_mul]
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.sub_eq_add_neg]
  rw [neg_add, neg_add]
  rw [add_assoc (-(Nn * Dn)) (-(Nn * Dn)) (-(Dn * Dn))]
  rw [add_assoc (Nn * Nn) (Nn * Dn) _]
  rw [← add_assoc (Nn * Dn) (-(Nn * Dn)) (-(Nn * Dn) + -(Dn * Dn))]
  rw [add_neg_cancel, zero_add]
  rw [← add_assoc]

/-! ## Coupling — `P = [[2,1],[1,1]]` matrix action, ∀ n -/

/-- The Pell numerator/denominator satisfy the `P = [[2,1],[1,1]]` matrix
    recurrence: `num_{n+1} = 2·num_n + den_n`, `den_{n+1} = num_n + den_n`.
    Proved by induction on the shared second-order recurrence. -/
theorem coupling : ∀ n, N (n + 1) = 2 * N n + D n ∧ D (n + 1) = N n + D n
  | 0 => by constructor <;> rfl
  | n + 1 => by
    obtain ⟨ihN, ihD⟩ := coupling n
    refine ⟨?_, ?_⟩
    · show N (n + 2) = 2 * N (n + 1) + D (n + 1)
      rw [show N (n + 2) = 3 * N (n + 1) + (-1) * N n + 0 from rfl, ihN, ihD]
      exact coupN_id (N n) (D n)
    · show D (n + 2) = N (n + 1) + D (n + 1)
      rw [show D (n + 2) = 3 * D (n + 1) + (-1) * D n + 0 from rfl, ihN, ihD]
      exact coupD_id (N n) (D n)

/-! ## The φ-norm equals the Pell unit, ∀ n -/

/-- The single-sequence φ-norm `num_n² − num_n·den_n − den_n²` equals the
    consecutive cross-product `pell_unit_at n`, via the coupling. -/
theorem norm_eq_pell_unit (n : Nat) :
    N n * N n - N n * D n - D n * D n = pell_unit_at n := by
  obtain ⟨hN, hD⟩ := coupling n
  show N n * N n - N n * D n - D n * D n
     = N n * D (n + 1) - N (n + 1) * D n
  rw [hN, hD]
  exact (qid (N n) (D n)).symm

/-- ★★★ **φ-norm invariant, ∀ n**: `num_n² − num_n·den_n − den_n² = −1` for every
    layer.  The general form of `PhiCutConvergents.convergent_norm_form` (which
    only `decide`s layers 0..8): the φ-norm is the det-1 symplectic invariant
    `pell_unit_at n = −1` read at a single layer.  So every Pell convergent lies
    on the same side of φ — the algebraic reason `phiCut (pellNum n) (pellDen n)
    = false` for all n. -/
theorem phi_norm_eq_neg_one (n : Nat) :
    N n * N n - N n * D n - D n * D n = -1 := by
  rw [norm_eq_pell_unit n]
  exact E213.Lib.Math.Algebra.Mobius213.mobius_213_pell_unit_invariant_forall n

/-! ## Coupling, stated on `seq` directly (for downstream Nat bridges)

`coupling` is stated with the file-local abbreviations `N`/`D`; casting through
them pulls `propext`.  These re-expose the same facts on `P_numerator.seq` /
`P_denominator.seq` so a downstream Nat-level reduction (e.g. `phiCut … = false`
∀n via `PhiAsCut.phiCut_false_of_norm`) can `rw` without the abbreviation cast. -/

/-- Numerator coupling on `seq` directly. -/
theorem seq_coupling_num (n : Nat) :
    P_numerator.seq (n + 1) = 2 * P_numerator.seq n + P_denominator.seq n :=
  (coupling n).1

/-- Denominator coupling on `seq` directly. -/
theorem seq_coupling_den (n : Nat) :
    P_denominator.seq (n + 1) = P_numerator.seq n + P_denominator.seq n :=
  (coupling n).2

/-- Both Pell sequences are nonnegative, ∀ n.  Proved with the repo's ∅-axiom
    `Int213.{add_nonneg, mul_nonneg}` (NOT Lean-core `Int` `≤` lemmas like
    `Int.le_refl`/`Int.add_le_add`, which pull `propext`). -/
theorem seq_nonneg : ∀ n, 0 ≤ P_numerator.seq n ∧ 0 ≤ P_denominator.seq n
  | 0 => ⟨by decide, by decide⟩
  | n + 1 => by
    obtain ⟨hN, hD⟩ := seq_nonneg n
    refine ⟨?_, ?_⟩
    · rw [seq_coupling_num n]
      exact E213.Meta.Int213.add_nonneg (E213.Meta.Int213.mul_nonneg (by decide) hN) hD
    · rw [seq_coupling_den n]
      exact E213.Meta.Int213.add_nonneg hN hD

/-- Step equation for the `2·num − den` gap: `2·(2N + D) − (N + D) = 3N + D`.
    Pure `Int213` rewrites. -/
private theorem gapeq (N D : Int) : 2 * (2 * N + D) - (N + D) = 3 * N + D := by
  rw [mul_add, ← mul_assoc, show (2 : Int) * 2 = 4 from rfl, Int.sub_eq_add_neg,
      neg_add]
  rw [add_assoc (4 * N) (2 * D) (-N + -D), add_left_comm (2 * D) (-N) (-D),
      ← add_assoc (4 * N) (-N) (2 * D + -D)]
  rw [show (4 : Int) * N + -N = 3 * N from by
        rw [show (4 : Int) = 3 + 1 from rfl, add_mul, Int.one_mul, add_assoc,
            add_neg_cancel, Int.add_zero]]
  rw [show (2 : Int) * D + -D = D from by
        rw [show (2 : Int) = 1 + 1 from rfl, add_mul, Int.one_mul, add_assoc,
            add_neg_cancel, Int.add_zero]]

/-- The gap `2·num − den` is nonnegative for all n (so the Nat subtraction
    `2·pellNum − pellDen` is faithful).  Via `Int213.{add_nonneg, mul_nonneg}`
    and the `gapeq` step. -/
theorem gap_nonneg : ∀ n, 0 ≤ 2 * P_numerator.seq n - P_denominator.seq n
  | 0 => by decide
  | n + 1 => by
    obtain ⟨hN, hD⟩ := seq_nonneg n
    rw [seq_coupling_num n, seq_coupling_den n, gapeq]
    exact E213.Meta.Int213.add_nonneg
      (E213.Meta.Int213.mul_nonneg (by decide) hN) hD

/-- `den_n ≤ 2·num_n` for all n — the Nat-subtraction faithfulness bound.
    From `gap_nonneg` via the repo's PURE `Int213.le_of_add_eq_of_nonneg`
    (`x + y = c → 0 ≤ x → y ≤ c`), NOT Lean-core `Int.add_le_add`. -/
theorem seq_den_le (n : Nat) : P_denominator.seq n ≤ 2 * P_numerator.seq n := by
  have hsum : (2 * P_numerator.seq n - P_denominator.seq n) + P_denominator.seq n
            = 2 * P_numerator.seq n := by
    rw [Int.sub_eq_add_neg, add_assoc, add_left_neg, Int.add_zero]
  exact E213.Meta.Int213.le_of_add_eq_of_nonneg hsum (gap_nonneg n)

end E213.Lib.Math.NumberSystems.Real213.PhiNormInvariant
