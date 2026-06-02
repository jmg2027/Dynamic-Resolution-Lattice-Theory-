import E213.Lib.Math.Real213.CrossDetOvertake
import E213.Lib.Math.Real213.GeometricThreshold
import E213.Meta.Nat.PureNat
import E213.Meta.Nat.PolyNat

/-!
# CompletabilityGrade — completability is a lex `(exponential-height, rate)` grade

`GeometricThreshold` showed that *within one exponential height* — a geometric
cross-determinant `W_i = r^i` over a geometric denominator `d_i = q^i` — completability
is decided by the **rate**: free iff `r < q` (`geom_boundary_iff`).  But the rate is not
the whole story.  This file adds the **height** axis: crossing one exponential layer up
breaks the bridge *regardless of rate*, so completability is governed by the
**lexicographic order `(height, rate)`** — an ordinal `ω·height + rate` — with **height
dominating rate**.

  * ★★ `height_two_overtakes` — a *double*-exponential cross-determinant `W_i = q^{b^i}`
    (height 2) over a *single*-exponential denominator `d_i = q^i` (height 1) **always**
    breaks `CrossDetSmall`, for any bases `q, b ≥ 2`.  The base/rate is irrelevant once
    the exponential height jumps: the height-2 term overruns the height-1 denominator's
    discrete growth at `i = 2` (`q^3 ≤ q^{b^2}`, via `overtake_breaks_at`).
  * ★★★ `completability_grade` — the two axes together: *within* a height, free iff the
    rate is strictly smaller (`r < q`); *up* a height, broken no matter the rate.  So the
    completability invariant is the lex pair `(exponential-height, rate)`, not the rate
    alone — height is the `ω`-coefficient, rate the finite part.

This is the first rung of grading the binary completability boundary into an ordinal:
the coarse step is the exponential height (the `ω`-jumps), the fine step the geometric
rate (the finite part within a height).

All zero-axiom.
-/

namespace E213.Lib.Math.Real213.CompletabilityGrade

open E213.Lib.Math.Real213.CrossDetOvertake
  (CrossDetSmall overtake_breaks_at two_pow_ge_succ two_pow_ge_self)
open E213.Lib.Math.Real213.GeometricThreshold (geom_boundary_iff)
open E213.Meta.Nat.PureNat (pow_add)
open E213.Meta.Nat.PolyNat (poly_id)
open E213.Tactic.NatHelper (add_mul mul_assoc)

/-! ## §1 — the `ω`-jump: one exponential height up breaks, regardless of rate -/

/-- ★★ **Height 2 over height 1 always overtakes.**  The double-exponential
    cross-determinant `W_i = q^{b^i}` over the single-exponential denominator
    `d_i = q^i` breaks `CrossDetSmall` for any `q, b ≥ 2`.  Tested at `i = 2`:
    `d_3 = q^3 ≤ q^{b^2} = W_2` (since `3 ≤ b^2`), and `overtake_breaks_at` fires —
    the exponential-height gap overruns the denominator's growth no matter the base. -/
theorem height_two_overtakes (q b : Nat) (hq : 2 ≤ q) (hb : 2 ≤ b) :
    ¬ CrossDetSmall (fun i => q ^ (b ^ i)) (fun i => q ^ i) := by
  have hq0 : 0 < q := Nat.lt_of_lt_of_le (by decide) hq
  refine overtake_breaks_at (fun i => q ^ (b ^ i)) (fun i => q ^ i)
    (fun i => Nat.pos_pow_of_pos i hq0) 2 (by decide) ?_
  show q ^ (2 + 1) ≤ q ^ (b ^ 2)
  have h3 : 3 ≤ b ^ 2 := Nat.le_trans (by decide) (Nat.pow_le_pow_left hb 2)
  exact Nat.pow_le_pow_right (Nat.le_trans (by decide) hq) h3

/-- ★★ **Height 1 under height 2 always completes.**  A single-exponential
    cross-determinant `W_i = q^i` over a *double*-exponential denominator `d_i = q^{b^i}`
    satisfies `CrossDetSmall` for any `q, b ≥ 2`: the denominator's double-exponential
    growth swamps both the polynomial factor and the single-exponential cross-det.  The
    symmetric counterpart of `height_two_overtakes` — going *down* an exponential height
    is always free. -/
theorem height_one_under_height_two (q b : Nat) (hq : 2 ≤ q) (hb : 2 ≤ b) :
    CrossDetSmall (fun i => q ^ i) (fun i => q ^ (b ^ i)) := by
  intro i _
  show i * (i + 1) * q ^ i + i * q ^ (b ^ i) ≤ (i + 1) * q ^ (b ^ (i + 1))
  have hq1 : 1 ≤ q := Nat.le_trans (by decide) hq
  have hibi : i ≤ b ^ i := Nat.le_trans (two_pow_ge_self i) (Nat.pow_le_pow_left hb i)
  have hqi : q ^ i ≤ q ^ (b ^ i) := Nat.pow_le_pow_right hq1 hibi
  have hbig : i + 1 ≤ q ^ (b ^ i) :=
    Nat.le_trans (two_pow_ge_succ i)
      (Nat.le_trans (Nat.pow_le_pow_right (by decide) hibi) (Nat.pow_le_pow_left hq (b ^ i)))
  have hbb : b ^ i + b ^ i ≤ b ^ (i + 1) := by
    rw [Nat.pow_succ, ← Nat.mul_two]; exact Nat.mul_le_mul_left (b ^ i) hb
  have hRHSbig : q ^ (b ^ i) * q ^ (b ^ i) ≤ q ^ (b ^ (i + 1)) := by
    rw [← pow_add]; exact Nat.pow_le_pow_right hq1 hbb
  have hp : (i + 1) * (i + 1) = i * (i + 1) + i + 1 :=
    poly_id (.mul (.add .X (.C 1)) (.add .X (.C 1)))
            (.add (.add (.mul .X (.add .X (.C 1))) .X) (.C 1)) rfl i
  have hcoef : i * (i + 1) + i ≤ (i + 1) * q ^ (b ^ i) :=
    Nat.le_trans (by rw [hp]; exact Nat.le_succ _) (Nat.mul_le_mul_left (i + 1) hbig)
  calc i * (i + 1) * q ^ i + i * q ^ (b ^ i)
      ≤ i * (i + 1) * q ^ (b ^ i) + i * q ^ (b ^ i) :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hqi) _
    _ = (i * (i + 1) + i) * q ^ (b ^ i) := (add_mul _ _ _).symm
    _ ≤ ((i + 1) * q ^ (b ^ i)) * q ^ (b ^ i) := Nat.mul_le_mul_right _ hcoef
    _ = (i + 1) * (q ^ (b ^ i) * q ^ (b ^ i)) := by rw [mul_assoc]
    _ ≤ (i + 1) * q ^ (b ^ (i + 1)) := Nat.mul_le_mul_left _ hRHSbig

/-! ## §2 — the grade: lex `(height, rate)`, height dominating rate -/

/-- ★★★ **Completability is a lex `(exponential-height, rate)` grade.**

    * **within one height** (both geometric, `q ≥ 2`): free ⟺ the rate is strictly
      smaller, `r < q` (`geom_boundary_iff`);
    * **up one height**: a double-exponential cross-determinant over a single-exponential
      denominator breaks `CrossDetSmall` for *every* base (`height_two_overtakes`).

    So the completability invariant is the ordinal `ω·height + rate`: the exponential
    height is the dominant (`ω`) coordinate, the geometric rate the finite refinement
    within a height.  Rate alone does not decide — height dominates.

    The three rungs:
    * **down a height** (height-1 over height-2): always free
      (`height_one_under_height_two`);
    * **within a height** (both geometric): free ⟺ `r < q` (`geom_boundary_iff`);
    * **up a height** (height-2 over height-1): always broken, any rate
      (`height_two_overtakes`). -/
theorem completability_grade :
    (∀ q b : Nat, 2 ≤ q → 2 ≤ b →
        CrossDetSmall (fun i => q ^ i) (fun i => q ^ (b ^ i)))
    ∧ (∀ q r : Nat, 2 ≤ q →
        (CrossDetSmall (fun i => r ^ i) (fun i => q ^ i) ↔ r < q))
    ∧ (∀ q b : Nat, 2 ≤ q → 2 ≤ b →
        ¬ CrossDetSmall (fun i => q ^ (b ^ i)) (fun i => q ^ i)) :=
  ⟨height_one_under_height_two, fun _ _ hq => geom_boundary_iff hq, height_two_overtakes⟩

end E213.Lib.Math.Real213.CompletabilityGrade
