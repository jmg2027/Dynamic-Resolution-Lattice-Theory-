import E213.Lib.Math.CayleyDickson.Levels.Cayley
import E213.Meta.Nat.IntHelpers
import E213.Lib.Math.CayleyDickson.Lipschitz.LipschitzHeavy
import E213.Lib.Math.Tactic.HurwitzRing
import E213.Lib.Math.CayleyDickson.Levels.CayleyAlgebra213
import E213.Meta.Algebra213.CDDoubleMoufang

namespace E213.Lib.Math.CayleyDickson.Levels.CayleyHeavy


open E213.Lib.Math.CayleyDickson.Integer.ZI
open E213.Lib.Math.CayleyDickson.Integer.ZI.ZI
open E213.Lib.Math.CayleyDickson.Levels.Cayley
open E213.Lib.Math.CayleyDickson.Tower.CDDouble
open E213.Lib.Math.CayleyDickson.Tower.CDDouble.Lipschitz
open E213.Tactic

set_option maxHeartbeats 1000000

/-- **Left alternativity** (universal): `(a·a)·b = a·(a·b)`. -/
theorem alt_left (a b : Cayley) : (a * a) * b = a * (a * b) := by
  hurwitz_ring

open E213.Tactic

/-- **Right alternativity** (universal): `a·(b·b) = (a·b)·b`. -/
theorem alt_right (a b : Cayley) : a * (b * b) = (a * b) * b := by
  hurwitz_ring

/-- **Flexibility** (universal): `(a·b)·a = a·(b·a)`. -/
theorem flexible (a b : Cayley) : (a * b) * a = a * (b * a) := by
  hurwitz_ring

open E213.Tactic E213.Lib.Math.CayleyDickson.Tower.CDDouble.Lipschitz E213.Lib.Math.CayleyDickson.Integer.ZI

/-- Cayley (octonion) norm-squared:
    `re.normSq + im.normSq` at Lipschitz level. -/
def normSq (u : Cayley) : Int :=
  Lipschitz.normSq u.re + Lipschitz.normSq u.im

/-- **Cayley (octonion) Hurwitz identity**: `|u·v|² = |u|² · |v|²`.
    Octonions form a composition algebra.  Proved **strict ∅-axiom**
    by bridging to the abstract `cd_normSq_mul` (the polarization
    Hurwitz identity over the non-commutative Lipschitz base) — no
    `hurwitz_ring` brute force, no `maxHeartbeats` bump. -/
theorem normSq_mul (u v : Cayley) :
    normSq (u * v) = normSq u * normSq v := by
  have h := E213.Meta.Algebra213.cd_normSq_mul
              (E213.Lib.Math.CayleyDickson.Levels.Cayley.toCDDouble u)
              (E213.Lib.Math.CayleyDickson.Levels.Cayley.toCDDouble v)
  rw [← E213.Lib.Math.CayleyDickson.Levels.Cayley.toCDDouble_mul] at h
  exact h

open E213.Tactic E213.Lib.Math.CayleyDickson.Tower.CDDouble.Lipschitz E213.Lib.Math.CayleyDickson.Integer.ZI

/-- `Lipschitz.normSq ≥ 0` (sum of integer squares). -/
private theorem lip_normSq_nonneg (u : Lipschitz) :
    0 ≤ Lipschitz.normSq u := by
  show 0 ≤ u.re.re * u.re.re + u.re.im * u.re.im +
           (u.im.re * u.im.re + u.im.im * u.im.im)
  have h1a := E213.Meta.Nat.IntHelpers.mul_self_nonneg u.re.re
  have h1b := E213.Meta.Nat.IntHelpers.mul_self_nonneg u.re.im
  have h1c := E213.Meta.Nat.IntHelpers.mul_self_nonneg u.im.re
  have h1d := E213.Meta.Nat.IntHelpers.mul_self_nonneg u.im.im
  omega

/-- `Cayley.normSq u = 0 ↔ u = 0`.  Sum of 8 integer squares
    = 0 iff each is 0; delegates to Lipschitz. -/
theorem normSq_eq_zero_iff (u : Cayley) : normSq u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have h1 := lip_normSq_nonneg u.re
    have h2 := lip_normSq_nonneg u.im
    have hre_z : Lipschitz.normSq u.re = 0 := by
      change Lipschitz.normSq u.re + Lipschitz.normSq u.im = 0 at h
      omega
    have him_z : Lipschitz.normSq u.im = 0 := by
      change Lipschitz.normSq u.re + Lipschitz.normSq u.im = 0 at h
      omega
    have hre : u.re = 0 := (E213.Lib.Math.CayleyDickson.Lipschitz.LipschitzHeavy.normSq_eq_zero_iff u.re).mp hre_z
    have him : u.im = 0 := (E213.Lib.Math.CayleyDickson.Lipschitz.LipschitzHeavy.normSq_eq_zero_iff u.im).mp him_z
    show u = ⟨0, 0⟩
    apply E213.Lib.Math.CayleyDickson.Levels.Cayley.Cayley.ext <;> assumption
  · rintro rfl; rfl

/-- **R3 at Cayley (= integer octonions)**: no zero divisors.
    Classical fact that the octonions form a division algebra;
    the integer-lattice subring inherits this.

    Proof: follows from `normSq_mul` + `normSq_eq_zero_iff`. -/
theorem no_zero_div (u v : Cayley) :
    u * v = 0 → u = 0 ∨ v = 0 := by
  intro huv
  have hnorm : normSq (u * v) = 0 := by rw [huv]; rfl
  rw [normSq_mul] at hnorm
  rcases Int.mul_eq_zero.mp hnorm with h | h
  · left; exact (normSq_eq_zero_iff u).mp h
  · right; exact (normSq_eq_zero_iff v).mp h

end E213.Lib.Math.CayleyDickson.Levels.CayleyHeavy
