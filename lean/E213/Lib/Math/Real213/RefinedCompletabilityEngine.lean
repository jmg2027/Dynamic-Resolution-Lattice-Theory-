import E213.Lib.Math.Real213.CompletabilityGrade
import E213.Lib.Math.Real213.IntensionalCompletability

/-!
# RefinedCompletabilityEngine — the two axes as one engine

The crude real/complex split was a 1-bit shadow (the discriminant sign).  The refined
*real* completability engine has two genuine axes, each closed ∅-axiom:

  * an **ordinal height** axis (`CompletabilityGrade`) — completability is graded
    `ω·height + rate`, the height ranging over the whole exponential tower (`expTower`),
    every `ω`-step up a hard break, the rate the finite refinement within a height;
  * an **intensional gauge** axis (`IntensionalCompletability`) — the sufficient *test*
    (`CrossDetSmall`) is presentation-relative (antitone under rescaling, gcd-reduced
    canonical), while the *truth* (the cut's completion) is gauge-invariant.

★★★ `refined_completability_engine` bundles both into one statement: the four facts
that constitute the engine.  Read together: a real's completability is the lex ordinal
`(height, rate)` of its **gcd-reduced** presentation, an intensional invariant of the
cut — not a yes/no fact, and not the bare cut, but the reduced presentation's ordinal
grade.

All zero-axiom.
-/

namespace E213.Lib.Math.Real213.RefinedCompletabilityEngine

open E213.Lib.Math.Real213.CrossDetOvertake (CrossDetSmall)
open E213.Lib.Math.Real213.RateModulus (rcut)
open E213.Lib.Math.Cauchy.DepthOmegaTower (expTower)
open E213.Lib.Math.Real213.CompletabilityGrade (completability_grade height_is_omega_coordinate)
open E213.Lib.Math.Real213.IntensionalCompletability (completability_is_intensional)

/-- ★★★ **The refined real completability engine.**  Four facts, one engine:

    **(I) ordinal grade** — lex `(height, rate)`: down a height always free, within a
    height free ⟺ `r < q`, up a height always broken;

    **(II) height is an `ω`-coordinate** — every step up the exponential tower
    `expTower q (·)` breaks `CrossDetSmall`, for every level `r`;

    **(III) the test is antitone** — `CrossDetSmall (c²·W) (c·d) → CrossDetSmall W d`:
    rescaling up only loses the bridge, so the gcd-reduced presentation is canonical;

    **(IV) the truth is gauge-invariant** — completion of `(c·a)/(c·d)` is that of `a/d`.

    So completability is the lex ordinal `(height, rate)` of the gcd-reduced presentation
    — an intensional invariant of the cut, neither a yes/no fact nor the bare cut. -/
theorem refined_completability_engine :
    ((∀ q b : Nat, 2 ≤ q → 2 ≤ b →
        CrossDetSmall (fun i => q ^ i) (fun i => q ^ (b ^ i)))
      ∧ (∀ q r : Nat, 2 ≤ q →
          (CrossDetSmall (fun i => r ^ i) (fun i => q ^ i) ↔ r < q))
      ∧ (∀ q b : Nat, 2 ≤ q → 2 ≤ b →
          ¬ CrossDetSmall (fun i => q ^ (b ^ i)) (fun i => q ^ i)))
    ∧ (∀ q : Nat, 2 ≤ q → ∀ r : Nat,
        ¬ CrossDetSmall (expTower q (r + 2)) (expTower q (r + 1)))
    ∧ (∀ c : Nat, 1 ≤ c → ∀ W d : Nat → Nat,
        CrossDetSmall (fun i => c * c * W i) (fun i => c * d i) → CrossDetSmall W d)
    ∧ (∀ c : Nat, 1 ≤ c → ∀ a d : Nat → Nat, ∀ m k : Nat,
        (∃ N, ∀ i j, i ≥ N → j ≥ N → rcut a d i m k = rcut a d j m k) →
        (∃ N, ∀ i j, i ≥ N → j ≥ N →
          rcut (fun i => c * a i) (fun i => c * d i) i m k
            = rcut (fun i => c * a i) (fun i => c * d i) j m k)) :=
  ⟨completability_grade,
   fun q hq => height_is_omega_coordinate q hq,
   completability_is_intensional.1,
   completability_is_intensional.2⟩

end E213.Lib.Math.Real213.RefinedCompletabilityEngine
