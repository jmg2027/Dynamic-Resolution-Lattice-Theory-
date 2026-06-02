import E213.Lib.Math.Real213.CrossDetOvertake
import E213.Lib.Math.Real213.PresentationDependence
import E213.Meta.Tactic.NatHelper

/-!
# IntensionalCompletability — the completion is gauge-invariant, the bridge is not

`PresentationDependence` showed the cross-determinant bridge `CrossDetSmall` reads the
**representation**: the cut `rcut` is invariant under rescaling `(a,d) ↦ (c·a, c·d)`,
while the cross-determinant scales `c²` against a denominator scaling `c`.  This file
pins the *intensional reduction* — separate the presentation-relative **test** from the
presentation-invariant **truth** — the second axis of the refined real engine (after the
ordinal height of `CompletabilityGrade`).

  * ★★★ `crossdet_rescale_antitone` — rescaling **up** only **loses** the bridge:
    `CrossDetSmall (c²·W) (c·d) → CrossDetSmall W d` for `c ≥ 1`.  Among all rescalings of
    one real, the **gcd-reduced** (smallest) presentation is the easiest to satisfy
    `CrossDetSmall` — the canonical place to apply the bridge.  The test is monotone *down*
    the rescaling order.
  * ★★★ `modulus_rescale_invariant` — the **completion itself** is gauge-invariant: a total
    modulus for `a/d` at `(m,k)` is *the same* one for the rescaled `(c·a)/(c·d)` (via
    `rcut_rescale`).  Whether a real completes is a fact about the cut, not the
    presentation.
  * `completability_is_intensional` bundles the two: the sufficient **test**
    (`CrossDetSmall`) is presentation-relative (antitone under rescaling), while the
    **truth** it certifies — the cut's completion — is presentation-invariant.

So the intensional content is the **gauge class** of a presentation under rescaling; the
cut is its invariant collapse, and the canonical grade (`CompletabilityGrade`) is read on
the reduced representative.  The refined engine reads the *intensional* invariant — the
reduced presentation's ordinal grade — not the bare cut.

All zero-axiom.
-/

namespace E213.Lib.Math.Real213.IntensionalCompletability

open E213.Lib.Math.Real213.CrossDetOvertake (CrossDetSmall)
open E213.Lib.Math.Real213.RateModulus (rcut)
open E213.Lib.Math.Real213.PresentationDependence (rcut_rescale)
open E213.Tactic.NatHelper (mul_left_comm)

/-! ## §1 — the bridge is antitone down the rescaling order (reduced is canonical) -/

/-- ★★★ **Rescaling up only loses the bridge.**  `CrossDetSmall (c²·W) (c·d) →
    CrossDetSmall W d` for `c ≥ 1`: the cross-determinant scales `c²` while the
    denominator scales `c`, so dividing by `c` and dropping the surplus `c` on the
    `W`-term recovers the un-rescaled smallness.  Hence the gcd-reduced presentation is
    the canonical (easiest) place to test `CrossDetSmall`. -/
theorem crossdet_rescale_antitone (c : Nat) (hc : 1 ≤ c) {W d : Nat → Nat}
    (h : CrossDetSmall (fun i => c * c * W i) (fun i => c * d i)) :
    CrossDetSmall W d := by
  intro i hi
  have hyp := h i hi
  have hccc : c ≤ c * c := Nat.le_mul_of_pos_right c hc
  have key : c * (i * (i + 1) * W i + i * d i) ≤ c * ((i + 1) * d (i + 1)) := by
    rw [Nat.mul_add]
    calc c * (i * (i + 1) * W i) + c * (i * d i)
        ≤ i * (i + 1) * (c * c * W i) + i * (c * d i) := by
          refine Nat.add_le_add ?_ ?_
          · calc c * (i * (i + 1) * W i)
                = i * (i + 1) * (c * W i) := (mul_left_comm (i*(i+1)) c (W i)).symm
              _ ≤ i * (i + 1) * (c * c * W i) :=
                  Nat.mul_le_mul_left _ (Nat.mul_le_mul_right (W i) hccc)
          · exact Nat.le_of_eq (mul_left_comm i c (d i)).symm
      _ ≤ (i + 1) * (c * d (i + 1)) := hyp
      _ = c * ((i + 1) * d (i + 1)) := mul_left_comm (i+1) c (d (i+1))
  exact Nat.le_of_mul_le_mul_left key hc

/-! ## §2 — the completion is gauge-invariant (the truth) -/

/-- ★★★ **The completion is gauge-invariant.**  If `a/d` completes at `(m,k)` (a total
    modulus `N`), then the rescaled `(c·a)/(c·d)` completes at the *same* `(m,k)` with the
    *same* `N` — immediately, because `rcut` cancels the common factor (`rcut_rescale`).
    Completion is a fact about the cut, not the presentation. -/
theorem modulus_rescale_invariant (c : Nat) (hc : 1 ≤ c) (a d : Nat → Nat) (m k : Nat)
    (hcomplete : ∃ N, ∀ i j, i ≥ N → j ≥ N → rcut a d i m k = rcut a d j m k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N →
      rcut (fun i => c * a i) (fun i => c * d i) i m k
        = rcut (fun i => c * a i) (fun i => c * d i) j m k := by
  obtain ⟨N, hN⟩ := hcomplete
  refine ⟨N, fun i j hi hj => ?_⟩
  rw [rcut_rescale c hc a d i m k, rcut_rescale c hc a d j m k]
  exact hN i j hi hj

/-! ## §3 — completability is intensional -/

/-- ★★★ **Completability is intensional.**  The sufficient *test* `CrossDetSmall` is
    presentation-relative — antitone under rescaling, so the gcd-reduced presentation is
    canonical (`crossdet_rescale_antitone`) — while the *truth* it certifies, the cut's
    completion, is presentation-invariant (`modulus_rescale_invariant`).  The intensional
    invariant is the gauge class; the cut is its collapse; the canonical ordinal grade is
    read on the reduced representative. -/
theorem completability_is_intensional :
    (∀ c : Nat, 1 ≤ c → ∀ W d : Nat → Nat,
        CrossDetSmall (fun i => c * c * W i) (fun i => c * d i) → CrossDetSmall W d)
    ∧ (∀ c : Nat, 1 ≤ c → ∀ a d : Nat → Nat, ∀ m k : Nat,
        (∃ N, ∀ i j, i ≥ N → j ≥ N → rcut a d i m k = rcut a d j m k) →
        (∃ N, ∀ i j, i ≥ N → j ≥ N →
          rcut (fun i => c * a i) (fun i => c * d i) i m k
            = rcut (fun i => c * a i) (fun i => c * d i) j m k)) :=
  ⟨fun c hc W d => crossdet_rescale_antitone c hc,
   fun c hc a d m k => modulus_rescale_invariant c hc a d m k⟩

end E213.Lib.Math.Real213.IntensionalCompletability
