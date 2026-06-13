import E213.Lib.Math.NumberSystems.Real213.PresentationDependence

/-!
# IntensionalCompletability — the completion is presentation-invariant, the bridge is not

`PresentationDependence` showed the cross-determinant bridge `CrossDetSmall` reads the
**representation**: the cut `rcut` is invariant under rescaling `(a,d) ↦ (c·a, c·d)`,
but `CrossDetSmall` is not (the cross-determinant scales `c²` against a denominator
scaling `c`).  This file pins the *intensional reduction* that follows: separate the
presentation-relative *test* from the presentation-invariant *truth*.

  * ★★★ `crossDetSmall_rescale_antitone` — rescaling **up** only **loses** the bridge:
    `CrossDetSmall (c²·W) (c·d) → CrossDetSmall W d` for `c ≥ 1`.  So among all rescalings
    of one real, the *smallest* (gcd-reduced) presentation is the easiest to satisfy
    `CrossDetSmall` — the canonical place to apply the bridge.  The smallness condition is
    monotone *down* the rescaling order.
  * ★★★ `modulus_rescale_invariant` — the **completion itself** is presentation-invariant:
    if `a/d` has a total modulus at `(m,k)`, the rescaled `(c·a)/(c·d)` has the *same* one
    (immediately, via `rcut_rescale`).  Whether a real completes is a fact about the cut,
    not the presentation.
  * `completability_is_intensional` bundles the two: the sufficient *test* `CrossDetSmall`
    is presentation-relative (antitone under rescaling), while the *truth* it certifies —
    the cut's completion — is presentation-invariant.

The intensional content (what `PresentationDependence` calls the rescaling-invariant
real) is the completion; `CrossDetSmall` is an extensional readout of a chosen
presentation.  Reducing the presentation can only help the test, never the truth — the
two come apart exactly along the rescaling action, and the cut is the invariant.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Completability.IntensionalCompletability

open E213.Lib.Math.NumberSystems.Real213.CrossDet.CrossDetOvertake (CrossDetSmall)
open E213.Lib.Math.NumberSystems.Real213.Modulus.RateModulus (rcut)
open E213.Lib.Math.NumberSystems.Real213.PresentationDependence (rcut_rescale)
open E213.Tactic.NatHelper (mul_left_comm mul_assoc)

/-! ## §1 — the bridge is monotone down the rescaling order -/

/-- ★★★ **Rescaling only loses `CrossDetSmall`.**  If the `c`-rescaled presentation
    (cross-determinant `c²·W` against denominator `c·d`) satisfies the smallness
    condition, so does the base `(W, d)` — for any `c ≥ 1`.  Each term carries `c` as a
    common left factor; cancelling it leaves the base condition with an extra `c` on the
    `W`-term, which `c ≥ 1` only strengthens.  So the gcd-reduced presentation is the
    canonical one for the bridge: rescaling up cannot rescue a real the reduced form
    fails, and cannot break one it passes-after-cancellation. -/
theorem crossDetSmall_rescale_antitone (W d : Nat → Nat) (c : Nat) (hc : 1 ≤ c)
    (hcs : CrossDetSmall (fun i => c * c * W i) (fun i => c * d i)) :
    CrossDetSmall W d := by
  intro i hi
  have hced := hcs i hi
  -- hced : i*(i+1)*(c*c*W i) + i*(c*d i) ≤ (i+1)*(c*d (i+1))
  have hL1 : i*(i+1)*(c*c*W i) = c*(i*(i+1)*(c*W i)) := by
    rw [mul_assoc c c (W i), mul_left_comm (i*(i+1)) c (c*W i)]
  have hL2 : i*(c*d i) = c*(i*d i) := mul_left_comm i c (d i)
  have hR : (i+1)*(c*d (i+1)) = c*((i+1)*d (i+1)) := mul_left_comm (i+1) c (d (i+1))
  rw [hL1, hL2, hR, ← Nat.mul_add] at hced
  have hcancel : i*(i+1)*(c*W i) + i*d i ≤ (i+1)*d (i+1) :=
    Nat.le_of_mul_le_mul_left hced hc
  have hWle : i*(i+1)*W i ≤ i*(i+1)*(c*W i) :=
    Nat.mul_le_mul_left (i*(i+1)) (Nat.le_mul_of_pos_left (W i) hc)
  exact Nat.le_trans (Nat.add_le_add_right hWle (i*d i)) hcancel

/-! ## §2 — the completion is presentation-invariant -/

/-- ★★★ **Completion is rescaling-invariant.**  If `a/d` has a total modulus at `(m,k)`
    (the cut is eventually constant past some `N`), then the rescaled `(c·a)/(c·d)` has
    the *same* modulus `N` — the cut is unchanged (`rcut_rescale`), so its completion is.
    Whether a real completes is a property of the cut, not of the presentation that
    happens to carry it. -/
theorem modulus_rescale_invariant (c : Nat) (hc : 1 ≤ c) (a d : Nat → Nat) (m k : Nat)
    (h : ∃ N, ∀ i j, i ≥ N → j ≥ N → rcut a d i m k = rcut a d j m k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N →
      rcut (fun i => c * a i) (fun i => c * d i) i m k
        = rcut (fun i => c * a i) (fun i => c * d i) j m k := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun i j hi hj => ?_⟩
  rw [rcut_rescale c hc a d i m k, rcut_rescale c hc a d j m k]
  exact hN i j hi hj

/-! ## §3 — the intensional reduction, bundled -/

/-- ★★★ **Completability is intensional.**  The two halves of the presentation/real
    split:

    1. the sufficient *test* `CrossDetSmall` is presentation-relative — rescaling up the
       presentation only loses it (`crossDetSmall_rescale_antitone`), so the reduced
       presentation is its canonical home;
    2. the *truth* it certifies — the cut's completion — is presentation-invariant
       (`modulus_rescale_invariant`).

    So "does this real complete?" is a fact about the cut (intensional, rescaling-stable);
    `CrossDetSmall` is an extensional readout of a chosen presentation, best read at the
    gcd-reduced one.  The two come apart exactly along the rescaling action. -/
theorem completability_is_intensional :
    (∀ (W d : Nat → Nat) (c : Nat), 1 ≤ c →
        CrossDetSmall (fun i => c * c * W i) (fun i => c * d i) → CrossDetSmall W d)
    ∧ (∀ (a d : Nat → Nat) (c : Nat), 1 ≤ c → ∀ m k,
        (∃ N, ∀ i j, i ≥ N → j ≥ N → rcut a d i m k = rcut a d j m k) →
        ∃ N, ∀ i j, i ≥ N → j ≥ N →
          rcut (fun i => c * a i) (fun i => c * d i) i m k
            = rcut (fun i => c * a i) (fun i => c * d i) j m k) :=
  ⟨fun W d c hc => crossDetSmall_rescale_antitone W d c hc,
   fun a d c hc m k => modulus_rescale_invariant c hc a d m k⟩

end E213.Lib.Math.NumberSystems.Real213.Completability.IntensionalCompletability
