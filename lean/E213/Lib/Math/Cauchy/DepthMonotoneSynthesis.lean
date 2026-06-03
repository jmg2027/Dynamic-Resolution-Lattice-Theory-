import E213.Lib.Math.Cauchy.PolyDepthMonotone
import E213.Lib.Math.Cauchy.DepthCharacterization
import E213.Lib.Math.Cauchy.ThueMorseRingEscape

/-!
# Synthesis: the order-theoretic and algebraic readings of divergence depth meet

Two independent threads characterised **finite divergence depth** (`polyDepthZ`):

  * the *algebraic* reading — `DepthCharacterization.finite_depthZ_iff`: `polyDepthZ d s ↔ s` is a
    degree-`≤d` polynomial in the Newton basis (`s = newtonZ c d`); and the finite-depth class is a
    **ring** (`PolynomialDepth.polyDepthZ_{add,mul,mono}`);
  * the *order-theoretic* reading — `PolyDepthMonotone.polyDepthZ_evMono`: `polyDepthZ d s ⟹ s` is
    **eventually monotone**.

Joining them gives two facts neither thread states alone:

  1. **Every Newton polynomial is eventually monotone** (`newtonZ_evMono`) — the algebraic objects
     of the depth ring carry the order structure of the monotone bridge.
  2. **The popcount counter is not any polynomial** (`s2Z_not_polynomial`) — the dense
     non-holonomic witness's counter, shown ring-escaping via monotonicity
     (`ThueMorseRingEscape.s2Z_not_polyDepthZ`), is now seen *through the characterization* to
     differ from **every** `newtonZ c d`.  The "automatic counter escapes the generating ring"
     slogan becomes literal: it is no polynomial.
-/

namespace E213.Lib.Math.Cauchy.DepthMonotoneSynthesis

open E213.Lib.Math.Cauchy.NewtonGregory (newtonZ)
open E213.Lib.Math.Cauchy.DepthCharacterization (finite_depthZ_iff polyDepthZ_newtonZ)
open E213.Lib.Math.Cauchy.PolyDepthMonotone (MonoFromZ AntiFromZ polyDepthZ_evMono)
open E213.Lib.Math.Cauchy.ThueMorseRingEscape (s2Z s2Z_not_polyDepthZ)

/-- ★★★ **Every Newton (degree-`≤d`) polynomial is eventually monotone.**  The depth ring's
    algebraic objects inherit the order structure of the finite-depth ⟹ eventually-monotone bridge:
    `newtonZ c d` is eventually non-decreasing or eventually non-increasing. -/
theorem newtonZ_evMono (c : Nat → Int) (d : Nat) :
    (∃ N, MonoFromZ N (fun n => newtonZ c d n)) ∨ (∃ N, AntiFromZ N (fun n => newtonZ c d n)) :=
  polyDepthZ_evMono d (fun n => newtonZ c d n) (polyDepthZ_newtonZ c d)

/-- ★★★ **The popcount counter is no polynomial.**  Through `finite_depthZ_iff`, the ring-escape
    `s2Z_not_polyDepthZ` says exactly: `s2Z` (the binary digit-sum) is equal to no Newton
    polynomial `newtonZ c d` for any degree `d`.  The automatic sequence's counter sits literally
    outside the polynomial generating ring. -/
theorem s2Z_not_polynomial : ¬ ∃ (d : Nat) (c : Nat → Int), ∀ n, s2Z n = newtonZ c d n := by
  rintro ⟨d, c, hc⟩
  exact s2Z_not_polyDepthZ ⟨d, finite_depthZ_iff.mpr ⟨c, hc⟩⟩

end E213.Lib.Math.Cauchy.DepthMonotoneSynthesis
