import E213.Math.Real213.CutMidMono
import E213.Math.Real213.ValidCutOps
import E213.Math.Real213.CutBisectionAlgo

/-!
# Research.Real213IVTContainment: bracket containment at fixed (m, k)

For RatioCut endpoints with cutLe a b, the bisection bracket
[a_n, b_n] (after n steps at query (m, k)) is contained in [a, b].

We use a pointwise (at fixed (m, k)) form of cutLe to avoid the
k = 0 edge case in the global cutLe.
-/

namespace E213.Math.Real213.IVTContainment

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutBisection (cutMid)
open E213.Math.Real213.CutPoset (cutLe)
open E213.Math.Real213.ValidCut (RatioCut)

/-- Pointwise cutLe at (m, k): cy m k → cx m k. -/
def cutLeAt (cx cy : Nat → Nat → Bool) (m k : Nat) : Prop :=
  cy m k = true → cx m k = true

/-- One-step bisection bracket containment, at fixed (m, k) with k ≥ 1.

    bisectStep a b oracle m k = (a', b') gives:
    - cutLeAt a a' m k (left endpoint moved up: a ≤ a').
    - cutLeAt b' b m k (right endpoint moved down: b' ≤ b).
    -/
theorem bisectStep_contains (a b : Nat → Nat → Bool)
    (hra : RatioCut a) (hrb : RatioCut b) (hle : cutLe a b)
    (oracle : Nat → Nat → Bool → Bool) (m k : Nat) (hk : k ≥ 1) :
    cutLeAt a (bisectStep a b oracle m k).1 m k
    ∧ cutLeAt (bisectStep a b oracle m k).2 b m k := by
  show cutLeAt a (if oracle m k (cutMid a b m k) = true
                  then (a, cutMid a b) else (cutMid a b, b)).1 m k
       ∧ cutLeAt (if oracle m k (cutMid a b m k) = true
                  then (a, cutMid a b) else (cutMid a b, b)).2 b m k
  by_cases h : oracle m k (cutMid a b m k) = true
  · rw [if_pos h]
    refine ⟨fun ha => ha,
            fun hb => cutLe_cutMid_b_at a b hrb hle m k hk hb⟩
  · rw [if_neg h]
    refine ⟨fun ha => cutLe_a_cutMid_at a b hra hle m k hk ha,
            fun hb => hb⟩

/-- cutLeAt is reflexive at any (m, k). -/
theorem cutLeAt_refl (c : Nat → Nat → Bool) (m k : Nat) :
    cutLeAt c c m k := fun h => h

/-- cutLeAt is transitive at fixed (m, k). -/
theorem cutLeAt_trans (cx cy cz : Nat → Nat → Bool) (m k : Nat)
    (hxy : cutLeAt cx cy m k) (hyz : cutLeAt cy cz m k) :
    cutLeAt cx cz m k := fun h => hxy (hyz h)

end E213.Math.Real213.IVTContainment
