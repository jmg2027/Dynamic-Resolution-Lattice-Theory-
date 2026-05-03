import E213.Math.Max213
import E213.Math.Real213.CutSum
import E213.Math.Real213.CutContinuity

/-!
# Research.Real213CutSumDetermined: cutSum locality framework

Depends only on *bounded values* of `cutSum` — 213 counterpart of
Bishop locatedness.

## Results

- `isLocallyDetermined2` : 2-arg locally-determined property.
- `cutSum_aux_congr_zero` : zero-case congruence (one step toward
  locally-determined cutSum).

## Note

Full `cutSum_locallyDetermined` proof is blocked by a Lean Bool/Prop ||
elaboration corner case (decide auto-coercion) — cleaner approach in
a separate session.
-/

namespace E213.Math.Real213.CutSumDetermined

open E213.Math.Real213.CutSum (cutSum)
open E213.Math.Real213.CutSum (cutSumAux)
open E213.Firmware E213.Hypervisor

/-- 2-arg locally-determined property. -/
def isLocallyDetermined2
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool) → (Nat → Nat → Bool)) : Prop :=
  ∀ m k, ∃ N : Nat,
    ∀ cx1 cx2 cy1 cy2 : Nat → Nat → Bool,
      (∀ m' k', m' ≤ N → k' ≤ N → cx1 m' k' = cx2 m' k') →
      (∀ m' k', m' ≤ N → k' ≤ N → cy1 m' k' = cy2 m' k') →
      f cx1 cy1 m k = f cx2 cy2 m k

/-- congruence of cutSumAux — agreeing cuts at the same precision. -/
theorem cutSumAux_congr (k m1Max : Nat)
    (cx1 cx2 cy1 cy2 : Nat → Nat → Bool)
    (hx : ∀ m', m' ≤ m1Max → cx1 m' (2*k) = cx2 m' (2*k))
    (hy : ∀ m', m' ≤ m1Max → cy1 m' (2*k) = cy2 m' (2*k))
    (n : Nat) (hn : n ≤ m1Max) :
    cutSumAux cx1 cy1 k m1Max n = cutSumAux cx2 cy2 k m1Max n := by
  induction n with
  | zero =>
    show (cx1 0 (2*k) && cy1 m1Max (2*k)) = (cx2 0 (2*k) && cy2 m1Max (2*k))
    rw [hx 0 (Nat.zero_le _), hy m1Max (Nat.le_refl _)]
  | succ i ih =>
    have hi : i ≤ m1Max := Nat.le_of_succ_le hn
    show ((cx1 (i+1) (2*k) && cy1 (m1Max - (i+1)) (2*k))
            || cutSumAux cx1 cy1 k m1Max i)
       = ((cx2 (i+1) (2*k) && cy2 (m1Max - (i+1)) (2*k))
            || cutSumAux cx2 cy2 k m1Max i)
    rw [hx (i+1) hn, hy (m1Max - (i+1)) (Nat.sub_le _ _), ih hi]

/-- **cutSum is locally determined**: N = max(2m, 2k). -/
theorem cutSum_locallyDetermined : isLocallyDetermined2 cutSum := by
  intro m k
  refine ⟨max (2*m) (2*k), ?_⟩
  intro cx1 cx2 cy1 cy2 hx hy
  show cutSumAux cx1 cy1 k (2*m) (2*m) = cutSumAux cx2 cy2 k (2*m) (2*m)
  apply cutSumAux_congr
  · intro m' hm'
    exact hx m' (2*k) (Nat.le_trans hm' (E213.Math.Max213.le_max_left _ _))
                       (E213.Math.Max213.le_max_right _ _)
  · intro m' hm'
    exact hy m' (2*k) (Nat.le_trans hm' (E213.Math.Max213.le_max_left _ _))
                       (E213.Math.Max213.le_max_right _ _)
  · exact Nat.le_refl _

end E213.Math.Real213.CutSumDetermined
