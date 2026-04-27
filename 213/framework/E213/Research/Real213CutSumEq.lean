import E213.Research.Real213CutSumDetermined
import E213.Research.Real213CutMulDetermined
import E213.Research.Real213CutPoset

/-!
# Research.Real213CutSumEq: cutSum / cutMul respect cutEq

cutSum 의 well-definedness modulo cutEq.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- cutSum respects cutEq in cx (left). -/
theorem cutSum_cutEq_left (cx cx' cy : Nat → Nat → Bool)
    (h : cutEq cx cx') (m k : Nat) :
    cutSum cx cy m k = cutSum cx' cy m k := by
  obtain ⟨N, hN⟩ := cutSum_locallyDetermined m k
  exact hN cx cx' cy cy (fun m' k' _ _ => h m' k') (fun _ _ _ _ => rfl)

/-- cutSum respects cutEq in cy (right). -/
theorem cutSum_cutEq_right (cx cy cy' : Nat → Nat → Bool)
    (h : cutEq cy cy') (m k : Nat) :
    cutSum cx cy m k = cutSum cx cy' m k := by
  obtain ⟨N, hN⟩ := cutSum_locallyDetermined m k
  exact hN cx cx cy cy' (fun _ _ _ _ => rfl) (fun m' k' _ _ => h m' k')

/-- cutMul respects cutEq in cx. -/
theorem cutMul_cutEq_left (cx cx' cy : Nat → Nat → Bool)
    (h : cutEq cx cx') (m k : Nat) :
    cutMul cx cy m k = cutMul cx' cy m k := by
  obtain ⟨N, hN⟩ := cutMul_locallyDetermined m k
  exact hN cx cx' cy cy (fun m' k' _ _ => h m' k') (fun _ _ _ _ => rfl)

/-- cutMul respects cutEq in cy. -/
theorem cutMul_cutEq_right (cx cy cy' : Nat → Nat → Bool)
    (h : cutEq cy cy') (m k : Nat) :
    cutMul cx cy m k = cutMul cx cy' m k := by
  obtain ⟨N, hN⟩ := cutMul_locallyDetermined m k
  exact hN cx cx cy cy' (fun _ _ _ _ => rfl) (fun m' k' _ _ => h m' k')

end E213.Research.Real213CutSum
