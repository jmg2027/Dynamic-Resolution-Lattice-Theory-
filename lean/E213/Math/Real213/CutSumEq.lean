import E213.Math.Real213.CutSumDetermined
import E213.Math.Real213.CutMulDetermined
import E213.Math.Real213.CutPoset
import E213.Math.Real213.CutSumComm
import E213.Math.Real213.CutMulComm

/-!
# Research.Real213CutSumEq: cutSum / cutMul respect cutEq

Well-definedness of cutSum modulo cutEq.
-/

namespace E213.Math.Real213.CutSumEq

open E213.Math.Real213.CutSum (cutSum)
open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutPoset (cutEq)

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

end E213.Math.Real213.CutSumEq

namespace E213.Math.Real213.CutSumEq

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutMul (cutMul)
open E213.Math.Real213.CutMulComm (cutMul_comm)
open E213.Math.Real213.CutPoset (cutEq cutLe)
open E213.Math.Real213.CutSum (cutSum)
open E213.Math.Real213.CutSumComm (cutSum_comm)

/-- cutEq commutativity of cutSum. -/
theorem cutSum_comm_cutEq (cx cy : Nat → Nat → Bool) :
    cutEq (cutSum cx cy) (cutSum cy cx) := fun m k => cutSum_comm cx cy m k

/-- cutEq commutativity of cutMul. -/
theorem cutMul_comm_cutEq (cx cy : Nat → Nat → Bool) :
    cutEq (cutMul cx cy) (cutMul cy cx) := fun m k => cutMul_comm cx cy m k

/-- cutEq composability of cutSum: cutEq cx cx', cutEq cy cy' →
    cutEq (cutSum cx cy) (cutSum cx' cy'). -/
theorem cutSum_cutEq_both (cx cx' cy cy' : Nat → Nat → Bool)
    (hx : cutEq cx cx') (hy : cutEq cy cy') :
    cutEq (cutSum cx cy) (cutSum cx' cy') := fun m k => by
  rw [cutSum_cutEq_left cx cx' cy hx m k]
  exact cutSum_cutEq_right cx' cy cy' hy m k

/-- cutEq composability of cutMul. -/
theorem cutMul_cutEq_both (cx cx' cy cy' : Nat → Nat → Bool)
    (hx : cutEq cx cx') (hy : cutEq cy cy') :
    cutEq (cutMul cx cy) (cutMul cx' cy') := fun m k => by
  rw [cutMul_cutEq_left cx cx' cy hx m k]
  exact cutMul_cutEq_right cx' cy cy' hy m k

/-- cutLe is preserved under cutSum (both args). -/
theorem cutSum_cutLe_both (cx1 cx2 cy1 cy2 : Nat → Nat → Bool)
    (hx : cutLe cx1 cx2) (hy : cutLe cy1 cy2) :
    cutLe (cutSum cx1 cy1) (cutSum cx2 cy2) := by
  intro m k h_sum2
  have step1 : cutSum cx1 cy2 m k = true :=
    cutSum_mono_left cx2 cx1 cy2 hx m k h_sum2
  exact cutSum_mono_right cx1 cy2 cy1 hy m k step1

/-- cutLe is preserved under cutMul (both args). -/
theorem cutMul_cutLe_both (cx1 cx2 cy1 cy2 : Nat → Nat → Bool)
    (hx : cutLe cx1 cx2) (hy : cutLe cy1 cy2) :
    cutLe (cutMul cx1 cy1) (cutMul cx2 cy2) := by
  intro m k h_mul2
  have step1 : cutMul cx1 cy2 m k = true :=
    cutMul_mono_left cx2 cx1 cy2 hx m k h_mul2
  exact cutMul_mono_right cx1 cy2 cy1 hy m k step1

/-- cutSum cutLe-preservation in one argument. -/
theorem cutSum_cutLe_left (cx1 cx2 cy : Nat → Nat → Bool)
    (hx : cutLe cx1 cx2) :
    cutLe (cutSum cx1 cy) (cutSum cx2 cy) :=
  cutSum_cutLe_both cx1 cx2 cy cy hx (cutLe_refl cy)

theorem cutSum_cutLe_right (cx cy1 cy2 : Nat → Nat → Bool)
    (hy : cutLe cy1 cy2) :
    cutLe (cutSum cx cy1) (cutSum cx cy2) :=
  cutSum_cutLe_both cx cx cy1 cy2 (cutLe_refl cx) hy

/-- cutMul cutLe-preservation in one argument. -/
theorem cutMul_cutLe_left (cx1 cx2 cy : Nat → Nat → Bool)
    (hx : cutLe cx1 cx2) :
    cutLe (cutMul cx1 cy) (cutMul cx2 cy) :=
  cutMul_cutLe_both cx1 cx2 cy cy hx (cutLe_refl cy)

theorem cutMul_cutLe_right (cx cy1 cy2 : Nat → Nat → Bool)
    (hy : cutLe cy1 cy2) :
    cutLe (cutMul cx cy1) (cutMul cx cy2) :=
  cutMul_cutLe_both cx cx cy1 cy2 (cutLe_refl cx) hy

end E213.Math.Real213.CutSumEq
