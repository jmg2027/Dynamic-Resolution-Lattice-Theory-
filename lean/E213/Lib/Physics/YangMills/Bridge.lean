import E213.Lib.Physics.YangMills.Gap
import E213.Lib.Physics.Couplings.PhotonKernel

/-!
# Yang-Mills ↔ Diamond bridge — α₃-channel atomic facts

The confined coupling reads `1/α_3 = NS²−1 = 8 = b_1(K_{3,2}^{(2)})`,
the harmonic gluon octet (adjoint of SU(NS)).

This file records the α₃-channel atomic integers (`b_1 = 8 = NS²−1`,
`d²−1 = 24`).  The mass gap itself — the smallest nonzero gauge-lattice
Laplacian eigenvalue `c·min(NS,NT) = 4 > 0` — lives in `YangMills/Gap.lean`
(`massGap_pos`); `b_1 = 8` is the octet the gap sits above, not the gap.
-/

namespace E213.Lib.Physics.YangMills.Bridge

/-- `1/α_3 = b_1 = NS²−1 = 8` (confined-coupling cycle space). -/
theorem alpha3_b1_atomic :
    E213.Lib.Physics.Couplings.PhotonKernel.b_1 = 8
    ∧ (8 : Nat) = 3 * 3 - 1 :=
  ⟨E213.Lib.Physics.Couplings.PhotonKernel.b_1_eq_8, by decide⟩

/-- adjoint SU(NS) = NS²−1 = 8. -/
theorem adjoint_SU_NS_atomic : 3 * 3 - 1 = 8 := by decide

/-- adjoint SU(d) = d²−1 = 24 (= α_2 prefactor). -/
theorem adjoint_SU_d_atomic : 5 * 5 - 1 = 24 := by decide

/-- α₃-channel atomic bundle: `b_1 = 8 = NS²−1` over `(NS,NT,d) = (3,2,5)`. -/
theorem alpha3_channel_bundle :
    E213.Lib.Physics.Couplings.PhotonKernel.b_1 = 8
    ∧ 3 * 3 - 1 = 8
    ∧ E213.Lib.Physics.Simplex.Counts.NS = 3
    ∧ E213.Lib.Physics.Simplex.Counts.NT = 2
    ∧ E213.Lib.Physics.Simplex.Counts.d = 5 := by
  refine ⟨E213.Lib.Physics.Couplings.PhotonKernel.b_1_eq_8, ?_, ?_, ?_, ?_⟩
  all_goals decide

/-- α₃ + α₂ prefactor bundle: `b_1 = 8 = NS²−1`, `d²−1 = 24`. -/
theorem alpha3_alpha2_bundle :
    E213.Lib.Physics.Couplings.PhotonKernel.b_1 = 8
    ∧ 3 * 3 - 1 = 8
    ∧ 5 * 5 - 1 = 24
    ∧ E213.Lib.Physics.Simplex.Counts.NS = 3
    ∧ E213.Lib.Physics.Simplex.Counts.d = 5 := by
  refine ⟨E213.Lib.Physics.Couplings.PhotonKernel.b_1_eq_8, ?_, ?_, ?_, ?_⟩
  all_goals decide

end E213.Lib.Physics.YangMills.Bridge
