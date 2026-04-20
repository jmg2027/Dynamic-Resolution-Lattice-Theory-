import E213.Firmware.Raw
import E213.Hypervisor.Lens
import E213.Meta.LensCatalog
import E213.Research.ZI
import E213.Research.ZIDomain
import E213.Research.ZIHom

/-!
# Research: the `ZI`-Lens as a candidate counterexample

Constructs `ziLens : Lens ZI` with `base_a = I`, `base_b = -I`,
`combine = ZI.mul`, and verifies R3 (NonVanishing) and R4
(SwapMatching) in Lean.

- R1, R2: built into the `Lens` structure + `Raw.fold`.
- R3: via `ZI.mul_ne_zero_of_ne_zero` (integral-domain, from
  the Diophantus identity `normSq(u·v) = normSq(u)·normSq(v)`
  proved in `ZIDomain.lean`).
- R4: via `Raw.fold_swap_hom` with the ring-hom lemmas for
  `ZI.conj` (see `ZIHom.lean`).

Hypothesis H is therefore **Lean-confirmed** for E1: `ℤ[i]`
is a self-recognising codomain under R1–R4 alone.
-/

namespace E213.Research

open E213.Firmware E213.Hypervisor E213.Meta

/-- The candidate Lens: codomain `ZI`, base values `i`, `-i`,
    combine = Gaussian multiplication. -/
def ziLens : Lens ZI where
  base_a  := ZI.I
  base_b  := ZI.negI
  combine := ZI.mul

-- Smoke test: base-value computations.
example : ziLens.view Raw.a = ZI.I    := rfl
example : ziLens.view Raw.b = ZI.negI := rfl

-- ═══ R3 — NonVanishing (ZI integral domain) ═══

/-- **R3 for `ziLens`.**  Gaussian multiplication has no zero
    divisors, so combining two nonzero views is nonzero. -/
theorem ziLens_nonVanishing : NonVanishing ziLens := by
  intro u v hu hv
  exact ZI.mul_ne_zero_of_ne_zero hu hv

-- ═══ R4 — SwapMatching with `ZI.conj` ═══

/-- **R4 for `ziLens`.**  `Raw.swap` matches `ZI.conj` under the
    ziLens view, and `ZI.conj` is a nontrivial involution. -/
theorem ziLens_swapMatching : SwapMatching ziLens ZI.conj := by
  refine ⟨?_, ?_, ?_⟩
  · -- involution
    intro u
    exact ZI.conj_conj u
  · -- nontrivial
    exact ZI.conj_ne_id
  · -- matches swap
    intro r
    show Raw.fold ZI.I ZI.negI ZI.mul (Raw.swap r)
       = ZI.conj (Raw.fold ZI.I ZI.negI ZI.mul r)
    exact Raw.fold_swap_hom ZI.I ZI.negI ZI.mul ZI.conj
      ZI.conj_I ZI.conj_negI ZI.conj_mul ZI.mul_comm r

end E213.Research
