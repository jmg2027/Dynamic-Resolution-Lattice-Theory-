import E213.Research.Real213Order

/-!
# Research.Real213Sign: zero + constructive positivity for Real213 (A5)

Phase A5 milestone of `E1_real213_analysis_roadmap.md`.

## Definitions

- `zero : Real213 := const Raw.b` — abLens.view of Raw.b = (0, 1) =
  ratio 0/1 = 0.
- `positive r := lt zero r` — Bishop-style formalization of 0 < r.
- Spelled out: ∃ m k, k ≥ 1 ∧ ∃ N, ∀ i ≥ N, orderProj m k of
  view (r.xs i) = false (= r is greater than m/k).  m = 0 allowed
  (orderProj 0 k = false iff a-count ≥ 1).

## Significance

- Constructive positivity without LEM.
- *Explicit margin* m/k is attached as evidence for "r > 0".
- A different object from ZFC's r > 0 (set-theoretic) — requires
  algorithmic separation.
-/

namespace E213.Research.Real213

open E213.Firmware E213.Hypervisor
open E213.Research.HasModulusNS
open E213.Research.ABLens
open E213.Research.ArchimedeanCauchy

/-- **Real213 zero**: const Raw.b (abLens.view = (0, 1), ratio 0). -/
def zero : Real213 := const Raw.b

/-- **Real213 positivity**: Bishop-style 0 < r. -/
def positive (r : Real213) : Prop := lt zero r

/-- **Positivity of const Raw.a**: Raw.a (view = (1, 0)) is greater than zero.
    Witness: m = k = 1.  orderProj 1 1 (0, 1) = true, orderProj 1 1 (1, 0) = false. -/
theorem const_a_positive : positive (const Raw.a) := by
  refine ⟨1, 1, Nat.le_refl 1, 0, fun i _ => ?_⟩
  refine ⟨?_, ?_⟩
  · show orderProj 1 1 (abLens.view Raw.b) = true
    rfl
  · show orderProj 1 1 (abLens.view Raw.a) = false
    rfl

end E213.Research.Real213
