import E213.Research.Real213Const

/-!
# Research.Real213Order: Real213 의 order (le, lt) — A4

`E1_real213_analysis_roadmap.md` 의 Phase A milestone A4.
Bishop-style constructive le: 모든 rational m/k 에 대 해 eventually
"r' ≤ m/k → r ≤ m/k".

## 정의

- `le r r' := ∀ m k, ∃ N, ∀ i ≥ N, orderProj 의 r'-implies-r`
- `lt r r' := ∃ m k, ∃ N, ∀ i ≥ N, r ≤ m/k 이지 만 r' > m/k`

orderProj m k (a, b) = decide (a*k ≤ b*m) — cross-mult form.

## 의의

- LEM 부재 의 constructive le.
- ZFC 의 r ≤ r' (set-theoretic) 와 *다 른 object* — explicit
  modulus 형 evidence 요구.
-/

namespace E213.Research.Real213

open E213.Firmware E213.Hypervisor
open E213.Research.HasModulusNS
open E213.Research.ABLens
open E213.Research.ArchimedeanCauchy

/-- **Real213 의 le**: 모든 rational m/k cut 에 대 해, eventually
    r' ≤ m/k 이면 r ≤ m/k.  Bishop-style constructive le. -/
def le (r r' : Real213) : Prop :=
  ∀ m k, k ≥ 1 → ∃ N, ∀ i, i ≥ N →
    orderProj m k (abLens.view (r'.xs i)) = true →
    orderProj m k (abLens.view (r.xs i)) = true

/-- **Real213 의 lt**: 어떤 m/k 가 r 와 r' 를 separate (r ≤ m/k < r'). -/
def lt (r r' : Real213) : Prop :=
  ∃ m k, k ≥ 1 ∧ ∃ N, ∀ i, i ≥ N →
    orderProj m k (abLens.view (r.xs i)) = true ∧
    orderProj m k (abLens.view (r'.xs i)) = false

end E213.Research.Real213

namespace E213.Research.Real213

open E213.Firmware E213.Hypervisor
open E213.Research.HasModulusNS
open E213.Research.ABLens
open E213.Research.ArchimedeanCauchy

/-- le 의 reflexivity. -/
theorem le_refl (r : Real213) : le r r := by
  intro _ _ _
  exact ⟨0, fun _ _ h => h⟩

/-- le 의 transitivity. -/
theorem le_trans (r r' r'' : Real213) :
    le r r' → le r' r'' → le r r'' := by
  intro h1 h2 m k hk
  obtain ⟨N1, h1N⟩ := h1 m k hk
  obtain ⟨N2, h2N⟩ := h2 m k hk
  refine ⟨max N1 N2, fun i hi h_r''_le => ?_⟩
  have hi1 : i ≥ N1 := Nat.le_trans (Nat.le_max_left N1 N2) hi
  have hi2 : i ≥ N2 := Nat.le_trans (Nat.le_max_right N1 N2) hi
  exact h1N i hi1 (h2N i hi2 h_r''_le)

/-- lt 의 irreflexivity. -/
theorem lt_irrefl (r : Real213) : ¬ lt r r := by
  intro h
  obtain ⟨m, k, _, N, hN⟩ := h
  obtain ⟨ht, hf⟩ := hN N (Nat.le_refl N)
  rw [ht] at hf
  exact Bool.noConfusion hf

end E213.Research.Real213
