import E213.Research.Real213.Const

/-!
# Research.Real213Order: order (le, lt) on Real213 — A4

Phase A milestone A4 of `E1_real213_analysis_roadmap.md`.
Bishop-style constructive le: for every rational m/k, eventually
"r' ≤ m/k → r ≤ m/k".

## Definitions

- `le r r' := ∀ m k, ∃ N, ∀ i ≥ N, orderProj r'-implies-r`
- `lt r r' := ∃ m k, ∃ N, ∀ i ≥ N, r ≤ m/k but r' > m/k`

orderProj m k (a, b) = decide (a*k ≤ b*m) — cross-mult form.

## Significance

- Constructive le without LEM.
- A *different object* from ZFC's r ≤ r' (set-theoretic) — requires
  explicit modulus-form evidence.
-/

namespace E213.Research.Real213.Order

open E213.Firmware E213.Hypervisor
open E213.Research.HasModulusNS
open E213.Research.ABLens
open E213.Research.ArchimedeanCauchy

/-- **Real213 le**: for every rational m/k cut, eventually
    r' ≤ m/k implies r ≤ m/k.  Bishop-style constructive le. -/
def le (r r' : Real213) : Prop :=
  ∀ m k, k ≥ 1 → ∃ N, ∀ i, i ≥ N →
    orderProj m k (abLens.view (r'.xs i)) = true →
    orderProj m k (abLens.view (r.xs i)) = true

/-- **Real213 lt**: some m/k separates r and r' (r ≤ m/k < r'). -/
def lt (r r' : Real213) : Prop :=
  ∃ m k, k ≥ 1 ∧ ∃ N, ∀ i, i ≥ N →
    orderProj m k (abLens.view (r.xs i)) = true ∧
    orderProj m k (abLens.view (r'.xs i)) = false

end E213.Research.Real213.Order

namespace E213.Research.Real213.Order

open E213.Firmware E213.Hypervisor
open E213.Research.HasModulusNS
open E213.Research.ABLens
open E213.Research.ArchimedeanCauchy

/-- Reflexivity of le. -/
theorem le_refl (r : Real213) : le r r := by
  intro _ _ _
  exact ⟨0, fun _ _ h => h⟩

/-- Transitivity of le. -/
theorem le_trans (r r' r'' : Real213) :
    le r r' → le r' r'' → le r r'' := by
  intro h1 h2 m k hk
  obtain ⟨N1, h1N⟩ := h1 m k hk
  obtain ⟨N2, h2N⟩ := h2 m k hk
  refine ⟨max N1 N2, fun i hi h_r''_le => ?_⟩
  have hi1 : i ≥ N1 := Nat.le_trans (Nat.le_max_left N1 N2) hi
  have hi2 : i ≥ N2 := Nat.le_trans (Nat.le_max_right N1 N2) hi
  exact h1N i hi1 (h2N i hi2 h_r''_le)

/-- Irreflexivity of lt. -/
theorem lt_irrefl (r : Real213) : ¬ lt r r := by
  intro h
  obtain ⟨m, k, _, N, hN⟩ := h
  obtain ⟨ht, hf⟩ := hN N (Nat.le_refl N)
  rw [ht] at hf
  exact Bool.noConfusion hf

end E213.Research.Real213.Order
