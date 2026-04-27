/-!
# Pigeonhole for `Fin`: no injection `Fin (N+1) → Fin N`

Lean 4 core has no `Fintype.card_le_card_of_injective`; we prove a
bare-bones pigeonhole directly by induction on `N`, using a
"shift-around" that identifies `Fin (n+1) \ {v}` with `Fin n`.
-/

namespace E213.OS.Pigeonhole

/-- Reindex `Fin (n+1) \ {v}` into `Fin n`: drop `v`, relabel. -/
private def shiftAround {n : Nat} (v w : Fin (n+1)) (h : w ≠ v) : Fin n :=
  if hlt : w.val < v.val then
    ⟨w.val, by have := v.isLt; omega⟩
  else
    ⟨w.val - 1, by
      have hvw : w.val ≠ v.val := fun eq => h (Fin.ext eq)
      have hge : v.val ≤ w.val := Nat.le_of_not_lt hlt
      have hw : w.val < n+1 := w.isLt
      omega⟩

/-- `shiftAround` is injective on its domain. -/
private theorem shiftAround_inj {n : Nat} (v : Fin (n+1))
    {w₁ w₂ : Fin (n+1)} (h₁ : w₁ ≠ v) (h₂ : w₂ ≠ v)
    (heq : shiftAround v w₁ h₁ = shiftAround v w₂ h₂) : w₁ = w₂ := by
  have hv₁ : w₁.val ≠ v.val := fun eq => h₁ (Fin.ext eq)
  have hv₂ : w₂.val ≠ v.val := fun eq => h₂ (Fin.ext eq)
  unfold shiftAround at heq
  have hval := congrArg Fin.val heq
  simp at hval
  by_cases hlt₁ : w₁.val < v.val <;> by_cases hlt₂ : w₂.val < v.val <;>
    simp [hlt₁, hlt₂] at hval
  · exact Fin.ext hval
  · exfalso
    have : v.val ≤ w₂.val := Nat.le_of_not_lt hlt₂
    omega
  · exfalso
    have : v.val ≤ w₁.val := Nat.le_of_not_lt hlt₁
    omega
  · have hge₁ : v.val ≤ w₁.val := Nat.le_of_not_lt hlt₁
    have hge₂ : v.val ≤ w₂.val := Nat.le_of_not_lt hlt₂
    exact Fin.ext (by omega)

/-- **Pigeonhole.** No injection `Fin (N+1) → Fin N`. -/
theorem no_inj_succ : ∀ (N : Nat) (g : Fin (N+1) → Fin N),
    (∀ i j : Fin (N+1), i ≠ j → g i ≠ g j) → False := by
  intro N
  induction N with
  | zero => intro g _; exact Fin.elim0 (g 0)
  | succ m ih =>
      intro g hinj
      let v : Fin (m+1) := g ⟨m+1, by omega⟩
      have hne : ∀ i : Fin (m+1), g ⟨i.val, by omega⟩ ≠ v := by
        intro i heq
        apply hinj ⟨i.val, by omega⟩ ⟨m+1, by omega⟩
          (fun h => by
            have h' : i.val = m+1 := by
              have := congrArg Fin.val h; exact this
            have : i.val < m+1 := i.isLt
            omega)
        exact heq
      let g' : Fin (m+1) → Fin m := fun i =>
        shiftAround v (g ⟨i.val, by omega⟩) (hne i)
      have g'_inj : ∀ i j : Fin (m+1), i ≠ j → g' i ≠ g' j := by
        intro i j hij heq
        have heq' : g ⟨i.val, by omega⟩ = g ⟨j.val, by omega⟩ :=
          shiftAround_inj v (hne i) (hne j) heq
        have hval_ne : i.val ≠ j.val := fun eq => hij (Fin.ext eq)
        have hidx_ne : (⟨i.val, by omega⟩ : Fin (m+2)) ≠ ⟨j.val, by omega⟩ :=
          fun h => hval_ne (by have := congrArg Fin.val h; simpa using this)
        exact hinj _ _ hidx_ne heq'
      exact ih g' g'_inj

/-- Generalized pigeonhole: no injection `Fin k → Fin N` when `N < k`. -/
theorem no_inj_lt {N k : Nat} (h : N < k) (g : Fin k → Fin N)
    (hinj : ∀ i j : Fin k, i ≠ j → g i ≠ g j) : False := by
  let g' : Fin (N+1) → Fin N := fun i => g ⟨i.val, by omega⟩
  apply no_inj_succ N g'
  intro i j hij heq
  have heq' : g ⟨i.val, by omega⟩ = g ⟨j.val, by omega⟩ := heq
  have hval_ne : i.val ≠ j.val := fun eq => hij (Fin.ext eq)
  have hidx_ne : (⟨i.val, by omega⟩ : Fin k) ≠ ⟨j.val, by omega⟩ :=
    fun h => hval_ne (by have := congrArg Fin.val h; simpa using this)
  exact hinj _ _ hidx_ne heq'

end E213.OS.Pigeonhole
