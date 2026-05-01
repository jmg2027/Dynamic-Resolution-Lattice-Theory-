import E213.Kernel.Tactic.Omega213
/-!
# Pigeonhole for `Fin`: no injection `Fin (N+1) → Fin N`

213-native (axiom-free) pigeonhole.  Originally used `omega` + `simp`
which forced `[propext, Quot.sound]` into every downstream theorem.
Rewritten using explicit `Nat.*` core lemmas + `dif_pos`/`dif_neg`
rewrites + `omega213` so the closure is strict ∅-axiom.
-/

open E213.Tactic

namespace E213.Math.Pigeonhole

private theorem ne_zero_of_lt_of_le {a b : Nat}
    (hge : b ≤ a) (hne : a ≠ b) : a ≠ 0 := by
  intro h0
  have hlt : b < a := Nat.lt_of_le_of_ne hge (Ne.symm hne)
  exact Nat.not_lt_zero _ (h0 ▸ hlt)

private theorem sub_one_lt_of_lt_succ_ne {a b n : Nat}
    (hge : b ≤ a) (hne : a ≠ b) (hlt : a < n + 1) : a - 1 < n := by
  have hpos : a ≠ 0 := ne_zero_of_lt_of_le hge hne
  have hsub : a - 1 < a := Nat.sub_one_lt hpos
  exact Nat.lt_of_lt_of_le hsub (Nat.le_of_lt_succ hlt)

/-- 213-native replacement for `Nat.sub_add_cancel` at b = 1.
    The Lean-core `Nat.sub_add_cancel` proof brings `propext`. -/
private theorem nat_sub_one_add_one {n : Nat} (h : n ≠ 0) : n - 1 + 1 = n := by
  cases n with
  | zero => exact absurd rfl h
  | succ k => rfl

/-- 213-native `Fin 0` elimination.  The Lean-core `Fin.elim0` brings
    `propext`, as does the `(0 : Fin 1)` literal via the `OfNat` instance. -/
private def fin0_absurd {α : Sort _} (h : Fin 0) : α :=
  absurd h.isLt (Nat.not_lt_zero h.val)

/-- Reindex `Fin (n+1) \ {v}` into `Fin n`: drop `v`, relabel. -/
private def shiftAround {n : Nat} (v w : Fin (n+1)) (h : w ≠ v) : Fin n :=
  if hlt : w.val < v.val then
    ⟨w.val, Nat.lt_of_lt_of_le hlt (Nat.le_of_lt_succ v.isLt)⟩
  else
    have hvw : w.val ≠ v.val := fun eq => h (Fin.ext eq)
    have hge : v.val ≤ w.val := Nat.le_of_not_lt hlt
    ⟨w.val - 1, sub_one_lt_of_lt_succ_ne hge hvw w.isLt⟩

end E213.Math.Pigeonhole

namespace E213.Math.Pigeonhole

/-- `shiftAround` is injective on its domain. -/
private theorem shiftAround_inj {n : Nat} (v : Fin (n+1))
    {w₁ w₂ : Fin (n+1)} (h₁ : w₁ ≠ v) (h₂ : w₂ ≠ v)
    (heq : shiftAround v w₁ h₁ = shiftAround v w₂ h₂) : w₁ = w₂ := by
  have hv₁ : w₁.val ≠ v.val := fun eq => h₁ (Fin.ext eq)
  have hv₂ : w₂.val ≠ v.val := fun eq => h₂ (Fin.ext eq)
  have hval := congrArg Fin.val heq
  by_cases hlt₁ : w₁.val < v.val
  · by_cases hlt₂ : w₂.val < v.val
    · have e₁ : (shiftAround v w₁ h₁).val = w₁.val := by
        unfold shiftAround; rw [dif_pos hlt₁]
      have e₂ : (shiftAround v w₂ h₂).val = w₂.val := by
        unfold shiftAround; rw [dif_pos hlt₂]
      exact Fin.ext (e₁ ▸ e₂ ▸ hval)
    · exfalso
      have e₁ : (shiftAround v w₁ h₁).val = w₁.val := by
        unfold shiftAround; rw [dif_pos hlt₁]
      have e₂ : (shiftAround v w₂ h₂).val = w₂.val - 1 := by
        unfold shiftAround; rw [dif_neg hlt₂]
      have heqv : w₁.val = w₂.val - 1 := e₁ ▸ e₂ ▸ hval
      have hge₂ : v.val ≤ w₂.val := Nat.le_of_not_lt hlt₂
      have hvlt₂ : v.val < w₂.val := Nat.lt_of_le_of_ne hge₂ (Ne.symm hv₂)
      have hvle : v.val ≤ w₂.val - 1 := Nat.le_pred_of_lt hvlt₂
      have hcontra : v.val ≤ w₁.val := heqv ▸ hvle
      exact Nat.not_lt_of_le hcontra hlt₁
  · by_cases hlt₂ : w₂.val < v.val
    · exfalso
      have e₁ : (shiftAround v w₁ h₁).val = w₁.val - 1 := by
        unfold shiftAround; rw [dif_neg hlt₁]
      have e₂ : (shiftAround v w₂ h₂).val = w₂.val := by
        unfold shiftAround; rw [dif_pos hlt₂]
      have heqv : w₁.val - 1 = w₂.val := e₁ ▸ e₂ ▸ hval
      have hge₁ : v.val ≤ w₁.val := Nat.le_of_not_lt hlt₁
      have hvlt₁ : v.val < w₁.val := Nat.lt_of_le_of_ne hge₁ (Ne.symm hv₁)
      have hvle : v.val ≤ w₁.val - 1 := Nat.le_pred_of_lt hvlt₁
      have hcontra : v.val ≤ w₂.val := heqv ▸ hvle
      exact Nat.not_lt_of_le hcontra hlt₂
    · have e₁ : (shiftAround v w₁ h₁).val = w₁.val - 1 := by
        unfold shiftAround; rw [dif_neg hlt₁]
      have e₂ : (shiftAround v w₂ h₂).val = w₂.val - 1 := by
        unfold shiftAround; rw [dif_neg hlt₂]
      have heqv : w₁.val - 1 = w₂.val - 1 := e₁ ▸ e₂ ▸ hval
      have hge₁ : v.val ≤ w₁.val := Nat.le_of_not_lt hlt₁
      have hge₂ : v.val ≤ w₂.val := Nat.le_of_not_lt hlt₂
      have hp₁ : w₁.val ≠ 0 := ne_zero_of_lt_of_le hge₁ hv₁
      have hp₂ : w₂.val ≠ 0 := ne_zero_of_lt_of_le hge₂ hv₂
      have hs₁ : w₁.val - 1 + 1 = w₁.val := nat_sub_one_add_one hp₁
      have hs₂ : w₂.val - 1 + 1 = w₂.val := nat_sub_one_add_one hp₂
      have hadd : w₁.val - 1 + 1 = w₂.val - 1 + 1 := congrArg (· + 1) heqv
      exact Fin.ext (hs₁ ▸ hs₂ ▸ hadd)

end E213.Math.Pigeonhole

namespace E213.Math.Pigeonhole

/-- **Pigeonhole.** No injection `Fin (N+1) → Fin N`. -/
theorem no_inj_succ : ∀ (N : Nat) (g : Fin (N+1) → Fin N),
    (∀ i j : Fin (N+1), i ≠ j → g i ≠ g j) → False := by
  intro N
  induction N with
  | zero => intro g _; exact fin0_absurd (g ⟨0, Nat.zero_lt_succ 0⟩)
  | succ m ih =>
      intro g hinj
      let v : Fin (m+1) := g ⟨m+1, Nat.lt_succ_self _⟩
      have hne : ∀ i : Fin (m+1), g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ≠ v := by
        intro i heq
        apply hinj ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⟨m+1, Nat.lt_succ_self _⟩
          (fun h => by
            have h' : i.val = m+1 := congrArg Fin.val h
            have hi : i.val < m+1 := i.isLt
            exact Nat.lt_irrefl _ (h' ▸ hi))
        exact heq
      let g' : Fin (m+1) → Fin m := fun i =>
        shiftAround v (g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) (hne i)
      have g'_inj : ∀ i j : Fin (m+1), i ≠ j → g' i ≠ g' j := by
        intro i j hij heq
        have heq' : g ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
                  = g ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ :=
          shiftAround_inj v (hne i) (hne j) heq
        have hval_ne : i.val ≠ j.val := fun eq => hij (Fin.ext eq)
        have hidx_ne : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m+2))
                     ≠ ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ :=
          fun h => hval_ne (congrArg (α := Fin (m+2)) Fin.val h)
        exact hinj _ _ hidx_ne heq'
      exact ih g' g'_inj

/-- Generalized pigeonhole: no injection `Fin k → Fin N` when `N < k`. -/
theorem no_inj_lt {N k : Nat} (h : N < k) (g : Fin k → Fin N)
    (hinj : ∀ i j : Fin k, i ≠ j → g i ≠ g j) : False := by
  have hk : ∀ i : Fin (N+1), i.val < k :=
    fun i => Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_of_lt h)
  let g' : Fin (N+1) → Fin N := fun i => g ⟨i.val, hk i⟩
  apply no_inj_succ N g'
  intro i j hij heq
  have heq' : g ⟨i.val, hk i⟩ = g ⟨j.val, hk j⟩ := heq
  have hval_ne : i.val ≠ j.val := fun eq => hij (Fin.ext eq)
  have hidx_ne : (⟨i.val, hk i⟩ : Fin k) ≠ ⟨j.val, hk j⟩ :=
    fun heqv => hval_ne (congrArg (α := Fin k) Fin.val heqv)
  exact hinj _ _ hidx_ne heq'

end E213.Math.Pigeonhole
