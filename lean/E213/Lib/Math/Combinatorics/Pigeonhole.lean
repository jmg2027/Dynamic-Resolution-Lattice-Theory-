import E213.Meta.Tactic.Omega213
import E213.Meta.Tactic.NatHelper
import E213.Meta.Tactic.Fin213
/-!
# Pigeonhole for `Fin`: no injection `Fin (N+1) → Fin N`

213-native (∅-axiom) pigeonhole.  Originally used `omega` + `simp`
which forced `[propext, Quot.sound]` into every downstream theorem.
Now uses explicit `Nat.*` core lemmas + `dif_pos`/`dif_neg` rewrites
+ `omega213` + `Nat213`/`Fin213` helpers so the closure is strict
∅-axiom.
-/

open E213.Tactic E213.Tactic.NatHelper E213.Tactic.Fin213

namespace E213.Lib.Math.Combinatorics.Pigeonhole

/-- Reindex `Fin (n+1) \ {v}` into `Fin n`: drop `v`, relabel. -/
private def shiftAround {n : Nat} (v w : Fin (n+1)) (h : w ≠ v) : Fin n :=
  if hlt : w.val < v.val then
    ⟨w.val, Nat.lt_of_lt_of_le hlt (Nat.le_of_lt_succ v.isLt)⟩
  else
    have hvw : w.val ≠ v.val := fun eq => h (Fin.ext eq)
    have hge : v.val ≤ w.val := Nat.le_of_not_lt hlt
    ⟨w.val - 1, sub_one_lt_of_lt_succ_ne hge hvw w.isLt⟩


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
      have hp₁ : w₁.val ≠ 0 := ne_zero_of_le_ne hge₁ hv₁
      have hp₂ : w₂.val ≠ 0 := ne_zero_of_le_ne hge₂ hv₂
      have hs₁ : w₁.val - 1 + 1 = w₁.val := sub_one_add_one hp₁
      have hs₂ : w₂.val - 1 + 1 = w₂.val := sub_one_add_one hp₂
      have hadd : w₁.val - 1 + 1 = w₂.val - 1 + 1 := congrArg (· + 1) heqv
      exact Fin.ext (hs₁ ▸ hs₂ ▸ hadd)


/-- **Pigeonhole.** No injection `Fin (N+1) → Fin N`. -/
theorem no_inj_succ : ∀ (N : Nat) (g : Fin (N+1) → Fin N),
    (∀ i j : Fin (N+1), i ≠ j → g i ≠ g j) → False := by
  intro N
  induction N with
  | zero => intro g _; exact absurd0 (g ⟨0, Nat.zero_lt_succ 0⟩)
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

/-! ## Constructive collision-finder (produces the pair, not just `False`)

`no_inj_lt` *refutes* injectivity; a divisibility/coincidence argument wants the
**actual colliding pair**.  The scan below searches a `Fin`-indexed family with
`DecidableEq (Fin N)` (axiom-clean) — no `Classical`, no decidable-`∃` instance —
and returns either a witnessed hit or a pointwise miss; `exists_collision` then
recurses through `shiftAround` to produce the explicit pair. -/

/-- **Bounded membership scan.**  For a family `r : Fin k → Fin N` and a target
    `v`, decide constructively whether `v` is hit — returning the witnessing
    index, or a pointwise miss.  Pure linear scan with `DecidableEq (Fin N)`. -/
theorem scan {N : Nat} (v : Fin N) :
    ∀ (k : Nat) (r : Fin k → Fin N), (∃ i, r i = v) ∨ (∀ i, r i ≠ v) := by
  intro k
  induction k with
  | zero => intro _; exact Or.inr (fun i => i.elim0)
  | succ m ih =>
      intro r
      let last : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
      by_cases hlast : r last = v
      · exact Or.inl ⟨last, hlast⟩
      · let r' : Fin m → Fin N := fun i => r ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
        rcases ih r' with ⟨i, hi⟩ | hmiss
        · exact Or.inl ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, hi⟩
        · refine Or.inr (fun j hj => ?_)
          by_cases hjm : j.val < m
          · have : r' ⟨j.val, hjm⟩ = v := by
              show r ⟨j.val, Nat.lt_succ_of_lt hjm⟩ = v
              have : (⟨j.val, Nat.lt_succ_of_lt hjm⟩ : Fin (m + 1)) = j :=
                Fin.ext rfl
              rw [this]; exact hj
            exact hmiss ⟨j.val, hjm⟩ this
          · have hjeq : j.val = m :=
              Nat.le_antisymm (Nat.le_of_lt_succ j.isLt) (Nat.le_of_not_lt hjm)
            have : j = last := Fin.ext hjeq
            exact hlast (this ▸ hj)

/-- **Constructive pigeonhole — the colliding pair.**  Any `g : Fin (N+1) → Fin N`
    has two distinct indices with `g i = g j`, *exhibited*: scan whether the top
    value recurs among the earlier indices; on a miss, `shiftAround` drops that
    value and the recursion returns the pair one level down.  No `Classical`. -/
theorem exists_collision : ∀ (N : Nat) (g : Fin (N + 1) → Fin N),
    ∃ i j : Fin (N + 1), i ≠ j ∧ g i = g j := by
  intro N
  induction N with
  | zero => intro g; exact (g ⟨0, Nat.lt_succ_self 0⟩).elim0
  | succ M ih =>
      intro g
      let last : Fin (M + 2) := ⟨M + 1, Nat.lt_succ_self (M + 1)⟩
      let v : Fin (M + 1) := g last
      let r : Fin (M + 1) → Fin (M + 1) :=
        fun k => g ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩
      rcases scan v (M + 1) r with ⟨k, hk⟩ | hmiss
      · -- `v` recurs at `k`:  `g ⟨k⟩ = v = g last`, and `⟨k⟩ ≠ last`.
        refine ⟨⟨k.val, Nat.lt_succ_of_lt k.isLt⟩, last, ?_, ?_⟩
        · intro h
          have : k.val = M + 1 := congrArg Fin.val h
          exact Nat.lt_irrefl _ (this ▸ k.isLt)
        · exact hk
      · -- nothing recurs:  drop `v` via `shiftAround`, recurse on `Fin M`.
        let g' : Fin (M + 1) → Fin M := fun k => shiftAround v (r k) (hmiss k)
        obtain ⟨i, j, hij, hg'⟩ := ih g'
        have hrij : r i = r j := shiftAround_inj v (hmiss i) (hmiss j) hg'
        refine ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩,
                ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩, ?_, hrij⟩
        intro h
        have hval : i.val = j.val :=
          congrArg (fun x : Fin (M + 2) => x.val) h
        exact hij (Fin.ext hval)

end E213.Lib.Math.Combinatorics.Pigeonhole
