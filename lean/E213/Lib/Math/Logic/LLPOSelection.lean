import E213.Lib.Math.Logic.LLPO
import E213.Lib.Math.Logic.Interleave

/-!
# Reverse Mathematics 213 — GB-cont4: König child selection from LLPO

Marathon field 17 (`blueprints/math/17_reverse_math_213.md`).  Tightens the König
child-selection cost from LPO (`ChildSelection.lpo_infChildExistsN`) to the weaker **LLPO**.

The proof is the monotone turn-off encoding on the `Interleave.lean` infrastructure: with
`fa = !existsLevel s0`, `fb = !existsLevel s1` (monotone, from `LevelAntitone`) and the
cover `∀n (e0 n ∨ e1 n)` giving `∀n ¬(fa n ∧ fb n)`, the rising-edge stream
`g = interleave (ftrue fa) (ftrue fb)` is **at-most-one-true** (each `ftrue` rises once —
`ftrue_unique`; and not both rise — `not_both`).  LLPO's even/odd split + `ftrue_all_false`
then gives `(∀n fa = false) ∨ (∀n fb = false)`, i.e. `InfB s0 ∨ InfB s1`.  All ∅-axiom.
-/

namespace E213.Lib.Math.Logic

/-- Monotone Bool stream: once true, stays true. -/
def Mono (f : Nat → Bool) : Prop := ∀ m n, m ≤ n → f m = true → f n = true

theorem and_left (a b : Bool) (h : (a && b) = true) : a = true := by
  cases a
  · exact Bool.noConfusion h
  · rfl

theorem and_right (a b : Bool) (h : (a && b) = true) : b = true := by
  cases a
  · exact Bool.noConfusion h
  · exact h

theorem and_eq_true (a b : Bool) (ha : a = true) (hb : b = true) : (a && b) = true := by
  cases a
  · exact Bool.noConfusion ha
  · exact hb

/-- De Morgan, one side: `(a ∨ b) = true ⟹ (¬a ∧ ¬b) = false`. -/
theorem demorgan (a b : Bool) (h : (a || b) = true) : ((!a) && (!b)) = false := by
  cases a
  · cases b
    · exact Bool.noConfusion h
    · rfl
  · rfl

/-- A rising edge implies the value is true there. -/
theorem ftrue_imp_self (f : Nat → Bool) : ∀ i, ftrue f i = true → f i = true
  | 0     => fun h => h
  | _ + 1 => fun h => and_left _ _ h

/-- A rising edge at `n+1` means `f` was false at `n`. -/
theorem ftrue_pred_false (f : Nat → Bool) (n : Nat) (h : ftrue f (n + 1) = true) :
    f n = false :=
  not_eq_true_imp (f n) (and_right _ _ h)

/-- For monotone `f`, two rising edges with `i < j` are impossible. -/
theorem ftrue_lt_false (f : Nat → Bool) (hmono : Mono f) (i j : Nat)
    (hi : ftrue f i = true) (hj : ftrue f j = true) (hij : i < j) : False := by
  cases j with
  | zero => exact Nat.not_lt_zero i hij
  | succ j0 =>
    have hfj0 : f j0 = false := ftrue_pred_false f j0 hj
    have hile : i ≤ j0 := Nat.le_of_lt_succ hij
    have hup : f j0 = true := hmono i j0 hile (ftrue_imp_self f i hi)
    exact Bool.noConfusion (hup.symm.trans hfj0)

/-- For monotone `f`, the rising edge is unique. -/
theorem ftrue_unique (f : Nat → Bool) (hmono : Mono f) (i j : Nat)
    (hi : ftrue f i = true) (hj : ftrue f j = true) : i = j :=
  (Nat.lt_trichotomy i j).elim
    (fun hlt => False.elim (ftrue_lt_false f hmono i j hi hj hlt))
    (fun h => h.elim (fun heq => heq)
      (fun hgt => False.elim (ftrue_lt_false f hmono j i hj hi hgt)))

/-- If `fa`, `fb` are monotone and never both true, their rising edges cannot both fire. -/
theorem not_both (fa fb : Nat → Bool) (hma : Mono fa) (hmb : Mono fb)
    (hdisj : ∀ n, (fa n && fb n) = false) (i j : Nat)
    (hi : ftrue fa i = true) (hj : ftrue fb j = true) : False := by
  have ha : fa (i + j) = true := hma i (i + j) (Nat.le_add_right i j) (ftrue_imp_self fa i hi)
  have hb : fb (i + j) = true := hmb j (i + j) (Nat.le_add_left j i) (ftrue_imp_self fb j hj)
  exact Bool.noConfusion ((and_eq_true _ _ ha hb).symm.trans (hdisj (i + j)))

/-- ★★★ **König child selection from LLPO** (tightening `lpo_infChildExistsN`).  If every
    depth below `s` has a node and the tree is downward-closed (`LevelAntitone`), then —
    using only **LLPO** — one child is infinite-below. -/
theorem llpo_infChildExistsN (hllpo : LLPO) (T : List Bool → Bool) (hmono : LevelAntitone T)
    (s : List Bool) (hs : InfB T s) :
    InfB T (s ++ [false]) ∨ InfB T (s ++ [true]) := by
  -- the two negated level streams
  let fa : Nat → Bool := fun n => !(existsLevel T (s ++ [false]) n)
  let fb : Nat → Bool := fun n => !(existsLevel T (s ++ [true]) n)
  -- monotone (from antitone existsLevel)
  have hma : Mono fa := by
    intro m n hmn hfam
    have he0m : existsLevel T (s ++ [false]) m = false := not_eq_true_imp _ hfam
    have he0n : existsLevel T (s ++ [false]) n = false :=
      ne_true_imp_false _ (fun hen =>
        Bool.noConfusion ((hmono (s ++ [false]) m n hmn hen).symm.trans he0m))
    exact congrArg (fun x => !x) he0n
  have hmb : Mono fb := by
    intro m n hmn hfbm
    have he1m : existsLevel T (s ++ [true]) m = false := not_eq_true_imp _ hfbm
    have he1n : existsLevel T (s ++ [true]) n = false :=
      ne_true_imp_false _ (fun hen =>
        Bool.noConfusion ((hmono (s ++ [true]) m n hmn hen).symm.trans he1m))
    exact congrArg (fun x => !x) he1n
  -- never both true (from the cover ∀n e0 n ∨ e1 n, which is hs at n+1)
  have hdisj : ∀ n, (fa n && fb n) = false := fun n => demorgan _ _ (hs (n + 1))
  -- the interleaved rising-edge stream is at-most-one-true
  let g : Nat → Bool := interleave (ftrue fa) (ftrue fb)
  have gamo : ∀ i j, g i = true → g j = true → i = j := by
    intro i j hgi hgj
    rcases even_or_odd i with ⟨a, hia⟩ | ⟨a, hia⟩ <;>
      rcases even_or_odd j with ⟨b, hjb⟩ | ⟨b, hjb⟩
    · -- i = 2a, j = 2b
      have hfa : ftrue fa a = true :=
        (il_even a (ftrue fa) (ftrue fb)).symm.trans ((congrArg g hia).symm.trans hgi)
      have hfb : ftrue fa b = true :=
        (il_even b (ftrue fa) (ftrue fb)).symm.trans ((congrArg g hjb).symm.trans hgj)
      exact hia.trans ((congrArg (fun x => 2 * x) (ftrue_unique fa hma a b hfa hfb)).trans hjb.symm)
    · -- i = 2a, j = 2b+1
      have hfa : ftrue fa a = true :=
        (il_even a (ftrue fa) (ftrue fb)).symm.trans ((congrArg g hia).symm.trans hgi)
      have hfb : ftrue fb b = true :=
        (il_odd b (ftrue fa) (ftrue fb)).symm.trans ((congrArg g hjb).symm.trans hgj)
      exact False.elim (not_both fa fb hma hmb hdisj a b hfa hfb)
    · -- i = 2a+1, j = 2b
      have hfb : ftrue fb a = true :=
        (il_odd a (ftrue fa) (ftrue fb)).symm.trans ((congrArg g hia).symm.trans hgi)
      have hfa : ftrue fa b = true :=
        (il_even b (ftrue fa) (ftrue fb)).symm.trans ((congrArg g hjb).symm.trans hgj)
      exact False.elim (not_both fa fb hma hmb hdisj b a hfa hfb)
    · -- i = 2a+1, j = 2b+1
      have hfa : ftrue fb a = true :=
        (il_odd a (ftrue fa) (ftrue fb)).symm.trans ((congrArg g hia).symm.trans hgi)
      have hfb : ftrue fb b = true :=
        (il_odd b (ftrue fa) (ftrue fb)).symm.trans ((congrArg g hjb).symm.trans hgj)
      exact hia.trans ((congrArg (fun x => 2 * x + 1) (ftrue_unique fb hmb a b hfa hfb)).trans hjb.symm)
  -- LLPO splits g into its even/odd halves
  rcases hllpo g gamo with hev | hod
  · -- ∀k g(2k)=false → ∀k ftrue fa k=false → ∀n fa n=false → InfB s0
    refine Or.inl (fun n => ?_)
    have hfa0 : ∀ k, ftrue fa k = false := fun k =>
      (il_even k (ftrue fa) (ftrue fb)).symm.trans (hev k)
    exact not_eq_false_imp _ (ftrue_all_false fa hfa0 n)
  · refine Or.inr (fun n => ?_)
    have hfb0 : ∀ k, ftrue fb k = false := fun k =>
      (il_odd k (ftrue fa) (ftrue fb)).symm.trans (hod k)
    exact not_eq_false_imp _ (ftrue_all_false fb hfb0 n)

/-- ★★ **König child selection from LLPO, for an actual downward-closed tree** — the
    LLPO-cost version of `lpo_infChildExists_downwardClosed`. -/
theorem llpo_infChildExists_downwardClosed (hllpo : LLPO) (T : List Bool → Bool)
    (hdc : ∀ u b, T (u ++ [b]) = true → T u = true) (s : List Bool) (hs : InfB T s) :
    InfB T (s ++ [false]) ∨ InfB T (s ++ [true]) :=
  llpo_infChildExistsN hllpo T (levelAntitone_of_downwardClosed T hdc) s hs

end E213.Lib.Math.Logic
