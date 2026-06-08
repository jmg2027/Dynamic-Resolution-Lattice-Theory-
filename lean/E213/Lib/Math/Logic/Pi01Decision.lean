import E213.Lib.Math.Logic.Omniscience

/-!
# Reverse Mathematics 213 — Phase GB: LPO decides Π⁰₁ (the cost of "infinite-below")

Marathon field 17, Phase GB (`blueprints/math/17_reverse_math_213.md`).

The König selection step `InfChildExists`
(`Lib/Math/Combinatorics/KonigConditional.lean`) was conjectured to be "an LLPO-instance".
The honest calibration splits it in two:

  - **deciding** "infinite-below `s`" — a `Π⁰₁` statement `∀ n, h n = true` — costs exactly
    **LPO** (this file);
  - **selecting which child** is infinite — the disjunction step — is the LLPO-flavoured
    part, and a clean formalization additionally needs the tree to be *downward-closed*
    (the König hypothesis).  That is Phase GB-cont (open).

So this file closes the predicate-decision half: `LPO` decides every `Π⁰₁`, and
"infinite-below" (the native level-existence stream `existsLevel`) is `Π⁰₁`, hence decided
by LPO.  Pure-Lean: `Bool.noConfusion` + `cases`, no `propext`.
-/

namespace E213.Lib.Math.Logic

/-- `!b = false ⟹ b = true` (Bool, propext-free). -/
theorem not_eq_false_imp (b : Bool) (h : (!b) = false) : b = true := by
  cases b
  · exact Bool.noConfusion h
  · rfl

/-- `!b = true ⟹ b = false` (Bool, propext-free). -/
theorem not_eq_true_imp (b : Bool) (h : (!b) = true) : b = false := by
  cases b
  · rfl
  · exact Bool.noConfusion h

/-- ★ **LPO decides every `Π⁰₁` statement** `∀ n, h n = true`.  Apply LPO to the negated
    stream `fun n => !(h n)`: an everywhere-false negation is everywhere-true `h`; a
    fire-witness of the negation refutes "everywhere true". -/
theorem lpo_decides_pi01 (hlpo : LPO) (h : Nat → Bool) :
    (∀ n, h n = true) ∨ ¬ (∀ n, h n = true) :=
  (hlpo (fun n => !(h n))).elim
    (fun he => Or.inr (fun hall =>
      he.elim (fun n hn =>
        Bool.noConfusion ((not_eq_true_imp (h n) hn).symm.trans (hall n)))))
    (fun hall => Or.inl (fun n => not_eq_false_imp (h n) (hall n)))

/-- ★ **LPO decides every `Σ⁰₁` statement** `∃ n, h n = true` — the dual of
    `lpo_decides_pi01`.  LPO's witness alternative gives the `∃`; its everywhere-false
    alternative refutes it. -/
theorem lpo_decides_sigma01 (hlpo : LPO) (h : Nat → Bool) :
    (∃ n, h n = true) ∨ ¬ (∃ n, h n = true) :=
  (hlpo h).elim (fun he => Or.inl he)
    (fun hall => Or.inr (fun he =>
      he.elim (fun n hn => Bool.noConfusion (hn.symm.trans (hall n)))))

/-- The native "infinite-below `s`" decision stream on a Bool tree: `existsLevel T s n` =
    is there a node at depth exactly `n` below `s` (a `Π⁰₁` body, by Bool recursion — no
    finite-enumeration needed). -/
def existsLevel (T : List Bool → Bool) (s : List Bool) : Nat → Bool
  | 0     => T s
  | n + 1 => existsLevel T (s ++ [false]) n || existsLevel T (s ++ [true]) n

/-- ★★ **LPO decides "infinite-below".**  Infinite-below `s` is `∀ n, existsLevel T s n =
    true` — a `Π⁰₁` statement — so it is an instance of `lpo_decides_pi01`.  This locates
    the omniscience cost of König's infinite-below predicate at exactly LPO; the
    which-child *selection* (the LLPO disjunction, needing tree-closure) is Phase GB-cont. -/
theorem lpo_decides_infiniteBelow (hlpo : LPO) (T : List Bool → Bool) (s : List Bool) :
    (∀ n, existsLevel T s n = true) ∨ ¬ (∀ n, existsLevel T s n = true) :=
  lpo_decides_pi01 hlpo (existsLevel T s)

end E213.Lib.Math.Logic
