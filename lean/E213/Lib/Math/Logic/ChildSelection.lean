import E213.Lib.Math.Logic.Pi01Decision

/-!
# Reverse Mathematics 213 — Phase GB-cont: child selection (König under tree-closure)

Marathon field 17, Phase GB-cont (`blueprints/math/17_reverse_math_213.md`).

Phase GB located the *predicate-decision* cost of "infinite-below" at LPO.  This file does
the *child selection* — the König heart "an infinite node has an infinite child" — for the
native `existsLevel` form, under the standard König hypothesis that the tree is
**downward-closed** (here in usable form: `existsLevel T s'` is antitone in depth — a deep
node has all its shallower prefixes).

**Result:** `LPO` + tree-monotonicity ⟹ child selection (`lpo_infChildExistsN`).  LLPO
would suffice (the disjunction is LLPO-shaped); LPO is the clean upper bound used here.
Pure-Lean: `cases` + `Bool.noConfusion`, no `propext`.
-/

namespace E213.Lib.Math.Logic

/-- "Infinite-below `s`" (native): a node at every depth below `s`. -/
def InfB (T : List Bool → Bool) (s : List Bool) : Prop := ∀ n, existsLevel T s n = true

/-- The tree property in usable form: each level-stream is antitone in depth (a
    downward-closed tree — a deep node implies all its shallower prefixes). -/
def LevelAntitone (T : List Bool → Bool) : Prop :=
  ∀ s' m n, m ≤ n → existsLevel T s' n = true → existsLevel T s' m = true

/-- `¬(b = true) ⟹ b = false` (Bool, propext-free). -/
theorem ne_true_imp_false (b : Bool) (h : b = true → False) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

/-- `(a || b) = true ⟹ a = true ∨ b = true` (Bool, propext-free). -/
theorem or_split (a b : Bool) (h : (a || b) = true) : a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

/-- From LPO, "not everywhere true" yields an explicit false witness. -/
theorem lpo_exists_false (hlpo : LPO) (e : Nat → Bool) (h : ¬ (∀ n, e n = true)) :
    ∃ n, e n = false :=
  (hlpo (fun n => !(e n))).elim
    (fun he => he.elim (fun n hn => ⟨n, not_eq_true_imp (e n) hn⟩))
    (fun hall => absurd (fun n => not_eq_false_imp (e n) (hall n)) h)

/-- ★★★ **König child selection from LPO + tree-monotonicity.**  If every depth below `s`
    has a node (`InfB T s`) and the tree is downward-closed (`LevelAntitone`), then one of
    the two children is infinite-below.  LPO decides the left child; if it is finite, it is
    empty beyond some depth (antitone), so — every depth of `s` being covered by a child —
    the right child is infinite-below. -/
theorem lpo_infChildExistsN (hlpo : LPO) (T : List Bool → Bool) (hmono : LevelAntitone T)
    (s : List Bool) (hs : InfB T s) :
    InfB T (s ++ [false]) ∨ InfB T (s ++ [true]) :=
  (lpo_decides_pi01 hlpo (existsLevel T (s ++ [false]))).elim
    (fun h0 => Or.inl h0)
    (fun h0 =>
      Or.inr (fun n =>
        (lpo_exists_false hlpo (existsLevel T (s ++ [false])) h0).elim (fun n0 hn0 =>
          have e0M : existsLevel T (s ++ [false]) (n0 + n) = false :=
            ne_true_imp_false _ (fun hem =>
              Bool.noConfusion
                ((hmono (s ++ [false]) n0 (n0 + n) (Nat.le_add_right n0 n) hem).symm.trans hn0))
          have e1M : existsLevel T (s ++ [true]) (n0 + n) = true :=
            (or_split (existsLevel T (s ++ [false]) (n0 + n))
                      (existsLevel T (s ++ [true]) (n0 + n)) (hs (n0 + n + 1))).elim
              (fun hb => Bool.noConfusion (hb.symm.trans e0M))
              (fun hb => hb)
          hmono (s ++ [true]) n (n0 + n) (Nat.le_add_left n n0) e1M)))

/-! ## GB-cont2 — `LevelAntitone` from a downward-closed tree

`lpo_infChildExistsN` takes monotonicity as a hypothesis.  Here it is *derived* from the
natural König condition: the tree is **downward-closed** — a node's immediate parent is a
node (`hdc`).  Then a deep node implies its shallower prefixes, i.e. `existsLevel` is
antitone, so König child selection holds for any actual downward-closed Bool tree. -/

/-- `a = true ⟹ (a || b) = true`. -/
theorem or_intro_left (a b : Bool) (h : a = true) : (a || b) = true := by
  cases a
  · exact Bool.noConfusion h
  · rfl

/-- `b = true ⟹ (a || b) = true`. -/
theorem or_intro_right (a b : Bool) (h : b = true) : (a || b) = true := by
  cases a
  · exact h
  · rfl

/-- **One step down.**  In a downward-closed tree, a node at depth `n+1` below `s` implies a
    node at depth `n` (drop the last bit).  By induction on `n`, descending into children. -/
theorem existsLevel_pred (T : List Bool → Bool)
    (hdc : ∀ u b, T (u ++ [b]) = true → T u = true) :
    ∀ n s, existsLevel T s (n + 1) = true → existsLevel T s n = true := by
  intro n
  induction n with
  | zero =>
    intro s h
    exact (or_split _ _ h).elim (fun hb => hdc s false hb) (fun hb => hdc s true hb)
  | succ n ih =>
    intro s h
    exact (or_split _ _ h).elim
      (fun hb => or_intro_left _ _ (ih (s ++ [false]) hb))
      (fun hb => or_intro_right _ _ (ih (s ++ [true]) hb))

/-- ★ **A downward-closed tree is level-antitone.**  By induction on the `≤` derivation,
    using `existsLevel_pred` at each step. -/
theorem levelAntitone_of_downwardClosed (T : List Bool → Bool)
    (hdc : ∀ u b, T (u ++ [b]) = true → T u = true) : LevelAntitone T := by
  intro s' m n hmn
  induction hmn with
  | refl => exact id
  | step _ ih => exact fun hn => ih (existsLevel_pred T hdc _ s' hn)

/-- ★★ **König child selection for an actual downward-closed tree.**  `LPO` + downward-closure
    ⟹ an infinite-below node has an infinite-below child — the monotonicity hypothesis of
    `lpo_infChildExistsN` discharged from the natural tree condition. -/
theorem lpo_infChildExists_downwardClosed (hlpo : LPO) (T : List Bool → Bool)
    (hdc : ∀ u b, T (u ++ [b]) = true → T u = true) (s : List Bool) (hs : InfB T s) :
    InfB T (s ++ [false]) ∨ InfB T (s ++ [true]) :=
  lpo_infChildExistsN hlpo T (levelAntitone_of_downwardClosed T hdc) s hs

end E213.Lib.Math.Logic
