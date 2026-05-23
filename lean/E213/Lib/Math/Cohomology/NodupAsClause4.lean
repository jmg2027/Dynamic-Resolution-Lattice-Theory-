import E213.Theory.Atomicity.AliveDerivation

/-!
# `List.Nodup` is the recursive Clause-4 application at list granularity

Companion to `Theory/Atomicity/AliveDerivation.lean`.  The
`AliveDerivation` file proved that the `IsAlive` parity predicate
on `(a, b)` is the count-Lens reading of Clause 4 of the 213 axiom
(`seed/AXIOM/02_axiom.md` §2.2 #4: no self-pair) applied
recursively at the binary-group level.

This file extends the same recursive-Clause-4 reading to a second
instance: the standard library predicate `List.Nodup` is the
count-Lens reading of Clause 4 applied at the *list-index* level.
A list has no duplicates iff no two distinct index positions are
paired with the same element — exactly the no-self-pair axiom
read at list granularity.

Together with `AliveDerivation`, this establishes the
recursive-Clause-4-application Pattern #9
(`theory/meta/methodology_patterns.md`) as a methodology with at
least two distinct instances rather than a single example.

PURE.  No `propext`, no new axiom, no Lean-core dirty lemmas.
-/

namespace E213.Lib.Math.Cohomology.NodupAsClause4

/-! ## §1. Clause-4 reading of list distinctness -/

/-- `l` has a "self-pairing" if some pair of distinct index
    positions carry the same element — the list-level analogue of
    `IsSelfPaired` for naturals.  Clause 4 of the 213 axiom forbids
    `x/x`; lifted to the list-index granularity, this becomes
    "two distinct indices must not map to the same element". -/
def IsListSelfPaired {α : Type u} (l : List α) : Prop :=
  ∃ (i j : Fin l.length), i.val ≠ j.val ∧ l.get i = l.get j

/-- The Clause-4-derived "distinctness" predicate: no self-pairing
    at the list-index level.  This is the recursive-Clause-4
    reading of `List.Nodup`. -/
def IsClause4Nodup {α : Type u} (l : List α) : Prop :=
  ¬ IsListSelfPaired l

/-- `IsClause4Nodup` reformulated as the ∀-form: distinct indices
    map to distinct elements.  Used as the bridge to the inductive
    list structure in §2–§3 below. -/
def IsClause4NodupForall {α : Type u} (l : List α) : Prop :=
  ∀ (i j : Fin l.length), i.val ≠ j.val → l.get i ≠ l.get j

theorem isClause4Nodup_imp_forall {α : Type u} {l : List α}
    (h : IsClause4Nodup l) : IsClause4NodupForall l :=
  fun i j hij heq => h ⟨i, j, hij, heq⟩

theorem forall_imp_isClause4Nodup {α : Type u} {l : List α}
    (h : IsClause4NodupForall l) : IsClause4Nodup l := by
  intro ⟨i, j, hij, heq⟩
  exact h i j hij heq

/-! ## §2. `List.Nodup` ⇒ Clause-4 reading (∀-form) -/

/-- Forward direction (∀-form): standard `List.Nodup` implies
    distinct indices carry distinct elements.  By induction on the
    list, pattern-matching on the `Pairwise` constructor directly
    (no `nodup_cons` simp lemma) to keep the proof PURE. -/
theorem nodup_imp_forall_ne {α : Type u} :
    ∀ {l : List α}, l.Nodup → IsClause4NodupForall l := by
  intro l
  induction l with
  | nil =>
    intro _ i _ _ _
    exact absurd i.isLt (Nat.not_lt_zero _)
  | cons a tail ih =>
    intro hnodup
    cases hnodup with
    | cons hmem htail =>
      intro i j hij heq
      match i, j with
      | ⟨0, _⟩, ⟨0, _⟩ => exact hij rfl
      | ⟨0, _⟩, ⟨k + 1, hk⟩ =>
        have hk' : k < tail.length := Nat.lt_of_succ_lt_succ hk
        have ha : a = tail.get ⟨k, hk'⟩ := heq
        exact hmem _ (List.get_mem tail ⟨k, hk'⟩) ha
      | ⟨k + 1, hk⟩, ⟨0, _⟩ =>
        have hk' : k < tail.length := Nat.lt_of_succ_lt_succ hk
        have ha : a = tail.get ⟨k, hk'⟩ := heq.symm
        exact hmem _ (List.get_mem tail ⟨k, hk'⟩) ha
      | ⟨k + 1, hk⟩, ⟨m + 1, hm⟩ =>
        have hk' : k < tail.length := Nat.lt_of_succ_lt_succ hk
        have hm' : m < tail.length := Nat.lt_of_succ_lt_succ hm
        have hkm : k ≠ m := fun h => hij (congrArg (· + 1) h)
        have heq' : tail.get ⟨k, hk'⟩ = tail.get ⟨m, hm'⟩ := heq
        exact ih htail ⟨k, hk'⟩ ⟨m, hm'⟩ hkm heq'

/-! ## §3. Clause-4 reading ⇒ `List.Nodup` -/

/-- Backward direction (∀-form): distinct indices ⇒ distinct
    elements implies `List.Nodup`.  By induction on the list,
    using `List.get_of_mem` (rather than the propext-bearing
    `mem_iff_get`) and direct `Nat.succ.inj` (rather than
    `Nat.succ_inj'`) to stay PURE. -/
theorem forall_ne_imp_nodup {α : Type u} :
    ∀ {l : List α}, IsClause4NodupForall l → l.Nodup := by
  intro l
  induction l with
  | nil => intro _; exact List.Pairwise.nil
  | cons a tail ih =>
    intro h
    refine List.Pairwise.cons ?_ (ih ?_)
    · intro b hb heq
      obtain ⟨⟨k, hk⟩, hget⟩ := List.get_of_mem hb
      have h0k : (0 : Nat) ≠ k + 1 :=
        fun h0 => Nat.noConfusion h0
      apply h ⟨0, Nat.succ_pos _⟩ ⟨k + 1, Nat.succ_lt_succ hk⟩ h0k
      show a = tail.get ⟨k, hk⟩
      exact heq.trans hget.symm
    · intro ⟨i, hi⟩ ⟨j, hj⟩ hij
      apply h ⟨i + 1, Nat.succ_lt_succ hi⟩ ⟨j + 1, Nat.succ_lt_succ hj⟩
      intro h_eq; exact hij (Nat.succ.inj h_eq)

/-! ## §4. ★★★★★ Capstone — `List.Nodup` IS recursive Clause-4 -/

/-- ★★★★★ **List.Nodup IS the recursive Clause-4 reading.**

    Promotes Pattern #9 (`theory/meta/methodology_patterns.md`)
    from one closed instance (`AliveDerivation.alive_iff_clause4_alive`
    at the binary parity level) to two: the standard list-
    distinctness predicate `List.Nodup` is what Clause 4 of the
    213 axiom (no `x/x`) says when applied recursively at the
    list-index granularity.

    Together with `AliveDerivation`, this establishes the
    recursive-Clause-4-application reading as a research methodology
    rather than a single ad-hoc derivation. -/
theorem nodup_imp_clause4Nodup {α : Type u} {l : List α}
    (h : l.Nodup) : IsClause4Nodup l :=
  forall_imp_isClause4Nodup (nodup_imp_forall_ne h)

theorem clause4Nodup_imp_nodup {α : Type u} {l : List α}
    (h : IsClause4Nodup l) : l.Nodup :=
  forall_ne_imp_nodup (isClause4Nodup_imp_forall h)

/-- ★★★★★ **Iff capstone**: `List.Nodup` IS the recursive
    Clause-4 reading.  Built from the two direction theorems via
    `Iff.intro`, which does not invoke `propext`. -/
theorem nodup_iff_clause4Nodup {α : Type u} {l : List α} :
    l.Nodup ↔ IsClause4Nodup l :=
  ⟨nodup_imp_clause4Nodup, clause4Nodup_imp_nodup⟩

/-! ## §5. Sanity check at small examples -/

/-- Empty list: Nodup, no self-pairing. -/
theorem nodup_nil_clause4 : IsClause4Nodup ([] : List Nat) :=
  nodup_imp_clause4Nodup List.Pairwise.nil

/-- Three-element list with duplicate: not Clause-4-Nodup, with
    explicit self-pairing witness at indices 0 and 2. -/
theorem self_paired_dup : IsListSelfPaired ([1, 2, 1] : List Nat) :=
  ⟨⟨0, by decide⟩, ⟨2, by decide⟩, by decide, rfl⟩

end E213.Lib.Math.Cohomology.NodupAsClause4
