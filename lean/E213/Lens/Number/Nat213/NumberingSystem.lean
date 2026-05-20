import E213.Lens.Number.Nat213.Raw

/-!
# Lens.Number.Nat213.NumberingSystem — meta pattern over (Z, C) choices

Method A `(Z = a, C = b)` is the simplest numbering.  An arbitrary
pair of distinct Raws `(Z, C)` with `Z ≠ C` yields *another* valid
numbering.  This module captures that meta-pattern.

## Statement

  - `NumberingSystem` = a pair `(Z, C : Raw)` with a witness `Z ≠ C`.
  - Each system has numerals `0, 1, 2, ...` built as a Raw chain.
  - The change-of-system map (Method A → S) is `foldRaw S.Z S.C
    slashOrSelf`.
  - That map sends numerals to numerals — `iso_numeral`.

## Why this matters

In standard mathematics: "the natural numbers are unique up to
isomorphism" (Peano triple isomorphism).  Here: for any pair of
distinguishable Raws (chart selection per `seed/AXIOM/
09_chart_relativity.md` §9.1), `foldRaw` realises an isomorphic
numbering concretely.

Related: this is the chart-relativity claim of
`seed/AXIOM/09_chart_relativity.md` §9.1 instantiated for the
numbering case.  `ChartGeneral.lean` is the closely-related (and
more recent) parameterised-chain construction.
-/

namespace E213.Lens.Number.Nat213.NumberingSystem

open E213.Theory E213.Theory.Raw.Endomorphic

/-- 213-native numbering system: `(Z, C)` is a pair of distinct
    Raws. -/
structure NumberingSystem where
  Z : Raw
  C : Raw
  hZC : Z ≠ C

/-- Successor in system `S` — wrap the previous numeral in `S.C`. -/
def succ (S : NumberingSystem) (n : Raw) : Raw :=
  slashOrSelf n S.C

/-- The `n`-th numeral in system `S`. -/
def numeral (S : NumberingSystem) : Nat → Raw
  | 0     => S.Z
  | n + 1 => succ S (numeral S n)

/-! ### Method A as canonical NumberingSystem -/

/-- Canonical Method A — `Z = Raw.a`, `C = Raw.b`. -/
def methodA : NumberingSystem where
  Z := Raw.a
  C := Raw.b
  hZC := by
    intro h
    have hval : Raw.a.val = Raw.b.val := congrArg Subtype.val h
    exact E213.Term.Internal.Tree.noConfusion hval

/-- The Method A numerals coincide with `Lens.Number.Nat213.Raw.
    numeral`. -/
theorem methodA_numeral_eq_nat213 (n : Nat) :
    numeral methodA n = E213.Lens.Number.Nat213.Raw.numeral n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show succ methodA _ = E213.Lens.Number.Nat213.Raw.succ _
      rw [ih]; rfl

/-! ### Isomorphism via foldRaw

The change-of-system map (Method A → S) sends:
  - `Raw.a = methodA.Z ↦ S.Z`
  - `Raw.b = methodA.C ↦ S.C`
  - the slash node recombines via `slashOrSelf`

This map is exactly `foldRaw S.Z S.C slashOrSelf`. -/

/-- Method A → S isomorphism. -/
def isoFromMethodA (S : NumberingSystem) : Raw → Raw :=
  foldRaw S.Z S.C slashOrSelf

theorem isoFromMethodA_a (S : NumberingSystem) :
    isoFromMethodA S Raw.a = S.Z := rfl

theorem isoFromMethodA_b (S : NumberingSystem) :
    isoFromMethodA S Raw.b = S.C := rfl

/-- Helper: the result of `Raw.slash` is never `Raw.b`.  `Raw.slash`
    produces a canonical `Tree.slash` node, and `Tree.slash ≠
    Tree.b`. -/
private theorem slash_ne_b (x y : Raw) (h : x ≠ y) :
    Raw.slash x y h ≠ Raw.b := by
  intro heq
  have hval : (Raw.slash x y h).val = (Raw.b).val :=
    congrArg Subtype.val heq
  unfold Raw.slash at hval
  split at hval
  · exact E213.Term.Internal.Tree.noConfusion hval
  · exact E213.Term.Internal.Tree.noConfusion hval
  · rename_i hcmp
    exact h (Subtype.ext (E213.Term.Internal.Tree.cmp_eq_to_eq _ _ hcmp))

/-- Helper: every Method A numeral differs from `Raw.b`. -/
theorem numeral_methodA_ne_b (n : Nat) : numeral methodA n ≠ Raw.b := by
  induction n with
  | zero =>
      intro h
      have hval : Raw.a.val = Raw.b.val := congrArg Subtype.val h
      exact E213.Term.Internal.Tree.noConfusion hval
  | succ k ih =>
      show slashOrSelf (numeral methodA k) Raw.b ≠ Raw.b
      rw [slashOrSelf_of_ne ih]
      exact slash_ne_b _ _ ih

/-- **Main isomorphism**: applying `isoFromMethodA S` to the `n`-th
    Method A numeral yields the `n`-th numeral in system `S`.

    This is the precise statement that "any two numbering systems
    are isomorphic" — the closed-universe (Raw-internal) form of
    the Peano triple uniqueness. -/
theorem iso_numeral (S : NumberingSystem) (n : Nat) :
    isoFromMethodA S (numeral methodA n) = numeral S n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      have hne : numeral methodA k ≠ Raw.b := numeral_methodA_ne_b k
      show isoFromMethodA S (slashOrSelf (numeral methodA k) Raw.b)
         = slashOrSelf (numeral S k) S.C
      rw [slashOrSelf_of_ne hne]
      show foldRaw S.Z S.C slashOrSelf
              (Raw.slash (numeral methodA k) Raw.b hne)
         = slashOrSelf (numeral S k) S.C
      rw [foldRaw_slash _ _ _ slashOrSelf_comm _ _ hne]
      show slashOrSelf (isoFromMethodA S (numeral methodA k)) S.C
         = slashOrSelf (numeral S k) S.C
      rw [ih]

end E213.Lens.Number.Nat213.NumberingSystem
