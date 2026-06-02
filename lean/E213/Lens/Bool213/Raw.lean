import E213.Theory.Raw.API

/-!
# Lens.Bool213.Raw — closed-universe Bool (Method A: T=a, F=b)

Bool is not imported as an external type; instead, two specific
Raw shapes encode it.  The operations are also closed: `Raw → Raw`
or `Raw → Raw → Raw`.

Lens meaning: **the `Raw.fold T F and` closed-Raw codomain
catamorphism** (`booleanProj`) — a Raw-internal vertical projection
onto the two-element canonical form `{T, F}`.

**Note (Option C refactor,)**: previously this header
cited `Nat213.leavesCountRaw` as the parallel construction.  That
projection has since been deleted (the Nat213 chart no longer
carries a Raw-side projection — `Lens.leaves.view` projects to
`Nat` directly).  Bool213 keeps its Raw-side `booleanProj` because
the canonical form `{T, F}` *is* the Raw image (both T and F are
themselves Raws), so projecting to Raw and to "the two-element
set" are the same thing.

## Infinitely many Bool213 systems (any T ≠ F pair)

Default choices:
  - Method A: T = Raw.a, F = Raw.b  (canonical)
  - Method B: T = Raw.b, F = Raw.a  (swap)

Other `(T, F)` pairs (e.g. T = `slash a b`, F = `a`) give the same
algebraic structure — collected in `Lens.Bool213.System` as a
NumberingSystem-style meta-pattern.
-/

namespace E213.Lens.Bool213.Raw

open E213.Theory E213.Theory.Raw.Endomorphic
open E213.Term.Internal (Tree)

/-! ### Method A: T = a, F = b (canonical) -/

/-- Raw encoding of "true" (Method A). -/
def T : Raw := Raw.a

/-- Raw encoding of "false" (Method A). -/
def F : Raw := Raw.b

/-- The two encodings are distinct Raws — `Raw.a` and `Raw.b` are
    different canonical Trees. -/
theorem T_ne_F : T ≠ F := by
  unfold T F
  intro h
  -- Raw is `Subtype { t : Tree // canonical }`; the two `.val`s differ.
  have hval : (Raw.a.val) = (Raw.b.val) := congrArg Subtype.val h
  exact E213.Term.Internal.Tree.noConfusion hval

/-! ### Bool213 operations (closed: Raw → Raw or Raw² → Raw) -/

/-- Whether `r` is a valid Bool213 — `T` or `F`. -/
def isBool (r : Raw) : Bool :=
  decide (r = T) || decide (r = F)

/-- `not` = swap.  Since `swap a = b` and `swap b = a`, this is the
    existing `Raw.swap` directly. -/
def not : Raw → Raw := Raw.swap

theorem not_T : not T = F := rfl
theorem not_F : not F = T := rfl

/-- `not (not r) = r` — borrowed directly from `Raw.swap`'s
    involution. -/
theorem not_not (r : Raw) : not (not r) = r := Raw.swap_swap r

/-- `and` — table-defined on Raw².  Under Method A (T = a, F = b),
    `and x y = T iff x = T ∧ y = T`. -/
def and (x y : Raw) : Raw :=
  if decide (x = T) ∧ decide (y = T) then T else F

/-- `and` truth table at (T, T), (T, F), (F, T), (F, F) bundled
    in one statement.  The four `_TT/_TF/_FT/_FF` cases compute
    by `unfold and; decide`. -/
theorem and_truth_table :
    and T T = T ∧ and T F = F ∧ and F T = F ∧ and F F = F := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold and; decide)

/-- `and` is commutative on every Raw input — `if`-branches match. -/
theorem and_comm (x y : Raw) : and x y = and y x := by
  unfold and
  by_cases hxT : x = T
  · subst hxT
    by_cases hyT : y = T
    · subst hyT; rfl
    · rw [if_neg, if_neg]
      · rintro ⟨h1, _⟩; exact hyT (of_decide_eq_true h1)
      · rintro ⟨_, h2⟩; exact hyT (of_decide_eq_true h2)
  · by_cases hyT : y = T
    · subst hyT
      rw [if_neg, if_neg]
      · rintro ⟨_, h2⟩; exact hxT (of_decide_eq_true h2)
      · rintro ⟨h1, _⟩; exact hxT (of_decide_eq_true h1)
    · rw [if_neg, if_neg]
      · rintro ⟨h1, _⟩; exact hyT (of_decide_eq_true h1)
      · rintro ⟨h1, _⟩; exact hxT (of_decide_eq_true h1)

/-! ### Vertical-internal projection — Raw → Bool213 canonical form

The Bool-side vertical-internal projection: collapse any Raw onto
one of the two Bool213 canonical forms (T, F).

Definition: `booleanProj := Raw.fold T F and` — universal-true form,
returns T iff every leaf is T; F if any leaf is F.

Properties:
  1. closure:     `booleanProj r ∈ {T, F}`  (for every r)
  2. idempotence: `booleanProj² = booleanProj`  (for every r)

This is the precise statement of the Bool-side vertical-internal
projection — the Raw-side projection pattern for Bool213.  (For
Nat213, ℕ₊ projects to the codomain `Nat` rather than back to
Raw.) -/

/-- The Bool-side vertical-internal projection —
    Raw → Bool213 canonical form. -/
def booleanProj : Raw → Raw := Raw.fold T F and

theorem booleanProj_T : booleanProj T = T := rfl
theorem booleanProj_F : booleanProj F = F := rfl

/-- The output of `and` is always T or F (by definition). -/
theorem and_isBool (x y : Raw) : and x y = T ∨ and x y = F := by
  unfold and
  split
  · left; rfl
  · right; rfl

/-- **Closure**: `booleanProj r ∈ {T, F}` for any Raw r.  Tree
    induction; the slash branch closes via `and_isBool`. -/
theorem booleanProj_isBool (r : Raw) :
    booleanProj r = T ∨ booleanProj r = F := by
  show Tree.fold T F and r.val = T ∨ Tree.fold T F and r.val = F
  generalize r.val = t
  induction t with
  | a => left; rfl
  | b => right; rfl
  | slash _ _ _ _ =>
      -- Tree.fold T F and (slash x y) = and (Tree.fold _ x) (Tree.fold _ y)
      show and _ _ = T ∨ and _ _ = F
      exact and_isBool _ _

/-- **Idempotence**: `booleanProj (booleanProj r) = booleanProj r`.
    Immediate from closure — `booleanProj r` is already T or F. -/
theorem booleanProj_idempotent (r : Raw) :
    booleanProj (booleanProj r) = booleanProj r := by
  rcases booleanProj_isBool r with h | h
  · rw [h]; exact booleanProj_T
  · rw [h]; exact booleanProj_F

/-! ### Fixed-point characterisation — Bool213 image is exactly
    `booleanProj`'s fixed-point set.

The vertical-internal projection on each of the three domains
(Nat213, Bool213, RawCut) follows the same meta-pattern: closure
+ idempotence + image-fixed-point ↔.  This section closes the
↔ direction on the Bool213 side. -/

/-- Raw `r` is in the Bool213 image — `r = T` or `r = F`. -/
def IsBool213 (r : Raw) : Prop := r = T ∨ r = F

/-- **Fixed-point characterisation**: `booleanProj` leaves `r`
    unchanged iff `r` is in Bool213 (`{T, F}`).  Parallel to
    RawCut's `cutBooleanProj_id_iff_isBool`. -/
theorem booleanProj_id_iff_isBool213 (r : Raw) :
    booleanProj r = r ↔ IsBool213 r := by
  refine ⟨?_, ?_⟩
  · -- booleanProj-fixed → Bool213
    intro h
    rcases booleanProj_isBool r with hT | hF
    · left; rw [← h]; exact hT
    · right; rw [← h]; exact hF
  · -- Bool213 → booleanProj-fixed
    rintro (hT | hF)
    · rw [hT]; exact booleanProj_T
    · rw [hF]; exact booleanProj_F

/-! ### Boundary mapping — Bool213 → Lean Bool

Parallel to Nat213's `value : Raw → Nat`: the Bool-side boundary
projection.

`boolValue := Raw.fold true false (·&&·)` — universal-true form,
true iff every leaf is `a`.

Properties (vertical-external isomorphism):
  - `boolValue T = true`, `boolValue F = false`  (base)
  - `boolValue ∘ booleanProj = boolValue`         (commutativity
    with vertical-internal)

This is the Bool case of isomorphism #3 (vertical-external,
Raw → Lean type) among G84's four isomorphisms.  Parallel to
post-Option-C Nat213's `Raw.value` — but the Nat213 side projects
straight to Nat without an intermediate Raw-internal step
(`seed/CLOSED_FORM_SPEC.md`). -/

/-- Boundary mapping — Bool213 universe → Lean Bool.
    Universal-true form. -/
def boolValue : Raw → Bool := Raw.fold true false (· && ·)

theorem boolValue_T : boolValue T = true := rfl
theorem boolValue_F : boolValue F = false := rfl

/-- Helper: tree induction shows `Tree.fold T F and t` (with α = Raw)
    is always T or F. -/
private theorem fold_T_F_and_isBool (t : Tree) :
    Tree.fold (α := Raw) T F and t = T ∨ Tree.fold (α := Raw) T F and t = F := by
  induction t with
  | a => left; rfl
  | b => right; rfl
  | slash _ _ _ _ => exact and_isBool _ _

/-- Helper: `boolValue (and X Y)` is the product when X, Y ∈ {T, F}. -/
private theorem boolValue_and_of_isBool (x y : Raw)
    (hx : x = T ∨ x = F) (hy : y = T ∨ y = F) :
    boolValue (and x y) = (boolValue x && boolValue y) := by
  rcases hx with hxT | hxF
  · rcases hy with hyT | hyF
    · subst hxT; subst hyT; decide
    · subst hxT; subst hyF; decide
  · rcases hy with hyT | hyF
    · subst hxF; subst hyT; decide
    · subst hxF; subst hyF; decide

/-- **Boundary commutativity**: `boolValue (booleanProj r) = boolValue r`
    for any Raw r.  Compatibility of the vertical-external
    isomorphism with the vertical-internal projection. -/
theorem boolValue_booleanProj (r : Raw) :
    boolValue (booleanProj r) = boolValue r := by
  show boolValue (Tree.fold (α := Raw) T F and r.val)
     = Tree.fold true false (· && ·) r.val
  generalize r.val = t
  induction t with
  | a => rfl
  | b => rfl
  | slash x y ihx ihy =>
      show boolValue (and (Tree.fold _ _ _ x) (Tree.fold _ _ _ y))
         = ((Tree.fold true false (· && ·) x) && (Tree.fold true false (· && ·) y))
      rw [boolValue_and_of_isBool _ _ (fold_T_F_and_isBool x) (fold_T_F_and_isBool y),
          ihx, ihy]

/-! ### `or` operator + De Morgan (, iteration #8)

Parallel to `and`: `or x y = T` iff at least one of `x, y` is `T`.
Closure under `{T, F}` (the canonical form image) gives a Boolean
algebra structure on the Bool213 canonical-form image.  -/

/-- `or` operator on Raw — companion to `and`.  Returns `T` if at
    least one of `x, y` is `T`, else `F`. -/
def or (x y : Raw) : Raw :=
  if decide (x = T) ∨ decide (y = T) then T else F

/-- `or` truth table bundled (parallel to `and_truth_table`). -/
theorem or_truth_table :
    or T T = T ∧ or T F = T ∧ or F T = T ∧ or F F = F := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (unfold or; decide)

/-- `or` is commutative on every Raw input. -/
theorem or_comm (x y : Raw) : or x y = or y x := by
  unfold or
  by_cases hxT : x = T
  · subst hxT
    by_cases hyT : y = T
    · subst hyT; rfl
    · rw [if_pos, if_pos]
      · right; exact decide_eq_true rfl
      · left;  exact decide_eq_true rfl
  · by_cases hyT : y = T
    · subst hyT
      rw [if_pos, if_pos]
      · left;  exact decide_eq_true rfl
      · right; exact decide_eq_true rfl
    · rw [if_neg, if_neg]
      · rintro (h1 | h2)
        · exact hyT (of_decide_eq_true h1)
        · exact hxT (of_decide_eq_true h2)
      · rintro (h1 | h2)
        · exact hxT (of_decide_eq_true h1)
        · exact hyT (of_decide_eq_true h2)

/-- `or` output is always `T` or `F`. -/
theorem or_isBool (x y : Raw) : or x y = T ∨ or x y = F := by
  unfold or
  split
  · left;  rfl
  · right; rfl

/-- **De Morgan (and side)**: `not (and x y) = or (not x) (not y)` for
    Bool213 inputs.  Direct 4-case enumeration. -/
theorem demorgan_and (x y : Raw)
    (hx : IsBool213 x) (hy : IsBool213 y) :
    not (and x y) = or (not x) (not y) := by
  rcases hx with hxT | hxF <;> rcases hy with hyT | hyF
  · subst hxT; subst hyT; decide
  · subst hxT; subst hyF; decide
  · subst hxF; subst hyT; decide
  · subst hxF; subst hyF; decide

/-- **De Morgan (or side)**: `not (or x y) = and (not x) (not y)` for
    Bool213 inputs. -/
theorem demorgan_or (x y : Raw)
    (hx : IsBool213 x) (hy : IsBool213 y) :
    not (or x y) = and (not x) (not y) := by
  rcases hx with hxT | hxF <;> rcases hy with hyT | hyF
  · subst hxT; subst hyT; decide
  · subst hxT; subst hyF; decide
  · subst hxF; subst hyT; decide
  · subst hxF; subst hyF; decide

/-! ### Boolean lattice laws (, iteration #11)

Idempotence, distributivity, absorption — complete the Boolean
lattice axioms on the Bool213 image.  Together with `and_comm`,
`or_comm`, and the De Morgan laws above, these give a Boolean
algebra structure on `{T, F}` under the chosen Method A encoding. -/

/-- `and x x = x` for Bool213 inputs. -/
theorem and_idem (x : Raw) (hx : IsBool213 x) : and x x = x := by
  rcases hx with hT | hF
  · subst hT; decide
  · subst hF; decide

/-- `or x x = x` for Bool213 inputs. -/
theorem or_idem (x : Raw) (hx : IsBool213 x) : or x x = x := by
  rcases hx with hT | hF
  · subst hT; decide
  · subst hF; decide

/-- Distributivity of `and` over `or`. -/
theorem and_distrib_or (x y z : Raw)
    (hx : IsBool213 x) (hy : IsBool213 y) (hz : IsBool213 z) :
    and x (or y z) = or (and x y) (and x z) := by
  rcases hx with hxT | hxF <;> rcases hy with hyT | hyF <;> rcases hz with hzT | hzF
  all_goals (try (subst hxT)); all_goals (try (subst hxF))
  all_goals (try (subst hyT)); all_goals (try (subst hyF))
  all_goals (try (subst hzT)); all_goals (try (subst hzF))
  all_goals decide

/-- Distributivity of `or` over `and`. -/
theorem or_distrib_and (x y z : Raw)
    (hx : IsBool213 x) (hy : IsBool213 y) (hz : IsBool213 z) :
    or x (and y z) = and (or x y) (or x z) := by
  rcases hx with hxT | hxF <;> rcases hy with hyT | hyF <;> rcases hz with hzT | hzF
  all_goals (try (subst hxT)); all_goals (try (subst hxF))
  all_goals (try (subst hyT)); all_goals (try (subst hyF))
  all_goals (try (subst hzT)); all_goals (try (subst hzF))
  all_goals decide

/-- Absorption: `and x (or x y) = x` for Bool213 inputs. -/
theorem and_or_absorb (x y : Raw) (hx : IsBool213 x) (hy : IsBool213 y) :
    and x (or x y) = x := by
  rcases hx with hxT | hxF <;> rcases hy with hyT | hyF
  all_goals (first | (subst hxT) | (subst hxF))
  all_goals (first | (subst hyT) | (subst hyF))
  all_goals decide

/-- Absorption: `or x (and x y) = x` for Bool213 inputs. -/
theorem or_and_absorb (x y : Raw) (hx : IsBool213 x) (hy : IsBool213 y) :
    or x (and x y) = x := by
  rcases hx with hxT | hxF <;> rcases hy with hyT | hyF
  all_goals (first | (subst hxT) | (subst hxF))
  all_goals (first | (subst hyT) | (subst hyF))
  all_goals decide

/-! ### Boolean-algebra completion — complement, identity/null, associativity

With the commutativity / idempotence / distributivity / absorption / De Morgan laws above,
these complete the equational laws of the two-element Boolean algebra on `{T, F}`: `and` /
`or` the meet / join, `T` / `F` the bounds, `not` the complement.  (These are the equational
laws, proved by the same `{T,F}` case-split; no `BooleanAlgebra` typeclass is constructed.) -/

/-- Complement: `and x (not x) = F` for Bool213 inputs (`x ∧ ¬x = ⊥`). -/
theorem and_compl (x : Raw) (hx : IsBool213 x) : and x (not x) = F := by
  rcases hx with hT | hF
  · subst hT; decide
  · subst hF; decide

/-- Complement: `or x (not x) = T` for Bool213 inputs (`x ∨ ¬x = ⊤`). -/
theorem or_compl (x : Raw) (hx : IsBool213 x) : or x (not x) = T := by
  rcases hx with hT | hF
  · subst hT; decide
  · subst hF; decide

/-- Identity: `and x T = x` — `T` is the `∧`-unit. -/
theorem and_T_right (x : Raw) (hx : IsBool213 x) : and x T = x := by
  rcases hx with hT | hF
  · subst hT; decide
  · subst hF; decide

/-- Null: `and x F = F` — `F` is the `∧`-zero. -/
theorem and_F_right (x : Raw) (hx : IsBool213 x) : and x F = F := by
  rcases hx with hT | hF
  · subst hT; decide
  · subst hF; decide

/-- Identity: `or x F = x` — `F` is the `∨`-unit. -/
theorem or_F_right (x : Raw) (hx : IsBool213 x) : or x F = x := by
  rcases hx with hT | hF
  · subst hT; decide
  · subst hF; decide

/-- Null: `or x T = T` — `T` is the `∨`-zero. -/
theorem or_T_right (x : Raw) (hx : IsBool213 x) : or x T = T := by
  rcases hx with hT | hF
  · subst hT; decide
  · subst hF; decide

/-- Associativity of `and` on Bool213 inputs. -/
theorem and_assoc213 (x y z : Raw)
    (hx : IsBool213 x) (hy : IsBool213 y) (hz : IsBool213 z) :
    and (and x y) z = and x (and y z) := by
  rcases hx with hxT | hxF <;> rcases hy with hyT | hyF <;> rcases hz with hzT | hzF
  all_goals (try (subst hxT)); all_goals (try (subst hxF))
  all_goals (try (subst hyT)); all_goals (try (subst hyF))
  all_goals (try (subst hzT)); all_goals (try (subst hzF))
  all_goals decide

/-- Associativity of `or` on Bool213 inputs. -/
theorem or_assoc213 (x y z : Raw)
    (hx : IsBool213 x) (hy : IsBool213 y) (hz : IsBool213 z) :
    or (or x y) z = or x (or y z) := by
  rcases hx with hxT | hxF <;> rcases hy with hyT | hyF <;> rcases hz with hzT | hzF
  all_goals (try (subst hxT)); all_goals (try (subst hxF))
  all_goals (try (subst hyT)); all_goals (try (subst hyF))
  all_goals (try (subst hzT)); all_goals (try (subst hzF))
  all_goals decide

/-- ★★ **The two-element Boolean-algebra laws hold on `{T, F}`.**  Complement
    (`and_compl`/`or_compl`), identity (`and_T_right`/`or_F_right`), and null
    (`and_F_right`/`or_T_right`) for a Bool213 input — together with commutativity,
    idempotence, distributivity, absorption, De Morgan, and associativity
    (`and_assoc213`/`or_assoc213`), the complete equational signature of the two-element
    Boolean algebra (`{T,F}, ∧, ∨, ¬, ⊥=F, ⊤=T`). -/
theorem bool213_boolean_algebra_laws (x : Raw) (hx : IsBool213 x) :
    and x (not x) = F ∧ or x (not x) = T
    ∧ and x T = x ∧ or x F = x
    ∧ and x F = F ∧ or x T = T :=
  ⟨and_compl x hx, or_compl x hx, and_T_right x hx, or_F_right x hx,
   and_F_right x hx, or_T_right x hx⟩

/-- **`boolValue` injectivity on the Bool213 image**: distinct
    Bool213 elements have distinct `boolValue`s.  Direct 4-case
    enumeration.  Combined with surjectivity onto `{true, false}`
    via `boolValue_T` / `boolValue_F`, this gives a bijection
    `IsBool213 ↔ Bool`. -/
theorem boolValue_injective_on_isBool {x y : Raw}
    (hx : IsBool213 x) (hy : IsBool213 y)
    (h : boolValue x = boolValue y) : x = y := by
  rcases hx with hxT | hxF <;> rcases hy with hyT | hyF
  · subst hxT; subst hyT; rfl
  · subst hxT; subst hyF
    exact absurd h (by decide)
  · subst hxF; subst hyT
    exact absurd h (by decide)
  · subst hxF; subst hyF; rfl

end E213.Lens.Bool213.Raw
