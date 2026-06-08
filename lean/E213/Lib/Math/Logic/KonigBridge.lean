import E213.Lib.Math.Logic.ChildSelection
import E213.Lib.Math.Combinatorics.KonigConditional

/-!
# Reverse Mathematics 213 — GB-cont3: `existsLevel` ↔ the König file's `InfBelow`

Marathon field 17 (`blueprints/math/17_reverse_math_213.md`).

The marathon's native "infinite-below" is `InfB T s := ∀ n, existsLevel T s n = true`
(`existsLevel` = level-existence by Bool recursion).  The König file states it in ∃-form:
`KonigConditional.InfBelow T s := ∀ n, ∃ s', s'.length = n ∧ T (s ++ s') = true`.  Here the
two are proved equivalent (`existsLevel` correctly captures depth-`n` existence), so the LPO
calibration (`lpo_decides_infiniteBelow`, `lpo_infChildExists_downwardClosed`) speaks the
König file's own predicate.  Pure-Lean: `cases` + `Nat.noConfusion` + `Nat.succ.inj` +
`congrArg`, no `propext` (note `Nat.succ.inj`, not `Nat.succ_ne_zero`).
-/

namespace E213.Lib.Math.Logic

/-- `l ++ [] = l`, propext-free (core `List.append_nil` pulls `propext` in this kernel). -/
theorem append_nil_pure : ∀ l : List Bool, l ++ [] = l
  | [] => rfl
  | a :: t => congrArg (a :: ·) (append_nil_pure t)

/-- `(a ++ b) ++ c = a ++ (b ++ c)`, propext-free (core `List.append_assoc` pulls
    `propext`). -/
theorem append_assoc_pure : ∀ a b c : List Bool, (a ++ b) ++ c = a ++ (b ++ c)
  | [], _, _ => rfl
  | x :: a, b, c => congrArg (x :: ·) (append_assoc_pure a b c)

/-- `existsLevel` ⟹ ∃ a depth-`n` node: by induction, reading off the chosen child bit. -/
theorem existsLevel_imp_exists (T : List Bool → Bool) :
    ∀ n s, existsLevel T s n = true → ∃ s', s'.length = n ∧ T (s ++ s') = true := by
  intro n
  induction n with
  | zero =>
    intro s h
    exact ⟨[], rfl, (congrArg T (append_nil_pure s)).trans h⟩
  | succ n ih =>
    intro s h
    rcases or_split _ _ h with hb | hb
    · rcases ih (s ++ [false]) hb with ⟨r, hr, hT⟩
      exact ⟨false :: r, congrArg Nat.succ hr,
             (congrArg T (append_assoc_pure s [false] r)).symm.trans hT⟩
    · rcases ih (s ++ [true]) hb with ⟨r, hr, hT⟩
      exact ⟨true :: r, congrArg Nat.succ hr,
             (congrArg T (append_assoc_pure s [true] r)).symm.trans hT⟩

/-- ∃ a depth-`n` node ⟹ `existsLevel`: split the witness's head bit into the matching
    child, by induction. -/
theorem exists_imp_existsLevel (T : List Bool → Bool) :
    ∀ n s, (∃ s', s'.length = n ∧ T (s ++ s') = true) → existsLevel T s n = true := by
  intro n
  induction n with
  | zero =>
    rintro s ⟨s', hlen, hT⟩
    cases s' with
    | nil => exact (congrArg T (append_nil_pure s)).symm.trans hT
    | cons _ _ => exact Nat.noConfusion hlen
  | succ n ih =>
    rintro s ⟨s', hlen, hT⟩
    cases s' with
    | nil => exact Nat.noConfusion hlen
    | cons b r =>
      have hr : r.length = n := Nat.succ.inj hlen
      have hT' : T ((s ++ [b]) ++ r) = true :=
        (congrArg T (append_assoc_pure s [b] r)).trans hT
      have hchild : existsLevel T (s ++ [b]) n = true := ih (s ++ [b]) ⟨r, hr, hT'⟩
      cases b with
      | false => exact or_intro_left _ _ hchild
      | true => exact or_intro_right _ _ hchild

/-- ★★ **The native infinite-below = the König file's `InfBelow`.**  So the LPO calibration
    of `InfB` transfers verbatim to `KonigConditional.InfBelow`. -/
theorem infB_iff_infBelow (T : List Bool → Bool) (s : List Bool) :
    InfB T s ↔ E213.Lib.Math.Combinatorics.KonigConditional.InfBelow T s :=
  ⟨fun h n => existsLevel_imp_exists T n s (h n),
   fun h n => exists_imp_existsLevel T n s (h n)⟩

end E213.Lib.Math.Logic
