import E213.Lib.Math.Cohomology.Cup.RangeFoldXor
import E213.Meta.Tactic.ListHelper

/-!
# Cohomology.Cup.IterErase — iterated `List.eraseIdx` structural lemmas

Foundational PURE lemmas characterising the iteration

  τ_i := (τ_{i-1}).eraseIdx k       τ_0 := τ

for a fixed split position `k`.  The key structural fact:

  for τ = front ++ back with front.length = k,
  iterErase k i (front ++ back) = front ++ back.drop i

This lemma is the structural core of the cup-self-reference depth
catalog's universal codim correspondence at arbitrary `d`.

PURE.
-/

namespace E213.Lib.Math.Cohomology.Cup.IterErase

/-- `iterEraseAt k i τ` — apply `eraseIdx k` to `τ` exactly `i`
    times.  Recursion on the count `i`.  PURE. -/
def iterEraseAt (k : Nat) : Nat → List Nat → List Nat
  | 0, τ => τ
  | i + 1, τ => iterEraseAt k i (τ.eraseIdx k)

/-- ★ **Single eraseIdx of front++back at split position**:
    `(front ++ back).eraseIdx front.length = front ++ back.drop 1`.
    PURE. -/
theorem eraseIdx_front_back_at_len :
    ∀ (front back : List Nat),
      (front ++ back).eraseIdx front.length
      = front ++ back.drop 1 := by
  intro front back
  induction front with
  | nil =>
    show back.eraseIdx 0 = back.drop 1
    cases back with
    | nil => rfl
    | cons _ _ => rfl
  | cons a front' ih =>
    show a :: (front' ++ back).eraseIdx front'.length
       = a :: front' ++ back.drop 1
    rw [ih]
    rfl

/-- ★★★ **Iterated eraseIdx structural lemma**:
    `iterEraseAt k i (front ++ back) = front ++ back.drop i`
    whenever `front.length = k`.  PURE — induction on `i` +
    `eraseIdx_front_back_at_len`. -/
theorem iterErase_front_back :
    ∀ (k i : Nat) (front back : List Nat),
      front.length = k →
      iterEraseAt k i (front ++ back) = front ++ back.drop i := by
  intro k i
  induction i with
  | zero =>
    intro front back _
    show front ++ back = front ++ back.drop 0
    cases back <;> rfl
  | succ i' ih =>
    intro front back h_front
    show iterEraseAt k i' ((front ++ back).eraseIdx k)
       = front ++ back.drop (i' + 1)
    subst h_front
    rw [eraseIdx_front_back_at_len]
    rw [ih front (back.drop 1) rfl]
    congr 1
    cases back with
    | nil =>
      show [].drop i' = ([] : List Nat).drop (i'+1)
      cases i' <;> rfl
    | cons _ bs =>
      show bs.drop i' = (bs.cons _).drop (i'+1)
      rfl

/-! ## §2.  cupList of iterErase — the structural characterisation -/

/-- ★★★★ **cupList factors through iterErase when front has length k**:

    `cupList k l α β (iterEraseAt k i (front ++ back))
        = α front && β (back.drop i)`

    when `front.length = k`.  This is the structural identity
    underlying the codim correspondence — the cup value at the
    `i`-th iteration depends only on `front` (locked) and
    `back.drop i` (the shrinking tail).  PURE. -/
theorem cupList_iterErase_front_back :
    ∀ (k l i : Nat) (front back : List Nat) (α β : List Nat → Bool),
      front.length = k →
      E213.Lib.Math.Cohomology.Cup.LeibnizLexListLevel.cupList k l α β
        (iterEraseAt k i (front ++ back))
      = (α front && β (back.drop i)) := by
  intro k l i front back α β h_front
  subst h_front
  rw [iterErase_front_back front.length i front back rfl]
  show (α ((front ++ back.drop i).take front.length)
        && β ((front ++ back.drop i).drop front.length))
     = (α front && β (back.drop i))
  have h_take :
      (front ++ back.drop i).take front.length = front := by
    have h_step :
        (front ++ back.drop i).take front.length
        = front.take front.length :=
      E213.Tactic.ListHelper.take_append_le front (back.drop i)
        front.length (Nat.le_refl _)
    rw [h_step]
    exact E213.Tactic.ListHelper.take_length_self front
  have h_drop :
      (front ++ back.drop i).drop front.length = back.drop i := by
    have h_step :
        (front ++ back.drop i).drop front.length
        = front.drop front.length ++ back.drop i :=
      E213.Tactic.ListHelper.drop_append_le front (back.drop i)
        front.length (Nat.le_refl _)
    rw [h_step]
    have h_empty : front.drop front.length = [] :=
      E213.Tactic.ListHelper.drop_length_self front
    rw [h_empty]
    rfl
  rw [h_take, h_drop]

end E213.Lib.Math.Cohomology.Cup.IterErase
