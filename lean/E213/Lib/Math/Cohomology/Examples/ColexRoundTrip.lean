import E213.Lib.Math.Cohomology.Examples.SimplexBasis
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Meta.Tactic.List213
import E213.Meta.Tactic.ListHelper
import E213.Meta.Tactic.NatHelper

import E213.Lib.Physics.Simplex.Counts
/-!
# Colex round-trip — the colex enumeration is a faithful index ↔ subset map

`kSubset n k : Nat → List Nat` enumerates the k-subsets of `{0..n-1}` in colex
order (`Examples/SimplexBasis.lean`); `subsetIdx n k : List Nat → Nat` inverts it
by `List.find?` over `List.range (binom n k)` (`Delta/Core.lean`).  The coboundary
`delta` composes these (remove a face vertex, re-index), so reasoning about
`delta` — and in particular the **dimension-free** `δ²=0`
(`research-notes/frontiers/the_dimension_free_dsquared.md`) — needs the
*round-trip* facts proved here, uniform in `(n, k)`:

  * `kSubset_mem_lt`  — every entry of `kSubset n k i` is `< n` (bounded).
  * `kSubset_length`  — `kSubset n k i` has length `k` (for `i < binom n k`).
  * `kSubset_inj`     — `kSubset n k` is **injective** on `{0..binom n k − 1}`.
  * `subsetIdx_kSubset` — the **forward round-trip** `subsetIdx n k (kSubset n k i) = i`.

The reverse direction `kSubset n k (subsetIdx n k s) = s` (for a sorted in-range
`s`) needs surjectivity of the colex enumeration and is the next step.

All ∅-axiom: structural induction on `n` + the pure `List213` / `ListHelper`
membership / append lemmas; no `funext`, no `decide` over a function space.
-/

namespace E213.Lib.Math.Cohomology.Examples.ColexRoundTrip

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Examples.SimplexBasis (kSubset)
open E213.Lib.Math.Cohomology.Delta.Core (subsetIdx)
open E213.Tactic.List213 (mem_append_iff)
open E213.Tactic.ListHelper (mem_append_singleton mem_append_singleton_right
  append_singleton_inj length_append_singleton)

/-- `b ≤ a → a < c + b → a - b < c`.  Local Nat helper, motive-stable
    (abstract variables, single occurrence) — avoids `▸` on `binom` subterms.
    Uses the propext-free `NatHelper.sub_add_cancel`. -/
private theorem sub_lt_of_lt_add_right {a b c : Nat}
    (hb : b ≤ a) (h : a < c + b) : a - b < c :=
  have hc : a - b + b = a := E213.Tactic.NatHelper.sub_add_cancel hb
  Nat.lt_of_add_lt_add_right (hc.symm ▸ h)

/-- `i < 1 → i = 0`, propext-free (replaces `Nat.lt_one_iff`, which leaks
    `propext` through the `↔`). -/
private theorem lt_one_eq_zero : ∀ {i : Nat}, i < 1 → i = 0
  | 0,     _ => rfl
  | _ + 1, h => absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero _)

/-! ## §1 — entries are bounded -/

/-- Every entry of `kSubset n k i` is `< n`.  Holds for **all** `i` (no range
    hypothesis): the colex recursion only ever appends `n` at level `n+1` and
    recurses into `{0..n-1}`.  Structural induction on `n`. -/
theorem kSubset_mem_lt : ∀ (n k i x : Nat), x ∈ kSubset n k i → x < n := by
  intro n
  induction n with
  | zero =>
    intro k i x hx
    cases k with
    | zero => cases hx
    | succ k => cases hx
  | succ n ih =>
    intro k i x hx
    cases k with
    | zero => cases hx
    | succ k =>
      by_cases hlt : i < binom n (k + 1)
      · have he : kSubset (n + 1) (k + 1) i = kSubset n (k + 1) i := if_pos hlt
        have hxin : x ∈ kSubset n (k + 1) i := he ▸ hx
        exact Nat.lt_succ_of_lt (ih (k + 1) i x hxin)
      · have he : kSubset (n + 1) (k + 1) i
                    = kSubset n k (i - binom n (k + 1)) ++ [n] := if_neg hlt
        have hxin : x ∈ kSubset n k (i - binom n (k + 1)) ++ [n] := he ▸ hx
        rcases mem_append_singleton _ n x hxin with h | h
        · exact Nat.lt_succ_of_lt (ih k (i - binom n (k + 1)) x h)
        · exact h ▸ Nat.lt_succ_self n

/-! ## §2 — length -/

/-- `kSubset n k i` has length `k` whenever `i < binom n k`.  Structural
    induction on `n`; the append branch adds the single vertex `n`. -/
theorem kSubset_length : ∀ (n k i : Nat), i < binom n k → (kSubset n k i).length = k := by
  intro n
  induction n with
  | zero =>
    intro k i hi
    cases k with
    | zero => rfl
    | succ k => exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro k i hi
    cases k with
    | zero => rfl
    | succ k =>
      have hi' : i < binom n k + binom n (k + 1) := hi
      by_cases hlt : i < binom n (k + 1)
      · have he : kSubset (n + 1) (k + 1) i = kSubset n (k + 1) i := if_pos hlt
        exact he ▸ ih (k + 1) i hlt
      · have hge : binom n (k + 1) ≤ i := Nat.le_of_not_lt hlt
        have hsub : i - binom n (k + 1) < binom n k :=
          sub_lt_of_lt_add_right hge hi'
        have he : kSubset (n + 1) (k + 1) i
                    = kSubset n k (i - binom n (k + 1)) ++ [n] := if_neg hlt
        have h1 : (kSubset n k (i - binom n (k + 1)) ++ [n]).length
                    = (kSubset n k (i - binom n (k + 1))).length + 1 :=
          length_append_singleton _ n
        have h2 : (kSubset n k (i - binom n (k + 1))).length = k :=
          ih k (i - binom n (k + 1)) hsub
        exact he ▸ (h1.trans (congrArg (· + 1) h2))

/-! ## §3 — injectivity of the colex enumeration -/

/-- `kSubset n k` is **injective** on the index range `{0..binom n k − 1}`:
    distinct in-range indices enumerate distinct subsets.  This is the key
    combinatorial fact making `(kSubset, subsetIdx)` a faithful index ↔ subset
    correspondence.  Structural induction on `n`; the cross case (one index
    below the Pascal split, one at-or-above) is impossible because the
    at-or-above subset contains the vertex `n`, which `kSubset_mem_lt` forbids
    in the below subset. -/
theorem kSubset_inj : ∀ (n k i j : Nat),
    i < binom n k → j < binom n k → kSubset n k i = kSubset n k j → i = j := by
  intro n
  induction n with
  | zero =>
    intro k i j hi hj _
    cases k with
    | zero =>
      have hi0 : i = 0 := lt_one_eq_zero hi
      have hj0 : j = 0 := lt_one_eq_zero hj
      exact hi0.trans hj0.symm
    | succ k => exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro k i j hi hj heq
    cases k with
    | zero =>
      have hi0 : i = 0 := lt_one_eq_zero hi
      have hj0 : j = 0 := lt_one_eq_zero hj
      exact hi0.trans hj0.symm
    | succ k =>
      have hi' : i < binom n k + binom n (k + 1) := hi
      have hj' : j < binom n k + binom n (k + 1) := hj
      by_cases hil : i < binom n (k + 1) <;> by_cases hjl : j < binom n (k + 1)
      · -- both below split: kSubset n (k+1) i = kSubset n (k+1) j
        have ki : kSubset (n + 1) (k + 1) i = kSubset n (k + 1) i := if_pos hil
        have kj : kSubset (n + 1) (k + 1) j = kSubset n (k + 1) j := if_pos hjl
        have h : kSubset n (k + 1) i = kSubset n (k + 1) j :=
          ki.symm.trans (heq.trans kj)
        exact ih (k + 1) i j hil hjl h
      · -- i below, j at-or-above: j-subset contains n, i-subset does not
        exfalso
        have ki : kSubset (n + 1) (k + 1) i = kSubset n (k + 1) i := if_pos hil
        have kj : kSubset (n + 1) (k + 1) j
                    = kSubset n k (j - binom n (k + 1)) ++ [n] := if_neg hjl
        have h : kSubset n (k + 1) i
                  = kSubset n k (j - binom n (k + 1)) ++ [n] :=
          ki.symm.trans (heq.trans kj)
        have hnmem : n ∈ kSubset n (k + 1) i :=
          h.symm ▸ mem_append_singleton_right _ n
        exact Nat.lt_irrefl n (kSubset_mem_lt n (k + 1) i n hnmem)
      · -- i at-or-above, j below: symmetric
        exfalso
        have ki : kSubset (n + 1) (k + 1) i
                    = kSubset n k (i - binom n (k + 1)) ++ [n] := if_neg hil
        have kj : kSubset (n + 1) (k + 1) j = kSubset n (k + 1) j := if_pos hjl
        have h : kSubset n k (i - binom n (k + 1)) ++ [n]
                  = kSubset n (k + 1) j :=
          ki.symm.trans (heq.trans kj)
        have hnmem : n ∈ kSubset n (k + 1) j :=
          h ▸ mem_append_singleton_right _ n
        exact Nat.lt_irrefl n (kSubset_mem_lt n (k + 1) j n hnmem)
      · -- both at-or-above split: cancel the [n] suffix, recurse at degree k
        have hige : binom n (k + 1) ≤ i := Nat.le_of_not_lt hil
        have hjge : binom n (k + 1) ≤ j := Nat.le_of_not_lt hjl
        have ki : kSubset (n + 1) (k + 1) i
                    = kSubset n k (i - binom n (k + 1)) ++ [n] := if_neg hil
        have kj : kSubset (n + 1) (k + 1) j
                    = kSubset n k (j - binom n (k + 1)) ++ [n] := if_neg hjl
        have h : kSubset n k (i - binom n (k + 1)) ++ [n]
                  = kSubset n k (j - binom n (k + 1)) ++ [n] :=
          ki.symm.trans (heq.trans kj)
        have hcancel : kSubset n k (i - binom n (k + 1))
                        = kSubset n k (j - binom n (k + 1)) :=
          append_singleton_inj _ _ n h
        have hisub : i - binom n (k + 1) < binom n k :=
          sub_lt_of_lt_add_right hige hi'
        have hjsub : j - binom n (k + 1) < binom n k :=
          sub_lt_of_lt_add_right hjge hj'
        have hsubeq : i - binom n (k + 1) = j - binom n (k + 1) :=
          ih k _ _ hisub hjsub hcancel
        -- add the split back to both sides
        have hi2 : (i - binom n (k + 1)) + binom n (k + 1) = i :=
          E213.Tactic.NatHelper.sub_add_cancel hige
        have hj2 : (j - binom n (k + 1)) + binom n (k + 1) = j :=
          E213.Tactic.NatHelper.sub_add_cancel hjge
        have : i = j := by
          have := congrArg (· + binom n (k + 1)) hsubeq
          exact hi2.symm.trans (this.trans hj2)
        exact this

/-! ## §4 — the forward round-trip `subsetIdx (kSubset i) = i`

`subsetIdx n k s` finds `s`'s colex index by `List.find?` over `List.range
(binom n k)`.  The core `List.range` / `List.find?` lemmas leak `propext` /
`Quot.sound`, so §4 first rebuilds the few facts needed **purely** (only
`List.find?_cons` is ∅-axiom out of the box), then closes the round-trip via
`kSubset_inj`. -/

/-- `(a :: as).find? p = some a` when `p a = true` (∅-axiom, `find?` reduction). -/
private theorem find?_cons_true {α} {p : α → Bool} {a : α} {as : List α}
    (h : p a = true) : (a :: as).find? p = some a := by
  show (match p a with | true => some a | false => as.find? p) = some a
  exact h ▸ rfl

/-- `(a :: as).find? p = as.find? p` when `p a = false` (∅-axiom). -/
private theorem find?_cons_false {α} {p : α → Bool} {a : α} {as : List α}
    (h : p a = false) : (a :: as).find? p = as.find? p := by
  show (match p a with | true => some a | false => as.find? p) = as.find? p
  exact h ▸ rfl

/-- If the left list has no match, `find?` falls through to the right.  ∅-axiom
    replacement for `List.find?_append` (which leaks `propext`). -/
private theorem find?_append_none {α} (p : α → Bool) :
    ∀ (l₁ l₂ : List α), l₁.find? p = none → (l₁ ++ l₂).find? p = l₂.find? p
  | [], _, _ => rfl
  | a :: as, l₂, h => by
    cases hpa : p a with
    | true => exact absurd ((find?_cons_true hpa).symm.trans h) (fun e => Option.noConfusion e)
    | false =>
      have hrec : as.find? p = none := (find?_cons_false hpa).symm.trans h
      show (a :: (as ++ l₂)).find? p = l₂.find? p
      exact (find?_cons_false hpa).trans (find?_append_none p as l₂ hrec)

/-- If the left list matches, `find?` returns that match.  ∅-axiom replacement. -/
private theorem find?_append_some {α} (p : α → Bool) :
    ∀ (l₁ l₂ : List α) (x : α), l₁.find? p = some x → (l₁ ++ l₂).find? p = some x
  | [], _, x, h => absurd h (fun e => Option.noConfusion e)
  | a :: as, l₂, x, h => by
    cases hpa : p a with
    | true =>
      have hax : a = x := Option.some.inj ((find?_cons_true hpa).symm.trans h)
      show (a :: (as ++ l₂)).find? p = some x
      exact (find?_cons_true hpa).trans (congrArg some hax)
    | false =>
      have hrec : as.find? p = some x := (find?_cons_false hpa).symm.trans h
      show (a :: (as ++ l₂)).find? p = some x
      exact (find?_cons_false hpa).trans (find?_append_some p as l₂ x hrec)

/-- `find?` of an all-failing list is `none`.  ∅-axiom. -/
private theorem find?_eq_none_of_forall {α} (p : α → Bool) :
    ∀ (l : List α), (∀ x, x ∈ l → p x = false) → l.find? p = none
  | [], _ => rfl
  | a :: as, h => by
    have ha : p a = false := h a (List.Mem.head as)
    exact (find?_cons_false ha).trans
      (find?_eq_none_of_forall p as (fun x hx => h x (List.Mem.tail a hx)))

/-- `List.range.loop n acc = List.range n ++ acc` — the colex enumeration's
    accumulator unrolls to an append.  ∅-axiom (induction on `n`). -/
private theorem range_loop_eq : ∀ (n : Nat) (acc : List Nat),
    List.range.loop n acc = List.range n ++ acc := by
  intro n
  induction n with
  | zero => intro acc; rfl
  | succ n ih =>
    intro acc
    show List.range.loop n (n :: acc) = List.range (n + 1) ++ acc
    have e1 : List.range.loop n (n :: acc) = List.range n ++ (n :: acc) := ih (n :: acc)
    have e2 : List.range (n + 1) = List.range n ++ [n] := by
      show List.range.loop n (n :: []) = List.range n ++ [n]
      exact ih (n :: [])
    have e3 : (List.range n ++ [n]) ++ acc = List.range n ++ (n :: acc) :=
      E213.Tactic.List213.append_assoc (List.range n) [n] acc
    exact e1.trans (e3.symm.trans (congrArg (· ++ acc) e2).symm)

/-- `List.range (m+1) = List.range m ++ [m]` — propext-free. -/
private theorem range_concat (m : Nat) :
    List.range (m + 1) = List.range m ++ [m] := by
  show List.range.loop m (m :: []) = List.range m ++ [m]
  exact range_loop_eq m (m :: [])

/-- Every entry of `List.range m` is `< m` — propext-free (`List.mem_range`
    leaks `propext` + `Quot.sound`). -/
private theorem mem_range_lt : ∀ (x m : Nat), x ∈ List.range m → x < m := by
  intro x m
  induction m with
  | zero => intro hx; cases hx
  | succ m ih =>
    intro hx
    have hx' : x ∈ List.range m ++ [m] := range_concat m ▸ hx
    rcases mem_append_singleton _ m x hx' with h | h
    · exact Nat.lt_succ_of_lt (ih h)
    · exact h ▸ Nat.lt_succ_self m

/-- `find?` over `List.range m` returns the **first** match: if `p i = true` and
    `p j = false` for every `j < i` (and `i < m`), then `(range m).find? p =
    some i`.  ∅-axiom (induction on `m` via `range_concat`). -/
private theorem find?_range_eq_some (p : Nat → Bool) :
    ∀ (m i : Nat), i < m → p i = true → (∀ j, j < i → p j = false) →
      (List.range m).find? p = some i
  | 0, i, hi, _, _ => absurd hi (Nat.not_lt_zero i)
  | m + 1, i, hi, hpi, hbelow => by
    have hcat : List.range (m + 1) = List.range m ++ [m] := range_concat m
    by_cases him : i < m
    · have hrec : (List.range m).find? p = some i :=
        find?_range_eq_some p m i him hpi hbelow
      have hap : (List.range m ++ [m]).find? p = some i :=
        find?_append_some p _ _ i hrec
      exact hcat ▸ hap
    · have hile : i ≤ m := Nat.le_of_lt_succ hi
      have hieq : i = m := Nat.le_antisymm hile (Nat.le_of_not_lt him)
      have hnone : (List.range m).find? p = none :=
        find?_eq_none_of_forall p (List.range m)
          (fun x hx => hbelow x (Nat.lt_of_lt_of_le (mem_range_lt x m hx)
            (Nat.le_of_eq hieq.symm)))
      have hpm : p m = true := hieq ▸ hpi
      have htail : (List.range m ++ [m]).find? p = some m :=
        (find?_append_none p (List.range m) [m] hnone).trans
          (find?_cons_true (a := m) (as := []) hpm)
      have hsome : (List.range m ++ [m]).find? p = some i :=
        htail.trans (congrArg some hieq.symm)
      exact hcat ▸ hsome

/-! ### BEq on `List Nat`, propext-free

The `subsetIdx` predicate uses `==`.  `beq_self_eq_true` / `eq_of_beq` route
through the `LawfulBEq (List Nat)` instance, which depends on `propext` +
`Quot.sound`.  So we rebuild reflexivity and `≠ → false` directly on the
`Nat.beq` / `List.beq` reductions — ∅-axiom. -/

private theorem band_false (x : Bool) : (x && false) = false := by cases x <;> rfl

-- The `BEq Nat` instance here is `instBEqOfDecidableEq`, so `(a == b)` is
-- defeq `decide (a = b)` — route reflexivity / `≠ → false` through `decide`
-- (∅-axiom; avoids the `Nat.beq` form, which this instance is *not*).
private theorem nat_beq_refl (a : Nat) : (a == a) = true :=
  (rfl : (a == a) = decide (a = a)).trans (decide_eq_true rfl)

private theorem nat_beq_false_of_ne (a b : Nat) (h : a ≠ b) : (a == b) = false :=
  (rfl : (a == b) = decide (a = b)).trans (decide_eq_false h)

private theorem list_beq_refl : ∀ (s : List Nat), (s == s) = true
  | []      => rfl
  | a :: as => (congrArg (· && (as == as)) (nat_beq_refl a)).trans (list_beq_refl as)

private theorem list_beq_false_of_ne : ∀ (a b : List Nat), a ≠ b → (a == b) = false
  | [],      [],      h => absurd rfl h
  | [],      _ :: _,  _ => rfl
  | _ :: _,  [],      _ => rfl
  | a :: as, b :: bs, h => by
    by_cases hab : a = b
    · have hasbs : as ≠ bs :=
        fun e => h ((congrArg (· :: as) hab).trans (congrArg (b :: ·) e))
      have h2 : (as == bs) = false := list_beq_false_of_ne as bs hasbs
      show (a == b && (as == bs)) = false
      exact (congrArg (a == b && ·) h2).trans (band_false _)
    · have h1 : (a == b) = false := nat_beq_false_of_ne a b hab
      show (a == b && (as == bs)) = false
      exact congrArg (· && (as == bs)) h1

/-- ★★★ **The forward colex round-trip.**  `subsetIdx n k (kSubset n k i) = i`
    for every in-range index `i < binom n k`: enumerate the `i`-th k-subset,
    look its index back up, recover `i`.  The first match `find?` returns is `i`
    itself, because `kSubset n k` is injective on the range (`kSubset_inj`), so
    no earlier index `j < i` enumerates the same subset.  ∅-axiom. -/
theorem subsetIdx_kSubset (n k i : Nat) (hi : i < binom n k) :
    subsetIdx n k (kSubset n k i) = i := by
  show ((List.range (binom n k)).find?
          (fun j => kSubset n k j == kSubset n k i)).getD (binom n k) = i
  have hpi : (kSubset n k i == kSubset n k i) = true := list_beq_refl _
  have hbelow : ∀ j, j < i → (kSubset n k j == kSubset n k i) = false := by
    intro j hj
    have hjb : j < binom n k := Nat.lt_trans hj hi
    have hne : kSubset n k j ≠ kSubset n k i :=
      fun heq => absurd (kSubset_inj n k j i hjb hi heq) (Nat.ne_of_lt hj)
    exact list_beq_false_of_ne _ _ hne
  have hfind : (List.range (binom n k)).find?
                  (fun j => kSubset n k j == kSubset n k i) = some i :=
    find?_range_eq_some _ (binom n k) i hi hpi hbelow
  exact hfind ▸ rfl

end E213.Lib.Math.Cohomology.Examples.ColexRoundTrip
