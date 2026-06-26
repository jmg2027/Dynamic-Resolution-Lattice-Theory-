import E213.Meta.Tactic.List213

/-!
# `rangeList n = [n−1, …, 0]` with pure `mem` / `Nodup` (∅-axiom)

The full residue list `[0, p)` with **∅-axiom** membership and no-duplication lemmas — the additive-shift
analogue of `EulerTheorem.totativeList`.  Lean-core `List.range`'s `mem_range`/`nodup_range` depend on
`Classical.choice`/`Quot.sound` (axiom-dirty, forbidden), so we rebuild a custom range list with pure
lemmas, exactly as the repo rebuilt `totListUpto` to avoid the dirty core list lemmas.

  * `mem_rangeList`   — `x ∈ rangeList n ↔ x < n`
  * `nodup_rangeList` — `(rangeList n).Nodup`

These feed the **additive-shift permutations** of `[0,p)` (`x ↦ (x+c)%p`) needed for the cubic Gauss
sum's off-diagonal coefficient (A3 route b).
∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.RangeList

/-- `rangeList n = [n−1, n−2, …, 0]` — all naturals below `n`, descending. -/
def rangeList : Nat → List Nat
  | 0 => []
  | n + 1 => n :: rangeList n

/-- ★★★ **Membership** — `x ∈ rangeList n ↔ x < n`.  Pure (no `Classical`). -/
theorem mem_rangeList : ∀ {n x : Nat}, x ∈ rangeList n ↔ x < n
  | 0, x => by
      constructor
      · intro h; nomatch h
      · intro h; exact absurd h (Nat.not_lt_zero x)
  | n + 1, x => by
      show x ∈ (n :: rangeList n) ↔ x < n + 1
      constructor
      · intro h
        cases h with
        | head => exact Nat.lt_succ_self n
        | tail _ h' => exact Nat.lt_succ_of_lt (mem_rangeList.mp h')
      · intro h
        rcases Nat.lt_or_ge x n with hlt | hge
        · exact List.Mem.tail _ (mem_rangeList.mpr hlt)
        · have hxn : x = n := Nat.le_antisymm (Nat.le_of_lt_succ h) hge
          rw [hxn]; exact List.Mem.head _

/-- ★★★ **No duplicates** — `(rangeList n).Nodup`.  Pure: the head `n` exceeds every tail element. -/
theorem nodup_rangeList : ∀ n, (rangeList n).Nodup
  | 0 => List.Pairwise.nil
  | n + 1 => by
      show (n :: rangeList n).Nodup
      refine List.Pairwise.cons (fun y hy => ?_) (nodup_rangeList n)
      have hyn : y < n := mem_rangeList.mp hy
      exact fun heq => Nat.lt_irrefl y (heq ▸ hyn)

/-- `(rangeList n).length = n`. -/
theorem length_rangeList : ∀ n, (rangeList n).length = n
  | 0 => rfl
  | n + 1 => by show (rangeList n).length + 1 = n + 1; rw [length_rangeList n]

end E213.Lib.Math.Combinatorics.RangeList
