import E213.Term.Tree
import E213.Theory.Raw.Core

/-!
# Theory.Raw.Swap: the swap automorphism + involutivity

Swap preserves canonicality by re-ordering children after
recursive swap.  `Raw.swap_swap` is Theorem 3.2 of the paper.
-/

namespace E213.Theory.Internal

def Tree.swap : Tree → Tree
  | .a         => .b
  | .b         => .a
  | .slash x y =>
      let x' := Tree.swap x
      let y' := Tree.swap y
      match Tree.cmp x' y' with
      | .lt => .slash x' y'
      | .gt => .slash y' x'
      | .eq => x'

theorem Tree.swap_canonical :
    ∀ t : Tree, t.canonical = true → (Tree.swap t).canonical = true := by
  intro t h
  induction t with
  | a => decide
  | b => decide
  | slash x y ihx ihy =>
      unfold Tree.canonical at h
      obtain ⟨hxy, _⟩ := Bool.and_eq_true_to_pair h
      obtain ⟨hx, hy⟩ := Bool.and_eq_true_to_pair hxy
      have ihx' := ihx hx
      have ihy' := ihy hy
      show (match Tree.cmp (Tree.swap x) (Tree.swap y) with
            | .lt => Tree.slash (Tree.swap x) (Tree.swap y)
            | .gt => Tree.slash (Tree.swap y) (Tree.swap x)
            | .eq => Tree.swap x).canonical = true
      split <;> rename_i hcmp
      · unfold Tree.canonical
        rw [ihx', ihy', hcmp]; rfl
      · unfold Tree.canonical
        rw [ihy', ihx', Tree.cmp_gt_to_lt_swap _ _ hcmp]; rfl
      · exact ihx'

end E213.Theory.Internal

namespace E213.Theory.Internal

theorem Tree.swap_swap : ∀ t : Tree,
    (t.canonical = true) → Tree.swap (Tree.swap t) = t := by
  intro t ht
  induction t with
  | a => rfl
  | b => rfl
  | slash x y ihx ihy =>
      unfold Tree.canonical at ht
      obtain ⟨hxy, hlt_raw⟩ := Bool.and_eq_true_to_pair ht
      obtain ⟨hx, hy⟩ := Bool.and_eq_true_to_pair hxy
      have hlt : Tree.cmp x y = .lt := by
        match hmatch : Tree.cmp x y with
        | .lt => rfl
        | .eq => rw [hmatch] at hlt_raw; cases hlt_raw
        | .gt => rw [hmatch] at hlt_raw; cases hlt_raw
      have ihx' := ihx hx
      have ihy' := ihy hy
      -- Tree.swap (Tree.slash x y) reduces by def; need to handle inner cmp
      show Tree.swap (match Tree.cmp (Tree.swap x) (Tree.swap y) with
                      | .lt => Tree.slash (Tree.swap x) (Tree.swap y)
                      | .gt => Tree.slash (Tree.swap y) (Tree.swap x)
                      | .eq => Tree.swap x) = Tree.slash x y
      split <;> rename_i hcmp_inner
      · -- inner cmp .lt: swap of slash (swap x) (swap y) reduces
        show (match Tree.cmp (Tree.swap (Tree.swap x))
                              (Tree.swap (Tree.swap y)) with
              | .lt => Tree.slash (Tree.swap (Tree.swap x))
                                  (Tree.swap (Tree.swap y))
              | .gt => Tree.slash (Tree.swap (Tree.swap y))
                                  (Tree.swap (Tree.swap x))
              | .eq => Tree.swap (Tree.swap x)) = Tree.slash x y
        rw [ihx', ihy', hlt]
      · -- inner cmp .gt: swap of slash (swap y) (swap x)
        show (match Tree.cmp (Tree.swap (Tree.swap y))
                              (Tree.swap (Tree.swap x)) with
              | .lt => Tree.slash (Tree.swap (Tree.swap y))
                                  (Tree.swap (Tree.swap x))
              | .gt => Tree.slash (Tree.swap (Tree.swap x))
                                  (Tree.swap (Tree.swap y))
              | .eq => Tree.swap (Tree.swap y)) = Tree.slash x y
        rw [ihx', ihy']
        have : Tree.cmp y x = .gt := by
          have := Tree.cmp_swap x y
          rw [hlt] at this
          cases hyx : Tree.cmp y x
          all_goals rw [hyx] at this
          all_goals first | rfl | cases this
        rw [this]
      · -- inner cmp .eq: swap x = swap y, hence x = y, contradiction
        exfalso
        have hxy_swap : Tree.swap x = Tree.swap y :=
          Tree.cmp_eq_to_eq _ _ hcmp_inner
        have hxy_eq : x = y := by rw [← ihx', ← ihy', hxy_swap]
        rw [hxy_eq] at hlt
        rw [Tree.cmp_self_eq y] at hlt
        cases hlt

end E213.Theory.Internal

namespace E213.Theory.Internal

-- Extract `cmp x y = .lt` from canonical `slash x y`.
theorem Tree.canonical_slash_lt
    {x y : Tree} (h : Tree.canonical (.slash x y) = true) :
    Tree.cmp x y = .lt := by
  unfold Tree.canonical at h
  obtain ⟨_, hlt_raw⟩ := Bool.and_eq_true_to_pair h
  match hm : Tree.cmp x y with
  | .lt => rfl
  | .eq => rw [hm] at hlt_raw; cases hlt_raw
  | .gt => rw [hm] at hlt_raw; cases hlt_raw

-- On a canonical `slash x y`, the inner-swap `.eq`
-- branch is impossible.
theorem Tree.swap_eq_unreach
    {x y : Tree} (hx : x.canonical = true) (hy : y.canonical = true)
    (hlt : Tree.cmp x y = .lt)
    (hcmp : Tree.cmp (Tree.swap x) (Tree.swap y) = .eq) : False := by
  have ihx' := Tree.swap_swap x hx
  have ihy' := Tree.swap_swap y hy
  have hxy' : Tree.swap x = Tree.swap y := Tree.cmp_eq_to_eq _ _ hcmp
  have hxy : x = y := by rw [← ihx', ← ihy', hxy']
  rw [hxy] at hlt
  rw [Tree.cmp_self_eq y] at hlt
  cases hlt

end E213.Theory.Internal

namespace E213.Theory

open E213.Theory.Internal

def Raw.swap (r : Raw) : Raw :=
  ⟨Tree.swap r.val, Tree.swap_canonical r.val r.property⟩

theorem Raw.swap_a : Raw.swap Raw.a = Raw.b := rfl
theorem Raw.swap_b : Raw.swap Raw.b = Raw.a := rfl

theorem Raw.swap_swap (r : Raw) : Raw.swap (Raw.swap r) = r := by
  apply Subtype.ext
  exact Tree.swap_swap r.val r.property

/-- Raw.swap is injective.  Follows directly from involutivity. -/
theorem Raw.swap_injective {x y : Raw} (h : Raw.swap x = Raw.swap y) : x = y := by
  have hswap : Raw.swap (Raw.swap x) = Raw.swap (Raw.swap y) :=
    congrArg Raw.swap h
  rw [Raw.swap_swap, Raw.swap_swap] at hswap
  exact hswap

end E213.Theory
