import E213.Firmware.Raw.Cmp

/-!
# Firmware.Raw.Swap: the swap automorphism + involutivity

Swap preserves canonicality by re-ordering children after
recursive swap.  `Raw.swap_swap` is Theorem 3.2 of the paper.

Extracted from monolithic `Raw.lean` (Phase D).
-/

namespace E213.Firmware.Internal

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
      simp only [Tree.canonical, Bool.and_eq_true] at h
      obtain ⟨⟨hx, hy⟩, _⟩ := h
      have ihx' := ihx hx
      have ihy' := ihy hy
      simp only [Tree.swap]
      split <;> rename_i hcmp
      · simp only [Tree.canonical, Bool.and_eq_true, ihx', ihy', true_and]
        rw [hcmp]
      · simp only [Tree.canonical, Bool.and_eq_true, ihx', ihy', true_and]
        rw [(Tree.cmp_gt_iff_lt_swap _ _).mp hcmp]
      · exact ihx'

end E213.Firmware.Internal

namespace E213.Firmware.Internal

theorem Tree.swap_swap : ∀ t : Tree,
    (t.canonical = true) → Tree.swap (Tree.swap t) = t := by
  intro t ht
  induction t with
  | a => rfl
  | b => rfl
  | slash x y ihx ihy =>
      simp only [Tree.canonical, Bool.and_eq_true] at ht
      obtain ⟨⟨hx, hy⟩, hlt_raw⟩ := ht
      have hlt : Tree.cmp x y = .lt := by
        match hmatch : Tree.cmp x y with
        | .lt => rfl
        | .eq => rw [hmatch] at hlt_raw; cases hlt_raw
        | .gt => rw [hmatch] at hlt_raw; cases hlt_raw
      have ihx' := ihx hx
      have ihy' := ihy hy
      simp only [Tree.swap]
      split <;> rename_i hcmp_inner
      · simp only [Tree.swap, ihx', ihy', hlt]
      · simp only [Tree.swap, ihx', ihy']
        have : Tree.cmp y x = .gt := (Tree.cmp_gt_iff_lt_swap y x).mpr hlt
        rw [this]
      · exfalso
        have hxy : Tree.swap x = Tree.swap y :=
          (Tree.cmp_eq_iff _ _).mp hcmp_inner
        have hxy' : x = y := by rw [← ihx', ← ihy', hxy]
        rw [hxy'] at hlt
        rw [show Tree.cmp y y = .eq from (Tree.cmp_eq_iff _ _).mpr rfl] at hlt
        cases hlt

end E213.Firmware.Internal

namespace E213.Firmware.Internal

-- Extract `cmp x y = .lt` from canonical `slash x y`.
theorem Tree.canonical_slash_lt
    {x y : Tree} (h : Tree.canonical (.slash x y) = true) :
    Tree.cmp x y = .lt := by
  simp only [Tree.canonical, Bool.and_eq_true] at h
  obtain ⟨_, hlt_raw⟩ := h
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
  have hxy' : Tree.swap x = Tree.swap y := (Tree.cmp_eq_iff _ _).mp hcmp
  have hxy : x = y := by rw [← ihx', ← ihy', hxy']
  rw [hxy] at hlt
  rw [show Tree.cmp y y = .eq from (Tree.cmp_eq_iff _ _).mpr rfl] at hlt
  cases hlt

end E213.Firmware.Internal

namespace E213.Firmware

open E213.Firmware.Internal

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

end E213.Firmware
