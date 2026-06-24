import E213.Theory.Raw.Core
import E213.Term.Tree

/-!
# Theory.Raw.Slash: the Raw smart constructor `slash` + Raw.depth

`Raw.slash` is the *referring* mechanism of §3.2 (selecting a
residue member), not an operator applied to arguments.  The
smart constructor canonicalises child order using `Tree.cmp`;
`Raw.slash_comm` reflects the axiom's directionless "between"
(§9.2 operation/object non-separation — the axiom imposes no
order, so the Tree's apparent (x, y) positions are encoding
artifact, re-unified by canonicalisation).  The `x ≠ y`
precondition enforces §3.2 clause 4 (anti-reflexive — pairing
with self does not create distinction; cf. §4.3).

`Raw.depth` is the basic structural observable (defined via
`Tree.depth` from Term.Internal.Tree.Levels).
-/

namespace E213.Theory

open E213.Term.Internal (Tree)

-- ═══ Public API: smart constructor ═══

protected def Raw.slash (x y : Raw) (h : x ≠ y) : Raw :=
  match hc : Tree.cmp x.val y.val with
  | .lt => ⟨.slash x.val y.val, by
            unfold Tree.canonical
            rw [x.property, y.property, hc]; rfl⟩
  | .gt => ⟨.slash y.val x.val, by
            have hlt : Tree.cmp y.val x.val = .lt :=
              Tree.cmp_gt_to_lt_swap x.val y.val hc
            unfold Tree.canonical
            rw [y.property, x.property, hlt]; rfl⟩
  | .eq => absurd (Tree.cmp_eq_to_eq _ _ hc)
            (fun e => h (Subtype.ext e))

protected theorem Raw.slash_comm (x y : Raw) (h : x ≠ y) :
    Raw.slash x y h = Raw.slash y x (Ne.symm h) := by
  unfold Raw.slash
  have hsw : Tree.cmp x.val y.val = (Tree.cmp y.val x.val).swap :=
    Tree.cmp_swap x.val y.val
  split <;> rename_i hc1 <;> split <;> rename_i hc2 <;>
    (first
      | rfl
      | (exfalso
         rw [hc1, hc2] at hsw
         cases hsw))

-- ═══ Public API: depth ═══

protected def Raw.depth (r : Raw) : Nat := r.val.depth

example : Raw.depth Raw.a = 0 := rfl
example : Raw.depth Raw.b = 0 := rfl

-- ═══ Public API: slash inequality ═══

/-- A canonical `Raw.slash x y h` is never equal to its right child.
    Follows from `Tree.leaves_pos`: the slash adds the leaves of `x`
    (≥ 1) to those of `y`, so the resulting tree has strictly more
    leaves than `y`. -/
protected theorem Raw.slash_ne_right (x y : Raw) (h : x ≠ y) :
    Raw.slash x y h ≠ y := by
  intro heq
  have hval : (Raw.slash x y h).val = y.val := congrArg Subtype.val heq
  -- (Raw.slash x y h).val.leaves = x.val.leaves + y.val.leaves
  -- (by direct computation on the `match` branches of Raw.slash)
  have hsum : (Raw.slash x y h).val.leaves
              = x.val.leaves + y.val.leaves := by
    unfold Raw.slash
    split <;> rename_i hc
    · rfl
    · show y.val.leaves + x.val.leaves = x.val.leaves + y.val.leaves
      exact Nat.add_comm _ _
    · exfalso
      exact h (Subtype.ext (Tree.cmp_eq_to_eq _ _ hc))
  -- y.val.leaves = x.val.leaves + y.val.leaves (substitute hval into hsum)
  -- but x.val.leaves ≥ 1 contradicts this
  rw [hval] at hsum
  have hx_pos : 1 ≤ x.val.leaves := Tree.leaves_pos x.val
  have : y.val.leaves < x.val.leaves + y.val.leaves := by
    calc y.val.leaves
        < y.val.leaves + 1 := Nat.lt_succ_self _
      _ ≤ y.val.leaves + x.val.leaves :=
          Nat.add_le_add_left hx_pos _
      _ = x.val.leaves + y.val.leaves := Nat.add_comm _ _
  rw [← hsum] at this
  exact Nat.lt_irrefl _ this

/-- A canonical `Raw.slash x y h` is never equal to its left child.
    By `slash_comm` + `slash_ne_right`. -/
protected theorem Raw.slash_ne_left (x y : Raw) (h : x ≠ y) :
    Raw.slash x y h ≠ x := by
  rw [Raw.slash_comm x y h]
  exact Raw.slash_ne_right y x (Ne.symm h)

/-- `Raw.slash x y h` is distinct from both arguments. -/
protected theorem Raw.slash_ne_both (x y : Raw) (h : x ≠ y) :
    Raw.slash x y h ≠ x ∧ Raw.slash x y h ≠ y :=
  ⟨Raw.slash_ne_left x y h, Raw.slash_ne_right x y h⟩

/-- A canonical `Raw.slash x y h` is never equal to `Raw.b`.  Both
    branches of `Raw.slash` produce a `Tree.slash` node at the
    Tree level, and `Tree.slash ≠ Tree.b` by `Tree.noConfusion`.
    The `Tree.cmp_eq_to_eq` branch is vacuous (would contradict
    the `x ≠ y` hypothesis). -/
protected theorem Raw.slash_ne_b (x y : Raw) (h : x ≠ y) :
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

/-- A canonical `Raw.slash x y h` is never equal to `Raw.a`.  Same
    pattern as `Raw.slash_ne_b`. -/
protected theorem Raw.slash_ne_a (x y : Raw) (h : x ≠ y) :
    Raw.slash x y h ≠ Raw.a := by
  intro heq
  have hval : (Raw.slash x y h).val = (Raw.a).val :=
    congrArg Subtype.val heq
  unfold Raw.slash at hval
  split at hval
  · exact E213.Term.Internal.Tree.noConfusion hval
  · exact E213.Term.Internal.Tree.noConfusion hval
  · rename_i hcmp
    exact h (Subtype.ext (E213.Term.Internal.Tree.cmp_eq_to_eq _ _ hcmp))

-- ═══ Public API: slash value + pair injectivity ═══

/-- Value of a canonical slash when `cmp` orders the inputs `lt`. -/
protected theorem Raw.slash_val_lt (x y : Raw) (h : x ≠ y)
    (hc : Tree.cmp x.val y.val = .lt) :
    (Raw.slash x y h).val = Tree.slash x.val y.val := by
  unfold Raw.slash
  split
  · rfl
  · rename_i hc'
    exact (E213.Term.Internal.ordNoConf (hc.symm.trans hc') : False).elim
  · rename_i hc'
    exact absurd (Subtype.ext (E213.Term.Internal.Tree.cmp_eq_to_eq _ _ hc')) h

/-- Value of a canonical slash when `cmp` orders the inputs `gt`. -/
protected theorem Raw.slash_val_gt (x y : Raw) (h : x ≠ y)
    (hc : Tree.cmp x.val y.val = .gt) :
    (Raw.slash x y h).val = Tree.slash y.val x.val := by
  unfold Raw.slash
  split
  · rename_i hc'
    exact (E213.Term.Internal.ordNoConf (hc.symm.trans hc') : False).elim
  · rfl
  · rename_i hc'
    exact absurd (Subtype.ext (E213.Term.Internal.Tree.cmp_eq_to_eq _ _ hc')) h

/-- **Pair injectivity**: equal slashes have equal unordered input
    pairs.  The two disjuncts are the direction-free pairing's only
    freedom (clause 3). -/
protected theorem Raw.slash_inj {x y z w : Raw} {h1 : x ≠ y} {h2 : z ≠ w}
    (he : Raw.slash x y h1 = Raw.slash z w h2) :
    (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
  have hv : (Raw.slash x y h1).val = (Raw.slash z w h2).val :=
    congrArg Subtype.val he
  cases hcxy : Tree.cmp x.val y.val with
  | lt =>
    rw [Raw.slash_val_lt x y h1 hcxy] at hv
    cases hczw : Tree.cmp z.val w.val with
    | lt =>
      rw [Raw.slash_val_lt z w h2 hczw] at hv
      injection hv with e1 e2
      exact Or.inl ⟨Subtype.ext e1, Subtype.ext e2⟩
    | gt =>
      rw [Raw.slash_val_gt z w h2 hczw] at hv
      injection hv with e1 e2
      exact Or.inr ⟨Subtype.ext e1, Subtype.ext e2⟩
    | eq =>
      exact absurd
        (Subtype.ext (E213.Term.Internal.Tree.cmp_eq_to_eq _ _ hczw)) h2
  | gt =>
    rw [Raw.slash_val_gt x y h1 hcxy] at hv
    cases hczw : Tree.cmp z.val w.val with
    | lt =>
      rw [Raw.slash_val_lt z w h2 hczw] at hv
      injection hv with e1 e2
      exact Or.inr ⟨Subtype.ext e2, Subtype.ext e1⟩
    | gt =>
      rw [Raw.slash_val_gt z w h2 hczw] at hv
      injection hv with e1 e2
      exact Or.inl ⟨Subtype.ext e2, Subtype.ext e1⟩
    | eq =>
      exact absurd
        (Subtype.ext (E213.Term.Internal.Tree.cmp_eq_to_eq _ _ hczw)) h2
  | eq =>
    exact absurd
      (Subtype.ext (E213.Term.Internal.Tree.cmp_eq_to_eq _ _ hcxy)) h1

end E213.Theory
