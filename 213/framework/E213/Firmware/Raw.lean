/-!
# Firmware: Raw API

Implements the 3-clause axiom as a free commutative magma on two
generators with no fixed points, emulated by a canonical-form
subtype. The internal `Tree` type and its ordering are
implementation details and are *not* part of the API.

**Public API (exports):**
- `Raw` (opaque to consumers)
- `Raw.a`, `Raw.b` — the two base somethings
- `Raw.slash : (x y : Raw) → x ≠ y → Raw` — the "distinction"
- `Raw.slash_comm` — symmetric: `x/y = y/x`
- `Raw.rec` — induction principle (clients destructure only via
  this)
- `Raw.depth` — leaves-counted height

**Forbidden to consumers:** `Tree`, `Tree.cmp`, `Tree.canonical`,
`Raw.val`. Downstream code uses `Raw.rec` instead of `match` on
the underlying Tree.
-/

namespace E213.Firmware

-- ═══ Internal (private): ordered tree scaffolding ═══

private inductive Tree : Type
  | a     : Tree
  | b     : Tree
  | slash : Tree → Tree → Tree
  deriving DecidableEq, Repr

private def Tree.cmp : Tree → Tree → Ordering
  | .a,         .a         => .eq
  | .a,         .b         => .lt
  | .a,         .slash _ _ => .lt
  | .b,         .a         => .gt
  | .b,         .b         => .eq
  | .b,         .slash _ _ => .lt
  | .slash _ _, .a         => .gt
  | .slash _ _, .b         => .gt
  | .slash x₁ y₁, .slash x₂ y₂ =>
      match Tree.cmp x₁ x₂ with
      | .eq => Tree.cmp y₁ y₂
      | ord => ord

private def Tree.canonical : Tree → Bool
  | .a         => true
  | .b         => true
  | .slash x y =>
      x.canonical && y.canonical &&
      (match Tree.cmp x y with | .lt => true | _ => false)

end E213.Firmware


namespace E213.Firmware

/-- The firmware type: a canonical-form Raw term. Internal
    structure is sealed; use the API below. -/
def Raw : Type := { t : Tree // t.canonical = true }

instance : DecidableEq Raw := fun ⟨x, _⟩ ⟨y, _⟩ =>
  match decEq x y with
  | .isTrue h  => .isTrue (Subtype.ext h)
  | .isFalse h => .isFalse (fun e => h (congrArg Subtype.val e))

-- Base constants.
def Raw.a : Raw := ⟨.a, rfl⟩
def Raw.b : Raw := ⟨.b, rfl⟩

/-- Lexical helper lemmas (private implementation support). -/
private theorem Tree.cmp_eq_iff (x y : Tree) : Tree.cmp x y = .eq ↔ x = y := by
  induction x generalizing y with
  | a => cases y <;> simp [Tree.cmp]
  | b => cases y <;> simp [Tree.cmp]
  | slash x₁ y₁ ihx ihy =>
      cases y with
      | a => simp [Tree.cmp]
      | b => simp [Tree.cmp]
      | slash x₂ y₂ =>
          simp only [Tree.cmp]
          constructor
          · intro h
            split at h <;> rename_i hc
            · rw [(ihy y₂).mp h]
              rw [show x₁ = x₂ from (ihx x₂).mp hc]
            all_goals (exfalso; exact Ordering.noConfusion h)
          · intro h
            injection h with hx hy
            rw [hx, hy]
            rw [show Tree.cmp x₂ x₂ = .eq from (ihx x₂).mpr rfl]
            exact (ihy y₂).mpr rfl

private theorem Tree.cmp_swap (x y : Tree) :
    Tree.cmp x y = (Tree.cmp y x).swap := by
  induction x generalizing y with
  | a => cases y <;> rfl
  | b => cases y <;> rfl
  | slash x₁ y₁ ihx ihy =>
      cases y with
      | a => rfl
      | b => rfl
      | slash x₂ y₂ =>
          show (match Tree.cmp x₁ x₂ with
                | .eq => Tree.cmp y₁ y₂
                | ord => ord)
              = (match Tree.cmp x₂ x₁ with
                 | .eq => Tree.cmp y₂ y₁
                 | ord => ord).swap
          rw [ihx x₂, ihy y₂]
          cases Tree.cmp x₂ x₁ <;> rfl

private theorem Tree.cmp_gt_iff_lt_swap (x y : Tree) :
    Tree.cmp x y = .gt ↔ Tree.cmp y x = .lt := by
  rw [Tree.cmp_swap x y]
  cases Tree.cmp y x <;> simp [Ordering.swap]

end E213.Firmware


namespace E213.Firmware

-- ═══ Public API: smart constructor ═══

/-- The "distinction" operator: given two **distinct** Raw terms,
    produce their symmetric `slash`. Canonical form is maintained
    internally. -/
def Raw.slash (x y : Raw) (h : x ≠ y) : Raw :=
  match hc : Tree.cmp x.val y.val with
  | .lt => ⟨.slash x.val y.val, by
            simp [Tree.canonical, x.property, y.property, hc]⟩
  | .gt => ⟨.slash y.val x.val, by
            have hlt : Tree.cmp y.val x.val = .lt :=
              (Tree.cmp_gt_iff_lt_swap x.val y.val).mp hc
            simp [Tree.canonical, y.property, x.property, hlt]⟩
  | .eq => absurd ((Tree.cmp_eq_iff _ _).mp hc)
            (fun e => h (Subtype.ext e))

/-- `slash` is symmetric: `x/y = y/x`. This reflects the axiom's
    "between" being directionless at the Raw level. -/
theorem Raw.slash_comm (x y : Raw) (h : x ≠ y) :
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

private def Tree.depth : Tree → Nat
  | .a         => 0
  | .b         => 0
  | .slash x y => 1 + max x.depth y.depth

def Raw.depth (r : Raw) : Nat := r.val.depth

example : Raw.depth Raw.a = 0 := rfl
example : Raw.depth Raw.b = 0 := rfl

end E213.Firmware


namespace E213.Firmware

-- ═══ Public API: catamorphism (for Hypervisor) ═══

private def Tree.fold {α : Type}
    (fa fb : α) (fc : α → α → α) : Tree → α
  | .a         => fa
  | .b         => fb
  | .slash x y => fc (Tree.fold fa fb fc x) (Tree.fold fa fb fc y)

/-- Catamorphism on Raw: the unique homomorphism into `(α, combine)`
    with the given base values for `a, b`. Implementing a Lens is
    a thin wrapper around `Raw.fold`. -/
def Raw.fold {α : Type}
    (base_a : α) (base_b : α) (combine : α → α → α)
    (r : Raw) : α :=
  Tree.fold base_a base_b combine r.val

-- Base cases compute correctly.
example : Raw.fold (0 : Nat) 1 (· + ·) Raw.a = 0 := rfl
example : Raw.fold (0 : Nat) 1 (· + ·) Raw.b = 1 := rfl

end E213.Firmware


namespace E213.Firmware

-- ═══ Public API: swap automorphism ═══

/-- Internal swap with on-the-fly canonicalization.  Base tokens
    exchange; `slash` nodes re-order children after recursive swap
    to preserve the canonical-form invariant. -/
private def Tree.swap : Tree → Tree
  | .a         => .b
  | .b         => .a
  | .slash x y =>
      let x' := Tree.swap x
      let y' := Tree.swap y
      match Tree.cmp x' y' with
      | .lt => .slash x' y'
      | .gt => .slash y' x'
      | .eq => x'  -- unreachable on canonical inputs

/-- Swap preserves the canonical invariant: re-ordering children
    after the recursive swap ensures the output is canonical. -/
private theorem Tree.swap_canonical :
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

/-- Swap on Raw: exchanges the two base somethings, extended
    through `slash` by structural recursion. -/
def Raw.swap (r : Raw) : Raw :=
  ⟨Tree.swap r.val, Tree.swap_canonical r.val r.property⟩

theorem Raw.swap_a : Raw.swap Raw.a = Raw.b := rfl
theorem Raw.swap_b : Raw.swap Raw.b = Raw.a := rfl

end E213.Firmware


namespace E213.Firmware

-- swap is involutive (Theorem 3.2 of PAPER).
private theorem Tree.swap_swap : ∀ t : Tree,
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
      -- Inner match on cmp (swap x) (swap y): three cases
      split <;> rename_i hcmp_inner
      · -- inner .lt: Tree.swap (slash (swap x) (swap y))
        -- = match cmp (swap(swap x)) (swap(swap y))
        -- = match cmp x y = .lt (by hlt + ihx' + ihy')
        simp only [Tree.swap, ihx', ihy', hlt]
      · -- inner .gt: similar but outer is slash (swap y) (swap x)
        simp only [Tree.swap, ihx', ihy']
        -- cmp y x = swap of cmp x y = swap .lt = .gt
        have : Tree.cmp y x = .gt := by
          have := Tree.cmp_swap x y
          rw [hlt] at this; simp [Ordering.swap] at this; exact this.symm
        rw [this]
      · -- inner .eq: cmp (swap x) (swap y) = .eq → swap x = swap y → x = y
        -- But cmp x y = .lt ⟹ x ≠ y (by cmp_eq_iff), swap injective via ihx',ihy' ⟹ contradiction
        exfalso
        have hxy : Tree.swap x = Tree.swap y := (Tree.cmp_eq_iff _ _).mp hcmp_inner
        -- Apply swap again: swap(swap x) = swap(swap y) → x = y
        have : x = y := by rw [← ihx', ← ihy', hxy]
        rw [this] at hlt
        rw [show Tree.cmp y y = .eq from (Tree.cmp_eq_iff _ _).mpr rfl] at hlt
        cases hlt

theorem Raw.swap_swap (r : Raw) : Raw.swap (Raw.swap r) = r := by
  apply Subtype.ext
  exact Tree.swap_swap r.val r.property

end E213.Firmware


namespace E213.Firmware

-- ═══ Level-≤2 enumeration (backing §1.3 of PAPER) ═══

/-- Level 0+1 terms. -/
def Raw.level1_set : List Raw :=
  [Raw.a, Raw.b, Raw.slash Raw.a Raw.b (by decide)]

/-- Level-2 additions (only). -/
def Raw.level2_new : List Raw :=
  [Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide)) (by decide),
   Raw.slash Raw.b (Raw.slash Raw.a Raw.b (by decide)) (by decide)]

-- Counts.
theorem Raw.level1_card : Raw.level1_set.length = 3 := rfl
theorem Raw.level2_new_card : Raw.level2_new.length = 2 := rfl
theorem Raw.level2_total_card :
    (Raw.level1_set ++ Raw.level2_new).length = 5 := rfl

-- The combined list has no duplicates (all 5 distinct).
example : (Raw.level1_set ++ Raw.level2_new).Nodup := by decide

end E213.Firmware
