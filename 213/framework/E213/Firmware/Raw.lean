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


namespace E213.Firmware

-- ═══ Thm 3.3 — swap bijectivity ═══

theorem Raw.swap_injective : Function.Injective Raw.swap := by
  intro x y h
  have := congrArg Raw.swap h
  rw [Raw.swap_swap, Raw.swap_swap] at this
  exact this

theorem Raw.swap_surjective : Function.Surjective Raw.swap :=
  fun y => ⟨Raw.swap y, Raw.swap_swap y⟩

theorem Raw.swap_bijective : Function.Bijective Raw.swap :=
  ⟨Raw.swap_injective, Raw.swap_surjective⟩

end E213.Firmware


namespace E213.Firmware

-- ═══ Thm 4.5 — catamorphism compatibility with slash ═══

theorem Raw.fold_a {α : Type} (ba bb : α) (c : α → α → α) :
    Raw.fold ba bb c Raw.a = ba := rfl

theorem Raw.fold_b {α : Type} (ba bb : α) (c : α → α → α) :
    Raw.fold ba bb c Raw.b = bb := rfl

/-- **Catamorphism compatibility with `slash`, for symmetric
    `combine`.**  Because `Raw.slash` canonicalises the order of
    its children (the Lean-artifact ordering of §1.2), the
    homomorphism equation for `Raw.fold` holds on `slash` exactly
    when `combine` is symmetric.  This matches the axiom's
    "between" requirement from §1.1. -/
theorem Raw.fold_slash {α : Type}
    (ba bb : α) (c : α → α → α)
    (hsym : ∀ u v : α, c u v = c v u)
    (x y : Raw) (h : x ≠ y) :
    Raw.fold ba bb c (Raw.slash x y h)
      = c (Raw.fold ba bb c x) (Raw.fold ba bb c y) := by
  unfold Raw.slash Raw.fold
  split <;> rename_i hc
  all_goals simp [Tree.fold]
  exact hsym _ _

end E213.Firmware


namespace E213.Firmware

-- ═══ Thm 3.5 — ℤ/2 structure on {id, swap} ═══

/-- `swap ∘ swap = id`: the subgroup `{id, swap}` of the bijection
    monoid of `Raw` is isomorphic to `ℤ/2` (via order-2 element). -/
theorem Raw.swap_comp_swap : Raw.swap ∘ Raw.swap = id := by
  funext r
  exact Raw.swap_swap r

/-- `swap` is not the identity: `swap Raw.a = Raw.b ≠ Raw.a`. -/
theorem Raw.swap_ne_id : Raw.swap ≠ id := by
  intro h
  have : Raw.swap Raw.a = id Raw.a := by rw [h]
  simp [Raw.swap_a] at this
  -- Raw.a ≠ Raw.b
  exact absurd this (by decide)

end E213.Firmware


namespace E213.Firmware

-- ═══ Swap behaviour on depth / leaves ═══

/-- Swap preserves `Tree.depth` (since canonicalisation only
    reorders children, and `depth` uses `max` which is symmetric). -/
private theorem Tree.swap_depth :
    ∀ t : Tree, t.canonical = true → (Tree.swap t).depth = t.depth := by
  intro t h
  induction t with
  | a => rfl
  | b => rfl
  | slash x y ihx ihy =>
      simp only [Tree.canonical, Bool.and_eq_true] at h
      obtain ⟨⟨hx, hy⟩, _⟩ := h
      have ihx' := ihx hx
      have ihy' := ihy hy
      simp only [Tree.swap]
      split
      all_goals simp only [Tree.depth, ihx', ihy', Nat.max_comm]

theorem Raw.swap_depth (r : Raw) : (Raw.swap r).depth = r.depth :=
  Tree.swap_depth r.val r.property

/-- Internal `leaves` on Tree; reproduced here for swap lemma. -/
private def Tree.leaves : Tree → Nat
  | .a         => 1
  | .b         => 1
  | .slash x y => x.leaves + y.leaves

private theorem Tree.swap_leaves :
    ∀ t : Tree, t.canonical = true → (Tree.swap t).leaves = t.leaves := by
  intro t h
  induction t with
  | a => rfl
  | b => rfl
  | slash x y ihx ihy =>
      simp only [Tree.canonical, Bool.and_eq_true] at h
      obtain ⟨⟨hx, hy⟩, _⟩ := h
      have ihx' := ihx hx
      have ihy' := ihy hy
      simp only [Tree.swap]
      split
      all_goals simp only [Tree.leaves, ihx', ihy', Nat.add_comm]

def Raw.leaves (r : Raw) : Nat := r.val.leaves

theorem Raw.swap_leaves (r : Raw) : (Raw.swap r).leaves = r.leaves :=
  Tree.swap_leaves r.val r.property

end E213.Firmware


namespace E213.Firmware

-- ═══ fold = depth / leaves bridges (Meta layer 에서 사용) ═══

private theorem Tree.fold_eq_depth : ∀ t : Tree,
    Tree.fold 0 0 (fun a b => 1 + max a b) t = t.depth := by
  intro t
  induction t with
  | a => rfl
  | b => rfl
  | slash x y ihx ihy =>
      show (1 + max (Tree.fold 0 0 _ x) (Tree.fold 0 0 _ y))
           = 1 + max x.depth y.depth
      rw [ihx, ihy]

theorem Raw.fold_eq_depth (r : Raw) :
    Raw.fold 0 0 (fun a b => 1 + max a b) r = r.depth :=
  Tree.fold_eq_depth r.val

private theorem Tree.fold_eq_leaves : ∀ t : Tree,
    Tree.fold 1 1 (· + ·) t = t.leaves := by
  intro t
  induction t with
  | a => rfl
  | b => rfl
  | slash x y ihx ihy =>
      show (Tree.fold 1 1 _ x + Tree.fold 1 1 _ y) = x.leaves + y.leaves
      rw [ihx, ihy]

theorem Raw.fold_eq_leaves (r : Raw) :
    Raw.fold 1 1 (· + ·) r = r.leaves :=
  Tree.fold_eq_leaves r.val

end E213.Firmware


namespace E213.Firmware

-- ═══ Signed lens-style identity (Meta 에서 사용) ═══

/-- Tree-level: `fold 1 -1 (+) (swap t) = -fold 1 -1 (+) t` on
    canonical `t`. The signed Lens realises swap as negation. -/
private theorem Tree.fold_signed_swap :
    ∀ t : Tree, t.canonical = true →
    Tree.fold (1 : Int) (-1) (· + ·) (Tree.swap t)
      = - Tree.fold (1 : Int) (-1) (· + ·) t := by
  intro t h
  induction t with
  | a => decide
  | b => decide
  | slash x y ihx ihy =>
      simp only [Tree.canonical, Bool.and_eq_true] at h
      obtain ⟨⟨hx, hy⟩, hcmp_raw⟩ := h
      have hcmp_lt : Tree.cmp x y = .lt := by
        match hm : Tree.cmp x y with
        | .lt => rfl
        | .eq => rw [hm] at hcmp_raw; cases hcmp_raw
        | .gt => rw [hm] at hcmp_raw; cases hcmp_raw
      have ihx' := ihx hx
      have ihy' := ihy hy
      simp only [Tree.swap]
      split <;> rename_i hcmp_inner
      · -- .lt branch
        show Tree.fold _ _ _ (Tree.swap x) + Tree.fold _ _ _ (Tree.swap y)
             = -(Tree.fold _ _ _ x + Tree.fold _ _ _ y)
        rw [ihx', ihy']; ring
      · -- .gt branch
        show Tree.fold _ _ _ (Tree.swap y) + Tree.fold _ _ _ (Tree.swap x)
             = -(Tree.fold _ _ _ x + Tree.fold _ _ _ y)
        rw [ihx', ihy']; ring
      · -- .eq branch is unreachable on canonical input
        exfalso
        have hsxy : Tree.swap x = Tree.swap y :=
          (Tree.cmp_eq_iff _ _).mp hcmp_inner
        have hxy : x = y := by
          have := congrArg Tree.swap hsxy
          rw [Tree.swap_swap x hx, Tree.swap_swap y hy] at this
          exact this
        rw [hxy] at hcmp_lt
        have := (Tree.cmp_eq_iff y y).mpr rfl
        rw [this] at hcmp_lt
        cases hcmp_lt

theorem Raw.fold_signed_swap (r : Raw) :
    Raw.fold (1 : Int) (-1) (· + ·) (Raw.swap r)
      = - Raw.fold (1 : Int) (-1) (· + ·) r :=
  Tree.fold_signed_swap r.val r.property

end E213.Firmware
