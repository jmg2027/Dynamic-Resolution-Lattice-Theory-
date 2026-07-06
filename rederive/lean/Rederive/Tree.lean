/-
Rederive/Tree.lean — the free difference structure (object-primary track, SPEC §1 F-obj).

Carrier: the smallest family containing two atoms `a`, `b` (ORIGIN_RAW §2:
pointing at `a` forces a minimal contrast `b`) and closed under an
*unordered* pairing of two *distinct* members (ORIGIN_RAW §3: the brackets
are the boundary itself; no absolute order; no self-pair).

Encoding of unorderedness WITHOUT quotients (Quot.sound is forbidden by the
program's zero-axiom contract): an ordered inductive `Tree` together with a
total comparison `Tree.cmp`, and a smart constructor `pairing` that sorts
its two children into the canonical order.  Symmetry (`pairing_comm`) and
child-recoverability (`pairing_inj`, `children_pairing`) are then theorems.

Zero dependencies: Lean 4 core only.  Every theorem here must satisfy
`#print axioms` = "does not depend on any axioms" (see Rederive/AxiomCheck.lean).
-/

namespace Rederive

/-- The ordered carrier.  `node` is the *raw* (ordered) pairing; the public
unordered pairing is the smart constructor `pairing` below, which sorts. -/
inductive Tree : Type where
  | a : Tree
  | b : Tree
  | node : Tree → Tree → Tree

namespace Tree

/-- The two atoms are distinct: the first distinction is real (SPEC choice C2). -/
theorem a_ne_b : (Tree.a : Tree) ≠ Tree.b := fun h => Tree.noConfusion h

/-! ## Total comparison -/

/-- Order-reversal on `Ordering` (defined locally to keep the file
self-contained; classical concept: opposite of a linear order). -/
def oswap : Ordering → Ordering
  | .lt => .gt
  | .eq => .eq
  | .gt => .lt

/-- Total comparison: `a < b < node _ _`, nodes lexicographically. -/
def cmp : Tree → Tree → Ordering
  | .a, .a => .eq
  | .a, .b => .lt
  | .a, .node _ _ => .lt
  | .b, .a => .gt
  | .b, .b => .eq
  | .b, .node _ _ => .lt
  | .node _ _, .a => .gt
  | .node _ _, .b => .gt
  | .node l₁ r₁, .node l₂ r₂ =>
    match cmp l₁ l₂ with
    | .lt => .lt
    | .gt => .gt
    | .eq => cmp r₁ r₂

theorem cmp_refl : ∀ x : Tree, cmp x x = .eq
  | .a => rfl
  | .b => rfl
  | .node l r => by
    simp only [cmp]
    rw [cmp_refl l, cmp_refl r]

theorem eq_of_cmp_eq : ∀ (x y : Tree), cmp x y = .eq → x = y
  | .a, .a, _ => rfl
  | .a, .b, h => Ordering.noConfusion h
  | .a, .node _ _, h => Ordering.noConfusion h
  | .b, .a, h => Ordering.noConfusion h
  | .b, .b, _ => rfl
  | .b, .node _ _, h => Ordering.noConfusion h
  | .node _ _, .a, h => Ordering.noConfusion h
  | .node _ _, .b, h => Ordering.noConfusion h
  | .node l₁ r₁, .node l₂ r₂, h => by
    simp only [cmp] at h
    cases hl : cmp l₁ l₂ with
    | lt => rw [hl] at h; exact Ordering.noConfusion h
    | gt => rw [hl] at h; exact Ordering.noConfusion h
    | eq =>
      rw [hl] at h
      rw [eq_of_cmp_eq l₁ l₂ hl, eq_of_cmp_eq r₁ r₂ h]

/-- Antisymmetry of the comparison, in swap form. -/
theorem cmp_oswap : ∀ (x y : Tree), oswap (cmp x y) = cmp y x
  | .a, .a => rfl
  | .a, .b => rfl
  | .a, .node _ _ => rfl
  | .b, .a => rfl
  | .b, .b => rfl
  | .b, .node _ _ => rfl
  | .node _ _, .a => rfl
  | .node _ _, .b => rfl
  | .node l₁ r₁, .node l₂ r₂ => by
    have hl := cmp_oswap l₁ l₂
    have hr := cmp_oswap r₁ r₂
    simp only [cmp]
    cases h : cmp l₁ l₂ with
    | lt =>
      rw [h] at hl
      rw [← hl]; rfl
    | gt =>
      rw [h] at hl
      rw [← hl]; rfl
    | eq =>
      rw [h] at hl
      rw [← hl]
      exact hr

theorem cmp_gt_of_lt {x y : Tree} (h : cmp x y = .lt) : cmp y x = .gt := by
  rw [← cmp_oswap x y, h]; rfl

theorem cmp_lt_of_gt {x y : Tree} (h : cmp x y = .gt) : cmp y x = .lt := by
  rw [← cmp_oswap x y, h]; rfl

/-- Totality: distinct trees compare strictly. -/
theorem cmp_lt_or_gt_of_ne {x y : Tree} (h : x ≠ y) :
    cmp x y = .lt ∨ cmp x y = .gt := by
  cases hc : cmp x y with
  | lt => exact Or.inl rfl
  | gt => exact Or.inr rfl
  | eq => exact absurd (eq_of_cmp_eq x y hc) h

/-! ## The unordered pairing (smart constructor) -/

/-- Unordered pairing: sorts the two children into canonical order.
The `eq` branch is arbitrary — the intended use has `x ≠ y`
(ORIGIN_RAW §3 / SPEC choice C4: no self-pair; nothing exists to
distinguish `x` from `x`). -/
def pairing (x y : Tree) : Tree :=
  match cmp x y with
  | .lt => node x y
  | .eq => node x y
  | .gt => node y x

theorem pairing_of_lt {x y : Tree} (h : cmp x y = .lt) : pairing x y = node x y := by
  unfold pairing; rw [h]

theorem pairing_of_gt {x y : Tree} (h : cmp x y = .gt) : pairing x y = node y x := by
  unfold pairing; rw [h]

/-- **Symmetry law**: the pairing is unordered.  (Holds even without the
distinctness hypothesis, since the `eq` branch forces `x = y`.) -/
theorem pairing_comm (x y : Tree) : pairing x y = pairing y x := by
  cases h : cmp x y with
  | lt => rw [pairing_of_lt h, pairing_of_gt (cmp_gt_of_lt h)]
  | gt => rw [pairing_of_gt h, pairing_of_lt (cmp_lt_of_gt h)]
  | eq => rw [eq_of_cmp_eq x y h]

/-- **Child-recoverability / injectivity on unordered pairs**: two composites
are equal only if they were built from the same unordered pair. -/
theorem pairing_inj {x y u v : Tree} (hxy : x ≠ y) (huv : u ≠ v)
    (h : pairing x y = pairing u v) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  cases cmp_lt_or_gt_of_ne hxy with
  | inl hxyl =>
    rw [pairing_of_lt hxyl] at h
    cases cmp_lt_or_gt_of_ne huv with
    | inl huvl =>
      rw [pairing_of_lt huvl] at h
      injection h with h₁ h₂
      exact Or.inl ⟨h₁, h₂⟩
    | inr huvg =>
      rw [pairing_of_gt huvg] at h
      injection h with h₁ h₂
      exact Or.inr ⟨h₁, h₂⟩
  | inr hxyg =>
    rw [pairing_of_gt hxyg] at h
    cases cmp_lt_or_gt_of_ne huv with
    | inl huvl =>
      rw [pairing_of_lt huvl] at h
      injection h with h₁ h₂
      exact Or.inr ⟨h₂, h₁⟩
    | inr huvg =>
      rw [pairing_of_gt huvg] at h
      injection h with h₁ h₂
      exact Or.inl ⟨h₂, h₁⟩

/-- Contrapositive form: **distinct unordered pairs give distinct composites**. -/
theorem pairing_ne {x y u v : Tree} (hxy : x ≠ y) (huv : u ≠ v)
    (hne : ¬((x = u ∧ y = v) ∨ (x = v ∧ y = u))) :
    pairing x y ≠ pairing u v :=
  fun h => hne (pairing_inj hxy huv h)

/-- Child extraction (partial: atoms have no children). -/
def children : Tree → Option (Tree × Tree)
  | .node l r => some (l, r)
  | _ => none

/-- **The unordered pair `{x, y}` is recoverable from the composite**:
`children` returns it in one of its two orders. -/
theorem children_pairing {x y : Tree} (h : x ≠ y) :
    children (pairing x y) = some (x, y) ∨ children (pairing x y) = some (y, x) := by
  cases cmp_lt_or_gt_of_ne h with
  | inl hl => rw [pairing_of_lt hl]; exact Or.inl rfl
  | inr hg => rw [pairing_of_gt hg]; exact Or.inr rfl

/-- A composite is never an atom: the pairing genuinely creates a *new*
something (ORIGIN_RAW §3: the reified difference is again a something). -/
theorem pairing_ne_a {x y : Tree} (h : x ≠ y) : pairing x y ≠ Tree.a := by
  cases cmp_lt_or_gt_of_ne h with
  | inl hl => rw [pairing_of_lt hl]; exact fun hc => Tree.noConfusion hc
  | inr hg => rw [pairing_of_gt hg]; exact fun hc => Tree.noConfusion hc

theorem pairing_ne_b {x y : Tree} (h : x ≠ y) : pairing x y ≠ Tree.b := by
  cases cmp_lt_or_gt_of_ne h with
  | inl hl => rw [pairing_of_lt hl]; exact fun hc => Tree.noConfusion hc
  | inr hg => rw [pairing_of_gt hg]; exact fun hc => Tree.noConfusion hc

end Tree

end Rederive
