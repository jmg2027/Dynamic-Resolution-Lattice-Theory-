/-!
# Group Theory 213 — Free group as a normal-form subtype (colimit/ambient
quotient built ∅-axiom, no `Quot.sound`)

This file is the **Side-A witness** named in
`research-notes/frontiers/colimit_quotient_synthesis.md`: a colimit /
ambient-quotient built ∅-axiom as a *normal-form subtype*, with **no**
`Quot.sound`.  It converts the synthesis memo's Side A from
"buildable in principle" to **built** — the analogue of how the modulated
Banach engine closed the constructive wall.

The cleanest confluent + terminating instance is the **free group word
problem via free reduction** — equivalently π₁ of a wedge of circles
`⋁ S¹` (a graph).  Free reduction repeatedly cancels adjacent
inverse-letter pairs `x · x⁻¹`; it is confluent + terminating, so the
quotient (the free group) *is* the type of freely-reduced words.

## Model

A free-group word is a `List` over a signed-generator alphabet
`Nat × Bool`: `(g, true) = xᵍ`, `(g, false) = (xᵍ)⁻¹`.  Two letters are
*inverse* when they share a generator and differ in sign.

`freeReduce` is a single `List.foldr` (structural recursion on the input
list — **no** `omega`, **no** termination obligation, the implicit ℕ-measure
is the list length consumed by the fold): pushing each letter onto a
running reduced suffix and cancelling on contact with its inverse.  Because
the suffix is always reduced and the new letter cancels at most the head,
one fold pass reaches the normal form directly — `freeReduce` is idempotent.

## The quotient as a Σ-type (no `Quot.sound`)

Mirroring `Lens.Unified.LensImage` / `LensImage.proj_val_eq_iff`:

  * `FreeGroup := {w : FreeWord // Reduced w}`        (normal-form subtype)
  * `proj : FreeWord → FreeGroup := ⟨freeReduce w, …⟩` (canonical section)
  * `proj_val_eq_iff : (proj u).val = (proj v).val ↔ FreeEquiv u v`
      — `Quot.sound`'s content, axiom-free.

`FreeEquiv u v := freeReduce u = freeReduce v` is a groupoid (refl/symm/trans
by `Eq`), and `freeEquiv_iff_reduce_eq` is the **word-problem decision**:
`u ~ v` is decided by `List`-equality of normal forms.

Boot anchors: `Lens/Unified.lean` (`LensImage`, `proj_val_eq_iff`),
`Theory/Raw/Lambek.lean` (ℕ-measure termination archetype).
-/

namespace E213.Lib.Math.Algebra.Group.FreeReduction

/-! ## 1. Alphabet, words, and the inverse-letter test -/

/-- A signed generator: `(g, true) = xᵍ`, `(g, false) = (xᵍ)⁻¹`. -/
abbrev Letter := Nat × Bool

/-- A free-group word: a list of signed generators. -/
abbrev FreeWord := List Letter

/-- The inverse of a letter: same generator, opposite sign. -/
def inv (l : Letter) : Letter := (l.1, !l.2)

/-- `inv` is an involution. -/
theorem inv_inv (l : Letter) : inv (inv l) = l := by
  cases l with
  | mk g s => cases s <;> rfl

/-- Boolean inverse-pair test: `a` and `b` cancel iff same generator,
    opposite sign. -/
def isInv (a b : Letter) : Bool := a.1.beq b.1 && (!(a.2 == b.2))

/-- `Nat.beq n n = true` by structural recursion (propext-free). -/
private theorem natBeqRefl : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => natBeqRefl n

/-- `a` is inverse to its own `inv`. -/
theorem isInv_self_inv (l : Letter) : isInv l (inv l) = true := by
  cases l with
  | mk g s =>
    have hg : Nat.beq g g = true := natBeqRefl g
    cases s with
    | false => show (g.beq g && true) = true; rw [hg]; rfl
    | true => show (g.beq g && true) = true; rw [hg]; rfl

/-! ## 2. The reduced predicate -/

/-- Boolean "freely reduced" test: no two adjacent letters are inverse. -/
def reducedB : FreeWord → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest =>
    match isInv a b with
    | true => false
    | false => reducedB (b :: rest)

/-- `Reduced w`: the word has no adjacent inverse pair (Prop form). -/
def Reduced (w : FreeWord) : Prop := reducedB w = true

/-- The empty word is reduced. -/
theorem reduced_nil : Reduced [] := rfl

/-- A singleton word is reduced. -/
theorem reduced_singleton (l : Letter) : Reduced [l] := rfl

/-- Cons onto a reduced tail, when the new head does not cancel the old
    head, stays reduced. -/
theorem reduced_cons {a b : Letter} {rest : FreeWord}
    (hcancel : isInv a b = false) (htail : Reduced (b :: rest)) :
    Reduced (a :: b :: rest) := by
  show (match isInv a b with | true => false | false => reducedB (b :: rest)) = true
  rw [hcancel]
  exact htail

/-- The tail of a reduced word is reduced. -/
theorem reduced_tail {a : Letter} {rest : FreeWord}
    (h : Reduced (a :: rest)) : Reduced rest := by
  cases rest with
  | nil => exact rfl
  | cons b rest' =>
    have hh : (match isInv a b with
                | true => false
                | false => reducedB (b :: rest')) = true := h
    cases hcase : isInv a b with
    | true => rw [hcase] at hh; exact Bool.noConfusion hh
    | false => rw [hcase] at hh; exact hh

/-! ## 3. One-step push with cancellation, and `freeReduce` -/

/-- Push a letter onto an already-reduced word, cancelling on contact.
    Since the accumulator is reduced, at most the head can cancel — so the
    result is reduced. -/
def push (l : Letter) : FreeWord → FreeWord
  | [] => [l]
  | h :: t =>
    match isInv l h with
    | true => t
    | false => l :: h :: t

/-- **Free reduction**: fold `push` over the word from the right.  The
    accumulator is the reduced normal form of the processed suffix.
    Structural recursion on the input list — no termination obligation. -/
def freeReduce (w : FreeWord) : FreeWord := w.foldr push []

/-! ### `push` preserves reducedness -/

/-- `push` onto a reduced word yields a reduced word. -/
theorem push_reduced (l : Letter) :
    ∀ {w : FreeWord}, Reduced w → Reduced (push l w)
  | [], _ => reduced_singleton l
  | h :: t, hw => by
    show Reduced (match isInv l h with | true => t | false => l :: h :: t)
    cases hcase : isInv l h with
    | true =>
      show Reduced t
      exact reduced_tail hw
    | false =>
      show Reduced (l :: h :: t)
      exact reduced_cons hcase hw

/-- **`freeReduce` produces a reduced word.** -/
theorem freeReduce_reduced (w : FreeWord) : Reduced (freeReduce w) := by
  show Reduced (w.foldr push [])
  induction w with
  | nil => exact reduced_nil
  | cons a rest ih =>
    show Reduced (push a (rest.foldr push []))
    exact push_reduced a ih

/-! ### Idempotence: `freeReduce` fixes reduced words -/

/-- A reduced word is a fixed point of `freeReduce`. -/
theorem freeReduce_fix : ∀ {w : FreeWord}, Reduced w → freeReduce w = w
  | [], _ => rfl
  | [l], _ => rfl
  | a :: b :: rest, hw => by
    have htail : Reduced (b :: rest) := reduced_tail hw
    have hcancel : isInv a b = false := by
      have hh : (match isInv a b with
                  | true => false
                  | false => reducedB (b :: rest)) = true := hw
      cases hcase : isInv a b with
      | false => rfl
      | true => rw [hcase] at hh; exact Bool.noConfusion hh
    show push a ((b :: rest).foldr push []) = a :: b :: rest
    rw [show (b :: rest).foldr push [] = freeReduce (b :: rest) from rfl,
        freeReduce_fix htail]
    show (match isInv a b with | true => rest | false => a :: b :: rest)
          = a :: b :: rest
    rw [hcancel]

/-- **`freeReduce` is idempotent.** -/
theorem freeReduce_idempotent (w : FreeWord) :
    freeReduce (freeReduce w) = freeReduce w :=
  freeReduce_fix (freeReduce_reduced w)

/-! ## 4. The free-group equivalence (a groupoid, no `Quot`) -/

/-- The free-group equivalence: two words are equal iff they share a
    normal form. -/
def FreeEquiv (u v : FreeWord) : Prop := freeReduce u = freeReduce v

/-- Reflexivity. -/
theorem freeEquiv_refl (u : FreeWord) : FreeEquiv u u := rfl

/-- Symmetry. -/
theorem freeEquiv_symm {u v : FreeWord} (h : FreeEquiv u v) : FreeEquiv v u :=
  h.symm

/-- Transitivity. -/
theorem freeEquiv_trans {u v w : FreeWord}
    (huv : FreeEquiv u v) (hvw : FreeEquiv v w) : FreeEquiv u w :=
  huv.trans hvw

/-- **Word-problem decision**: `u ~ v` holds iff their normal forms are
    equal as lists.  Decidable, since both sides are reduced words compared
    by `List`-equality. -/
theorem freeEquiv_iff_reduce_eq (u v : FreeWord) :
    FreeEquiv u v ↔ freeReduce u = freeReduce v := Iff.rfl

/-! ## 5. The quotient as a Σ-type — no `Quot.sound`

Mirrors `Lens.Unified.LensImage` / `LensImage.proj_val_eq_iff`. -/

/-- **The free group** as the subtype of freely-reduced words.  This is the
    colimit / ambient-quotient built ∅-axiom: the normal-form subtype,
    not `Quot FreeEquiv`.  `FreeGroup` over `Nat`-many generators is
    π₁(⋁ S¹). -/
def FreeGroup : Type := { w : FreeWord // Reduced w }

/-- Canonical projection `FreeWord → FreeGroup`.  PURE substitute for
    `Quot.mk FreeEquiv` — sends a word to its normal form with the
    reducedness witness. -/
def proj (w : FreeWord) : FreeGroup := ⟨freeReduce w, freeReduce_reduced w⟩

/-- **Projection-value characterisation** — the analogue of
    `LensImage.proj_val_eq_iff`, i.e. `Quot.sound`'s content axiom-free:
    `proj` values coincide iff the words are free-group equivalent. -/
theorem proj_val_eq_iff (u v : FreeWord) :
    (proj u).val = (proj v).val ↔ FreeEquiv u v := Iff.rfl

/-- Every element of `FreeGroup` is the projection of its own underlying
    word (the normal-form section is onto). -/
theorem proj_section (g : FreeGroup) : proj g.val = g := by
  cases g with
  | mk w hw =>
    show (⟨freeReduce w, freeReduce_reduced w⟩ : FreeGroup) = ⟨w, hw⟩
    exact Subtype.ext (freeReduce_fix hw)

/-! ## 6. Headline bundle -/

/-- **`free_group_quotient_no_quot`** — the colimit / ambient-quotient
    (Side A of `colimit_quotient_synthesis.md`) is built ∅-axiom with **no**
    `Quot.sound`.  Bundles:

      1. the Σ-type quotient characterisation `proj_val_eq_iff`
         (`Quot.sound`'s content, axiom-free);
      2. the decidable word problem `freeEquiv_iff_reduce_eq`
         (normal forms compared by `List`-equality);
      3. idempotent normalisation `freeReduce_idempotent`;
      4. reducedness of every normal form `freeReduce_reduced`;
      5. the normal-form section is onto `proj_section`.

    This promotes the synthesis memo's Side A from "buildable in principle"
    to a built ∅-axiom witness. -/
theorem free_group_quotient_no_quot :
    (∀ u v : FreeWord, (proj u).val = (proj v).val ↔ FreeEquiv u v) ∧
    (∀ u v : FreeWord, FreeEquiv u v ↔ freeReduce u = freeReduce v) ∧
    (∀ w : FreeWord, freeReduce (freeReduce w) = freeReduce w) ∧
    (∀ w : FreeWord, Reduced (freeReduce w)) ∧
    (∀ g : FreeGroup, proj g.val = g) :=
  ⟨proj_val_eq_iff, freeEquiv_iff_reduce_eq, freeReduce_idempotent,
   freeReduce_reduced, proj_section⟩

/-! ## 7. Sanity computations (concrete normal forms) -/

/-- `x · x⁻¹` reduces to the empty word. -/
example : freeReduce [(0, true), (0, false)] = [] := rfl

/-- `x · y · y⁻¹` reduces to `x`. -/
example : freeReduce [(0, true), (1, true), (1, false)] = [(0, true)] := rfl

/-- `x · x⁻¹ · y` reduces to `y` (cancellation exposes the cascade). -/
example : freeReduce [(0, true), (0, false), (1, true)] = [(1, true)] := rfl

/-- `x · y⁻¹ · y · x⁻¹` reduces to the empty word (nested cancellation). -/
example :
    freeReduce [(0, true), (1, false), (1, true), (0, false)] = [] := rfl

/-- `x · x` does NOT reduce (same sign — not an inverse pair). -/
example : freeReduce [(0, true), (0, true)] = [(0, true), (0, true)] := rfl

end E213.Lib.Math.Algebra.Group.FreeReduction
