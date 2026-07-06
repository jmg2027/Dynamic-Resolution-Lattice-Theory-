/-
Rederive/Object1.lean — self-indication and the diagonal milestone
(SPEC §1 F-obj + memo task A2).

`object1 r` is the indicator of `r`: the difference structure pointing at
one of its own members.  Theorems:

* `object1_injective`     — faithfulness: distinct members give distinct
                            indicators (self-indication loses nothing).
* `object1_not_surjective`— the constructive Cantor diagonal: NO self-cover
                            `f : Tree → Tree → Bool` is total on predicates;
                            the diagonal `fun x => !(f x x)` is missed by
                            every row.  (Existence half of the residue.)
* `inImageExt_iff_uniqueIndicator` — first step of the hard half (residue
                            *shape*): the extensional image of `object1` is
                            exactly the single-point indicators.  Corollaries:
                            constant-false, constant-true, and every
                            two-point indicator lie outside the image.

Extensional vs intensional (stated openly): full function equality
`p = object1 r` from pointwise equality needs `funext`, whose core proof
uses `Quot.sound` — forbidden here.  So image membership is phrased
pointwise (`∀ x, p x = object1 r x`); the intensional→extensional direction
(`congrFun`) is axiom-free and provided.  All *negative* results (diagonal,
non-membership) are stated intensionally where possible, since disequality
needs no funext.

Zero dependencies: Lean 4 core only, zero axioms.
-/

import Rederive.Tree

namespace Rederive

namespace Tree

/-! ## Boolean equality (hand-written, verified axiom-free) -/

/-- Structural boolean equality on `Tree`. -/
def beq : Tree → Tree → Bool
  | .a, .a => true
  | .b, .b => true
  | .node l₁ r₁, .node l₂ r₂ => beq l₁ l₂ && beq r₁ r₂
  | _, _ => false

instance : BEq Tree := ⟨beq⟩

theorem beq_refl : ∀ x : Tree, beq x x = true
  | .a => rfl
  | .b => rfl
  | .node l r => by
    simp only [beq]
    rw [beq_refl l, beq_refl r]
    rfl

theorem eq_of_beq : ∀ {x y : Tree}, beq x y = true → x = y
  | .a, .a, _ => rfl
  | .a, .b, h => Bool.noConfusion h
  | .a, .node _ _, h => Bool.noConfusion h
  | .b, .a, h => Bool.noConfusion h
  | .b, .b, _ => rfl
  | .b, .node _ _, h => Bool.noConfusion h
  | .node _ _, .a, h => Bool.noConfusion h
  | .node _ _, .b, h => Bool.noConfusion h
  | .node l₁ r₁, .node l₂ r₂, h => by
    simp only [beq] at h
    cases hl : beq l₁ l₂ with
    | false => rw [hl] at h; exact Bool.noConfusion h
    | true =>
      rw [hl, Bool.true_and] at h
      rw [eq_of_beq hl, eq_of_beq h]

theorem beq_eq_false_of_ne {x y : Tree} (h : x ≠ y) : beq x y = false := by
  cases hb : beq x y with
  | false => rfl
  | true => exact absurd (eq_of_beq hb) h

/-- Decidable equality, built from `beq` (no `Classical`, no derivation
machinery — everything inspectable). -/
instance decEq : DecidableEq Tree := fun x y =>
  match hb : beq x y with
  | true => isTrue (eq_of_beq hb)
  | false => isFalse (fun h => by rw [h, beq_refl] at hb; exact Bool.noConfusion hb)

end Tree

/-! ## Self-indication -/

open Tree

/-- Self-indication: `object1 r` is the indicator predicate of `r` —
the structure pointing at one of its own members.  De-intentionalised:
just a function `Tree → Tree → Bool`, no observer. -/
def object1 (r : Tree) : Tree → Bool := fun x => beq x r

theorem object1_self (r : Tree) : object1 r r = true := beq_refl r

theorem object1_eq_true_iff {r x : Tree} : object1 r x = true ↔ x = r :=
  ⟨eq_of_beq, fun h => by rw [h]; exact beq_refl r⟩

theorem object1_eq_false_of_ne {r x : Tree} (h : x ≠ r) : object1 r x = false :=
  beq_eq_false_of_ne h

/-! ## Faithfulness -/

/-- Extensional faithfulness: distinct members disagree somewhere
(namely at `r` itself). -/
theorem object1_injective_ext {r s : Tree} (h : r ≠ s) :
    ¬(∀ x, object1 r x = object1 s x) := by
  intro he
  have hr : object1 r r = object1 s r := he r
  rw [object1_self] at hr
  exact h (eq_of_beq hr.symm)

/-- **Faithfulness** (`object1_injective`): `r ≠ s → object1 r ≠ object1 s`.
Self-indication is injective — no information is lost in the pointing. -/
theorem object1_injective {r s : Tree} (h : r ≠ s) : object1 r ≠ object1 s :=
  fun he => object1_injective_ext h (fun x => congrFun he x)

/-! ## The diagonal: no self-cover is total -/

/-- The Cantor diagonal of a self-cover `f`. -/
def diag (f : Tree → Tree → Bool) : Tree → Bool := fun x => !(f x x)

/-- The diagonal is missed by every row of `f`. -/
theorem diag_ne (f : Tree → Tree → Bool) (r : Tree) : diag f ≠ f r := by
  intro h
  have h2 : (!(f r r)) = f r r := congrFun h r
  cases hfr : f r r with
  | true => rw [hfr] at h2; exact Bool.noConfusion h2
  | false => rw [hfr] at h2; exact Bool.noConfusion h2

/-- **The residue exists** (`object1_not_surjective`, constructive): for
EVERY self-cover `f : Tree → Tree → Bool` there is a predicate no row of
`f` reaches — the witness is the explicit diagonal `fun x => !(f x x)`.
In particular self-indication itself, though faithful, is never total:
distinguishing always leaves a remainder. -/
theorem object1_not_surjective :
    ∀ f : Tree → Tree → Bool, ∃ p : Tree → Bool, ∀ r, p ≠ f r :=
  fun f => ⟨diag f, diag_ne f⟩

/-- The diagonal of `object1` itself is (pointwise) the constant-false
predicate: the first concrete inhabitant of the residue. -/
theorem diag_object1_eq_false (x : Tree) : diag object1 x = false := by
  show (!(beq x x)) = false
  rw [beq_refl]
  rfl

/-! ## Residue shape (first step of the hard half, memo A2) -/

/-- `p` lies in the *extensional* image of self-indication. -/
def InImageExt (p : Tree → Bool) : Prop :=
  ∃ r, ∀ x, p x = object1 r x

/-- `p` is a single-point indicator: true at exactly one tree. -/
def UniqueIndicator (p : Tree → Bool) : Prop :=
  ∃ r, p r = true ∧ ∀ x, p x = true → x = r

/-- Intensional membership implies extensional membership (axiom-free
direction; the converse is `funext`-strength, left open). -/
theorem inImageExt_of_eq {p : Tree → Bool} (h : ∃ r, p = object1 r) :
    InImageExt p := by
  cases h with
  | intro r hr => exact ⟨r, fun x => by rw [hr]⟩

/-- **Residue shape**: the extensional image of `object1` is EXACTLY the
single-point indicators.  Everything else — however definable — is residue. -/
theorem inImageExt_iff_uniqueIndicator (p : Tree → Bool) :
    InImageExt p ↔ UniqueIndicator p := by
  constructor
  · intro h
    cases h with
    | intro r hr =>
      refine ⟨r, ?_, ?_⟩
      · rw [hr r]; exact object1_self r
      · intro x hx
        rw [hr x] at hx
        exact eq_of_beq hx
  · intro h
    cases h with
    | intro r hr =>
      refine ⟨r, fun x => ?_⟩
      cases hp : p x with
      | true =>
        have hx : x = r := hr.2 x hp
        rw [hx, object1_self]
      | false =>
        have hne : x ≠ r := fun hx => by
          rw [hx, hr.1] at hp
          exact Bool.noConfusion hp
        rw [object1_eq_false_of_ne hne]

/-! ### Corollaries: three concrete residue inhabitants -/

/-- The constant-false predicate (the empty view) is residue. -/
theorem constFalse_not_inImageExt : ¬ InImageExt (fun _ => false) := by
  intro h
  cases h with
  | intro r hr =>
    have := hr r
    rw [object1_self] at this
    exact Bool.noConfusion this

/-- Intensional corollary: constant-false is not any `object1 r`. -/
theorem constFalse_ne_object1 (r : Tree) : (fun _ => false : Tree → Bool) ≠ object1 r :=
  fun h => constFalse_not_inImageExt ⟨r, fun x => congrFun h x⟩

/-- The constant-true predicate (the total view) is residue —
because the two atoms are distinct. -/
theorem constTrue_not_inImageExt : ¬ InImageExt (fun _ => true) := by
  intro h
  have hu := (inImageExt_iff_uniqueIndicator _).mp h
  cases hu with
  | intro r hr =>
    have ha : Tree.a = r := hr.2 Tree.a rfl
    have hb : Tree.b = r := hr.2 Tree.b rfl
    exact Tree.a_ne_b (by rw [ha, hb])

theorem constTrue_ne_object1 (r : Tree) : (fun _ => true : Tree → Bool) ≠ object1 r :=
  fun h => constTrue_not_inImageExt ⟨r, fun x => congrFun h x⟩

/-- The two-point indicator `{u, v}` (u ≠ v) is residue: self-indication
points at exactly one something, never at two. -/
theorem twoIndicator_not_inImageExt {u v : Tree} (huv : u ≠ v) :
    ¬ InImageExt (fun x => beq x u || beq x v) := by
  intro h
  have hu := (inImageExt_iff_uniqueIndicator _).mp h
  cases hu with
  | intro r hr =>
    have hpu : (beq u u || beq u v) = true := by rw [beq_refl]; rfl
    have hpv : (beq v u || beq v v) = true := by rw [beq_refl, Bool.or_true]
    have h1 : u = r := hr.2 u hpu
    have h2 : v = r := hr.2 v hpv
    exact huv (by rw [h1, h2])

theorem twoIndicator_ne_object1 {u v : Tree} (huv : u ≠ v) (r : Tree) :
    (fun x => beq x u || beq x v) ≠ object1 r :=
  fun h => twoIndicator_not_inImageExt huv ⟨r, fun x => congrFun h x⟩

end Rederive
