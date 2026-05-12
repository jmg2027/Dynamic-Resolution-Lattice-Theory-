import E213.Theory.Raw
import E213.Lens.LensCore

/-!
# RawInitiality: Raw is the initial object in the Raw-algebra category

Formalization of the Note 32 claim.  For any Lens `L : Lens α`,
a homomorphism `Raw → α` exists (= `L.view`) and is unique.

## Significance

The **rigorous half** of the Note 31 §7 theorem candidate ("every
mathematical structure requires at least 2 mutually necessary elements")
— the universal property restricted to the Raw-algebra case.

Existence is `Lens.view` itself.  This file provides **machine verification
of uniqueness**.

## §1. Uniqueness theorem (Lens.view_unique)

If an arbitrary function f : Raw → α satisfies the Lens homomorphism
conditions, then f = Lens.view.
-/

namespace E213.Lens.Initiality

open E213.Theory E213.Lens

/-- **Uniqueness of Raw-algebra homomorphisms (commutative combine).**

    If an arbitrary `f : Raw → α` satisfies the following, then f = L.view:
    - L.combine is commutative.
    - `f Raw.a = L.base_a`
    - `f Raw.b = L.base_b`
    - `f (Raw.slash x y h) = L.combine (f x) (f y)` (for all x, y, h)

    That is, Raw is the initial object in the commutative Lens-algebra category
    (the uniqueness half of the universal property).

    Why `hsym` is needed: due to Raw's internal canonicalization (Tree.cmp),
    `L.view (slash x y h)` follows canonical ordering and may produce
    `combine (view x) (view y)` or `combine (view y) (view x)`.
    For these to be equal, combine must be symmetric.  See note 25 §3
    Lens-layer observation.  -/
theorem Lens.view_unique {α : Type} (L : Lens α)
    (hsym : ∀ u v : α, L.combine u v = L.combine v u)
    (f : Raw → α)
    (ha : f Raw.a = L.base_a)
    (hb : f Raw.b = L.base_b)
    (hslash : ∀ (x y : Raw) (h : x ≠ y),
              f (Raw.slash x y h) = L.combine (f x) (f y)) :
    ∀ r : Raw, f r = L.view r := by
  intro r
  induction r using Raw.rec with
  | a => rw [ha]; rfl
  | b => rw [hb]; rfl
  | slash x y h ihx ihy =>
      rw [hslash x y h, ihx, ihy]
      -- Goal: L.combine (L.view x) (L.view y) = L.view (Raw.slash x y h).
      -- Resolved by Raw.fold_slash.
      symm
      show L.view (Raw.slash x y h) = L.combine (L.view x) (L.view y)
      exact Raw.fold_slash L.base_a L.base_b L.combine hsym x y h

end E213.Lens.Initiality

namespace E213.Lens.Initiality

open E213.Theory E213.Lens

/-! ## §2. Existence + uniqueness = universal property

Existence: `Lens.view L` is itself the required homomorphism.
Uniqueness: `Lens.view_unique` (§1).

### §2.1 Existence witnesses (already in Theory.Raw)
-/

/-- `L.view` sends Raw.a to base_a. -/
theorem Lens.view_a {α : Type} (L : Lens α) : L.view Raw.a = L.base_a := rfl

/-- `L.view` sends Raw.b to base_b. -/
theorem Lens.view_b {α : Type} (L : Lens α) : L.view Raw.b = L.base_b := rfl

/-- `L.view` sends slashes to combine (under commutative combine). -/
theorem Lens.view_slash {α : Type} (L : Lens α)
    (hsym : ∀ u v : α, L.combine u v = L.combine v u)
    (x y : Raw) (h : x ≠ y) :
    L.view (Raw.slash x y h) = L.combine (L.view x) (L.view y) :=
  Raw.fold_slash L.base_a L.base_b L.combine hsym x y h

/-! ### §2.2 Universal property corollary

Combining existence and uniqueness: the homomorphism for a given Lens
is exactly one.
-/

/-- **Universal property — existence + uniqueness (conditioned on commutativity)**.
    Raw is the initial object in the commutative Raw-algebra category.
    For a given L, the L-compatible function is exactly `L.view`. -/
theorem Lens.initiality {α : Type} (L : Lens α)
    (hsym : ∀ u v : α, L.combine u v = L.combine v u) :
    ∃ f : Raw → α,
      (f Raw.a = L.base_a) ∧
      (f Raw.b = L.base_b) ∧
      (∀ (x y : Raw) (h : x ≠ y),
        f (Raw.slash x y h) = L.combine (f x) (f y)) ∧
      (∀ g : Raw → α,
        g Raw.a = L.base_a →
        g Raw.b = L.base_b →
        (∀ x y h, g (Raw.slash x y h) = L.combine (g x) (g y)) →
        g = f) := by
  refine ⟨L.view, ?_, ?_, ?_, ?_⟩
  · exact Lens.view_a L
  · exact Lens.view_b L
  · intro x y h; exact Lens.view_slash L hsym x y h
  · intro g ha hb hslash
    funext r
    exact Lens.view_unique L hsym g ha hb hslash r

end E213.Lens.Initiality
