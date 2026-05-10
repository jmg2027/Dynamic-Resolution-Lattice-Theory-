import E213.Lens.SemanticAtom

/-!
# InstanceReach: boundary of the image of universalMorphism

`universalMorphism α : Raw → α` from `SemanticAtom.lean` is a
morphism into HasDistinguishing instance α.  Is the image *always*
all of α? — Answer: **no**.  The carrier of α can be strictly
larger than the image.

## Significance

A sharpening of the semantic atom thesis:

> Raw is a *generator* of every distinguishing-framework instance
> (the image is a distinguishing-closed sub-instance).  But the
> carrier of an instance can be *strictly larger* than the image —
> separating the framework's reach from the carrier.

That is, the semantic atom is the minimum generator, and an instance
can carry "unreachable" elements above it.  This makes the framework's
*reach boundary* explicit.

## Witness

`Fin 3` with `a := 0, b := 1, combine := λ _ _, 0`:
- reach = {0, 1} (image from Raw).
- carrier = {0, 1, 2}.
- 2 ∉ image — strict subset.

Note 80 analysis.
-/

namespace E213.Lens.Instances.Reach

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom

/-! ### Witness: trivial-combine instance on Fin 3 -/

instance fin3HasDistinguishing : HasDistinguishing (Fin 3) where
  a := 0
  b := 1
  distinct := by decide
  combine _ _ := 0
  combine_sym _ _ := rfl

/-- Forward closure of the image: universalMorphism (Fin 3) always
    yields 0 or 1 (combine always returns 0). -/
theorem fin3_image_in_01 (r : Raw) :
    universalMorphism (Fin 3) r = 0 ∨ universalMorphism (Fin 3) r = 1 := by
  induction r using Raw.rec with
  | a => left; exact universalMorphism_a (Fin 3)
  | b => right; exact universalMorphism_b (Fin 3)
  | slash x y h _ _ =>
      left
      rw [universalMorphism_slash (Fin 3) x y h]
      rfl

end E213.Lens.Instances.Reach

namespace E213.Lens.Instances.Reach

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom

/-- **Strict subset of the image**: element 2 of Fin 3 is outside
    the image of universalMorphism.  Explicit witness of the separation
    between the framework's reach and the carrier. -/
theorem fin3_image_strict :
    ∃ x : Fin 3, ¬ ∃ r : Raw, universalMorphism (Fin 3) r = x := by
  refine ⟨2, ?_⟩
  intro ⟨r, hr⟩
  rcases fin3_image_in_01 r with h | h
  · rw [h] at hr; exact absurd hr (by decide)
  · rw [h] at hr; exact absurd hr (by decide)

end E213.Lens.Instances.Reach

namespace E213.Lens.Instances.Reach

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom

/-! ### Dual: Bool instance is surjective

`Fin 3` is a witness of non-surjectivity.  `Bool` is *always*
surjective — the two bases a, b alone cover the entire carrier.
An example of an instance where reach = carrier. -/

instance boolHasDistinguishing : HasDistinguishing Bool where
  a := true
  b := false
  distinct := by decide
  combine := and
  combine_sym := Bool.and_comm

/-- universalMorphism of the Bool instance is surjective. -/
theorem bool_image_surjective :
    ∀ b : Bool, ∃ r : Raw, universalMorphism Bool r = b := by
  intro b
  cases b with
  | true => exact ⟨Raw.a, universalMorphism_a Bool⟩
  | false => exact ⟨Raw.b, universalMorphism_b Bool⟩

end E213.Lens.Instances.Reach

namespace E213.Lens.Instances.Reach

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom

/-! ### Minimality property of the image (closure under bases) -/

/-- The image always contains d.a. -/
theorem image_contains_a (α : Type) [d : HasDistinguishing α] :
    ∃ r : Raw, universalMorphism α r = d.a :=
  ⟨Raw.a, universalMorphism_a α⟩

/-- The image always contains d.b. -/
theorem image_contains_b (α : Type) [d : HasDistinguishing α] :
    ∃ r : Raw, universalMorphism α r = d.b :=
  ⟨Raw.b, universalMorphism_b α⟩

/-- The combine of distinct image elements is also in the image —
    direct application of Raw.slash. -/
theorem image_closed_under_distinct_combine (α : Type) [d : HasDistinguishing α]
    (rx ry : Raw) (h : rx ≠ ry) :
    ∃ r : Raw,
      universalMorphism α r
        = d.combine (universalMorphism α rx) (universalMorphism α ry) :=
  ⟨Raw.slash rx ry h, universalMorphism_slash α rx ry h⟩

end E213.Lens.Instances.Reach

namespace E213.Lens.Instances.Reach

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom

/-! ### Infinite surjective: Nat with addition

Bool is finite surjective.  Fin 3 (constant combine) is finite
non-surjective.  Nat with addition: **infinite surjective** —
every Nat is in the image, carrier is infinite.

`a := 0`, `b := 1`, `combine := (· + ·)`.  combine_sym is trivial
(`Nat.add_comm`).

Witness: r n := slash (r (n-1)) Raw.b _ for n ≥ 1, r 0 := Raw.a.
universalMorphism = n by induction. -/

instance natHasDistinguishing : HasDistinguishing Nat where
  a := 0
  b := 1
  distinct := by decide
  combine := (· + ·)
  combine_sym := Nat.add_comm

end E213.Lens.Instances.Reach

namespace E213.Lens.Instances.Reach

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom

/-- Concrete witnesses for small Nat values — Raw.a, Raw.b cover
    {0, 1}, and slash generates larger elements. -/
theorem nat_image_zero : ∃ r : Raw, universalMorphism Nat r = 0 :=
  ⟨Raw.a, universalMorphism_a Nat⟩

theorem nat_image_one : ∃ r : Raw, universalMorphism Nat r = 1 :=
  ⟨Raw.b, universalMorphism_b Nat⟩

/-- 0 + 1 = 1 via slash a b. -/
theorem nat_image_via_slash_ab :
    universalMorphism Nat (Raw.slash Raw.a Raw.b (by decide)) = 1 := by
  rw [universalMorphism_slash Nat Raw.a Raw.b (by decide)]
  rw [universalMorphism_a Nat, universalMorphism_b Nat]
  rfl

end E213.Lens.Instances.Reach

namespace E213.Lens.Instances.Reach

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom

/-! ### Nat surjective: complete proof

`natHasDistinguishing` is surjective — ∀ n : Nat, ∃ r : Raw,
universalMorphism Nat r = n.

Witness construction: induction on n.
- n = 0: r = Raw.a.
- n ≥ 1: r n := Raw.slash (Raw.a) (witness for n-1 ≥ 1) + base
  case Raw.b for n = 1.

Trick: induction with strong invariant — r n ≠ Raw.a for n ≥ 1
+ universalMorphism r n = n.  Then slash Raw.a (r n) (a ≠ rn).
-/

/-- Inline 213-native max_comm helper (avoiding Nat.max_comm propext leak). -/
private theorem nat_max_comm_pure (a b : Nat) : Nat.max a b = Nat.max b a := by
  rcases Nat.le_total a b with hab | hba
  · show (if a ≤ b then b else a) = (if b ≤ a then a else b)
    rw [if_pos hab]
    by_cases h : b ≤ a
    · rw [if_pos h]; exact Nat.le_antisymm h hab
    · rw [if_neg h]
  · show (if a ≤ b then b else a) = (if b ≤ a then a else b)
    rw [if_pos hba]
    by_cases h : a ≤ b
    · rw [if_pos h]; exact Nat.le_antisymm hba h
    · rw [if_neg h]

/-- Helper: result of Raw.slash differs from Raw.a (depth-based proof). -/
private theorem slash_ne_a (x y : Raw) (h : x ≠ y) :
    Raw.slash x y h ≠ Raw.a := by
  intro heq
  have hview := congrArg Lens.depth.view heq
  have hslash : Lens.depth.view (Raw.slash x y h)
                = 1 + max (Lens.depth.view x) (Lens.depth.view y) := by
    apply Raw.fold_slash
    intro u v
    show 1 + max u v = 1 + max v u
    exact congrArg (1 + ·) (nat_max_comm_pure u v)
  rw [hslash] at hview
  show False
  have h_a : Lens.depth.view Raw.a = 0 := rfl
  rw [h_a] at hview
  -- hview : 1 + max ... = 0.  Use Nat.add_comm to get succ form.
  rw [Nat.add_comm 1 (max _ _)] at hview
  -- hview : Nat.succ (max ...) = 0 — impossible
  cases hview

end E213.Lens.Instances.Reach

namespace E213.Lens.Instances.Reach

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom

/-! ### natWitness construction note

Explicit Raw witness for each Nat n:
- r 0 := Raw.a (universalMorphism = 0).
- r (n+1) := slash Raw.b (r n) (proof Raw.b ≠ r n).
  → universalMorphism = 1 + n.
Need: ∀ n, r n ≠ Raw.b.  By induction:
- r 0 = Raw.a ≠ Raw.b (decide).
- r (n+1) = slash _ _ _ ≠ Raw.b (proved via slash_ne_b).
-/

/-- Helper: result of Raw.slash differs from Raw.b. -/
private theorem slash_ne_b (x y : Raw) (h : x ≠ y) :
    Raw.slash x y h ≠ Raw.b := by
  intro heq
  have hview := congrArg Lens.depth.view heq
  have hslash : Lens.depth.view (Raw.slash x y h)
                = 1 + max (Lens.depth.view x) (Lens.depth.view y) := by
    apply Raw.fold_slash
    intro u v
    show 1 + max u v = 1 + max v u
    exact congrArg (1 + ·) (nat_max_comm_pure u v)
  rw [hslash] at hview
  show False
  have h_b : Lens.depth.view Raw.b = 0 := rfl
  rw [h_b] at hview
  rw [Nat.add_comm 1 (max _ _)] at hview
  cases hview

end E213.Lens.Instances.Reach

namespace E213.Lens.Instances.Reach

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom

/-- Helper: combined `r ≠ Raw.b` for both Raw.a and slash forms. -/
private theorem natWitness_ne_b_helper (r : Raw)
    (h : r = Raw.a ∨ ∃ x y h', r = Raw.slash x y h') :
    r ≠ Raw.b := by
  rcases h with hra | ⟨x, y, h', hsl⟩
  · subst hra; decide
  · subst hsl; exact slash_ne_b x y h'

end E213.Lens.Instances.Reach

namespace E213.Lens.Instances.Reach

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom

/-- **Nat surjective with form invariant**: for every n, simultaneously
    induct on the explicit Raw witness's form (form invariant used in
    the induction step). -/
theorem nat_surjective_with_form : ∀ n : Nat, ∃ r : Raw,
    universalMorphism Nat r = n ∧
    (r = Raw.a ∨ ∃ x y h, r = Raw.slash x y h) := by
  intro n
  induction n with
  | zero => exact ⟨Raw.a, universalMorphism_a Nat, Or.inl rfl⟩
  | succ n ih =>
      obtain ⟨r, hr_view, hr_form⟩ := ih
      have h_ne : r ≠ Raw.b := natWitness_ne_b_helper r hr_form
      have h_b_ne_r : Raw.b ≠ r := Ne.symm h_ne
      refine ⟨Raw.slash Raw.b r h_b_ne_r, ?_, Or.inr ⟨Raw.b, r, h_b_ne_r, rfl⟩⟩
      rw [universalMorphism_slash Nat Raw.b r h_b_ne_r,
          universalMorphism_b Nat, hr_view]
      show 1 + n = n + 1
      exact Nat.add_comm 1 n

/-- **Main result**: universalMorphism of the Nat instance is surjective. -/
theorem nat_image_surjective :
    ∀ n : Nat, ∃ r : Raw, universalMorphism Nat r = n := by
  intro n
  obtain ⟨r, hview, _⟩ := nat_surjective_with_form n
  exact ⟨r, hview⟩

end E213.Lens.Instances.Reach

namespace E213.Lens.Instances.Reach

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom

/-! ### Int with addition: infinite non-surjective

Bool finite surj, Fin 3 finite non-surj, Nat infinite surj.
Int with addition: **infinite non-surjective** — only the positive
part of Nat ⊊ Int is reachable; negative numbers are unreachable
(combine = + is always non-decreasing).

This is an explicit witness of surjectivity failure for an infinite
carrier — the image is a *strict* infinite subset. -/

instance intHasDistinguishing : HasDistinguishing Int where
  a := 0
  b := 1
  distinct := by decide
  combine := (· + ·)
  combine_sym := Int.add_comm

/-- Forward closure of the image: universalMorphism Int always
    yields a result ≥ 0. -/
theorem int_image_nonneg (r : Raw) : 0 ≤ universalMorphism Int r := by
  induction r using Raw.rec with
  | a =>
      rw [universalMorphism_a Int]
      exact Int.le_refl 0
  | b =>
      rw [universalMorphism_b Int]
      decide
  | slash x y h ihx ihy =>
      rw [universalMorphism_slash Int x y h]
      exact Int.add_nonneg ihx ihy

/-- **Strict subset of the image (infinite case)**: -1 ∈ Int is
    outside the image of universalMorphism.  Non-surjectivity witness
    for an infinite carrier. -/
theorem int_image_strict :
    ∃ x : Int, ¬ ∃ r : Raw, universalMorphism Int r = x := by
  refine ⟨-1, ?_⟩
  intro ⟨r, hr⟩
  have h_nonneg : 0 ≤ universalMorphism Int r := int_image_nonneg r
  rw [hr] at h_nonneg
  exact absurd h_nonneg (by decide)

end E213.Lens.Instances.Reach
