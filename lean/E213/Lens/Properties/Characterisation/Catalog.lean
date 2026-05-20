import E213.Theory.Raw.API
import E213.Lens.LensCore
import E213.Prelude

/-!
# Meta: Lens catalog — different lenses, different mathematics

The axiom supplies `Raw` only. Any mathematical *content* (numbers,
equality, set-like collections, …) arises from applying a Lens.
A Lens is a free choice of codomain and combine; distinct Lenses
yield distinct extracted mathematics from the same `Raw`.

**Organising principle.** A Lens's visibility of `Raw.swap`
partitions the catalogue:

- *Swap-blind:* `L.view (swap r) = L.view r` for all `r`.
- *Swap-visible:* `L.view (swap r)` differs from `L.view r`.

We show the swap-blind branch formally (`depth`, `leaves` Lenses);
the swap-visible branch is illustrated by a ℤ-valued "signed"
Lens realising `swap` as negation — an integer-level analogue of
complex conjugation.
-/

namespace E213.Lens.Properties.Characterisation.Catalog
open E213.Theory E213.Lens

-- ═══ Swap-blind lenses ═══

/-- **Depth lens is swap-blind.**  With `base_a = base_b = 0`,
    the Lens collapses the `a ↔ b` distinction already at the
    base; `swap` is invisible at every level. -/
theorem depth_swap_invariant (r : Raw) :
    Lens.depth.view (Raw.swap r) = Lens.depth.view r := by
  show Raw.fold 0 0 (fun a b => 1 + max a b) (Raw.swap r)
     = Raw.fold 0 0 (fun a b => 1 + max a b) r
  rw [Raw.fold_eq_depth, Raw.fold_eq_depth, Raw.swap_depth]

/-- **Leaves lens is swap-blind.** Same base value for `a` and
    `b`. The Lens counts size, erasing identity. -/
theorem leaves_swap_invariant (r : Raw) :
    Lens.leaves.view (Raw.swap r) = Lens.leaves.view r := by
  show Raw.fold 1 1 (· + ·) (Raw.swap r) = Raw.fold 1 1 (· + ·) r
  rw [Raw.fold_eq_leaves, Raw.fold_eq_leaves, Raw.swap_leaves]

end E213.Lens.Properties.Characterisation.Catalog
-- ═══ Swap-visible lens: signed (Int) ═══

namespace E213.Lens.Properties.Characterisation.Catalog
open E213.Theory

/-- Signed lens: `a ↦ 1`, `b ↦ -1`, combine = `+`.
    Base values differ in sign, so `swap` becomes visible as
    negation on the image. This is the ℤ-level analogue of
    "swap realised as complex conjugation" (the axiom's ℂ-Lens
    identification of §4 of the paper). -/
def signedLens : Lens Int where
  base_a  := 1
  base_b  := -1
  combine := (· + ·)

/-- Swap acts as negation on the image of the signed Lens. -/
theorem signed_swap_neg (r : Raw) :
    signedLens.view (Raw.swap r) = - signedLens.view r := by
  show Raw.fold (1 : Int) (-1) (· + ·) (Raw.swap r)
     = - Raw.fold (1 : Int) (-1) (· + ·) r
  exact Raw.fold_signed_swap r

open E213.Theory E213.Lens

-- ═══ Swap-invariance characterisation ═══

/-- **Necessary condition for swap-blindness.**  If a Lens is
    swap-invariant (view unchanged by swap), then in particular
    its value on `a` equals its value on `swap a = b`; hence the
    two base values coincide. -/
theorem swap_invariant_base_eq {α : Type} {L : Lens α}
    (h : ∀ r : Raw, L.view (Raw.swap r) = L.view r) :
    L.base_a = L.base_b := by
  have h0 := h Raw.a
  rw [Raw.swap_a] at h0
  -- h0 : L.view Raw.b = L.view Raw.a
  -- both sides reduce by computation
  exact h0.symm


-- ═══ R3–R5 — structural Lens requirements ═══

-- R1, R2 are built into the `Lens` structure and `Lens.view`
-- (there must be a `combine`, and `view` is the catamorphism
-- applying it recursively).  R3–R5 are predicates on Lenses.

/-- **R3 — Non-vanishing.**  If two codomain values are both
    nonzero (present), their combine is also nonzero. Equivalently
    (for ℝ-algebra codomains) the combine has no zero divisors. -/
def NonVanishing {α : Type} [Zero α] (L : Lens α) : Prop :=
  ∀ u v : α, u ≠ 0 → v ≠ 0 → L.combine u v ≠ 0

/-- **R4 — Swap matches exactly one nontrivial involution.**  On
    the codomain `α` there is a function `conj : α → α` such that
    `conj` is an involution, has a non-fixed point
    (`∃ x, conj x ≠ x`), and `view (swap r) = conj (view r)` for
    every `r`.

    The non-trivial clause is **point-wise** (`∃ x, conj x ≠ x`)
    rather than the function-level inequality `conj ≠ id` — the
    point-wise form is ∅-axiom-friendly (no `funext` needed when
    consumed), and mathematically equivalent (every concrete
    instance constructs the witness directly). -/
def SwapMatching {α : Type} (L : Lens α) (conj : α → α) : Prop :=
  (∀ u, conj (conj u) = u) ∧
  (∃ x, conj x ≠ x) ∧
  (∀ r : Raw, L.view (Raw.swap r) = conj (L.view r))

/-- **R5 — Distinguishing.**  Different Raw terms have different
    images; equivalently, `L.view` is injective.  The continuity /
    minimality clause of R5 (the image is the smallest connected
    ℝ-algebra on which this is possible) is not expressible in
    Lean 4 core; we record the injectivity half and treat the
    minimality identification (→ ℝ) at the prose level. -/
def Distinguishing {α : Type} (L : Lens α) : Prop :=
  Function.Injective L.view


-- ═══ signedLens: verified R4 (swap = negation) ═══

/-- `signedLens` realises R4 with `conj = Neg.neg` on `Int`:
    swap on `Raw` corresponds to negation on the image.
    ∅-axiom — uses `∃`-form non-trivial witness (x = 1, -1 ≠ 1). -/
theorem signed_R4 :
    SwapMatching signedLens (fun n : Int => -n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u; exact Int.neg_neg u
  · exact ⟨1, by decide⟩
  · intro r
    exact signed_swap_neg r

/-- Swap-invariant Lenses fail R4 pointwise: if
    `view (swap r) = view r` for all `r`, then any R4-candidate
    `conj` must fix every image point of `view`. -/
theorem swap_invariant_R4_fixes_image
    {α : Type} {L : Lens α} {conj : α → α}
    (hinv : ∀ r : Raw, L.view (Raw.swap r) = L.view r)
    (hmatch : SwapMatching L conj)
    (r : Raw) : conj (L.view r) = L.view r := by
  have h1 : L.view (Raw.swap r) = conj (L.view r) := hmatch.2.2 r
  have h2 : L.view (Raw.swap r) = L.view r := hinv r
  rw [h2] at h1
  exact h1.symm

end E213.Lens.Properties.Characterisation.Catalog