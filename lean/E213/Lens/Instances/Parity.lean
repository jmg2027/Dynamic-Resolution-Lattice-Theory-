import E213.Theory.Raw
import E213.Lens.LensCore
import E213.Lens.Characterisation.Catalog
import E213.Prelude

/-!
# ParityLens: finite-codomain R5-fail witness

`parityLens : Lens Bool` with `base_a = true`, `base_b = true`,
`combine = xor`.  The view tracks leaves mod 2 (true = odd,
false = even).

**Two simultaneous failure witnesses in one Lens.**

1. *R5 (Distinguishing) fails.*  The finite codomain `Bool`
   cannot separate `Raw.a` from `Raw.b` — both map to `true`
   — so `Lens.view` is not injective.

2. *R4 (Swap matching with nontrivial involution) fails.*  Being
   swap-blind (`base_a = base_b`), any R4-candidate `conj` must
   fix the entire image; but the image contains both `true`
   (e.g. `Raw.a`) and `false` (e.g. `Raw.slash Raw.a Raw.b`),
   forcing `conj = id` — contradicting R4's `conj ≠ id`
   clause.

Together with the already-catalogued `signedLens` (R4 pass) and
`boolXorLens` (R4 homomorphism fail), this completes a three-way
split of swap-visibility × R4-admissibility at the Bool/Int
level.
-/

namespace E213.Lens.Instances.Parity
open E213.Theory E213.Lens
open E213.Lens.Characterisation.Catalog

/-- **Parity lens.**  `a ↦ true`, `b ↦ true`, combine = xor.
    View = `true` iff `Raw.leaves` is odd. -/
def parityLens : Hypervisor.Lens Bool where
  base_a  := true
  base_b  := true
  combine := xor

private theorem xor_comm_bool : ∀ u v : Bool, xor u v = xor v u := by
  intro u v; cases u <;> cases v <;> rfl

/-- **Swap-blindness.**  `base_a = base_b = true` and
    `conj = id` satisfies `fold_swap_hom`, so `view` is
    swap-invariant. -/
theorem parityLens_swap_invariant (r : Raw) :
    parityLens.view (Raw.swap r) = parityLens.view r := by
  have h := Raw.fold_swap_hom (true : Bool) true xor id
    (rfl) (rfl)
    (fun _ _ => rfl)
    xor_comm_bool
    r
  exact h

end E213.Lens.Instances.Parity
namespace E213.Lens.Instances.Parity
open E213.Theory E213.Lens
open E213.Lens.Characterisation.Catalog

/-- **R5 fails.**  `Raw.a ≠ Raw.b` but both map to `true`. -/
theorem parityLens_not_injective :
    ¬ Function.Injective parityLens.view := by
  intro hinj
  have hab : parityLens.view Raw.a = parityLens.view Raw.b := rfl
  have habs : Raw.a = Raw.b := hinj hab
  exact absurd habs (by decide)

/-- A level-2 Raw term `a / b` whose parity-view is `false`
    (even leaf count = 2). -/
def parityLens_sample_even : Raw :=
  Raw.slash Raw.a Raw.b (by decide)

theorem parityLens_sample_even_view :
    parityLens.view parityLens_sample_even = false := by
  show Raw.fold true true xor (Raw.slash Raw.a Raw.b _) = false
  rw [Raw.fold_slash true true xor xor_comm_bool Raw.a Raw.b (by decide)]
  rfl

/-- **R4 fails.**  Swap-blindness forces any matching `conj`
    to fix every image point; with both `true` and `false`
    reachable, that forces `conj = id`, contradicting the
    `conj ≠ id` clause of R4. -/
theorem parityLens_R4_fails :
    ¬ ∃ conj : Bool → Bool, SwapMatching parityLens conj := by
  rintro ⟨conj, hmatch⟩
  have hsw : ∀ r : Raw, parityLens.view (Raw.swap r) = parityLens.view r :=
    parityLens_swap_invariant
  have hfix : ∀ r : Raw, conj (parityLens.view r) = parityLens.view r :=
    fun r => swap_invariant_R4_fixes_image hsw hmatch r
  have htrue : conj true = true := hfix Raw.a
  have hfalse : conj false = false := by
    have h := hfix parityLens_sample_even
    rw [parityLens_sample_even_view] at h
    exact h
  have hid : conj = id := by
    funext u; cases u
    · exact hfalse
    · exact htrue
  exact hmatch.2.1 hid

end E213.Lens.Instances.Parity