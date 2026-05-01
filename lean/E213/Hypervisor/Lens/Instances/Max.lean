import E213.Firmware.Raw
import E213.Hypervisor.Lens
import E213.Hypervisor.Lens.Characterisation.Catalog
import E213.Prelude

/-!
# Meta.MaxLens: swap-visible but R4-fail via idempotence

`maxLens : Lens Nat` with `base_a = 0`, `base_b = 1`,
`combine = max`.  Swap-visible on base objects
(`view a = 0, view b = 1`), but R4 fails for a structural
reason distinct from the XOR-fails-homomorphism or
Parity-fails-by-swap-blindness patterns:

**Inconsistency across swap-action classes.**  `Raw.b` has
view `1`, and `view (swap Raw.b) = view Raw.a = 0`, forcing
`conj 1 = 0`.  But `Raw.slash Raw.a Raw.b` ALSO has view `1`
(since `max 0 1 = 1`), and it is *swap-invariant* (swap maps
it to itself as a Raw term), forcing `conj 1 = 1`.  The two
constraints are incompatible, so no `SwapMatching conj`
exists.

This mechanism requires `combine` to be **idempotent with
absorbing behaviour**: a non-trivial image element (here `1`)
is reachable both as a swap-flipped base (`view b`) and as a
swap-fixed composite (`view (a/b)`).  The same pattern would
break any lattice-valued Lens with non-discrete base values.
-/

namespace E213.Hypervisor.Lens.Instances.Max
open E213.Firmware E213.Hypervisor

/-- **Max lens.**  `a ↦ 0`, `b ↦ 1`, combine = max. -/
def maxLens : Hypervisor.Lens Nat where
  base_a  := 0
  base_b  := 1
  combine := max

-- Base + level-2 view values (direct reduction).

example : maxLens.view Raw.a = 0 := rfl
example : maxLens.view Raw.b = 1 := rfl

theorem maxLens_view_ab :
    maxLens.view (Raw.slash Raw.a Raw.b (by decide)) = 1 := rfl

/-- `slash a b` is swap-invariant at the Raw level.  Tree.swap
    sends `slash a b` to `slash (swap a) (swap b) = slash b a`
    which re-canonicalises back to `slash a b`. -/
theorem slash_ab_swap_fixed :
    Raw.swap (Raw.slash Raw.a Raw.b (by decide))
      = Raw.slash Raw.a Raw.b (by decide) := by
  apply Subtype.ext; rfl

end E213.Hypervisor.Lens.Instances.Max
namespace E213.Hypervisor.Lens.Instances.Max
open E213.Firmware E213.Hypervisor

-- ═══ R4 fails: two Raw terms force inconsistent `conj 1` values ═══

/-- **R4 fails for `maxLens`.**  Two witnesses pin down `conj 1`
    to contradictory values:
    - `Raw.b` has view `1`; `view (swap b) = view a = 0`, so
      `conj 1 = 0`.
    - `Raw.slash a b` has view `1` and is swap-invariant, so
      `conj 1 = 1`.

    `0 ≠ 1` completes the contradiction. -/
theorem maxLens_R4_fails :
    ¬ ∃ conj : Nat → Nat, SwapMatching maxLens conj := by
  rintro ⟨conj, hmatch⟩
  have hswap := hmatch.2.2
  have h1_from_b : conj 1 = 0 := by
    have h := hswap Raw.b
    show conj 1 = 0
    rw [show maxLens.view Raw.b = 1 from rfl,
        show Raw.swap Raw.b = Raw.a from Raw.swap_b,
        show maxLens.view Raw.a = 0 from rfl] at h
    exact h.symm
  have h1_from_ab : conj 1 = 1 := by
    let r : Raw := Raw.slash Raw.a Raw.b (by decide)
    have h := hswap r
    rw [show maxLens.view r = 1 from rfl,
        slash_ab_swap_fixed] at h
    exact h.symm
  rw [h1_from_b] at h1_from_ab
  exact absurd h1_from_ab (by decide)

-- ═══ R5 fails: only 0 and 1 are reachable ═══

/-- **R5 fails for `maxLens`.**  The image is contained in
    `{0, 1}` (base values are 0, 1 and `max` preserves this
    set), so any Lens separating > 2 distinct Raw terms fails.
    Explicit witness: `Raw.b` and `Raw.slash a b` both map to
    `1` but are distinct Raw terms. -/
theorem maxLens_not_injective :
    ¬ Function.Injective maxLens.view := by
  intro hinj
  let r : Raw := Raw.slash Raw.a Raw.b (by decide)
  have heq : maxLens.view Raw.b = maxLens.view r := rfl
  have : Raw.b = r := hinj heq
  exact absurd (congrArg Subtype.val this) (by decide)

end E213.Hypervisor.Lens.Instances.Max