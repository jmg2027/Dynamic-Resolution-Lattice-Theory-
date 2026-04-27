import E213.Research.FoldStructured
import E213.Research.RawACharLens

/-!
# Research.SlashCharNotFold: the characteristic of a specific slash is not fold-structured

**Correspondence**: leaf characteristics are Lens-expressible (RawACharLens.lean)
but **the characteristic of a specific slash is NOT**.

## Witness

`slashAB := slash Raw.a Raw.b`.  `f r := decide (r = slashAB)`.

- f(Raw.a) = false, f(Raw.b) = false, f(slashAB) = true.
- Assuming fold structure: c(false, false) = true (slashAB case).
- But slash(Raw.a, slash(Raw.a, slashAB)): f = false for all subs,
  so overall f = false.  c(false, false) must be false.
- The same c(false, false) cannot be both true and false.  Contradiction.

## Significance

**Asymmetry of leaf vs. non-leaf in Raw**: leaf (Raw.a, Raw.b) can each
be individually identified, but a specific slash cannot be identified
at the view level — slash is "compositional" and cannot distinguish itself
by view alone.

This is the precise limit of the "observation" concept: the **specific
structure** Raw.slash x y h is not distinguishable by a "top-down" Lens.
Lens only permits fold-compositional observation.
-/

namespace E213.Research.SlashCharNotFold

open E213.Firmware E213.Hypervisor
open E213.Research.FoldStructured

/-- slashAB = slash(Raw.a, Raw.b). -/
def slashAB : Raw := Raw.slash Raw.a Raw.b (by decide)

/-- slash(a, slash(a, slashAB)). -/
def outerR : Raw :=
  Raw.slash Raw.a (Raw.slash Raw.a slashAB (by decide)) (by decide)

/-- f r := decide (r = slashAB). -/
def slashCharFn (r : Raw) : Bool := decide (r = slashAB)

end E213.Research.SlashCharNotFold

namespace E213.Research.SlashCharNotFold

open E213.Firmware E213.Hypervisor
open E213.Research.FoldStructured

private theorem slashCharFn_a : slashCharFn Raw.a = false := by decide
private theorem slashCharFn_b : slashCharFn Raw.b = false := by decide
private theorem slashCharFn_slashAB : slashCharFn slashAB = true := by decide
private theorem slashCharFn_outerR : slashCharFn outerR = false := by decide

-- f of slash(a, slashAB) = false (≠ slashAB since the structure differs).
private def innerR : Raw := Raw.slash Raw.a slashAB (by decide)
private theorem slashCharFn_innerR : slashCharFn innerR = false := by decide

/-- **slashCharFn 은 fold-structured 아님**. -/
theorem slashCharFn_not_fold_structured :
    ¬ FoldStructured slashCharFn := by
  intro ⟨ba, bb, c, hba, hbb, _, hslash⟩
  -- slashAB = slash(a, b, _).  f(slashAB) = c(f a)(f b) = c(ba)(bb)
  --                                        = c(false)(false) (after hba, hbb)
  -- f(slashAB) = true ⟹ c(false, false) = true.
  have h1 : slashCharFn slashAB
              = c (slashCharFn Raw.a) (slashCharFn Raw.b) :=
    hslash Raw.a Raw.b (by decide)
  rw [slashCharFn_slashAB, slashCharFn_a, slashCharFn_b] at h1
  -- h1 : true = c false false
  -- outerR = slash(a, innerR, _).  f(outerR) = c(f a)(f innerR) = c(false, false)
  -- f(outerR) = false ⟹ c(false, false) = false.
  have h2 : slashCharFn outerR
              = c (slashCharFn Raw.a) (slashCharFn innerR) :=
    hslash Raw.a innerR (by decide)
  rw [slashCharFn_outerR, slashCharFn_a, slashCharFn_innerR] at h2
  -- h2 : false = c false false
  -- h1, h2: c(false, false) = true and false. Contradiction.
  rw [← h1] at h2
  exact absurd h2 (by decide)

end E213.Research.SlashCharNotFold
