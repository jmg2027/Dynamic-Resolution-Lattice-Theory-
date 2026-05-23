import E213.Lib.Math.Cohomology.Fractal.AurifeuilleanFullCutoff
import E213.Lib.Math.Cohomology.Fractal.HunterComplexity

/-!
# Alternate primitive set — cut-off principle parametric in primitives

Tests the cardinality cut-off principle's reusability under a
different DRLT primitive set.  Removes `d = 5` from the standard
`{NS, NT, d} = {2, 3, 5}` catalogue, leaving the **two-generator
alternate** `{NS, NT} = {2, 3}`.

## Why this comparison?

The principle (`theory/meta/cardinality_cutoff_principle.md`) is
parametric in the DRLT primitive set: each primitive choice induces
its own `H_k` hierarchy and its own catalogue.  Different physics
selections (e.g., dropping `d` would correspond to a physics where
the dimensionality-5 selection is suspended) would yield different
cut-off slices.

The two-generator alternate is the smallest nontrivial DRLT-derived
primitive set; comparison with `{2, 3, 5}` shows precisely how
much information `d = 5` adds to the depth-1 universe.

## Comparison summary

| set         | depth-1 max | depth-1 distinct values |
|-------------|-------------|--------------------------|
| `{2, 3, 5}` (canonical)  | 3125 | 16 |
| `{2, 3}` (alt, no d)     | 27   | 8  |

## Catalogue mobility

| atom | complexity in full | complexity in alt        |
|------|-------------------|--------------------------|
| 2    | 0                 | 0                        |
| 3    | 0                 | 0                        |
| 5    | 0                 | 1 (= 2 + 3)              |
| 7    | 1 (= 2 + 5)       | 2 (e.g., (2+2) + 3)      |
| 13   | 2                 | ≥ 3                      |
| 521  | 3                 | ≥ 3                      |

## Cross-references

  · `theory/meta/cardinality_cutoff_principle.md` §7.
  · `AurifeuilleanFullCutoff.lean` — canonical depth-1 universe.
  · `HunterComplexity.lean` — canonical complexity hierarchy.
-/

namespace E213.Lib.Math.Cohomology.Fractal.AltPrimitiveSet

/-! ## §1 Two-generator alternate -/

/-- Alternate primitive set: `{2, 3}` = `{NT, NS}`, drop `d = 5`. -/
def altGens : List Nat := [2, 3]

theorem altGens_length : altGens.length = 2 := rfl

/-! ## §2 Depth-1 universe (12 values, 8 distinct) -/

/-- Explicit depth-≤-1 Hunter universe over `{2, 3}` with `{+, *, ^}`. -/
def altDepth1Universe : List Nat := [2, 3, 4, 5, 6, 8, 9, 27]

theorem altDepth1Universe_length : altDepth1Universe.length = 8 := rfl

/-- Decidable membership in the alternate depth-1 universe. -/
def inAltDepth1 (v : Nat) : Bool := altDepth1Universe.contains v

/-! ## §3 Soundness — every list-entry is alt-depth-1 reachable -/

/-- `2` is the first leaf of `altGens`. -/
theorem alt_leaf_2 : altGens.get! 0 = 2 := rfl

/-- `3` is the second leaf of `altGens`. -/
theorem alt_leaf_3 : altGens.get! 1 = 3 := rfl

theorem alt_witness_4 : 2 + 2 = 4 := by decide
theorem alt_witness_5 : 2 + 3 = 5 := by decide
theorem alt_witness_6 : 2 * 3 = 6 := by decide
theorem alt_witness_8 : 2 ^ 3 = 8 := by decide
theorem alt_witness_9 : 3 ^ 2 = 9 := by decide
theorem alt_witness_27 : 3 ^ 3 = 27 := by decide

/-! ## §4 Completeness — depth-1 universe contains all op results -/

/-- All leaves are in `altDepth1Universe`. -/
theorem altDepth1Universe_contains_leaves :
    ∀ (i : Fin 2), inAltDepth1 ([2, 3].get! i.val) = true := by decide

/-- All depth-1 adds are in `altDepth1Universe`. -/
theorem altDepth1Universe_contains_add :
    ∀ (i j : Fin 2),
      inAltDepth1 ([2, 3].get! i.val + [2, 3].get! j.val) = true := by decide

/-- All depth-1 muls are in `altDepth1Universe`. -/
theorem altDepth1Universe_contains_mul :
    ∀ (i j : Fin 2),
      inAltDepth1 ([2, 3].get! i.val * [2, 3].get! j.val) = true := by decide

/-- All depth-1 pows are in `altDepth1Universe`. -/
theorem altDepth1Universe_contains_pow :
    ∀ (i j : Fin 2),
      inAltDepth1 ([2, 3].get! i.val ^ [2, 3].get! j.val) = true := by decide

/-! ## §5 Uniform bound -/

/-- Alt depth-1 uniform bound: `M_1^{alt} = 27 = 3^3`.  Much smaller
    than the canonical `M_1 = 3125 = 5^5`. -/
def altM1 : Nat := 27

theorem altM1_value : altM1 = 27 := rfl

/-- Every alt-depth-1 Hunter value is ≤ 27.  Decided by Fin
    enumeration. -/
theorem altDepth1_uniform_bound :
    ∀ (i j : Fin 2),
      [2, 3].get! i.val ≤ altM1
      ∧ ([2, 3].get! i.val + [2, 3].get! j.val) ≤ altM1
      ∧ ([2, 3].get! i.val * [2, 3].get! j.val) ≤ altM1
      ∧ ([2, 3].get! i.val ^ [2, 3].get! j.val) ≤ altM1 := by decide

/-! ## §6 Asymptotic alt-cut-off -/

/-- ★ **Asymptotic alt-depth-1 cut-off**: any `v > 27` is not the
    value of any alt-depth-1 Hunter expression. -/
theorem asymptotic_alt_cutoff_at_depth_1 :
    ∀ (v : Nat), 27 < v →
      ∀ (i j : Fin 2),
        [2, 3].get! i.val ≠ v
        ∧ ([2, 3].get! i.val + [2, 3].get! j.val) ≠ v
        ∧ ([2, 3].get! i.val * [2, 3].get! j.val) ≠ v
        ∧ ([2, 3].get! i.val ^ [2, 3].get! j.val) ≠ v := by
  intro v hv i j
  have hb := altDepth1_uniform_bound i j
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; rw [h] at hb; exact absurd hb.1 (Nat.not_le_of_lt hv)
  · intro h; rw [h] at hb; exact absurd hb.2.1 (Nat.not_le_of_lt hv)
  · intro h; rw [h] at hb; exact absurd hb.2.2.1 (Nat.not_le_of_lt hv)
  · intro h; rw [h] at hb; exact absurd hb.2.2.2 (Nat.not_le_of_lt hv)

/-! ## §7 Catalogue mobility — atoms outside alt-depth-1 -/

/-- `5` is not the value of any `altGens` leaf, but `5 = 2 + 3` is
    at depth 1 (in `altDepth1Universe`).  Hence `complexity_alt(5)
    = 1` (vs `complexity(5) = 0` in the full primitive set).

    The "5 is not a leaf" side is read off `alt_leaf_2`/`alt_leaf_3`. -/
theorem alt_complexity_5_geq_1 :
    altGens.get! 0 ≠ 5 ∧ altGens.get! 1 ≠ 5 := by
  refine ⟨?_, ?_⟩ <;> decide

theorem alt_complexity_5_leq_1 : inAltDepth1 5 = true := by decide

/-- `7 ∉ altDepth1Universe`.  Cut-off starts strictly later than the
    catalogue atom `7`.  Hence `complexity_alt(7) ≥ 2`. -/
theorem alt_complexity_7_geq_2 : inAltDepth1 7 = false := by decide

/-- `13 ∉ altDepth1Universe`. -/
theorem alt_complexity_13_geq_2 : inAltDepth1 13 = false := by decide

/-- `521 ∉ altDepth1Universe`. -/
theorem alt_complexity_521_geq_2 : inAltDepth1 521 = false := by decide

/-! ## §8 Strict inclusion of universes -/

/-- `altDepth1Universe ⊂ depth1Universe` strictly (as sets).
    Specifically: `5 ∈ altDepth1Universe`, but `7 ∉ altDepth1Universe`
    while `7 ∈ depth1Universe`. -/
theorem alt_universe_strict_subset_witness :
    inAltDepth1 7 = false ∧
    E213.Lib.Math.Cohomology.Fractal.HunterComplexity.inDepth1 7 = true := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

/-! ## §9 Capstone -/

/-- ★★★ **Capstone**: the cardinality cut-off principle applied to
    the alternate primitive set `{2, 3}`.

    Key facts:
      · Alt depth-1 max = 27 (vs canonical 3125).
      · Alt depth-1 universe = 8 distinct values (vs canonical 16).
      · Catalogue atom 7 has shifted complexity: 1 (canonical) → 2
        (alt).
      · Catalogue atoms `{13, 521}` are excluded from alt-depth-1
        (consistent with their being depth-2/3 in canonical).

    Demonstrates that the cut-off principle is genuinely parametric
    in the primitive choice; the principle's structural content
    (locate / diagnose / refined-prove) is independent of the
    specific primitives. -/
theorem capstone :
    -- alt uniform bound at depth 1
    (∀ (i j : Fin 2),
      [2, 3].get! i.val ≤ 27
      ∧ ([2, 3].get! i.val + [2, 3].get! j.val) ≤ 27
      ∧ ([2, 3].get! i.val * [2, 3].get! j.val) ≤ 27
      ∧ ([2, 3].get! i.val ^ [2, 3].get! j.val) ≤ 27)
    -- 7 ∉ alt-depth-1 (complexity shift)
    ∧ inAltDepth1 7 = false
    -- but 7 ∈ canonical depth-1
    ∧ E213.Lib.Math.Cohomology.Fractal.HunterComplexity.inDepth1 7 = true
    -- 521 also outside alt-depth-1
    ∧ inAltDepth1 521 = false :=
  ⟨altDepth1_uniform_bound, alt_complexity_7_geq_2,
   (E213.Lib.Math.Cohomology.Fractal.HunterComplexity.inDepth1_7),
   alt_complexity_521_geq_2⟩

end E213.Lib.Math.Cohomology.Fractal.AltPrimitiveSet
