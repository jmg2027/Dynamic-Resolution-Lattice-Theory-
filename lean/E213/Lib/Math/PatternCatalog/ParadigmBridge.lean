import E213.Lib.Math.PatternCatalog.Core
import E213.Lib.Math.PatternCatalog.Algebra
import E213.Lib.Math.ParadigmDomain
/-!
# Pattern Catalog ↔ ParadigmDomain bridge

Bridges the *abstract* pattern stratification (atomic games +
operators) in `PatternCatalog/` with the *applied* paradigm
unification (9 domain witnesses) in `ParadigmDomain`.

**Bridge thesis**:

  Each `ParadigmWitness` instance is a `Typeclass`-pattern record
  (3 fields, no recursion, no period).  The 9 paradigm-domain
  instances are the `facts` field of an `Aggregate ParadigmWitness`
  with arity 9.  The forced-uniformity statement
  `∀ i < 9, (facts i).truncation_grade = 5` instantiates the
  `Forced` operator pattern on the grade field.

In Pattern-Catalog operator-word language (`PatternCatalog.Algebra`):

  ParadigmDomain  ≅  Apply (A · F) (ParadigmWitness)
                  ≅  Aggregate (Forced grade-at-5) ParadigmWitness

Reading: ParadigmDomain instantiates the operator word "AF" — the
Aggregate operator (bundle 9 facts) composed with the Forced
operator (each fact's grade is uniquely 5).

All declarations PURE.
-/

namespace E213.Lib.Math.PatternCatalog.ParadigmBridge

open E213.Lib.Math.PatternCatalog.Core (Aggregate)
open E213.Lib.Math.PatternCatalog.Algebra (OpWord)
open E213.Lib.Math.ParadigmDomain
  (ParadigmWitness
   Combinatorics_paradigm Probability_paradigm Information_paradigm
   Logic_paradigm Topology_paradigm Multivariable_paradigm
   Complex_paradigm Measure_paradigm Cohomology_paradigm)

/-- The 9 paradigm-domain instances indexed by `Fin 9` / `Nat`.

    Index map:
      0 → Combinatorics,  1 → Probability,  2 → Information,
      3 → Logic,          4 → Topology,     5 → Multivariable,
      6 → Complex,        7 → Measure,      8 → Cohomology

    Out-of-range indices default to Combinatorics for totality. -/
def paradigmAt : Nat → ParadigmWitness
  | 0 => Combinatorics_paradigm
  | 1 => Probability_paradigm
  | 2 => Information_paradigm
  | 3 => Logic_paradigm
  | 4 => Topology_paradigm
  | 5 => Multivariable_paradigm
  | 6 => Complex_paradigm
  | 7 => Measure_paradigm
  | 8 => Cohomology_paradigm
  | _ => Combinatorics_paradigm

/-- The full bridge object: ParadigmDomain as an `Aggregate`
    of `ParadigmWitness` from the Pattern Catalog.  Phase `"BB"`
    (Both-Bound) — both endpoints fixed: arity 9, grades all 5. -/
def paradigmAggregate : Aggregate ParadigmWitness :=
  { phase := "BB",
    arity := 9,
    facts := paradigmAt }

/-! ## Pointwise uniformity at each domain index -/

/-- Every paradigm-domain entry has `truncation_grade = 5`. -/
theorem paradigm_grade_at : ∀ i, i < 9 →
    (paradigmAt i).truncation_grade = 5
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | n + 9, hi => absurd hi (by
      show ¬ (n + 9 < 9)
      exact Nat.not_lt.mpr (Nat.le_add_left 9 n))

/-- Every paradigm-domain entry has `truncation_holds = true`. -/
theorem paradigm_holds_at : ∀ i, i < 9 →
    (paradigmAt i).truncation_holds = true
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | n + 9, hi => absurd hi (by
      show ¬ (n + 9 < 9)
      exact Nat.not_lt.mpr (Nat.le_add_left 9 n))

/-- Every paradigm-domain entry has `atom_decidable = true`. -/
theorem paradigm_decide_at : ∀ i, i < 9 →
    (paradigmAt i).atom_decidable = true
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | n + 9, hi => absurd hi (by
      show ¬ (n + 9 < 9)
      exact Nat.not_lt.mpr (Nat.le_add_left 9 n))

/-! ## Forced-uniqueness reading -/

/-- All 9 paradigm-domain entries are **literally equal** at the
    structure level.  This is the Forced-Uniqueness pattern
    instantiated at the typeclass-record level: the bundle is
    "trivially uniform" (constant function). -/
theorem paradigm_all_equal : ∀ i, i < 9 →
    paradigmAt i = Combinatorics_paradigm
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | n + 9, hi => absurd hi (by
      show ¬ (n + 9 < 9)
      exact Nat.not_lt.mpr (Nat.le_add_left 9 n))

/-- The aggregate's arity is exactly the paradigm-domain count (9). -/
theorem paradigmAggregate_arity :
    paradigmAggregate.arity = 9 := rfl

/-- The aggregate's phase tag. -/
theorem paradigmAggregate_phase :
    paradigmAggregate.phase = "BB" := rfl

/-! ## Operator-word reading

In Pattern-Catalog algebra (`OpWord`), `paradigmAggregate` instantiates
the **2-letter word** `A F` (Aggregate of Forced) over the base type
`ParadigmWitness`.

The forced-uniqueness layer says "each entry's grade is forced to 5";
the aggregate layer says "9 such forced entries are bundled".  The
composition is the operator word `A F` applied to `ParadigmWitness`.
-/

/-- The operator-word reading of `ParadigmDomain`.  Length 2,
    aggCount 1, forCount 1. -/
def paradigmOpWord : OpWord :=
  .A (.F .nil)

theorem paradigmOpWord_length :
    paradigmOpWord.length = 2 := rfl

theorem paradigmOpWord_aggCount :
    paradigmOpWord.aggCount = 1 := rfl

theorem paradigmOpWord_forCount :
    paradigmOpWord.forCount = 1 := rfl

/-! ## Capstone: bridge witness

The bridge witness packages: (a) the aggregate object, (b) the
uniformity statement, (c) the operator-word reading.  This is the
single Lean-level statement of "ParadigmDomain instantiates the
PatternCatalog A·F operator word". -/

/-- ★★★★ **Bridge capstone**: `ParadigmDomain` IS a `PatternCatalog`
    `Aggregate ∘ Forced` instantiation on `ParadigmWitness`.

    Bundles: arity 9 ∧ uniform grade 5 ∧ uniform holds ∧ uniform
    decidability ∧ operator-word AF (length 2, aggCount 1, forCount 1). -/
theorem paradigm_pattern_bridge_capstone :
    paradigmAggregate.arity = 9
    ∧ (∀ i, i < 9 → (paradigmAt i).truncation_grade = 5)
    ∧ (∀ i, i < 9 → (paradigmAt i).truncation_holds = true)
    ∧ (∀ i, i < 9 → (paradigmAt i).atom_decidable = true)
    ∧ paradigmOpWord.length = 2
    ∧ paradigmOpWord.aggCount = 1
    ∧ paradigmOpWord.forCount = 1 := by
  refine ⟨rfl, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · exact paradigm_grade_at
  · exact paradigm_holds_at
  · exact paradigm_decide_at

end E213.Lib.Math.PatternCatalog.ParadigmBridge
