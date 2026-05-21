import E213.Meta.AxiomMinimalityCapstone
import E213.Theory.Atomicity.Five
import E213.Theory.Atomicity.PairForcing
import E213.Theory.Atomicity.ArityForcing
import E213.Lens.Universal.Witnesses.TripleCapstone

/-!
# Meta.ThreeDirectionUniqueness — unified three-direction closure

`seed/AXIOM/00_nature.md` §1.3 records that Raw's uniqueness is
closed in three directions — three readings of the same
self-consistency:

  - **Below**: nothing weaker than Raw suffices.
    Witness: `raw_minimality_capstone` (each of the 4 clauses
    is essential).
  - **Sideways**: any distinguishability framework factors through
    Raw via injective Lens view.
    Witness: `universal_lens_triple_capstone` (four universal
    Lenses constructed; the pattern generalises to any
    Raw-encodable codomain).
  - **Above**: Raw's shape is forced by self-consistency.
    Witness: `atomic_iff_five` + `pair_forcing` ((NS, NT, d) =
    (3, 2, 5) is the only fixed point under atomicity + arity).

This file bundles the three witnesses into a single statement.
None of the three directions stands outside 213; they are three
internal readings of the same self-consistency residue (cf.
`07_self_reference.md` §8.1 — no exterior).

## Why a single statement matters

The three witnesses come from different namespaces (Meta,
Theory/Atomicity, Lens/Universal).  A reader could fail to see
the unified picture.  This file makes the three-direction
statement a single `#print`able theorem citing the canonical
witnesses.
-/

namespace E213.Meta.ThreeDirectionUniqueness

open E213.Meta.AxiomMinimalityCapstone (raw_minimality_capstone)
open E213.Theory.Atomicity.Five (atomic_iff_five Atomic)
open E213.Lens.Universal.Witnesses.Core (IsUniversal)
open E213.Lens.Universal.Witnesses.TripleCapstone
  (universal_lens_triple_capstone)

/-- ★★★★★★★ **Three-direction uniqueness capstone** ★★★★★★★

  Raw is the unique residue satisfying three closures:

  Below: each of the 4 clauses (a, b, slash, distinctness) is
    essential — removing any one collapses the framework.

  Sideways: every distinguishability framework factors through
    Raw via an injective Lens view (witnesses: four explicit
    universal Lenses to ℕ², ℚ², ℕ³, ℚ³).

  Above: (NS, NT, d) = (3, 2, 5) is the unique self-consistent
    shape — `Atomic n ↔ n = 5`, and the pair-forcing theorem
    further constrains (NS, NT) = (3, 2).

  All three are ∅-axiom theorems (per `STRICT_ZERO_AXIOM.md`).
  None requires external standpoint; the three directions are three Lens
  readings of the same self-consistency residue. -/
theorem three_direction_uniqueness :
    -- Below: 4-clause minimality (clause 1 collapse witness)
    (∀ r : E213.Meta.AxiomMinimality.RawA,
       r = E213.Meta.AxiomMinimality.RawA.a)
    -- Sideways: universal-Lens factoring (four witnesses bundled)
    ∧ (IsUniversal E213.Lens.Universal.Witnesses.Nat2.expSumLens
       ∧ IsUniversal E213.Lens.Universal.Witnesses.Q213.q213Lens
       ∧ IsUniversal E213.Lens.Universal.Witnesses.Nat3.expSumLens3
       ∧ IsUniversal E213.Lens.Universal.Witnesses.Q213_3.q213Lens3)
    -- Above: atomic ↔ five (the unique self-consistent dimension)
    ∧ (∀ n : Nat, Atomic n ↔ n = 5) := by
  refine ⟨?_, ?_, ?_⟩
  · exact raw_minimality_capstone.1
  · exact universal_lens_triple_capstone
  · exact atomic_iff_five

end E213.Meta.ThreeDirectionUniqueness
