import E213.Lib.Physics.AlphaEM.ChannelCohomologyLoss

/-!
# Aut(K_{3,2}^{(c=2)}) — automorphism group structure (C3 step 1)

Step 1 of conjecture C3 (Aut(K) gauge group emergence) per
`research-notes/G35_chiral_cup_ring_catalog.md`.

The automorphism group of K_{3,2}^{(c=2)} as a multi-graph
decomposes into

  Aut(K_{3,2}^{(c=2)}) = C_2^(NS·NT) ⋊ (Sym(NS) × Sym(NT))

where:

  · **External symmetry** Sym(NS) × Sym(NT) permutes the
    bipartite vertex sets (S = {0, 1, 2}, T = {3, 4})
    independently.
  · **Internal symmetry** C_2^(NS·NT) swaps the c=2 sheets at
    each of the NS·NT = 6 distinct ST edges (independent
    binary choice per edge).
  · The action is semidirect because permuting vertices
    permutes the edge index set, hence reindexes the C_2 group.

This file encodes the cardinality |Aut| = 768 and its
decomposition `768 = NS! · NT! · 2^(NS·NT) = 6 · 2 · 64`.

## Connection to gauge group emergence

The semidirect structure (Sym(NS) × Sym(NT)) ⋊ C_2^E exhibits a
chiral bipartite factorization.  The internal C_2^E ("sheet
swap") + external Sym(NS) × Sym(NT) decomposition is the
213-internal structure that a gauge-and-spacetime Lens would
name as a "bipartite gauge symmetry"; here it is intrinsic to
the simplex, no spacetime/gauge dichotomy is invoked.

Adjoint SU dimensions match cohomological loss counts:
  · dim adj SU(NS) = NS² − 1 = 8 = 1/α_3 = dim H¹(K)
  · dim adj SU(NT) = NT² − 1 = 3
  · sum 8 + 3 = 11 (composite count of the bipartite adjoint)

These are NOT yet representations — full representation
decomposition of Aut(K) on H*(K, Δ⁴) is the open frontier.
This file provides the **group structure data** required for
that next step.

STRICT ∅-AXIOM (decide on Nat identities).
-/

namespace E213.Lib.Physics.Symmetry.AutKChiral

open E213.Lib.Physics.Simplex.Counts (NS NT)



/-! ## §1 — Factorial (decide-friendly local def) -/

/-- Factorial as a structurally-recursive Nat function. -/
def fac : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fac n

/-! ## §2 — Aut order computation -/

/-- |Sym(NS)| = NS! = 3! = 6 (S-vertex permutations). -/
def sym_NS_order : Nat := fac NS

/-- |Sym(NT)| = NT! = 2! = 2 (T-vertex permutations). -/
def sym_NT_order : Nat := fac NT

/-- External symmetry order = NS! · NT! = 12 = c·NS·NT (= K-edge count). -/
def external_order : Nat := sym_NS_order * sym_NT_order

/-- Internal symmetry C_2^(NS·NT) = 2^6 = 64 sheet-swap choices. -/
def internal_order : Nat := 2 ^ (NS * NT)

/-- Total |Aut(K_{3,2}^{(c=2)})| = external · internal = 12 · 64 = 768. -/
def aut_order : Nat := external_order * internal_order

/-! ## §3 — Adjoint SU dimensions (gauge group hint) -/

/-- dim adjoint SU(NS) = NS² − 1.  Matches `1/α_3 = 8` and
    `dim H¹(K_{3,2}^{(c=2)})` (the "lost cohomology" rank). -/
def adj_SU_NS : Nat := NS * NS - 1

/-- ★ Externally used (by `GluonChannelInterpretation`).  The other
    numeric witnesses (`sym_NS_order = 6`, `adj_SU_NT = 3`, etc.)
    are now conjuncts of the master capstone below. -/
theorem adj_SU_NS_eq_8 : adj_SU_NS = 8 := by decide

/-- dim adjoint SU(NT) = NT² − 1 = 3. -/
def adj_SU_NT : Nat := NT * NT - 1

/-- Adjoint sum = (NS² − 1) + (NT² − 1) = 11. -/
def adj_sum : Nat := adj_SU_NS + adj_SU_NT

/-- adj SU(NS) · adj SU(NT) = 8 · 3 = 24 = adjoint SU(d).
    (d² − 1 with d = NS + NT = 5: 5² − 1 = 24.) -/
def adj_product : Nat := adj_SU_NS * adj_SU_NT

/-! ## §4 — Edge-count and external-Aut order: structural identity -/

/-- K_{3,2}^{(c=2)} edge count E = c · NS · NT = 12. -/
def E_K : Nat := 2 * NS * NT

/-! ## §5 — Master Aut(K) structure theorem (C3 step 1) -/

/-- ★★★★★ Aut(K_{3,2}^{(c=2)}) Structure Master Theorem.
    STRICT ∅-AXIOM.

    This is **Step 1** of conjecture C3 (Aut → gauge group emergence).
    It establishes the group-cardinality data only; full
    representation decomposition (the gauge-group-emergence
    theorem itself) remains open.

    Bundles:

      (i)   |Aut| = NS! · NT! · 2^(NS·NT) = 6 · 2 · 64 = **768**
      (ii)  External / internal decomposition:
              external = Sym(NS) × Sym(NT), order 12 = c·NS·NT
              internal = C_2^(NS·NT), order 64 = 2^6
      (iii) Adjoint SU dimensions:
              dim adj SU(NS) = NS² − 1 = 8 (= 1/α_3)
              dim adj SU(NT) = NT² − 1 = 3
              dim adj SU(d)  = (NS+NT)² − 1 = 24 = adj·adj
      (iv)  Structural identity: |external Aut| = E_K (= 12)
            (NS! · NT! = c · NS · NT under atomicity (3, 2)).
      (v)   Internal sheet-swap order = 2^(E_K / c) = 2^(NS·NT). -/
theorem aut_K_structure_master :
    -- (i) Aut order
    aut_order = 768
    ∧ aut_order = fac NS * fac NT * 2^(NS*NT)
    -- (ii) External/internal decomposition
    ∧ external_order = 12
    ∧ internal_order = 64
    ∧ aut_order = external_order * internal_order
    -- (iii) Adjoint SU dimensions
    ∧ adj_SU_NS = 8
    ∧ adj_SU_NT = 3
    ∧ adj_sum = 11
    ∧ adj_product = 24
    ∧ adj_product = (NS + NT) * (NS + NT) - 1
    -- (iv) external = E_K structural identity
    ∧ external_order = E_K
    ∧ E_K = 12
    -- (v) Internal sheet-swap form
    ∧ internal_order = 2 ^ (NS * NT)
    ∧ internal_order = 2 ^ (E_K / 2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Physics.Symmetry.AutKChiral
