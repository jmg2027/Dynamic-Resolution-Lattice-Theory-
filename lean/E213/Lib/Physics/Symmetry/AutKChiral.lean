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

end E213.Lib.Physics.Symmetry.AutKChiral

namespace E213.Lib.Physics.Symmetry.AutKChiral

open E213.Lib.Physics.Simplex.Counts (NS NT)

/-! ## §1 — Factorial (decide-friendly local def) -/

/-- Factorial as a structurally-recursive Nat function. -/
def fac : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * fac n

theorem fac_0 : fac 0 = 1 := by decide
theorem fac_1 : fac 1 = 1 := by decide
theorem fac_2 : fac 2 = 2 := by decide
theorem fac_3 : fac 3 = 6 := by decide
theorem fac_4 : fac 4 = 24 := by decide
theorem fac_5 : fac 5 = 120 := by decide

/-! ## §2 — Aut order computation -/

/-- |Sym(NS)| = NS! = 3! = 6 (S-vertex permutations). -/
def sym_NS_order : Nat := fac NS
theorem sym_NS_order_eq_6 : sym_NS_order = 6 := by decide

/-- |Sym(NT)| = NT! = 2! = 2 (T-vertex permutations). -/
def sym_NT_order : Nat := fac NT
theorem sym_NT_order_eq_2 : sym_NT_order = 2 := by decide

/-- External symmetry order = NS! · NT! = 12 = c·NS·NT (= K-edge count). -/
def external_order : Nat := sym_NS_order * sym_NT_order
theorem external_order_eq_12 : external_order = 12 := by decide

/-- Internal symmetry C_2^(NS·NT) = 2^6 = 64 sheet-swap choices. -/
def internal_order : Nat := 2 ^ (NS * NT)
theorem internal_order_eq_64 : internal_order = 64 := by decide

/-- Total |Aut(K_{3,2}^{(c=2)})| = external · internal = 12 · 64 = 768. -/
def aut_order : Nat := external_order * internal_order

theorem aut_order_eq_768 : aut_order = 768 := by decide

/-- Master formula: |Aut| = NS! · NT! · 2^(NS·NT). -/
theorem aut_order_formula : aut_order = fac NS * fac NT * 2^(NS*NT) := by decide

end E213.Lib.Physics.Symmetry.AutKChiral

namespace E213.Lib.Physics.Symmetry.AutKChiral

open E213.Lib.Physics.Simplex.Counts (NS NT)

/-! ## §3 — Adjoint SU dimensions (gauge group hint) -/

/-- dim adjoint SU(NS) = NS² − 1.  Matches `1/α_3 = 8` and
    `dim H¹(K_{3,2}^{(c=2)})` (the "lost cohomology" rank). -/
def adj_SU_NS : Nat := NS * NS - 1
theorem adj_SU_NS_eq_8 : adj_SU_NS = 8 := by decide

/-- dim adjoint SU(NT) = NT² − 1 = 3. -/
def adj_SU_NT : Nat := NT * NT - 1
theorem adj_SU_NT_eq_3 : adj_SU_NT = 3 := by decide

/-- Adjoint sum = (NS² − 1) + (NT² − 1) = 11. -/
def adj_sum : Nat := adj_SU_NS + adj_SU_NT
theorem adj_sum_eq_11 : adj_sum = 11 := by decide

/-- adj SU(NS) · adj SU(NT) = 8 · 3 = 24 = adjoint SU(d).
    (d² − 1 with d = NS + NT = 5: 5² − 1 = 24.) -/
def adj_product : Nat := adj_SU_NS * adj_SU_NT
theorem adj_product_eq_24 : adj_product = 24 := by decide
theorem adj_product_eq_adj_SU_d : adj_product = (NS + NT) * (NS + NT) - 1 := by decide

/-! ## §4 — Edge-count and external-Aut order: structural identity -/

/-- K_{3,2}^{(c=2)} edge count E = c · NS · NT = 12. -/
def E_K : Nat := 2 * NS * NT

theorem E_K_eq_12 : E_K = 12 := by decide

/-- Structural identity: |external Aut| = K-edge count = 12.  Both equal
    NS! · NT! and c · NS · NT respectively, but coincide
    numerically because NS! · NT! = 6 · 2 = 12 = 2 · 3 · 2 = c · NS · NT. -/
theorem external_order_eq_E_K : external_order = E_K := by decide

/-! ## §5 — Internal C_2^E vs sheet-swap count -/

/-- Internal symmetry order = 2^(distinct ST edges) = 2^6 = 64.
    This is the ℤ₂ "phase choice" group at each ST edge, the
    finite analog of a U(1)^E gauge field. -/
theorem internal_eq_64_eq_2_to_NS_NT : internal_order = 2 ^ (NS * NT) := by decide

/-- Sheet-swap doubling: c · NS · NT (= K edges) = NS · NT (= ST
    edges) · c, so internal C_2^E = 2^(K-edges/c) = 2^(NS·NT). -/
theorem sheet_swap_decomp : internal_order = 2 ^ (E_K / 2) := by decide

end E213.Lib.Physics.Symmetry.AutKChiral

namespace E213.Lib.Physics.Symmetry.AutKChiral

open E213.Lib.Physics.Simplex.Counts (NS NT)

/-! ## §6 — Master Aut(K) structure theorem (C3 step 1) -/

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
