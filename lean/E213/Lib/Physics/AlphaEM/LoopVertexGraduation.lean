import E213.Lib.Physics.AlphaEM.PerLayerCoupling

/-!
# Loop-vertex graduation — structural interpretation of `(k+1)`

Formalises the structural interpretation of the `(k+1)` α-power
graduation in the refined cup-ladder formula

      Δ_H^k(c) = ||c||² · (α/d)^(k+1)

via the **cohomology-degree ↔ vacuum-polarization-loop-count**
correspondence:

  · An H^k cohomology class corresponds to a k-loop diagram in
    the QED vacuum polarization expansion of `1/α_em`.
  · A k-loop diagram has `(k+1)` Feynman vertices, each
    contributing one α factor of coupling.
  · Hence the α-power for an H^k class is `(k+1)`.

## Cup-axiom gap

The existing `cup : Cochain n k × Cochain n l → Cochain n (k+l)`
in `Math/Cohomology/Cup/Core.lean` has output cohomology degree
`k + l`.  Under bilinear self-pairing this gives `2k`, NOT `(k+1)`.

  · At k = 1: bilinear self-cup has output degree 2; (k+1) = 2.
    ✓ Coincides at k = 1.
  · At k = 2: bilinear self-cup has output degree 4; (k+1) = 3.
    ✗ Differ at k = 2.

Hence the `(k+1)` graduation does NOT follow from the existing
bilinear cup arity at `k ≥ 2`.  Candidate cohomology-theoretic
derivations:

  · **Higher cup operations** (cup_i, Steenrod squares): produce
    output at `k + l − i` for i ≥ 0; cup_2 at H² self-pairing
    gives output degree 2 (back to top of `K_{3,2}^{(c=2)}`
    2-skeleton).  Formalisation requires Steenrod algebra
    machinery not yet in `Math/Cohomology/`.
  · **Massey products**: triple Massey ⟨a, b, c⟩ defined when
    `ab = 0 = bc`, landing in `H^(a+b+c-1)`.  Would give a 3-fold
    structure matching α³ at H², but requires partial-operation
    formalisation.
  · **Filtration spectral sequence**: the `d_r` differential
    increases filtration depth by r; at page r the surviving
    classes have α-coupling order `r + 1`.  Hodge-De Rham
    spectral sequence formalisation is also a substantial
    undertaking.

Recorded here at the **interpretive** level: structural posit with
documented physics interpretation, NOT a cup-axiom derivation.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Physics.AlphaEM.LoopVertexGraduation

open E213.Lib.Math.Cohomology.Bipartite.Filled3CellCohomology
open E213.Lib.Physics.AlphaEM.GradedFormulaPrecision
open E213.Lib.Physics.AlphaEM.GramSelfConsistency
open E213.Lib.Physics.AlphaEM.OmegaH2Trace
open E213.Lib.Physics.AlphaEM.OmegaPostGramFull
open E213.Lib.Physics.AlphaEM.PerLayerCoupling

/-! ## §1 — Cohomology degree ↔ loop count -/

/-- An H^k cohomology class on `K_{3,2}^{(c=2)}` corresponds to a
    k-loop diagram in the QED vacuum polarization expansion of
    `1/α_em`.  Identity map at the structural level. -/
def loopCountAtH (k : Nat) : Nat := k

/-! ## §2 — Loop count ↔ Feynman vertex count -/

/-- A k-loop diagram has `(k+1)` Feynman vertices in the vacuum
    polarization expansion of `1/α_em`.  Each vertex contributes
    one α coupling factor.

    · 0-loop (tree): 1 vertex → α¹ (raw 5-layer formula).
    · 1-loop:         2 vertices → α² (Gram self-energy).
    · 2-loop:         3 vertices → α³ (ω contribution).
    · k-loop:        (k+1) vertices → α^(k+1). -/
def vertexCountAtLoops (loops : Nat) : Nat := loops + 1

/-! ## §3 — α-power graduation = vertex count -/

/-- α-power for an H^k cohomology class: composed of the
    cohomology-to-loop map and the loop-to-vertex map. -/
def alphaPowerAtH (k : Nat) : Nat := vertexCountAtLoops (loopCountAtH k)

/-- ★★★ Identity: `alphaPowerAtH k = k + 1` (composition reduces
    to the (k+1) graduation rule). -/
theorem alphaPower_eq_k_plus_1 (k : Nat) : alphaPowerAtH k = k + 1 := rfl

/-! ## §4 — Specialisations at k = 1 (H¹ Gram) and k = 2 (H² ω) -/

/-- ★★★★ H¹ Gram self-energy: 1-loop vacuum polarization, 2
    vertices, α² coupling. -/
theorem h1_gram_loop_vertex :
    loopCountAtH 1 = 1
    ∧ vertexCountAtLoops 1 = 2
    ∧ alphaPowerAtH 1 = 2 := by
  refine ⟨rfl, rfl, rfl⟩

/-- ★★★★ H² ω self-pairing: 2-loop vacuum polarization, 3
    vertices, α³ coupling. -/
theorem h2_omega_loop_vertex :
    loopCountAtH 2 = 2
    ∧ vertexCountAtLoops 2 = 3
    ∧ alphaPowerAtH 2 = 3 := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## §5 — Bridge to refined formula in `PerLayerCoupling` -/

/-- ★★★★★ H¹ Gram correction expressed via the loop-vertex
    graduation: `(α/d)^(alphaPowerAtH 1) = (α/d)² = Gram`. -/
theorem gram_via_loop_vertex :
    gram_correction_e9 = alpha_over_d_pow_e9 (alphaPowerAtH 1) := by
  unfold alphaPowerAtH vertexCountAtLoops loopCountAtH
  exact gram_eq_alpha_over_d_sq

/-- ★★★★★ H² ω-weighted correction expressed via the loop-vertex
    graduation: `NS² · (α/d)^(alphaPowerAtH 2) = 9 · (α/d)³ =
    ω-weighted trace`. -/
theorem omega_weighted_via_loop_vertex :
    omega_weighted_trace_e9 = 9 * alpha_over_d_pow_e9 (alphaPowerAtH 2) := by
  unfold alphaPowerAtH vertexCountAtLoops loopCountAtH
  exact omega_weighted_eq_NS_sq_alpha_over_d_cubed

/-! ## §6 — Cup-axiom gap: bilinear cup vs loop-vertex graduation -/

/-- Output cohomology degree of bilinear cup at degree (k, l) per
    `Math/Cohomology/Cup/Core.lean` `cup`. -/
def cupBilinearOutputDegree (k l : Nat) : Nat := k + l

/-- ★★★ Bilinear cup self-pairing at degree k gives output `2k`.
    This MATCHES α-power `(k+1)` only at k = 1. -/
theorem cup_bilinear_vs_loop_vertex_at_k1 :
    cupBilinearOutputDegree 1 1 = alphaPowerAtH 1 := rfl

/-- ★★★ At k = 2: bilinear cup gives 4, loop-vertex gives 3.
    The two structural rules DIVERGE at k ≥ 2 — the (k+1)
    graduation requires structure BEYOND bilinear cup arity. -/
theorem cup_bilinear_vs_loop_vertex_at_k2 :
    cupBilinearOutputDegree 2 2 = 4
    ∧ alphaPowerAtH 2 = 3
    ∧ cupBilinearOutputDegree 2 2 ≠ alphaPowerAtH 2 := by
  refine ⟨rfl, rfl, by decide⟩

/-! ## §7 — Master capstone -/

/-- ★★★★★★★★ **LoopVertexGraduation master**.  STRICT ∅-AXIOM.

    Formalises the structural interpretation of the `(k+1)` α-power
    graduation as the **cohomology-degree ↔ vacuum-polarization-
    loop-count** correspondence:

      · H^k class ↔ k-loop diagram ↔ (k+1) Feynman vertices ↔ α^(k+1).

    Specialisations:
      · H¹ Gram (1-loop, 2 vertices, α²): matches Gram self-energy.
      · H² ω (2-loop, 3 vertices, α³): matches ω-weighted closure.

    Cup-axiom gap:
      · Bilinear cup at degree (k, l) produces output `k + l`.
      · Self-pairing at degree k gives `2k`, matching (k+1) ONLY at k = 1.
      · At k ≥ 2 the bilinear cup arity DIVERGES from the (k+1) rule.
      · Derivation of (k+1) from cup-product axioms requires higher-cup
        machinery (cup_i, Massey products, or spectral sequences) —
        the Phase 9+ open frontier.

    This file records the loop-vertex correspondence at the
    **interpretive** level: structural posit with documented physics
    interpretation, not a cup-axiom derivation.  Pending higher-cup
    formalisation, the `(k+1)` rule remains a cohomology-degree
    indexed posit whose specialisations match the proved Phase 4-7
    closures at k = 1, 2. -/
theorem loop_vertex_graduation_master :
    -- Cohomology-to-loop map (identity)
    loopCountAtH 1 = 1
    ∧ loopCountAtH 2 = 2
    -- Loop-to-vertex map (loops + 1)
    ∧ vertexCountAtLoops 1 = 2
    ∧ vertexCountAtLoops 2 = 3
    -- Composed α-power graduation
    ∧ alphaPowerAtH 1 = 2
    ∧ alphaPowerAtH 2 = 3
    ∧ (∀ k, alphaPowerAtH k = k + 1)
    -- Bridge to PerLayerCoupling closures
    ∧ gram_correction_e9 = alpha_over_d_pow_e9 (alphaPowerAtH 1)
    ∧ omega_weighted_trace_e9 = 9 * alpha_over_d_pow_e9 (alphaPowerAtH 2)
    -- Cup-axiom gap: bilinear cup ≠ (k+1) at k ≥ 2
    ∧ cupBilinearOutputDegree 1 1 = alphaPowerAtH 1
    ∧ cupBilinearOutputDegree 2 2 ≠ alphaPowerAtH 2 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_,
          gram_via_loop_vertex, omega_weighted_via_loop_vertex,
          rfl, ?_⟩
  · intro k; rfl
  · decide

end E213.Lib.Physics.AlphaEM.LoopVertexGraduation
