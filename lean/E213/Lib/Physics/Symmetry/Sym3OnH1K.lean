import E213.Lib.Math.Cohomology.Bipartite.V32
import E213.Lib.Math.Cohomology.Bipartite.H1K
import E213.Lib.Physics.Symmetry.Sym3OnKEdges

/-!
# Sym(3) descent to H¹(K) via δ⁰ equivariance

Phase 4 of the **C3 chain**.  Phase 3 (`Sym3OnKEdges.lean`)
constructed the edge action; this file proves the action
**descends to H¹(K)** by exhibiting the corresponding vertex
permutations and verifying δ⁰ equivariance:

  `delta0 (σ ∘ φ_V) = (delta0 σ) ∘ φ_E`

This equivariance implies the edge action sends coboundaries to
coboundaries, hence induces a well-defined action on
H¹(K) = Z¹ / im(δ⁰).

## Vertex permutations

S-vertices are {0, 1, 2}; T-vertices are {3, 4}.

  · `φ_V_S01` swaps vertices 0 ↔ 1, fixes {2, 3, 4}
  · `φ_V_S12` swaps vertices 1 ↔ 2, fixes {0, 3, 4}

Edge encoding via src/tgt (from `V32.lean`):
  · src e = (e/2)/2 ∈ {0,1,2}   (S-vertex)
  · tgtFin e = 3 + (e/2)%2 ∈ {3,4}   (T-vertex)

Compatibility: φ_V (src e) = src (φ_E e) and φ_V (tgtFin e) = tgtFin (φ_E e).
The src equivariance is the substantive content; tgt equivariance is
trivial since both transpositions fix T-vertices.

All theorems below are **PURE** via `decide`.
-/

namespace E213.Lib.Physics.Symmetry.Sym3OnH1K

open E213.Lib.Math.Cohomology.Bipartite.V32 (CochV CochE delta0 srcFin tgtFin)
open E213.Lib.Physics.Symmetry.Sym3OnKEdges (σ_S01 σ_S12 σ_S02 σ_act_E)

/-! ## §1.  Vertex permutations -/

/-- Vertex permutation for σ_S01: swap 0 ↔ 1, fix {2, 3, 4}. -/
def φ_V_S01 (v : Fin 5) : Fin 5 :=
  match v.val with
  | 0 => ⟨1, by decide⟩
  | 1 => ⟨0, by decide⟩
  | _ => v

/-- Vertex permutation for σ_S12: swap 1 ↔ 2, fix {0, 3, 4}. -/
def φ_V_S12 (v : Fin 5) : Fin 5 :=
  match v.val with
  | 1 => ⟨2, by decide⟩
  | 2 => ⟨1, by decide⟩
  | _ => v

/-- φ_V_S01 is an involution. -/
theorem φ_V_S01_involution : ∀ v : Fin 5, φ_V_S01 (φ_V_S01 v) = v := by decide

/-- φ_V_S12 is an involution. -/
theorem φ_V_S12_involution : ∀ v : Fin 5, φ_V_S12 (φ_V_S12 v) = v := by decide

/-! ## §2.  δ⁰ equivariance

For each transposition (σ_E, φ_V), the equivariance
`srcFin ∘ σ_E = φ_V ∘ srcFin` and
`tgtFin ∘ σ_E = φ_V ∘ tgtFin`
hold edge-by-edge (decide-verified). -/

/-- σ_S01 / φ_V_S01 source equivariance: `srcFin (σ_S01 e) = φ_V_S01 (srcFin e)`. -/
theorem src_equiv_S01 :
    ∀ e : Fin 12, srcFin (σ_S01 e) = φ_V_S01 (srcFin e) := by decide

/-- σ_S01 / φ_V_S01 target equivariance: T-vertices fixed. -/
theorem tgt_equiv_S01 :
    ∀ e : Fin 12, tgtFin (σ_S01 e) = φ_V_S01 (tgtFin e) := by decide

/-- σ_S12 / φ_V_S12 source equivariance. -/
theorem src_equiv_S12 :
    ∀ e : Fin 12, srcFin (σ_S12 e) = φ_V_S12 (srcFin e) := by decide

/-- σ_S12 / φ_V_S12 target equivariance. -/
theorem tgt_equiv_S12 :
    ∀ e : Fin 12, tgtFin (σ_S12 e) = φ_V_S12 (tgtFin e) := by decide

/-! ## §3.  Vertex-cochain action -/

/-- Pullback action on vertex cochains: (φ · σ)(v) := σ(φ v). -/
def φ_act_V (φ : Fin 5 → Fin 5) (σ : CochV) : CochV :=
  fun v => σ (φ v)

/-! ## §4.  δ⁰ equivariance theorem

The key result: `delta0 (φ_V · σ) (e) = (σ_E · (delta0 σ)) (e)` for
each transposition pair.  Pointwise, no funext. -/

/-- δ⁰ equivariance under σ_S01 / φ_V_S01.  PURE. -/
theorem delta0_equiv_S01 (σ : CochV) (e : Fin 12) :
    delta0 (φ_act_V φ_V_S01 σ) e
      = σ_act_E σ_S01 (delta0 σ) e := by
  show xor (σ (φ_V_S01 (srcFin e))) (σ (φ_V_S01 (tgtFin e)))
      = xor (σ (srcFin (σ_S01 e))) (σ (tgtFin (σ_S01 e)))
  rw [src_equiv_S01 e, tgt_equiv_S01 e]

/-- δ⁰ equivariance under σ_S12 / φ_V_S12.  PURE. -/
theorem delta0_equiv_S12 (σ : CochV) (e : Fin 12) :
    delta0 (φ_act_V φ_V_S12 σ) e
      = σ_act_E σ_S12 (delta0 σ) e := by
  show xor (σ (φ_V_S12 (srcFin e))) (σ (φ_V_S12 (tgtFin e)))
      = xor (σ (srcFin (σ_S12 e))) (σ (tgtFin (σ_S12 e)))
  rw [src_equiv_S12 e, tgt_equiv_S12 e]

/-! ## §5.  Descent to H¹(K)

The equivariance theorem implies:

  (σ_E · (delta0 σ)) = delta0 (φ_V · σ)

so the edge action sends coboundaries to coboundaries.  Therefore
σ_E descends to a well-defined action on H¹(K) = CochE / im(δ⁰). -/

/-- ★ The image of a coboundary under σ_S01 is a coboundary.
    Witness: `σ_act_E σ_S01 (delta0 σ) = delta0 (φ_act_V φ_V_S01 σ)`.
    Pointwise form, no funext. -/
theorem σ_S01_preserves_coboundaries (σ : CochV) (e : Fin 12) :
    σ_act_E σ_S01 (delta0 σ) e = delta0 (φ_act_V φ_V_S01 σ) e :=
  (delta0_equiv_S01 σ e).symm

/-- ★ The image of a coboundary under σ_S12 is a coboundary. -/
theorem σ_S12_preserves_coboundaries (σ : CochV) (e : Fin 12) :
    σ_act_E σ_S12 (delta0 σ) e = delta0 (φ_act_V φ_V_S12 σ) e :=
  (delta0_equiv_S12 σ e).symm

/-! ## §6.  Action on H1K basis vectors

For the explicit non-tree edge basis of H1K (per `H1K.lean`):
non-tree edges {1, 3, 5, 6, 7, 9, 10, 11}.  σ_S01 permutes these:
  1 (S0-T0, m1) ↔ 5 (S1-T0, m1)
  3 (S0-T1, m1) ↔ 7 (S1-T1, m1)
  6 (S1-T1, m0) → 2 (S0-T1, m0) — tree edge!  Coboundary correction needed.
  9 (S2-T0, m1) fixed (S2-related)
  10 (S2-T1, m0) fixed
  11 (S2-T1, m1) fixed

The non-tree → tree transitions create non-trivial coboundary
corrections in the H1K representation matrix.  Per Phase 5,
the full Sym(3)-irrep decomposition resolves these into 1+1+2+...
copies of the standard Sym(3) irreps.  Below we record the bare
edge permutation on non-tree edges for sanity. -/

/-- σ_S01 sends non-tree edge 1 to non-tree edge 5. -/
theorem σ_S01_nontree_1 : σ_S01 ⟨1, by decide⟩ = ⟨5, by decide⟩ := rfl

/-- σ_S01 sends non-tree edge 3 to non-tree edge 7. -/
theorem σ_S01_nontree_3 : σ_S01 ⟨3, by decide⟩ = ⟨7, by decide⟩ := rfl

/-- σ_S01 sends non-tree edge 6 to **tree edge 2** — coboundary needed. -/
theorem σ_S01_nontree_6_to_tree : σ_S01 ⟨6, by decide⟩ = ⟨2, by decide⟩ := rfl

/-- σ_S01 sends non-tree edge 7 to non-tree edge 3 (inverse of edge 3 map). -/
theorem σ_S01_nontree_7 : σ_S01 ⟨7, by decide⟩ = ⟨3, by decide⟩ := rfl

/-- σ_S01 fixes S2-related non-tree edges {9, 10, 11}. -/
theorem σ_S01_fixes_S2 :
    σ_S01 ⟨9, by decide⟩ = ⟨9, by decide⟩
    ∧ σ_S01 ⟨10, by decide⟩ = ⟨10, by decide⟩
    ∧ σ_S01 ⟨11, by decide⟩ = ⟨11, by decide⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-! ## §7.  Phase-4 capstone -/

/-- ★★ **Phase-4 capstone**: Sym(3) descends to a well-defined
    action on H¹(K_{3,2}^{(c=2)}) via δ⁰ equivariance.

    Substantive content:
      (a) Vertex permutations φ_V_S01, φ_V_S12 are involutions
      (b) src/tgt equivariance for each transposition pair
      (c) δ⁰ equivariance: σ_E · delta0 = delta0 · φ_V (pointwise)
      (d) Image of coboundary under σ_E is a coboundary
      (e) Hence σ_E induces a well-defined action on
          H¹(K) = Z¹ / im(δ⁰)
      (f) Edge mappings on non-tree basis: explicit values
          (some non-tree → tree transitions require coboundary
          correction in the basis decomposition).

    PURE. -/
theorem Sym3OnH1K_phase4_capstone :
    -- Vertex permutations are involutions
    (∀ v : Fin 5, φ_V_S01 (φ_V_S01 v) = v)
    ∧ (∀ v : Fin 5, φ_V_S12 (φ_V_S12 v) = v)
    -- src/tgt equivariance
    ∧ (∀ e : Fin 12, srcFin (σ_S01 e) = φ_V_S01 (srcFin e))
    ∧ (∀ e : Fin 12, tgtFin (σ_S01 e) = φ_V_S01 (tgtFin e))
    ∧ (∀ e : Fin 12, srcFin (σ_S12 e) = φ_V_S12 (srcFin e))
    ∧ (∀ e : Fin 12, tgtFin (σ_S12 e) = φ_V_S12 (tgtFin e))
    -- δ⁰ equivariance ⇒ coboundary preservation (σ_S01)
    ∧ (∀ σ : CochV, ∀ e : Fin 12,
        σ_act_E σ_S01 (delta0 σ) e = delta0 (φ_act_V φ_V_S01 σ) e)
    -- δ⁰ equivariance ⇒ coboundary preservation (σ_S12)
    ∧ (∀ σ : CochV, ∀ e : Fin 12,
        σ_act_E σ_S12 (delta0 σ) e = delta0 (φ_act_V φ_V_S12 σ) e)
    -- Sample edge mappings (non-tree behaviour)
    ∧ σ_S01 ⟨1, by decide⟩ = ⟨5, by decide⟩
    ∧ σ_S01 ⟨6, by decide⟩ = ⟨2, by decide⟩
    := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact φ_V_S01_involution
  · exact φ_V_S12_involution
  · exact src_equiv_S01
  · exact tgt_equiv_S01
  · exact src_equiv_S12
  · exact tgt_equiv_S12
  · exact σ_S01_preserves_coboundaries
  · exact σ_S12_preserves_coboundaries
  · rfl
  · rfl

end E213.Lib.Physics.Symmetry.Sym3OnH1K
