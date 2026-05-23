import E213.Lib.Math.Cohomology.Bipartite.H1K
import E213.Lib.Physics.Symmetry.Sym3OnH1KMatrix

/-!
# Sym(3) Cayley structure on H¹(K) — Phase 6

Phase 6 of the **C3 chain** — extends Phase 5's σ_S01 matrix
with the σ_S12 representation matrix and verifies the full
Sym(3) Cayley structure at the H1K matrix level.

## σ_S12 structure (no tree correction needed)

σ_S12 swaps S1 ↔ S2, hence:
  · Edges 4, 5, 6, 7 (src=1)  ↔  edges 8, 9, 10, 11 (src=2)
  · Edges 0, 1, 2, 3 (src=0)  fixed.

Tree edges {0, 2, 4, 8}:
  · 0, 2 fixed; 4 ↔ 8 — both tree edges.  Tree set preserved.

Non-tree edges {1, 3, 5, 6, 7, 9, 10, 11}:
  · 1, 3 fixed
  · 5 ↔ 9, 6 ↔ 10, 7 ↔ 11 — all non-tree ↔ non-tree.
  · No tree-coboundary correction required!

So M_S12 is a **pure permutation matrix** on the H1K basis:
  identity on {e_0, e_1}, three transpositions (e_2 e_5)(e_3 e_6)(e_4 e_7).

  intTrace M_S12 = 2  (e_0 + e_1 fixed; six others paired).
  sign of permutation = (-1)^3 = -1  (3 transpositions).

## Cayley relations

ρ_S = σ_S12 ∘ σ_S01.  We compute M_ρ = M_S12 · M_S01 directly
and verify ρ_S has order 3 at the matrix level.

All theorems below are **PURE** via `decide`.
-/

namespace E213.Lib.Physics.Symmetry.Sym3OnH1KCayley

open E213.Lib.Math.Cohomology.Bipartite.H1K (H1K)
open E213.Lib.Physics.Symmetry.Sym3OnH1KMatrix
  (M_S01 M_mul_vec M_mul_M IdMatrix boolTrace intTrace
   M_S01_squared_pointwise boolTrace_M_S01 intTrace_M_S01)

/-! ## §1.  σ_S12 representation matrix -/

/-- The σ_S12 representation matrix on H1K (8 column vectors).
    Pure permutation: identity on {e_0, e_1}, transpositions
    (e_2 e_5)(e_3 e_6)(e_4 e_7). -/
def M_S12 : Fin 8 → H1K := fun i =>
  match i.val with
  | 0 => fun j => decide (j.val = 0)
  | 1 => fun j => decide (j.val = 1)
  | 2 => fun j => decide (j.val = 5)
  | 3 => fun j => decide (j.val = 6)
  | 4 => fun j => decide (j.val = 7)
  | 5 => fun j => decide (j.val = 2)
  | 6 => fun j => decide (j.val = 3)
  | _ => fun j => decide (j.val = 4)

/-- M_S12 is an involution: M_S12² = I. -/
theorem M_S12_squared_pointwise :
    ∀ i j : Fin 8, M_mul_M M_S12 M_S12 i j = IdMatrix i j := by decide

/-- M_S12 row e_2 has a single `true` at coordinate 5. -/
theorem M_S12_e2 : M_S12 ⟨2, by decide⟩ ⟨5, by decide⟩ = true := rfl

/-- M_S12 row e_5 has a single `true` at coordinate 2. -/
theorem M_S12_e5 : M_S12 ⟨5, by decide⟩ ⟨2, by decide⟩ = true := rfl

/-- M_S12 fixes e_0. -/
theorem M_S12_e0 : M_S12 ⟨0, by decide⟩ ⟨0, by decide⟩ = true := rfl

/-- Bool-trace of M_S12 = false (mod-2 character).  2 fixed = 0 mod 2. -/
theorem boolTrace_M_S12 : boolTrace M_S12 = false := by decide

/-- Integer-trace of M_S12 = 2 (e_0, e_1 fixed). -/
theorem intTrace_M_S12 : intTrace M_S12 = 2 := by decide

/-! ## §2.  Sym(3) 3-cycle representation matrix

ρ = σ_S12 ∘ σ_S01 (or equivalently σ_S01 followed by σ_S12 in our
convention).  M_ρ = M_S12 · M_S01 by matrix multiplication. -/

/-- The ρ_S representation matrix on H1K: M_ρ = M_S12 · M_S01. -/
def M_ρ : Fin 8 → H1K := M_mul_M M_S12 M_S01

/-- M_ρ³ = I at the matrix level (ρ has order 3). -/
theorem M_ρ_cubed_pointwise :
    ∀ i j : Fin 8, M_mul_M (M_mul_M M_ρ M_ρ) M_ρ i j = IdMatrix i j := by decide

/-- Bool-trace of M_ρ = true.  Over F_2 this is the mod-2 character
    on the 3-cycle class of Sym(3). -/
theorem boolTrace_M_ρ : boolTrace M_ρ = true := by decide

/-- Integer-trace of M_ρ = 1.  Only e_3 is fixed in the diagonal
    expansion (via the tree-decomp correction).  Counted directly.
    Note: tr is basis-dependent over ℤ; the basis-independent
    F_2-trace is bool-trace = true. -/
theorem intTrace_M_ρ : intTrace M_ρ = 1 := by decide

/-! ## §3.  σ_S02 derived matrix

σ_S02 = σ_S01 · σ_S12 · σ_S01, so M_S02 = M_S01 · M_S12 · M_S01. -/

/-- The σ_S02 representation matrix on H1K. -/
def M_S02 : Fin 8 → H1K := M_mul_M (M_mul_M M_S01 M_S12) M_S01

/-- M_S02² = I (σ_S02 is a transposition, order 2). -/
theorem M_S02_squared_pointwise :
    ∀ i j : Fin 8, M_mul_M M_S02 M_S02 i j = IdMatrix i j := by decide

/-! ## §4.  Cayley relation check

The standard Sym(3) presentation: σ_S01² = σ_S12² = (σ_S01 · σ_S12)³ = e.
We've verified the first two; (σ_S01 · σ_S12)³ corresponds to ρ³ = I
in our convention. -/

/-- ★ Sym(3) Cayley relation σ_S01² = I (already proven in Phase 5,
    re-asserted here for the Cayley capstone). -/
theorem cayley_σ_S01_sq :
    ∀ i j : Fin 8, M_mul_M M_S01 M_S01 i j = IdMatrix i j :=
  M_S01_squared_pointwise

/-- ★ Sym(3) Cayley relation σ_S12² = I. -/
theorem cayley_σ_S12_sq :
    ∀ i j : Fin 8, M_mul_M M_S12 M_S12 i j = IdMatrix i j :=
  M_S12_squared_pointwise

/-- ★ Sym(3) Cayley relation (σ_S12 · σ_S01)³ = I. -/
theorem cayley_ρ_cubed :
    ∀ i j : Fin 8, M_mul_M (M_mul_M M_ρ M_ρ) M_ρ i j = IdMatrix i j :=
  M_ρ_cubed_pointwise

/-! ## §5.  Phase-6 capstone -/

/-- ★★ **Phase-6 capstone**: full Sym(3) Cayley structure realised
    at the H1K matrix level.

      (a) M_S01, M_S12 — transposition generators (order 2)
      (b) M_S02 — third transposition (conjugate of S12 by S01)
      (c) M_ρ = M_S12 · M_S01 — 3-cycle generator (order 3)
      (d) Standard presentation: ⟨σ₁, σ₂ | σ₁² = σ₂² = (σ₁σ₂)³ = e⟩
          all verified at the matrix level by decide
      (e) Integer-trace data (basis-dependent count of fixed
          basis vectors):
            tr(M_S01) = 4, tr(M_S12) = 2, tr(M_ρ) = 1
          Note: over ℤ this depends on the chosen basis (the
          tree-decomp correction for σ_S01 puts a fixed
          contribution at e_3 that doesn't carry over via
          conjugation).  The basis-independent F_2 character
          (boolTrace) is what defines the representation:
            boolTrace(M_S01) = 0, boolTrace(M_S12) = 0,
            boolTrace(M_ρ) = 1
          consistent with σ_S01, σ_S12 conjugate (both
          transpositions, equal F_2 trace).

    The 8-dim H1K rep is realised; the Sym(3)-irrep decomposition
    is a remaining task (Phase 7).  PURE. -/
theorem Sym3OnH1KCayley_capstone :
    -- Generator relations
    (∀ i j : Fin 8, M_mul_M M_S01 M_S01 i j = IdMatrix i j)
    ∧ (∀ i j : Fin 8, M_mul_M M_S12 M_S12 i j = IdMatrix i j)
    ∧ (∀ i j : Fin 8, M_mul_M M_S02 M_S02 i j = IdMatrix i j)
    -- 3-cycle relation
    ∧ (∀ i j : Fin 8, M_mul_M (M_mul_M M_ρ M_ρ) M_ρ i j = IdMatrix i j)
    -- Integer-trace data (basis-dependent fixed-basis counts)
    ∧ intTrace M_S01 = 4
    ∧ intTrace M_S12 = 2
    ∧ intTrace M_ρ = 1
    -- Bool-traces (basis-independent F_2 characters; equal for
    -- conjugate elements: σ_S01, σ_S12 transpositions both → 0)
    ∧ boolTrace M_S01 = false
    ∧ boolTrace M_S12 = false
    ∧ boolTrace M_ρ = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact cayley_σ_S01_sq
  · exact cayley_σ_S12_sq
  · exact M_S02_squared_pointwise
  · exact cayley_ρ_cubed
  · exact intTrace_M_S01
  · exact intTrace_M_S12
  · exact intTrace_M_ρ
  · exact boolTrace_M_S01
  · exact boolTrace_M_S12
  · exact boolTrace_M_ρ

end E213.Lib.Physics.Symmetry.Sym3OnH1KCayley
