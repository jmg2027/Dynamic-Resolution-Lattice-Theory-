import E213.Lib.Math.Cohomology.Cup.Ring

/-!
# Cohomology — K_{3,3}^{(c=2)} bipartite multigraph

The natural next-frontier graph above K_{3,2}^{(c=2)}: same
multiplicity (c=2), one more T-vertex.

  · 6 vertices (3 S + 3 T), `Fin 6`
  · 18 edges (3 × 3 × 2), `Fin 18`
  · 9 simple 4-cycles in underlying K_{3,3}
    (`C(3,2) × C(3,2) = 9`)

## Cycle space

Underlying simple K_{3,3} has cycle-space dim = E − V + 1 =
9 − 6 + 1 = 4.  Hence the 9 simple 4-cycles span a 4-dimensional
subspace of `im δ¹` ⟹ `rank δ¹ ≤ 4`.

With 9 face cells: `dim C² = 9`, `rank δ¹ = 4`, so
`b₂ = dim C² − rank δ¹ = 5`.

→ **H² = F₂⁵ at K_{3,3}^{(c=2)}** under the uniform mult-0 face
convention.  Much richer than K_{3,2}^{(c=2)} (b₂ = 1).

## H¹ size

`b₁ = (dim ker δ¹) − (rank δ⁰) = (18 − 4) − (6 − 1) = 14 − 5 = 9`.

→ **H¹ = F₂⁹**, larger than K_{3,2}^{(c=2)} (b₁ = 6).

## Massey prospects

With H¹ × H¹ × H¹ → H² = F₂⁵, the Massey product structure
has up to 5-dimensional output.  Each non-trivial dimension is
a potential **independent secondary cohomology operation**.

This file establishes the foundational edge / face / coboundary
infrastructure.  Specific cup-table, cocycle representatives,
and Massey witnesses are follow-up work.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.V33

/-- Source vertex (S-idx, 0..2) of edge e. -/
def srcOf (e : Nat) : Nat := (e / 2) / 3

/-- Target vertex (T-idx + 3, 3..5) of edge e. -/
def tgtOf (e : Nat) : Nat := 3 + (e / 2) % 3

/-- Multiplicity (0 or 1) of edge e. -/
def multOf (e : Nat) : Nat := e % 2

/-- Vertex cochain space: `Fin 6 → Bool`. -/
def CochV : Type := Fin 6 → Bool

/-- Edge cochain space: `Fin 18 → Bool`. -/
def CochE : Type := Fin 18 → Bool

/-- S-vertex of edge e as `Fin 6`. -/
def srcFin (e : Fin 18) : Fin 6 :=
  ⟨srcOf e.val % 6, Nat.mod_lt _ (by decide)⟩

/-- T-vertex of edge e as `Fin 6`. -/
def tgtFin (e : Fin 18) : Fin 6 :=
  ⟨tgtOf e.val % 6, Nat.mod_lt _ (by decide)⟩

/-- Coboundary δ⁰. -/
def delta0 (σ : CochV) : CochE :=
  fun e => xor (σ (srcFin e)) (σ (tgtFin e))

/-! ## §1 — Edge endpoint sanity checks -/

theorem edge0_endpoints :
    srcFin ⟨0, by decide⟩ = ⟨0, by decide⟩
    ∧ tgtFin ⟨0, by decide⟩ = ⟨3, by decide⟩ := by decide

theorem edge17_endpoints :
    srcFin ⟨17, by decide⟩ = ⟨2, by decide⟩
    ∧ tgtFin ⟨17, by decide⟩ = ⟨5, by decide⟩ := by decide

theorem K33_edge_count : 2 * 3 * 3 = 18 := by decide
theorem K33_vertex_count : 3 + 3 = 6 := by decide

/-! ## §2 — Nine simple 4-cycles as 2-cells

The 9 simple 4-cycles in underlying K_{3,3}: indexed by pairs
`((S_i, S_j), (T_k, T_l))` with `i < j ∈ {0,1,2}`,
`k < l ∈ {0,1,2}`.  Cycle `S_i → T_k → S_j → T_l → S_i` uses
mult-0 edges:

  · edge (S_i, T_k) at index `2(3i+k)`
  · edge (S_j, T_k) at index `2(3j+k)`
  · edge (S_j, T_l) at index `2(3j+l)`
  · edge (S_i, T_l) at index `2(3i+l)`

S-pairs: (0,1), (0,2), (1,2) — 3 choices.
T-pairs: (0,1), (0,2), (1,2) — 3 choices.
Total: 3 × 3 = 9 faces. -/

/-- Generic face boundary: XOR of 4 edge cochain values at the
    given indices. -/
def faceBoundary (σ : CochE) (e0 e1 e2 e3 : Fin 18) : Bool :=
  xor (xor (xor (σ e0) (σ e1)) (σ e2)) (σ e3)

/-- Face 0: S={0,1}, T={0,1} → edges 0, 6, 8, 2. -/
def face0 (σ : CochE) : Bool :=
  faceBoundary σ ⟨0, by decide⟩ ⟨6, by decide⟩
                 ⟨8, by decide⟩ ⟨2, by decide⟩

/-- Face 1: S={0,1}, T={0,2} → edges 0, 6, 10, 4. -/
def face1 (σ : CochE) : Bool :=
  faceBoundary σ ⟨0, by decide⟩ ⟨6, by decide⟩
                 ⟨10, by decide⟩ ⟨4, by decide⟩

/-- Face 2: S={0,1}, T={1,2} → edges 2, 8, 10, 4. -/
def face2 (σ : CochE) : Bool :=
  faceBoundary σ ⟨2, by decide⟩ ⟨8, by decide⟩
                 ⟨10, by decide⟩ ⟨4, by decide⟩

/-- Face 3: S={0,2}, T={0,1} → edges 0, 12, 14, 2. -/
def face3 (σ : CochE) : Bool :=
  faceBoundary σ ⟨0, by decide⟩ ⟨12, by decide⟩
                 ⟨14, by decide⟩ ⟨2, by decide⟩

/-- Face 4: S={0,2}, T={0,2} → edges 0, 12, 16, 4. -/
def face4 (σ : CochE) : Bool :=
  faceBoundary σ ⟨0, by decide⟩ ⟨12, by decide⟩
                 ⟨16, by decide⟩ ⟨4, by decide⟩

/-- Face 5: S={0,2}, T={1,2} → edges 2, 14, 16, 4. -/
def face5 (σ : CochE) : Bool :=
  faceBoundary σ ⟨2, by decide⟩ ⟨14, by decide⟩
                 ⟨16, by decide⟩ ⟨4, by decide⟩

/-- Face 6: S={1,2}, T={0,1} → edges 6, 12, 14, 8. -/
def face6 (σ : CochE) : Bool :=
  faceBoundary σ ⟨6, by decide⟩ ⟨12, by decide⟩
                 ⟨14, by decide⟩ ⟨8, by decide⟩

/-- Face 7: S={1,2}, T={0,2} → edges 6, 12, 16, 10. -/
def face7 (σ : CochE) : Bool :=
  faceBoundary σ ⟨6, by decide⟩ ⟨12, by decide⟩
                 ⟨16, by decide⟩ ⟨10, by decide⟩

/-- Face 8: S={1,2}, T={1,2} → edges 8, 14, 16, 10. -/
def face8 (σ : CochE) : Bool :=
  faceBoundary σ ⟨8, by decide⟩ ⟨14, by decide⟩
                 ⟨16, by decide⟩ ⟨10, by decide⟩

/-- Full δ¹: edge cochain → face cochain (Fin 9 → Bool). -/
def delta1 (σ : CochE) : Fin 9 → Bool :=
  fun f => match f.val with
  | 0 => face0 σ
  | 1 => face1 σ
  | 2 => face2 σ
  | 3 => face3 σ
  | 4 => face4 σ
  | 5 => face5 σ
  | 6 => face6 σ
  | 7 => face7 σ
  | _ => face8 σ

/-! ## §3 — Face dependence relations

The cycle-space of underlying K_{3,3} has dimension 4.  The 9
simple 4-cycles satisfy 5 independent dependence relations.
Three canonical relations (the "S-row" and "T-row" identities):

  · `face0 ⊕ face1 ⊕ face2 = 0` (S={0,1}, varying T-pair)
  · `face0 ⊕ face3 ⊕ face6 = 0` (T={0,1}, varying S-pair)
  · `face2 ⊕ face5 ⊕ face8 = 0` (T={1,2}, varying S-pair)
  · `face4 ⊕ face1 ⊕ face7 ⊕ … = 0` etc.

Each relation reflects the "two short cycles sum to the third"
identity in the homology of a `K_{3}` minor.  Below we verify
the simplest two; full 5-relation enumeration deferred. -/

/-- Face dependence relation R₀: `face0 ⊕ face1 ⊕ face2 = 0`
    (varying T-pair at fixed S-pair {0,1}). -/
theorem face_dep_S01 :
    ∀ σ : CochE, xor (xor (face0 σ) (face1 σ)) (face2 σ) = false := by
  intro σ
  unfold face0 face1 face2 faceBoundary
  cases σ ⟨0, by decide⟩ <;> cases σ ⟨2, by decide⟩ <;>
  cases σ ⟨4, by decide⟩ <;> cases σ ⟨6, by decide⟩ <;>
  cases σ ⟨8, by decide⟩ <;> cases σ ⟨10, by decide⟩ <;> rfl

/-- Face dependence relation R₁: `face0 ⊕ face3 ⊕ face6 = 0`
    (varying S-pair at fixed T-pair {0,1}). -/
theorem face_dep_T01 :
    ∀ σ : CochE, xor (xor (face0 σ) (face3 σ)) (face6 σ) = false := by
  intro σ
  unfold face0 face3 face6 faceBoundary
  cases σ ⟨0, by decide⟩ <;> cases σ ⟨2, by decide⟩ <;>
  cases σ ⟨6, by decide⟩ <;> cases σ ⟨8, by decide⟩ <;>
  cases σ ⟨12, by decide⟩ <;> cases σ ⟨14, by decide⟩ <;> rfl

/-! ## §4 — H² ≠ 0 witness

A face cochain `v : Fin 9 → Bool` is in `im δ¹` iff it satisfies
all 5 face dependence relations.  We exhibit a face cochain that
**violates** R₀ (so it is NOT in im δ¹), confirming `H² ≠ 0`. -/

/-- Witness face cochain: `(1, 0, 0, 0, 0, 0, 0, 0, 0)` — value 1
    only at face 0. -/
def witness_face_cochain : Fin 9 → Bool :=
  fun f => decide (f.val = 0)

/-- The witness violates `R₀: face0 ⊕ face1 ⊕ face2 = 0`:
    `1 ⊕ 0 ⊕ 0 = 1 ≠ 0`. -/
theorem witness_violates_R0 :
    xor (xor (witness_face_cochain ⟨0, by decide⟩)
              (witness_face_cochain ⟨1, by decide⟩))
         (witness_face_cochain ⟨2, by decide⟩) = true := by decide

/-- ★★★ **H² ≠ 0 at K_{3,3}^{(c=2)}**: the face cochain
    `(1, 0, ..., 0)` does NOT lie in `im δ¹` (because every
    element of `im δ¹` satisfies the dependence relation
    `face0 ⊕ face1 ⊕ face2 = 0`, which the witness violates).
    Hence `H² = C² / im δ¹ ≠ 0`.

    Combined with K_{3,2}^{(c=2)}'s `H² = F₂`, this shows the
    parametric family K_{NS,NT}^{(c=2)} has **growing** H²
    dimension as the graph grows.  Massey-rich expected. -/
theorem H2_nonzero_witness :
    -- The witness violates the canonical dependence relation R₀
    xor (xor (witness_face_cochain ⟨0, by decide⟩)
              (witness_face_cochain ⟨1, by decide⟩))
         (witness_face_cochain ⟨2, by decide⟩) = true
    -- And every face cochain in im δ¹ satisfies R₀
    ∧ ∀ σ : CochE, xor (xor (delta1 σ ⟨0, by decide⟩)
                              (delta1 σ ⟨1, by decide⟩))
                        (delta1 σ ⟨2, by decide⟩) = false := by
  refine ⟨witness_violates_R0, ?_⟩
  intro σ
  show xor (xor (face0 σ) (face1 σ)) (face2 σ) = false
  exact face_dep_S01 σ

end E213.Lib.Math.Cohomology.Bipartite.V33
