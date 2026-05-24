/-!
# Cohomology — K_{4,3}^{(c=2)} bipartite multigraph

Asymmetric bipartite multigraph `K_{NS, NT}^{(c)}` at `(NS, NT, c) = (4, 3, 2)`.

  · 7 vertices (4 S + 3 T), `Fin 7`
  · 24 edges (4·3·2), `Fin 24`
  · 18 simple 4-cycles in underlying K_{4,3}
    (`C(4,2) × C(3,2) = 6 × 3 = 18`)

## Cycle space

Underlying simple K_{4,3} has cycle-space dim = E − V + 1 =
12 − 7 + 1 = 6.  Hence the 18 simple 4-cycles satisfy 12
independent dependence relations.

With 18 face cells: `dim C² = 18`, `rank δ¹ ≤ 6`, so
`b₂ ≥ dim C² − rank δ¹ ≥ 18 − 6 = 12`.

→ **H² ≥ F₂¹²** at K_{4,3}^{(c=2)}.  Richer than K_{3,3}.

## Massey prospects

With H¹ × H¹ × H¹ → H² ≥ F₂¹², the Massey product structure
has up-to-12-dimensional output.  Each non-trivial dimension is
a potential independent secondary cohomology operation.

This file establishes the foundational edge / face / coboundary
infrastructure.  Specific cup-table, cocycle representatives,
and Massey witnesses are follow-up work.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.V43

/-- Vertex cochain space: `Fin 7 → Bool` (NS=4, NT=3). -/
def CochV : Type := Fin 7 → Bool

/-- Edge cochain space: `Fin 24 → Bool` (NS·NT·c = 24).

    Edge indexing convention: edge (S_i, T_j) at mult m has index
    `12·m + 3·i + j` for i ∈ Fin 4, j ∈ Fin 3, m ∈ Fin 2. -/
def CochE : Type := Fin 24 → Bool

/-- Source vertex (S-idx, 0..3) of edge e. -/
def srcOf (e : Nat) : Nat := (e / 2) / 3

/-- Target vertex (T-idx + 4, 4..6) of edge e. -/
def tgtOf (e : Nat) : Nat := 4 + (e / 2) % 3

/-- Multiplicity (0 or 1) of edge e. -/
def multOf (e : Nat) : Nat := e % 2

/-! ## §1 — Generic face boundary -/

/-- Generic face boundary: XOR of 4 edge cochain values. -/
def faceBoundary (σ : CochE) (e0 e1 e2 e3 : Fin 24) : Bool :=
  xor (xor (xor (σ e0) (σ e1)) (σ e2)) (σ e3)

/-! ## §2 — Sample face cycles (mult-0)

The first 3 faces use S-pair (0,1) with the 3 T-pairs (0,1), (0,2),
(1,2).  Edge indexing: edge (i, j, mult=0) at index `6·i + 2·j`. -/

/-- Face (S={0,1}, T={0,1}, mult-0): edges (0,0,0), (0,1,0), (1,0,0), (1,1,0). -/
def face_S01_T01 (σ : CochE) : Bool :=
  faceBoundary σ ⟨0, by decide⟩ ⟨2, by decide⟩
                 ⟨6, by decide⟩ ⟨8, by decide⟩

/-- Face (S={0,1}, T={0,2}, mult-0): edges (0,0,0), (0,2,0), (1,0,0), (1,2,0). -/
def face_S01_T02 (σ : CochE) : Bool :=
  faceBoundary σ ⟨0, by decide⟩ ⟨4, by decide⟩
                 ⟨6, by decide⟩ ⟨10, by decide⟩

/-- Face (S={0,1}, T={1,2}, mult-0): edges (0,1,0), (0,2,0), (1,1,0), (1,2,0). -/
def face_S01_T12 (σ : CochE) : Bool :=
  faceBoundary σ ⟨2, by decide⟩ ⟨4, by decide⟩
                 ⟨8, by decide⟩ ⟨10, by decide⟩

/-! ## §3 — Sample face dependence relation R_{S₀₁}

`face_S01_T01 ⊕ face_S01_T02 ⊕ face_S01_T12 = 0` — sum over the 3
T-pairs at fixed S-pair (0,1).  This is a homological dependence
analogous to V33's `face_dep_S01`. -/

theorem face_dep_S01_at_K43 :
    ∀ σ : CochE,
      xor (xor (face_S01_T01 σ) (face_S01_T02 σ)) (face_S01_T12 σ) = false := by
  intro σ
  unfold face_S01_T01 face_S01_T02 face_S01_T12 faceBoundary
  cases σ ⟨0, by decide⟩ <;> cases σ ⟨2, by decide⟩ <;>
    cases σ ⟨4, by decide⟩ <;> cases σ ⟨6, by decide⟩ <;>
    cases σ ⟨8, by decide⟩ <;> cases σ ⟨10, by decide⟩ <;> rfl

/-! ## §3.5 — Additional S-row face cycles (S-pair indexing)

S-pairs of Fin 4: (0,1), (0,2), (0,3), (1,2), (1,3), (2,3) — 6 pairs.
Already defined: S01_T01, S01_T02, S01_T12.  Additional S-pair faces
needed below. -/

/-- Face (S={0,2}, T={0,1}, mult-0): edges (0,0,0), (0,1,0), (2,0,0), (2,1,0). -/
def face_S02_T01 (σ : CochE) : Bool :=
  faceBoundary σ ⟨0, by decide⟩ ⟨2, by decide⟩
                 ⟨12, by decide⟩ ⟨14, by decide⟩

/-- Face (S={0,2}, T={0,2}, mult-0). -/
def face_S02_T02 (σ : CochE) : Bool :=
  faceBoundary σ ⟨0, by decide⟩ ⟨4, by decide⟩
                 ⟨12, by decide⟩ ⟨16, by decide⟩

/-- Face (S={0,2}, T={1,2}, mult-0). -/
def face_S02_T12 (σ : CochE) : Bool :=
  faceBoundary σ ⟨2, by decide⟩ ⟨4, by decide⟩
                 ⟨14, by decide⟩ ⟨16, by decide⟩

/-- S-row dependence at S={0,2}: 3 T-pair faces sum to 0. -/
theorem face_dep_S02_at_K43 :
    ∀ σ : CochE,
      xor (xor (face_S02_T01 σ) (face_S02_T02 σ)) (face_S02_T12 σ) = false := by
  intro σ
  unfold face_S02_T01 face_S02_T02 face_S02_T12 faceBoundary
  cases σ ⟨0, by decide⟩ <;> cases σ ⟨2, by decide⟩ <;>
    cases σ ⟨4, by decide⟩ <;> cases σ ⟨12, by decide⟩ <;>
    cases σ ⟨14, by decide⟩ <;> cases σ ⟨16, by decide⟩ <;> rfl

/-- Face (S={2,3}, T={0,1}, mult-0): edges (2,0,0), (2,1,0), (3,0,0), (3,1,0). -/
def face_S23_T01 (σ : CochE) : Bool :=
  faceBoundary σ ⟨12, by decide⟩ ⟨14, by decide⟩
                 ⟨18, by decide⟩ ⟨20, by decide⟩

/-- Face (S={2,3}, T={0,2}, mult-0). -/
def face_S23_T02 (σ : CochE) : Bool :=
  faceBoundary σ ⟨12, by decide⟩ ⟨16, by decide⟩
                 ⟨18, by decide⟩ ⟨22, by decide⟩

/-- Face (S={2,3}, T={1,2}, mult-0). -/
def face_S23_T12 (σ : CochE) : Bool :=
  faceBoundary σ ⟨14, by decide⟩ ⟨16, by decide⟩
                 ⟨20, by decide⟩ ⟨22, by decide⟩

/-- S-row dependence at S={2,3}. -/
theorem face_dep_S23_at_K43 :
    ∀ σ : CochE,
      xor (xor (face_S23_T01 σ) (face_S23_T02 σ)) (face_S23_T12 σ) = false := by
  intro σ
  unfold face_S23_T01 face_S23_T02 face_S23_T12 faceBoundary
  cases σ ⟨12, by decide⟩ <;> cases σ ⟨14, by decide⟩ <;>
    cases σ ⟨16, by decide⟩ <;> cases σ ⟨18, by decide⟩ <;>
    cases σ ⟨20, by decide⟩ <;> cases σ ⟨22, by decide⟩ <;> rfl

/-- Face (S={0,3}, T={0,1}, mult-0). -/
def face_S03_T01 (σ : CochE) : Bool :=
  faceBoundary σ ⟨0, by decide⟩ ⟨2, by decide⟩
                 ⟨18, by decide⟩ ⟨20, by decide⟩

def face_S03_T02 (σ : CochE) : Bool :=
  faceBoundary σ ⟨0, by decide⟩ ⟨4, by decide⟩
                 ⟨18, by decide⟩ ⟨22, by decide⟩

def face_S03_T12 (σ : CochE) : Bool :=
  faceBoundary σ ⟨2, by decide⟩ ⟨4, by decide⟩
                 ⟨20, by decide⟩ ⟨22, by decide⟩

theorem face_dep_S03_at_K43 :
    ∀ σ : CochE,
      xor (xor (face_S03_T01 σ) (face_S03_T02 σ)) (face_S03_T12 σ) = false := by
  intro σ
  unfold face_S03_T01 face_S03_T02 face_S03_T12 faceBoundary
  cases σ ⟨0, by decide⟩ <;> cases σ ⟨2, by decide⟩ <;>
    cases σ ⟨4, by decide⟩ <;> cases σ ⟨18, by decide⟩ <;>
    cases σ ⟨20, by decide⟩ <;> cases σ ⟨22, by decide⟩ <;> rfl

def face_S12_T01 (σ : CochE) : Bool :=
  faceBoundary σ ⟨6, by decide⟩ ⟨8, by decide⟩
                 ⟨12, by decide⟩ ⟨14, by decide⟩

def face_S12_T02 (σ : CochE) : Bool :=
  faceBoundary σ ⟨6, by decide⟩ ⟨10, by decide⟩
                 ⟨12, by decide⟩ ⟨16, by decide⟩

def face_S12_T12 (σ : CochE) : Bool :=
  faceBoundary σ ⟨8, by decide⟩ ⟨10, by decide⟩
                 ⟨14, by decide⟩ ⟨16, by decide⟩

theorem face_dep_S12_at_K43 :
    ∀ σ : CochE,
      xor (xor (face_S12_T01 σ) (face_S12_T02 σ)) (face_S12_T12 σ) = false := by
  intro σ
  unfold face_S12_T01 face_S12_T02 face_S12_T12 faceBoundary
  cases σ ⟨6, by decide⟩ <;> cases σ ⟨8, by decide⟩ <;>
    cases σ ⟨10, by decide⟩ <;> cases σ ⟨12, by decide⟩ <;>
    cases σ ⟨14, by decide⟩ <;> cases σ ⟨16, by decide⟩ <;> rfl

def face_S13_T01 (σ : CochE) : Bool :=
  faceBoundary σ ⟨6, by decide⟩ ⟨8, by decide⟩
                 ⟨18, by decide⟩ ⟨20, by decide⟩

def face_S13_T02 (σ : CochE) : Bool :=
  faceBoundary σ ⟨6, by decide⟩ ⟨10, by decide⟩
                 ⟨18, by decide⟩ ⟨22, by decide⟩

def face_S13_T12 (σ : CochE) : Bool :=
  faceBoundary σ ⟨8, by decide⟩ ⟨10, by decide⟩
                 ⟨20, by decide⟩ ⟨22, by decide⟩

theorem face_dep_S13_at_K43 :
    ∀ σ : CochE,
      xor (xor (face_S13_T01 σ) (face_S13_T02 σ)) (face_S13_T12 σ) = false := by
  intro σ
  unfold face_S13_T01 face_S13_T02 face_S13_T12 faceBoundary
  cases σ ⟨6, by decide⟩ <;> cases σ ⟨8, by decide⟩ <;>
    cases σ ⟨10, by decide⟩ <;> cases σ ⟨18, by decide⟩ <;>
    cases σ ⟨20, by decide⟩ <;> cases σ ⟨22, by decide⟩ <;> rfl

/-- ★★★★ All 6 S-row dependences at K_{4,3}^(c=2) bundled. -/
theorem K43_all_S_row_deps_bundle :
    ∀ σ : CochE,
      xor (xor (face_S01_T01 σ) (face_S01_T02 σ)) (face_S01_T12 σ) = false
      ∧ xor (xor (face_S02_T01 σ) (face_S02_T02 σ)) (face_S02_T12 σ) = false
      ∧ xor (xor (face_S03_T01 σ) (face_S03_T02 σ)) (face_S03_T12 σ) = false
      ∧ xor (xor (face_S12_T01 σ) (face_S12_T02 σ)) (face_S12_T12 σ) = false
      ∧ xor (xor (face_S13_T01 σ) (face_S13_T02 σ)) (face_S13_T12 σ) = false
      ∧ xor (xor (face_S23_T01 σ) (face_S23_T02 σ)) (face_S23_T12 σ) = false := by
  intro σ
  exact ⟨face_dep_S01_at_K43 σ, face_dep_S02_at_K43 σ, face_dep_S03_at_K43 σ,
         face_dep_S12_at_K43 σ, face_dep_S13_at_K43 σ, face_dep_S23_at_K43 σ⟩

/-! ## §4 — Edge / vertex counts -/

theorem K43_edge_count : 4 * 3 * 2 = 24 := by decide
theorem K43_vertex_count : 4 + 3 = 7 := by decide
theorem K43_simple_face_count : 6 * 3 = 18 := by decide
theorem K43_cycle_space_dim : (4 * 3) - (4 + 3) + 1 = 6 := by decide

end E213.Lib.Math.Cohomology.Bipartite.V43
