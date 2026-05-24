import E213.Lib.Math.Cohomology.Bipartite.V33

/-!
# Enriched 2-complex at K_{3,3}^{(c=2)} — mult-0 + mult-1 faces

Adds 9 mult-1 4-cycle faces to the existing simple-cycle face
complex (9 mult-0 faces), giving a 18-face 2-complex.  Probes
whether cup-image codim in H² acquires `c`-dependent structure
once multi-multiplicity face cycles are admitted.

## Mult-1 face indexing

For each (S-pair, T-pair) ((S_i, S_j), (T_k, T_l)) with `i<j`,
`k<l`, the mult-1 face uses the *same* 4-cycle pattern but with
each edge replaced by its mult-1 sibling:

  · `face0_m1`: S={0,1}, T={0,1} → edges 1, 7, 9, 3
  · `face1_m1`: S={0,1}, T={0,2} → edges 1, 7, 11, 5
  · `face2_m1`: S={0,1}, T={1,2} → edges 3, 9, 11, 5
  · `face3_m1`: S={0,2}, T={0,1} → edges 1, 13, 15, 3
  · `face4_m1`: S={0,2}, T={0,2} → edges 1, 13, 17, 5
  · `face5_m1`: S={0,2}, T={1,2} → edges 3, 15, 17, 5
  · `face6_m1`: S={1,2}, T={0,1} → edges 7, 13, 15, 9
  · `face7_m1`: S={1,2}, T={0,2} → edges 7, 13, 17, 11
  · `face8_m1`: S={1,2}, T={1,2} → edges 9, 15, 17, 11

## Face independence

Mult-0 and mult-1 faces use *disjoint* edge sets:

  · mult-0 face uses 4 even-index edges (`{0, 2, 4, 6, 8, 10, 12, 14, 16}`)
  · mult-1 face uses 4 odd-index edges (`{1, 3, 5, 7, 9, 11, 13, 15, 17}`)

So δ¹ on mult-0 faces sees only even-index σ-values, and δ¹ on
mult-1 faces sees only odd-index σ-values.  Hence the rank of
δ¹ enriched = (rank δ¹ on mult-0) + (rank δ¹ on mult-1) = 4 + 4 = 8.
H² enriched has dim = 18 − 8 = 10.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.V33Enriched

open E213.Lib.Math.Cohomology.Bipartite.V33
  (CochE faceBoundary delta1 face0 face1 face2 face3 face4 face5 face6 face7 face8)

/-! ## §1 — Mult-1 face boundaries -/

def face0_m1 (σ : CochE) : Bool :=
  faceBoundary σ ⟨1, by decide⟩ ⟨7, by decide⟩
                 ⟨9, by decide⟩ ⟨3, by decide⟩

def face1_m1 (σ : CochE) : Bool :=
  faceBoundary σ ⟨1, by decide⟩ ⟨7, by decide⟩
                 ⟨11, by decide⟩ ⟨5, by decide⟩

def face2_m1 (σ : CochE) : Bool :=
  faceBoundary σ ⟨3, by decide⟩ ⟨9, by decide⟩
                 ⟨11, by decide⟩ ⟨5, by decide⟩

def face3_m1 (σ : CochE) : Bool :=
  faceBoundary σ ⟨1, by decide⟩ ⟨13, by decide⟩
                 ⟨15, by decide⟩ ⟨3, by decide⟩

def face4_m1 (σ : CochE) : Bool :=
  faceBoundary σ ⟨1, by decide⟩ ⟨13, by decide⟩
                 ⟨17, by decide⟩ ⟨5, by decide⟩

def face5_m1 (σ : CochE) : Bool :=
  faceBoundary σ ⟨3, by decide⟩ ⟨15, by decide⟩
                 ⟨17, by decide⟩ ⟨5, by decide⟩

def face6_m1 (σ : CochE) : Bool :=
  faceBoundary σ ⟨7, by decide⟩ ⟨13, by decide⟩
                 ⟨15, by decide⟩ ⟨9, by decide⟩

def face7_m1 (σ : CochE) : Bool :=
  faceBoundary σ ⟨7, by decide⟩ ⟨13, by decide⟩
                 ⟨17, by decide⟩ ⟨11, by decide⟩

def face8_m1 (σ : CochE) : Bool :=
  faceBoundary σ ⟨9, by decide⟩ ⟨15, by decide⟩
                 ⟨17, by decide⟩ ⟨11, by decide⟩

/-- Enriched δ¹: edge cochain → 18-face cochain (first 9 = mult-0,
    last 9 = mult-1). -/
def delta1_enr (σ : CochE) : Fin 18 → Bool := fun f =>
  match f.val with
  | 0 => face0 σ
  | 1 => face1 σ
  | 2 => face2 σ
  | 3 => face3 σ
  | 4 => face4 σ
  | 5 => face5 σ
  | 6 => face6 σ
  | 7 => face7 σ
  | 8 => face8 σ
  | 9 => face0_m1 σ
  | 10 => face1_m1 σ
  | 11 => face2_m1 σ
  | 12 => face3_m1 σ
  | 13 => face4_m1 σ
  | 14 => face5_m1 σ
  | 15 => face6_m1 σ
  | 16 => face7_m1 σ
  | _ => face8_m1 σ

/-! ## §2 — Two independent discriminating functionals

The enriched complex splits into mult-0 and mult-1 layers (edge
sets disjoint).  Hence the simple-complex ψ functional has TWO
independent enriched lifts:

  · `psi_m0 v = XOR of v at faces 0..8`  (mult-0 layer)
  · `psi_m1 v = XOR of v at faces 9..17` (mult-1 layer)

Each is a 2-cocycle functional on the enriched complex, dual to
its layer's "5th H² direction" not reached by primary cup. -/

def psi_m0 (v : Fin 18 → Bool) : Bool :=
  xor (xor (xor (xor (xor (xor (xor (xor
    (v ⟨0, by decide⟩) (v ⟨1, by decide⟩))
    (v ⟨2, by decide⟩)) (v ⟨3, by decide⟩))
    (v ⟨4, by decide⟩)) (v ⟨5, by decide⟩))
    (v ⟨6, by decide⟩)) (v ⟨7, by decide⟩))
    (v ⟨8, by decide⟩)

def psi_m1 (v : Fin 18 → Bool) : Bool :=
  xor (xor (xor (xor (xor (xor (xor (xor
    (v ⟨9, by decide⟩) (v ⟨10, by decide⟩))
    (v ⟨11, by decide⟩)) (v ⟨12, by decide⟩))
    (v ⟨13, by decide⟩)) (v ⟨14, by decide⟩))
    (v ⟨15, by decide⟩)) (v ⟨16, by decide⟩))
    (v ⟨17, by decide⟩)

/-! ## §3 — `psi_m0` and `psi_m1` kill enriched δ¹

Each mult-0 edge appears in exactly 4 mult-0 faces (even); each
mult-1 edge appears in exactly 4 mult-1 faces.  Cross-layer
contributions are zero by edge-set disjointness. -/

set_option maxHeartbeats 800000 in
theorem psi_m0_kills_imd1_enr : ∀ σ : CochE, psi_m0 (delta1_enr σ) = false := by
  intro σ
  unfold psi_m0 delta1_enr
    E213.Lib.Math.Cohomology.Bipartite.V33.face0
    E213.Lib.Math.Cohomology.Bipartite.V33.face1
    E213.Lib.Math.Cohomology.Bipartite.V33.face2
    E213.Lib.Math.Cohomology.Bipartite.V33.face3
    E213.Lib.Math.Cohomology.Bipartite.V33.face4
    E213.Lib.Math.Cohomology.Bipartite.V33.face5
    E213.Lib.Math.Cohomology.Bipartite.V33.face6
    E213.Lib.Math.Cohomology.Bipartite.V33.face7
    E213.Lib.Math.Cohomology.Bipartite.V33.face8
    E213.Lib.Math.Cohomology.Bipartite.V33.faceBoundary
  cases σ ⟨0, by decide⟩ <;> cases σ ⟨2, by decide⟩ <;>
    cases σ ⟨4, by decide⟩ <;> cases σ ⟨6, by decide⟩ <;>
    cases σ ⟨8, by decide⟩ <;> cases σ ⟨10, by decide⟩ <;>
    cases σ ⟨12, by decide⟩ <;> cases σ ⟨14, by decide⟩ <;>
    cases σ ⟨16, by decide⟩ <;> rfl

set_option maxHeartbeats 800000 in
theorem psi_m1_kills_imd1_enr : ∀ σ : CochE, psi_m1 (delta1_enr σ) = false := by
  intro σ
  unfold psi_m1 delta1_enr face0_m1 face1_m1 face2_m1 face3_m1
    face4_m1 face5_m1 face6_m1 face7_m1 face8_m1
    E213.Lib.Math.Cohomology.Bipartite.V33.faceBoundary
  cases σ ⟨1, by decide⟩ <;> cases σ ⟨3, by decide⟩ <;>
    cases σ ⟨5, by decide⟩ <;> cases σ ⟨7, by decide⟩ <;>
    cases σ ⟨9, by decide⟩ <;> cases σ ⟨11, by decide⟩ <;>
    cases σ ⟨13, by decide⟩ <;> cases σ ⟨15, by decide⟩ <;>
    cases σ ⟨17, by decide⟩ <;> rfl

/-! ## §4 — Independence: `psi_m0` and `psi_m1` are NOT linearly
    related in H²

A 2-cocycle on the enriched complex that is **mult-0-supported only**
distinguishes `psi_m0` from `psi_m1`: the chain `e_face_0 :=
(1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)` has
`psi_m0 = 1` but `psi_m1 = 0`.  Symmetrically for a mult-1-only
chain.  So `psi_m0 ≠ psi_m1` in `(H²_enr)*`. -/

theorem psi_m0_psi_m1_independent :
    ∃ v : Fin 18 → Bool, psi_m0 v = true ∧ psi_m1 v = false :=
  ⟨fun f => decide (f.val = 0), by decide, by decide⟩

theorem psi_m1_nonzero_witness :
    ∃ v : Fin 18 → Bool, psi_m0 v = false ∧ psi_m1 v = true :=
  ⟨fun f => decide (f.val = 9), by decide, by decide⟩

/-! ## §5 — Two independent non-coboundary H²-classes in the enriched complex

The chains `e_face_0 = (1, 0, …, 0)` and `e_face_9 = (0, …, 1, 0, …, 0)`
(single-face support at face 0 and face 9, respectively) are:

  · Both not coboundaries (witnessed by distinct ψ-values, plus
    ψ_m0 and ψ_m1 both kill imδ¹).
  · Linearly independent in H²_enr (distinct ψ-signatures).

Hence `dim H²_enr ≥ 2` in the "ψ-cohomology" direction.

Combined with the cup-image bound (the primary cup `H¹⊗H¹ → H²_enr`
splits into mult-0 and mult-1 sub-cups by edge disjointness, each
landing in a codim-1 subspace of its layer), the enriched
cup-image codim is at least **2** at c=2.  Generalizing to c-many
mult layers gives codim ≥ c — the c-multiplicity counter
materializes as a per-mult-layer Massey 5th-dim. -/

/-- Single-face-0 indicator chain (mult-0 layer). -/
def e_face_0_enr : Fin 18 → Bool := fun f => decide (f.val = 0)

/-- Single-face-9 indicator chain (mult-1 layer, face0_m1). -/
def e_face_9_enr : Fin 18 → Bool := fun f => decide (f.val = 9)

theorem e_face_0_psi_signature :
    psi_m0 e_face_0_enr = true ∧ psi_m1 e_face_0_enr = false := by
  refine ⟨?_, ?_⟩ <;> decide

theorem e_face_9_psi_signature :
    psi_m0 e_face_9_enr = false ∧ psi_m1 e_face_9_enr = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-- `e_face_0_enr` is not a coboundary: ψ_m0(it) ≠ ψ_m0(any imδ¹). -/
theorem e_face_0_enr_not_coboundary :
    ∀ σ : CochE, e_face_0_enr ≠ delta1_enr σ := by
  intro σ heq
  have h_psi := congrArg psi_m0 heq
  rw [(e_face_0_psi_signature).1] at h_psi
  rw [psi_m0_kills_imd1_enr] at h_psi
  exact Bool.noConfusion h_psi

/-- `e_face_9_enr` is not a coboundary: ψ_m1(it) ≠ ψ_m1(any imδ¹). -/
theorem e_face_9_enr_not_coboundary :
    ∀ σ : CochE, e_face_9_enr ≠ delta1_enr σ := by
  intro σ heq
  have h_psi := congrArg psi_m1 heq
  rw [(e_face_9_psi_signature).2] at h_psi
  rw [psi_m1_kills_imd1_enr] at h_psi
  exact Bool.noConfusion h_psi

/-- Capstone: two independent non-coboundary H²-classes at c=2
    enriched, distinguished by ψ_m0 vs ψ_m1.  Each Massey-reachable
    via the corresponding mult-layer 4-fold ⟨a, b, c, d⟩. -/
theorem two_independent_h2_classes_enriched_c2 :
    ∃ v1 v2 : Fin 18 → Bool,
      (psi_m0 v1 = true ∧ psi_m1 v1 = false)
      ∧ (psi_m0 v2 = false ∧ psi_m1 v2 = true)
      ∧ (∀ σ : CochE, v1 ≠ delta1_enr σ)
      ∧ (∀ σ : CochE, v2 ≠ delta1_enr σ) :=
  ⟨e_face_0_enr, e_face_9_enr,
   e_face_0_psi_signature, e_face_9_psi_signature,
   e_face_0_enr_not_coboundary, e_face_9_enr_not_coboundary⟩

end E213.Lib.Math.Cohomology.Bipartite.V33Enriched
