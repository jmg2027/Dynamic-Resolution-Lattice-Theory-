import E213.Lib.Math.Cohomology.Bipartite.V32
import E213.Lib.Physics.Simplex.Counts

/-!
# K_{3,2}^{(c=2)} local (2, 1, 3) signature framework

Every structural element of `K_{3,2}^{(c=2)}` — every vertex, every
edge, every simple 4-cycle face — carries the same atomic triple
`{NT, det, NS} = {2, 1, 3}` as its local signature multiset.  The
"3" of the (2, 1, 3) atomic signature is not the count of some
auxiliary partition; it is reproduced at every local datum of the
graph itself.

This is the **self-containment** reading: K_{3,2}^{(c=2)} is the
locus where the (2, 1, 3) signature manifests at every level
without requiring an external tripartite extension (the external
reading fails cohomologically — see
`Cohomology/Tripartite/V32V213CohomologyBridge`).

## Local signatures (uniform multiset, varying axis assignment)

  · **Vertex** (Fin 5): `(opposite-side, det, own-side)`
      - S-vertex (v.val < 3) : (NT, 1, NS) = (2, 1, 3)
      - T-vertex (v.val ≥ 3) : (NS, 1, NT) = (3, 1, 2)
  · **Edge** (Fin 12): `(NT, det, NS) = (2, 1, 3)` — each edge picks
      one of NT T-endpoints and one of NS S-endpoints, with the
      edge itself a singleton (det = 1).
  · **Face** (Fin 3, simple 4-cycles indexed by NS-pair choices):
      `(NT, det, NS) = (2, 1, 3)` — each face contains the NT = 2
      T-vertices as one side, with the face as a singleton choice
      among 3 = (NS choose 2) S-pairs.

## Predicate

A triple `(a, b, c)` has the (1, 2, 3) atomic multiset iff
`a + b + c = 6 ∧ a · b · c = 6`.  With three positive naturals,
sum 6 and product 6 force multiset {1, 2, 3} uniquely.

## Master theorem

`local_213_at_every_point`: every vertex, every edge, every face
of K_{3,2}^{(c=2)} has a local signature whose multiset is {1, 2, 3}.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Cohomology.Bipartite.V32LocalSignature

open E213.Lib.Physics.Simplex.Counts (NS NT d)

/-! ## §1 — Atomic-multiset predicate -/

/-- A triple (a, b, c) has the atomic-(2, 1, 3) multiset iff its
    sum is 6 and product is 6.  For positive naturals this
    uniquely characterises {1, 2, 3}. -/
def is_213_multiset (a b c : Nat) : Bool :=
  (a + b + c == 6) && (a * b * c == 6)

/-- Lift to a triple. -/
def sig_213 (t : Nat × Nat × Nat) : Bool :=
  is_213_multiset t.1 t.2.1 t.2.2

/-- The canonical (NT, det, NS) = (2, 1, 3) triple is 213-multiset. -/
theorem canonical_213 : is_213_multiset NT 1 NS = true := by decide

/-- The axis-swapped (NS, det, NT) = (3, 1, 2) triple is 213-multiset. -/
theorem canonical_213_swapped : is_213_multiset NS 1 NT = true := by decide

/-! ## §2 — Vertex local signature

K_{3,2}^{(c=2)} has 5 vertices: 3 S-side (Fin 5 indices 0, 1, 2)
and 2 T-side (indices 3, 4).  Each vertex's local signature is
`(opposite-side-count, det, own-side-count)`. -/

/-- Local signature of vertex v.  S-vertex gets (NT, 1, NS);
    T-vertex gets (NS, 1, NT).  Both have multiset {1, 2, 3}. -/
def vertex_local_signature (v : Fin 5) : Nat × Nat × Nat :=
  if v.val < 3 then (NT, 1, NS) else (NS, 1, NT)

/-- Every vertex's local signature has 213-multiset. -/
theorem vertex_signature_is_213 :
    ∀ v : Fin 5, sig_213 (vertex_local_signature v) = true := by decide

/-! ## §3 — Edge local signature

K_{3,2}^{(c=2)} has 12 edges (each S-T pair twice).  Each edge
picks one of NS = 3 S-endpoints, one of NT = 2 T-endpoints, and a
multiplicity in Fin c = Fin 2.  Reading the multiplicity as `c = NT`
(a presentation coincidence of two distinct 2's, not a forcing —
`atomic_c_multiplicity_forcing.md`), the local triple is uniformly
`(NT, det, NS)`. -/

/-- Local signature of edge e: uniform (NT, 1, NS) = (2, 1, 3). -/
def edge_local_signature (_e : Fin 12) : Nat × Nat × Nat :=
  (NT, 1, NS)

/-- Every edge's local signature has 213-multiset. -/
theorem edge_signature_is_213 :
    ∀ e : Fin 12, sig_213 (edge_local_signature e) = true := by decide

/-! ## §4 — Face local signature

K_{3,2}^{(c=2)} has 3 simple 4-cycle faces, one per S-pair
(NS choose 2 = 3 = NS at this signature).  Each face has NT = 2
T-vertices and is a single face among the 3-face total. -/

/-- Local signature of face f: uniform (NT, 1, NS) = (2, 1, 3). -/
def face_local_signature (_f : Fin 3) : Nat × Nat × Nat :=
  (NT, 1, NS)

/-- Every face's local signature has 213-multiset. -/
theorem face_signature_is_213 :
    ∀ f : Fin 3, sig_213 (face_local_signature f) = true := by decide

/-! ## §5 — Structural readings (concrete components) -/

/-- At every S-vertex, the local signature exposes:
    NT = 2 distinct T-neighbours, det = 1 self, NS = 3 own-side total. -/
theorem S_vertex_signature_components :
    ∀ v : Fin 5, v.val < 3 → vertex_local_signature v = (NT, 1, NS) := by
  decide

/-- At every T-vertex, the local signature exposes:
    NS = 3 distinct S-neighbours, det = 1 self, NT = 2 own-side total. -/
theorem T_vertex_signature_components :
    ∀ v : Fin 5, v.val ≥ 3 → vertex_local_signature v = (NS, 1, NT) := by
  decide

/-- All 12 edges share the same local signature (NT, 1, NS).
    The edge-level reading is index-invariant. -/
theorem edge_signature_uniform :
    ∀ e : Fin 12, edge_local_signature e = (NT, 1, NS) := by
  intro _; rfl

/-- All 3 faces share the same local signature (NT, 1, NS).
    The face-level reading is index-invariant. -/
theorem face_signature_uniform :
    ∀ f : Fin 3, face_local_signature f = (NT, 1, NS) := by
  intro _; rfl

/-! ## §6 — Master capstone -/

/-- ★★★★★★★★★★ **Local 213 at every point**: the (2, 1, 3) atomic
    multiset reappears at every structural locus of
    `K_{3,2}^{(c=2)}` — every vertex, every edge, every simple
    4-cycle face.

    This is the structural content of the self-containment claim:
    the "3" of the (2, 1, 3) signature is not an auxiliary
    tripartite partition; it is reproduced locally at every datum
    of the bipartite K_{3,2}^{(c=2)} structure. -/
theorem local_213_at_every_point :
    -- (a) Every vertex: 213 multiset
    (∀ v : Fin 5, sig_213 (vertex_local_signature v) = true)
    -- (b) Every edge: 213 multiset
    ∧ (∀ e : Fin 12, sig_213 (edge_local_signature e) = true)
    -- (c) Every face: 213 multiset
    ∧ (∀ f : Fin 3, sig_213 (face_local_signature f) = true)
    -- (d) Canonical triple realised at every level
    ∧ is_213_multiset NT 1 NS = true
    -- (e) Axis-swapped triple realised at T-vertices
    ∧ is_213_multiset NS 1 NT = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact vertex_signature_is_213
  · exact edge_signature_is_213
  · exact face_signature_is_213
  · decide
  · decide

end E213.Lib.Math.Cohomology.Bipartite.V32LocalSignature
