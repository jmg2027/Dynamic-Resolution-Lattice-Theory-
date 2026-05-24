import E213.Lib.Math.Cohomology.Bipartite.V33
import E213.Lib.Math.Cohomology.Bipartite.V43

/-!
# Cross-graph pattern: S-row dependence at K_{3,3} and K_{4,3}

The "S-row dependence" — sum of 4-cycle faces over varying T-pair at
fixed S-pair = 0 — is a UNIVERSAL structural fact across bipartite
multigraphs `K_{NS, NT}^{(c)}` with `NT = 3`.

This file bundles the K_{3,3} and K_{4,3} instances as a cross-graph
witness of the same pattern.

For general `NT = 3`: at any S-pair (i, j) in K_{NS, 3}^(c), the
3 simple 4-cycles using T-pairs (0,1), (0,2), (1,2) sum to zero
in F₂.  Algebraically: each S-side endpoint contributes the same
2 edges in each cycle; the 3 T-side edges form a triangle that
self-cancels in F₂.

NS doesn't enter the S-row dependence proof — only NT = 3 and the
specific S-pair structure matter.  This is the GRAPH UNIVERSALITY
of the c-counter framework: the same proof template ports across
bipartite graphs sharing NT = 3.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.CrossGraphPattern

/-! ## §1 — K_{3,3} S-row pattern -/

open E213.Lib.Math.Cohomology.Bipartite.V33
  (face_dep_S01)

theorem k33_S01_row_dep_recall :
    ∀ σ : E213.Lib.Math.Cohomology.Bipartite.V33.CochE,
      xor (xor (E213.Lib.Math.Cohomology.Bipartite.V33.face0 σ)
                (E213.Lib.Math.Cohomology.Bipartite.V33.face1 σ))
           (E213.Lib.Math.Cohomology.Bipartite.V33.face2 σ) = false :=
  face_dep_S01

/-! ## §2 — K_{4,3} S-row pattern -/

open E213.Lib.Math.Cohomology.Bipartite.V43
  (face_dep_S01_at_K43 face_dep_S02_at_K43 face_dep_S03_at_K43
   face_dep_S12_at_K43 face_dep_S13_at_K43 face_dep_S23_at_K43)

/-! ## §3 — Cross-graph capstone

Same structural fact: at any S-pair (with `NT = 3`), the 3 T-pair
4-cycles sum to zero.  K_{3,3} (NS = 3) has 3 S-pairs giving 3
instances; K_{4,3} (NS = 4) has 6 S-pairs giving 6 instances.

The pattern is `NT = 3`-dependent (3 T-pairs), `NS`-independent at
the per-pair level. -/

theorem cross_graph_S_row_dependence_pattern :
    -- K_{3,3}^(c=2): face0 + face1 + face2 = 0 (S={0,1} sum)
    (∀ σ : E213.Lib.Math.Cohomology.Bipartite.V33.CochE,
      xor (xor (E213.Lib.Math.Cohomology.Bipartite.V33.face0 σ)
                (E213.Lib.Math.Cohomology.Bipartite.V33.face1 σ))
           (E213.Lib.Math.Cohomology.Bipartite.V33.face2 σ) = false)
    -- K_{4,3}^(c=2): all 6 S-row sums = 0
    ∧ (∀ σ : E213.Lib.Math.Cohomology.Bipartite.V43.CochE,
        xor (xor (E213.Lib.Math.Cohomology.Bipartite.V43.face_S01_T01 σ)
                  (E213.Lib.Math.Cohomology.Bipartite.V43.face_S01_T02 σ))
             (E213.Lib.Math.Cohomology.Bipartite.V43.face_S01_T12 σ) = false
        ∧ xor (xor (E213.Lib.Math.Cohomology.Bipartite.V43.face_S02_T01 σ)
                    (E213.Lib.Math.Cohomology.Bipartite.V43.face_S02_T02 σ))
               (E213.Lib.Math.Cohomology.Bipartite.V43.face_S02_T12 σ) = false
        ∧ xor (xor (E213.Lib.Math.Cohomology.Bipartite.V43.face_S03_T01 σ)
                    (E213.Lib.Math.Cohomology.Bipartite.V43.face_S03_T02 σ))
               (E213.Lib.Math.Cohomology.Bipartite.V43.face_S03_T12 σ) = false
        ∧ xor (xor (E213.Lib.Math.Cohomology.Bipartite.V43.face_S12_T01 σ)
                    (E213.Lib.Math.Cohomology.Bipartite.V43.face_S12_T02 σ))
               (E213.Lib.Math.Cohomology.Bipartite.V43.face_S12_T12 σ) = false
        ∧ xor (xor (E213.Lib.Math.Cohomology.Bipartite.V43.face_S13_T01 σ)
                    (E213.Lib.Math.Cohomology.Bipartite.V43.face_S13_T02 σ))
               (E213.Lib.Math.Cohomology.Bipartite.V43.face_S13_T12 σ) = false
        ∧ xor (xor (E213.Lib.Math.Cohomology.Bipartite.V43.face_S23_T01 σ)
                    (E213.Lib.Math.Cohomology.Bipartite.V43.face_S23_T02 σ))
               (E213.Lib.Math.Cohomology.Bipartite.V43.face_S23_T12 σ) = false) := by
  refine ⟨face_dep_S01, ?_⟩
  intro σ
  exact ⟨face_dep_S01_at_K43 σ, face_dep_S02_at_K43 σ, face_dep_S03_at_K43 σ,
         face_dep_S12_at_K43 σ, face_dep_S13_at_K43 σ, face_dep_S23_at_K43 σ⟩

/-! ## §4 — Structural moral

The S-row dependence works the same way at K_{3,3} and K_{4,3}.  At each
S-pair `(i, j)`, the 3 4-cycles using T-pairs `(0,1), (0,2), (1,2)`
sum to zero in F₂ because:

  · The 2 S-side edges of each cycle (from `i, j` to T-vertices)
    are the SAME 2 edges across all 3 cycles.  They each appear in
    2 of the 3 cycles (once per pair containing the T-vertex), so
    contribute even-many times → XOR cancels.
  · The 1 T-side "diagonal edge" (between the 2 T-vertices in the
    T-pair) is different in each cycle, but across the 3 T-pairs
    the 3 such diagonals form the triangle on Fin 3 T-vertices,
    which sums to zero (each T-side edge appears in 2 of 3 T-pairs).

This argument is `NT = 3`-specific (relies on the 3-pair triangle).
For `NT ≥ 4` we'd need a different dependence pattern (no triangle
closure for arbitrary T-pair triples).

The pattern's `NS`-independence demonstrates the c-counter framework's
GRAPH UNIVERSALITY at fixed `NT`. -/

end E213.Lib.Math.Cohomology.CrossGraphPattern
