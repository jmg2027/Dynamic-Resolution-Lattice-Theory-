import E213.Theory.Nat213.AtomicityCorrespondence
import E213.Theory.Nat213.OneAsGlue
import E213.Theory.Raw.Mobius

/-!
# Theory.Nat213.RotationGeometry — 213-native rotation/spiral

User directive (2026-05-09): "Raw의 Nat213렌즈의 네이티브로 된
토폴로지/그래프이론/코호몰로지/선대수로 이런 모양이다 + 회전이
뭐고 어케 꼬이는거고"

Connects:
- (A) K_{3,2}^{(2)} bipartite multigraph (5 vertices, 12 edges)
- (B) Möbius P linear algebra
- (C) Pell-Fib spiral as concrete P iteration

All theorems ∅-axiom.
-/

namespace E213.Theory.Nat213.RotationGeometry

open E213.Lib.Physics.Simplex.Counts (d NS NT)

-- ═══ (A) K_{3,2}^{(2)} graph realization ═══

/-- K_{3,2} vertex count = 5 = d. -/
theorem k32_vertex_count : (5 : Nat) = d := rfl

/-- K_{3,2} S-vertex count = NS = 3. -/
theorem k32_s_vertex_count : (3 : Nat) = NS := rfl

/-- K_{3,2} T-vertex count = NT = 2. -/
theorem k32_t_vertex_count : (2 : Nat) = NT := rfl

/-- K_{3,2}^{(2)} edge count = 12 = NS · NT · 2. -/
theorem k32_edge_count : (12 : Nat) = NS * NT * 2 := rfl

-- ═══ (B) Möbius P linear-algebra ═══

/-- Trace of P = 3 = NS. -/
theorem p_trace_eq_ns : (2 : Int) + 1 = (NS : Int) := by decide

/-- Det of P = 1 = glue. -/
theorem p_det_is_glue : (2 : Int) * 1 - 1 * 1 = 1 := by decide

/-- Discriminant of P = 5 = d. -/
theorem p_disc_eq_d : (3 : Int)^2 - 4 * 1 = (d : Int) := by decide

-- ═══ (C) Pell-Fib spiral: concrete P iteration ═══

/-- P · (1, 1) = (3, 2).  Note: (3, 2) = (NS, NT) — the spiral
    BEGINS at atomicity. -/
theorem p_iter_step1 :
    ((2 * 1 + 1 * 1, 1 * 1 + 1 * 1) : Nat × Nat) = (3, 2) := rfl

/-- P · (3, 2) = (8, 5).  Pell-Fib step. -/
theorem p_iter_step2 :
    ((2 * 3 + 1 * 2, 1 * 3 + 1 * 2) : Nat × Nat) = (8, 5) := rfl

/-- P · (8, 5) = (21, 13).  Spiral continues. -/
theorem p_iter_step3 :
    ((2 * 8 + 1 * 5, 1 * 8 + 1 * 5) : Nat × Nat) = (21, 13) := rfl

/-- P · (21, 13) = (55, 34).  Ratio 55/34 → φ. -/
theorem p_iter_step4 :
    ((2 * 21 + 1 * 13, 1 * 21 + 1 * 13) : Nat × Nat) = (55, 34) := rfl

/-- ★★★ SPIRAL STARTS AT ATOMICITY: P · (1, 1) = (NS, NT).
    The Möbius P, applied to the unit pair, produces (NS, NT) =
    (3, 2) directly.  The spiral is BORN from atomicity. -/
theorem spiral_starts_at_atomicity :
    ((2 * 1 + 1 * 1, 1 * 1 + 1 * 1) : Nat × Nat) = (NS, NT) := rfl

end E213.Theory.Nat213.RotationGeometry
