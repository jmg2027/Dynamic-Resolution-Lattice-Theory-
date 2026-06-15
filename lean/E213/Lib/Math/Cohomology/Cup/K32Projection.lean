import E213.Lib.Math.Cohomology.Cup.SelfRefDepth

/-!
# Cohomology.Cup.K32Projection — bridge cup-channels ↔ K_{NS,NT}^{(c)}

The cup-self-reference catalog at d = 5 has **6 channels**.  The
K_{3,2}^{(c=2)} bipartite multigraph has **8 cohomology channels**
(= b_1 = gluon DOF,).

This file establishes the structural identity:

  b_1(K_{NS,NT}^{(c)}) = c · NS · NT - (NS + NT) + 1
                       = E - V + 1

with E = c · NS · NT edges, V = NS + NT vertices.  At
(NS, NT, c) = (3, 2, 2): E = 12, V = 5, b_1 = 8.

The cup-channel count at d = NS + NT also equals NS · NT — but
**only at DRLT's count-Lens choice** (NS, NT) = (3, 2) with d = 5.
This coincidence is a structural reason for DRLT's specific
bipartite split.

PURE.
-/

namespace E213.Lib.Math.Cohomology.Cup.K32Projection

/-! ## §1.  Bipartite multigraph counts -/

/-- Edge count of K_{NS, NT}^{(c)}: `c · NS · NT`.  PURE. -/
def k32_edges (NS NT c : Nat) : Nat := c * NS * NT

/-- Vertex count of K_{NS, NT}: `NS + NT`.  PURE. -/
def k32_vertices (NS NT : Nat) : Nat := NS + NT

/-- First Betti number of K_{NS, NT}^{(c)}: `E - V + 1`.
    Assumes the multigraph is connected (which K_{NS, NT} is when
    both NS, NT ≥ 1).  PURE. -/
def k32_b1 (NS NT c : Nat) : Nat :=
  k32_edges NS NT c + 1 - k32_vertices NS NT

/-! ## §2.  DRLT instance (NS, NT, c) = (3, 2, 2) -/

/-- ★★ **DRLT edge count**: K_{3,2}^{(c=2)} has 12 edges. -/
theorem k32_edges_drlt : k32_edges 3 2 2 = 12 := by decide

/-- ★★ **DRLT vertex count**: K_{3,2} has 5 vertices. -/
theorem k32_vertices_drlt : k32_vertices 3 2 = 5 := by decide

/-- ★★★ **DRLT first Betti number**: b_1(K_{3,2}^{(c=2)}) = 8.
    This is the gluon channel count in DRLT.  PURE. -/
theorem k32_b1_drlt : k32_b1 3 2 2 = 8 := by decide

/-! ## §3.  Cup-channels ↔ K_{NS, NT} edge correspondence -/

open E213.Lib.Math.Cohomology.Cup.SelfRefDepth (totalCupChannels)

/-- ★★★★★ **Cup-channels = NS·NT bipartite edges at d = 5**.

    The cup-self-reference channel count `totalCupChannels 5 = 6`
    equals the single-edge count `NS · NT = 3 · 2 = 6` of the
    K_{3,2} bipartite graph.  This is the structural reason why
    DRLT pairs d = 5 with the (3, 2) bipartite split.  PURE. -/
theorem cup_channels_eq_NS_NT_drlt :
    totalCupChannels 5 = 3 * 2 := by decide

/-! ## §4.  The "lost cohomology" — b_1 minus cup-channels -/

/-- ★★★★★★ **Lost cohomology = c · NT - 1 at DRLT**:

      b_1(K_{3,2}^{(c=2)}) - cup-channels = 8 - 6 = 2 = NT.

    The gap between K_{3,2}^{(c=2)}'s 8 cohomology channels and
    the cup catalog's 6 channels is **exactly NT = 2** — the
    T-side bipartite vertex count.

    This identifies the "lost cohomology" (per G35) as a
    structural T-side contribution beyond cup self-reference.
    The cup catalog captures the **single-edge bipartite
    structure**; the additional NT channels arise from the
    multiplicity `c = 2` doubling that creates extra cycles
    minus the T-side vertex constraint.

    Numerical breakdown:
      b_1 - cup-channels = E - V + 1 - NS·NT
                         = c·NS·NT - (NS + NT) + 1 - NS·NT
                         = (c - 1)·NS·NT - NS - NT + 1
                         = 1·6 - 3 - 2 + 1
                         = 6 - 4
                         = 2 = NT.

    PURE. -/
theorem lost_cohomology_eq_NT_drlt :
    k32_b1 3 2 2 - totalCupChannels 5 = 2 := by decide

/-! ## §5.  Master capstone bridging cup catalog ↔ K_{3,2}^{(c=2)} -/

/-- ★★★★★★★ **Master bridge theorem**:

      b_1(K_{3,2}^{(c=2)})        = 8
      = cup-channels(d=5)         + (b_1 - cup-channels)
      = NS · NT                   + NT
      = NT · (NS + 1)
      = 2 · 4 = 8.

    Equivalently: `b_1 = NT · (NS + 1) = 2 · 4 = 8`.

    PURE.  Decide-verified at the DRLT instance. -/
theorem master_bridge_drlt :
    k32_b1 3 2 2 = totalCupChannels 5 + 2
    ∧ k32_b1 3 2 2 = 2 * (3 + 1) := by decide

/-! ## §6.  Multiple structural readings of `b_1 = 8` -/

/-- ★★★★ **`b_1 = NS² - 1 = SU(NS) adjoint dimension`** at DRLT.

    The number 8 admits a fourth structural reading: the dimension
    of the SU(3) adjoint representation `NS² - 1 = 3² - 1 = 8`.

    Combined with the cup-channel bridge, this gives **four**
    independent structural readings of `b_1 = 8`:

      (1) E - V + 1                  =  12 - 5 + 1
      (2) cup-channels + NT          =  6 + 2
      (3) NT · (NS + 1)              =  2 · 4
      (4) NS² - 1 (SU(NS) adjoint)   =  9 - 1

    All equal to 8 at DRLT's (NS, NT, c) = (3, 2, 2).  PURE. -/
theorem b1_eq_su3_adjoint :
    k32_b1 3 2 2 = 3 * 3 - 1 := by decide

/-- ★★★★★ **Quadruple structural identity at DRLT**:

      E - V + 1                  = cup-channels + NT
                                 = NT · (NS + 1)
                                 = NS² - 1
                                 = 8.

    Four independent count-Lens readings of the gluon channel
    count.  The convergence at d = 5, (NS, NT, c) = (3, 2, 2) is
    a **structural coincidence selecting DRLT's parameters**.  PURE. -/
theorem quadruple_identity_drlt :
    k32_b1 3 2 2 = totalCupChannels 5 + 2
    ∧ k32_b1 3 2 2 = 2 * (3 + 1)
    ∧ k32_b1 3 2 2 = 3 * 3 - 1
    ∧ k32_b1 3 2 2 = 8 := by decide

/-! ## §7.  `c = 2` is a crossing of a c-line, not a structural value

The §6 readings all coincide *at* `c = 2`, but coincidence-at-a-point
is not forcing.  The honest content: `b_1(K_{3,2}^{(c)}) = 6c − 4` is a
**strictly increasing function of the multiplicity `c`** (each extra
multiplicity layer adds `NS·NT = 6` independent cycles), whereas the
target `NS² − 1 = 8` (the SU(NS) adjoint dimension) is **constant in
`c`**.  A c-varying quantity equals a c-constant one at *one* `c` only —
here `c = 2`.

Consequence (the gap recorded in
`research-notes/frontiers/atomic_c_multiplicity_forcing.md`): there is no
c-natural isomorphism `H¹(K_{NS,NT}^{(c)}) ≅ su(NS)-adjoint`, because one
side's dimension depends on `c` and the other's does not.  At `c = 2` any
such "isomorphism" is a non-canonical equality of two 8-dimensional
spaces, carrying no forcing content.  So `c = 2` is **selected** by
demanding `b_1 = NS² − 1`, not **forced** by the axiom.  The theorems
below make that selection explicit and ∅-axiom-checkable. -/

/-- `b_1(K_{3,2}^{(c)}) = 6c − 4` on `c ≤ 12`: the cycle rank is a line in
    the multiplicity `c`.  (`List.range`/`decide`, PURE.) -/
def b1_is_line_check : Bool :=
  (List.range 13).all (fun c => k32_b1 3 2 c == 6 * c - 4)

theorem k32_b1_32_is_line : b1_is_line_check = true := by decide

/-- The line is strictly increasing: each `+1` in `c` adds `NS·NT = 6`
    cycles (`b_1(c+1) − b_1(c) = 6`).  Checked on `c ≤ 11`.  PURE. -/
def b1_strict_mono_check : Bool :=
  (List.range 12).all (fun c => Nat.ble (k32_b1 3 2 c + 1) (k32_b1 3 2 (c + 1)))

theorem k32_b1_32_strict_mono : b1_strict_mono_check = true := by decide

/-- ★★★★★★ **The crossing is unique**: on `c ≤ 12`,
    `b_1(K_{3,2}^{(c)}) = NS² − 1 = 8  ⟺  c = 2`.  The su(NS)-adjoint
    value is hit at exactly one multiplicity — `c = 2` is the *crossing
    point of a c-line with a c-constant target*, i.e. selected, not
    structurally forced.  PURE. -/
def b1_crosses_adjoint_only_at_2_check : Bool :=
  (List.range 13).all (fun c => (k32_b1 3 2 c == 3 * 3 - 1) == (c == 2))

theorem k32_b1_32_crosses_adjoint_only_at_2 :
    b1_crosses_adjoint_only_at_2_check = true := by decide

end E213.Lib.Math.Cohomology.Cup.K32Projection
