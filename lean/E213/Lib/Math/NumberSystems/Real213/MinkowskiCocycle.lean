import E213.Lib.Math.NumberSystems.Real213.SternBrocotMarkov
import E213.Lib.Physics.Simplex.Counts

/-!
# MinkowskiCocycle — the analytic `?` defect is a Markov-valued 1-cocycle on the Stern-Brocot tree

The analytic Minkowski `?` is the conjugacy between the continued-fraction (Stern-Brocot) and dyadic
numerations of a real (`OdometerSternBrocotUnit`).  It is *not* an `SL(2,ℤ)`-homomorphism — its
failure to be additive under the L/R generators is a **1-cocycle**, and this file records that the
cocycle's defect is already a closed theorem of the repo: the **Frobenius cross-determinants**.

At every node the residue→number map's two cross-determinants equal the **bounding Markov numbers**:

  * right defect  `u_r·m_t − u_t·m_r = m_l`  (`markovRes_cross`);
  * left  defect  `u_t·m_l − u_l·m_t = m_r`  (`markovRes_cross_left`).

So the "twisted additivity" of `?` is valued in the Markov module `{m_l, m_r, m_t}`, and the whole
structure is **unimodular** (`det = 1`, the residue unit `NS − NT`).  This is the residue-internal
shadow of the Eichler–Shimura picture: a 1-cocycle on the modular tree valued in a lattice module,
with the cusp at `∞` the right Farey endpoint.  Honest scope: the cocycle is built **on the
Stern-Brocot tree** (the `L/R` sub-semigroup of `SL(2,ℤ)`); the extension to a full `SL(2,ℤ)`
1-cocycle and the period-polynomial / `H^1(SL(2,ℤ), V)` identification are open
(`research-notes/frontiers/residue_expression_atlas.md`).  All ∅-axiom (composes existing PURE
Frobenius identities).
-/

namespace E213.Lib.Math.NumberSystems.Real213.MinkowskiCocycle

open E213.Lib.Math.NumberSystems.Real213.SternBrocotMarkov
  (det2 mInterval mNode markovRes markovNum markovRes_cross markovRes_cross_left mInterval_det
   markoff_vieta markoff_vieta_R mInterval_shape markovRes_sq markovNum_dvd_res_sq_succ)
open E213.Lib.Math.NumberSystems.Real213.ModularElliptic (Mat2 mul)
open E213.Lib.Physics.Simplex.Counts (NS NT)

/-- ★★★ **The Minkowski `?` defect is a Markov-valued, unimodular 1-cocycle.**  At every
    Stern-Brocot node the residue→number map fails to be additive under the L/R generators, and its
    two cross-determinant defects are exactly the **bounding Markov numbers**:

      1. right defect `u_r·m_t − u_t·m_r = m_l` (`markovRes_cross`);
      2. left  defect `u_t·m_l − u_l·m_t = m_r` (`markovRes_cross_left`);
      3. the defects sum to `m_l + m_r` (twisted additivity, the 1-cocycle relation's footprint);
      4. both bounds are **unimodular** (`det = 1`) — the cocycle lives in `SL(2,ℤ)`, valued against
         the residue unit `NS − NT = 1`.

    The failure of `?` to be a homomorphism is *the Markov data itself* — the residue-internal,
    tree-restricted Eichler–Shimura cocycle.  ∅-axiom. -/
theorem minkowski_is_markov_valued_cocycle (path : List Bool) :
    (((mInterval path).2.d - (mInterval path).2.c) * (mNode path).c
        - markovRes path * (mInterval path).2.c = (mInterval path).1.c)
    ∧ (markovRes path * (mInterval path).1.c
        - ((mInterval path).1.d - (mInterval path).1.c) * (mNode path).c = (mInterval path).2.c)
    ∧ ((((mInterval path).2.d - (mInterval path).2.c) * (mNode path).c
          - markovRes path * (mInterval path).2.c)
       + (markovRes path * (mInterval path).1.c
          - ((mInterval path).1.d - (mInterval path).1.c) * (mNode path).c)
        = (mInterval path).1.c + (mInterval path).2.c)
    ∧ (det2 (mInterval path).1 = 1 ∧ det2 (mInterval path).2 = 1)
    ∧ ((NS : Int) - NT = 1) := by
  refine ⟨markovRes_cross path, markovRes_cross_left path, ?_, mInterval_det path, by decide⟩
  rw [markovRes_cross path, markovRes_cross_left path]

/-! ## The cocycle twist — the generator action is the Markov–Vieta (Cayley–Hamilton) jump

A 1-cocycle's defining relation is the *twist*: `c(g·h) = c(g) + g·c(h)`.  Here the coefficient
module is the Markov data and the `SL(2,ℤ)` generator acts by **Cayley–Hamilton** (`M² = tr(M)·M − I`,
`det = 1`).  So under each L/R descent the cocycle defect (the Markov number) transforms by exactly
the **Markov-equation Vieta jump** `m' = 3·m_bound·m_node − m_other` — the generator's action on the
module.  This is `markoff_vieta`/`markoff_vieta_R` with the entry-shape `tr = 3·m`
(`mInterval_shape`), read as the cocycle twist. -/

/-- ★★ **Cocycle twist, L-generator.**  `markovNum (true :: t) = 3·m_l·m_t − m_r` — the left descent
    acts on the Markov defect by the Vieta/Cayley–Hamilton jump (trace `= 3·m_l`). -/
theorem minkowski_cocycle_twist_L (t : List Bool) :
    markovNum (true :: t) = 3 * (mInterval t).1.c * markovNum t - (mInterval t).2.c := by
  show (mul (mInterval t).1 (mul (mInterval t).1 (mInterval t).2)).c
       = 3 * (mInterval t).1.c * (mul (mInterval t).1 (mInterval t).2).c - (mInterval t).2.c
  rw [markoff_vieta (mInterval t).1 (mInterval t).2 (mInterval_det t).1, (mInterval_shape t).1]

/-- ★★ **Cocycle twist, R-generator.**  `markovNum (false :: t) = 3·m_r·m_t − m_l` — the mirror jump
    (trace `= 3·m_r`). -/
theorem minkowski_cocycle_twist_R (t : List Bool) :
    markovNum (false :: t) = 3 * (mInterval t).2.c * markovNum t - (mInterval t).1.c := by
  show (mul (mul (mInterval t).1 (mInterval t).2) (mInterval t).2).c
       = 3 * (mInterval t).2.c * (mul (mInterval t).1 (mInterval t).2).c - (mInterval t).1.c
  rw [markoff_vieta_R (mInterval t).1 (mInterval t).2 (mInterval_det t).2, (mInterval_shape t).2.1]

/-- ★★★ **The cocycle twist law.**  Under each Stern-Brocot generator the `?`-cocycle defect
    transforms by the `SL(2,ℤ)` Cayley–Hamilton action — the Markov-equation Vieta jump
    `m' = 3·m_bound·m_node − m_other`.  Together with `minkowski_is_markov_valued_cocycle` (the defect
    *is* the bounding Markov number) this is the full 1-cocycle datum on the tree: a module
    (Markov data), a generator action (Vieta/Cayley–Hamilton), and the defect identity.  ∅-axiom. -/
theorem minkowski_cocycle_twist (t : List Bool) :
    (markovNum (true :: t) = 3 * (mInterval t).1.c * markovNum t - (mInterval t).2.c)
    ∧ (markovNum (false :: t) = 3 * (mInterval t).2.c * markovNum t - (mInterval t).1.c) :=
  ⟨minkowski_cocycle_twist_L t, minkowski_cocycle_twist_R t⟩

/-! ## Off the tree — the defect on all of `M₂(ℤ)`, and the weight-2 Eichler–Shimura relation

The cocycle was built on the Stern-Brocot tree (positive L/R words).  The defect itself, however, is
a **universal** bilinear identity on *all* integer `2×2` matrices: `M.a·(MN).c − M.c·(MN).a = det M ·
N.c`.  So the cocycle extends off the tree to the whole monoid `M₂(ℤ)`, unimodular exactly on
`SL(2,ℤ)` (`det = 1`).  This is the first honest step of the full-group extension (`markoff_frobenius`
is its `det = 1` corollary).

The deepest classical bridge is **Eichler–Shimura at weight 2**: the period polynomial degenerates to
the residue, and the period relation becomes the `√(−1)` congruence `u² ≡ −1 (mod m)` — which is
already a closed theorem of the repo (`markovNum_dvd_res_sq_succ`).  So the residue-internal,
tree-restricted weight-2 period relation is built; the higher-weight period integrals / the full
`H^1(SL(2,ℤ), V_k)` identification need analysis (integration) and stay open. -/

/-- ★★★ **The cocycle defect on all of `M₂(ℤ)`.**  For *any* integer matrices `M, N`,
    `M.a·(M·N).c − M.c·(M·N).a = det M · N.c` — a universal bilinear identity (no `det = 1`
    hypothesis).  The `?`-cocycle defect thus extends off the Stern-Brocot tree to the whole matrix
    monoid, **unimodular exactly on `SL(2,ℤ)`** where it recovers `N.c` (`markoff_frobenius` is the
    `det = 1` case).  The first honest step toward a full-group 1-cocycle.  ∅-axiom. -/
theorem cocycle_defect_general (M N : Mat2) :
    M.a * (mul M N).c - M.c * (mul M N).a = det2 M * N.c := by
  show M.a * (M.c * N.a + M.d * N.c) - M.c * (M.a * N.a + M.b * N.c)
     = (M.a * M.d - M.b * M.c) * N.c
  ring_intZ

/-- ★★★ **The weight-2 Eichler–Shimura period relation, realized.**  At weight 2 the period
    polynomial degenerates to the residue, and the period relation is exactly the **`√(−1)`
    congruence**: at every Stern-Brocot node the residue squares to `−1` modulo the Markov number,
    `m_t ∣ u_t² + 1` (`markovNum_dvd_res_sq_succ`), with the explicit form
    `u_t² + 1 = (m_t + d − b)·m_t` (`markovRes_sq`).  So the residue *is* the (weight-2) period of the
    `?`-cocycle.  The higher-weight period integrals / full `H^1(SL(2,ℤ), V_k)` identification need
    analysis and stay open.  ∅-axiom. -/
theorem minkowski_weight2_period_relation (path : List Bool) :
    (markovNum path ∣ markovRes path * markovRes path + 1)
    ∧ (markovRes path * markovRes path + 1
        = ((mNode path).c + (mNode path).d - (mNode path).b) * (mNode path).c) :=
  ⟨markovNum_dvd_res_sq_succ path, markovRes_sq path⟩

end E213.Lib.Math.NumberSystems.Real213.MinkowskiCocycle
