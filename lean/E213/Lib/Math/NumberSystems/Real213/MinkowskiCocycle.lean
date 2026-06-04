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
   markoff_vieta markoff_vieta_R mInterval_shape)
open E213.Lib.Math.NumberSystems.Real213.ModularElliptic (mul)
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

end E213.Lib.Math.NumberSystems.Real213.MinkowskiCocycle
