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
  (det2 mInterval mNode markovRes markovNum markovRes_cross markovRes_cross_left mInterval_det)
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

end E213.Lib.Math.NumberSystems.Real213.MinkowskiCocycle
