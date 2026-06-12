# Cross-domain: holonomy + the simplex tower ↔ main's arcs

Insights linking this branch's content (`HolonomyLattice` + the
`simplicial_operation_tower` gut) to arcs already on main.  Tagged `[∅]` (proven
both sides) / `[res]` (resonance, a shared *form* to test, not yet a theorem).

## 1. `det = 1` flatness ↔ the ±1 cross-determinant family `[∅ both sides, res for the unifier]`

Holonomy's conserved invariant is `det (holonomy w) = 1 = NS − NT`
(`det_holonomy_eq_one`) — the flat connection.  This is the **same `±1`
symplectic defect of two convergent paths** that already recurs across main:

  - `Mobius213.mobius_213_pell_unit_invariant_forall` — the Pell-unit
    cross-determinant `num·den' − num'·den = −1` (the convergent pair);
  - the Cassini / Casoratian unit (`CassiniUnimodular`, the weld
    `weld_casoratian` det-floor `+1`);
  - the Markov / Frobenius cross-determinant (`SternBrocotMarkov`);
  - `selfref_matrix_crossdomain`'s thesis: **`det = 1` unimodularity is the one
    shared engine** (`det(AB) = det A · det B`, here `det_mul` `[∅]`).

So holonomy adds a new readout to that family: the flat invariant of a *loop* is
the same `det = 1` the convergent-pair, Cassini, weld and Markov arcs all carry.
The originator's geometric "two trajectories to one destination differ by **1
unit**" (the `^`-twist, `simplicial_operation_tower` L5) is the *same form* read
on the operation tower `[res]`.

## 2. Holonomy is born from the negation fold = ℤ's birth `[∅ both sides]`

`first_loop_is_the_fold`: the first non-trivial loop appears exactly when the
negation-fold composite `S = N·R` is admitted (`[S,S] = −I`, order 4).  This is
the **same fold** that builds ℤ from ℕ — the swap `(a,b) ↦ (b,a)` read as
negation (`FoundingDynamicBridge.founding_swap_is_elliptic_floor`,
`integers_as_difference_lens.md`, §6.7).  So:

> **ℤ's birth and holonomy's birth are one event** — admitting the sign fold.
> The count-Lens (ℕ⁺) sector is loop-free (`positive_loop_trivial`, a tree); the
> difference-Lens (ℤ) is what creates the first closed loop.  Holonomy is the
> residue-internal signature of the same fold the number tower's ℕ→ℤ rung is.

This sharpens `FoundingDynamicBridge` (static pair-completion = dynamic
discriminant floor) with a *third* face: the fold is also where **loop holonomy**
turns on.

## 3. The operation tower reconstructs the `(NS,NT,d)` simplex `[res]`

`simplicial_operation_tower` L3: iterating a commutative binary operation builds a
**simplicial cone** (`C(n+k−1,k)` = dilated `(n−1)`-simplex).  The repo's atomic
object is the `(NS,NT,d) = (3,2,5)` **simplex** combinatorics (physics branch,
§6.8; cohomology essays `k32_cohomology_simplex_higher_insight`,
`layer_multiplication_pattern`).  Two independent roads — operation iteration vs
the K_{3,2} link — landing on the same simplex is the operational signature of
"no exterior" (§6.8): the same residue under two Lenses.  Worth a bridge once the
simplex theorem (L3) is ∅-axiom.

## 4. The commutativity count-dial ↔ `where_commutativity_is_born` `[res]`

`simplicial_operation_tower` L4: the per-degree count distinguishes commutative
(simplex / polynomial `C(n+k−1,k)`) from non-commutative (cube / exponential
`nᵏ`).  This is a **counting** witness for the commutativity boundary that
`theory/essays/analysis/where_commutativity_is_born.md` + `HyperAssoc.pow_not_comm`
locate algebraically — the same `^`-wall, measured two ways (an algebraic
counterexample vs a growth-class jump in the enumeration count).

---

These are recorded as cross-domain *observations* (the proven cores are closed on
both sides; the unifiers in 1/3/4 are resonances to test).  Bridges 2 is a genuine
shared mechanism (one fold, three faces); 1/3/4 are forms worth a theorem.
