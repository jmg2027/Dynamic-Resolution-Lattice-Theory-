import E213.Lib.Math.Analysis.Cauchy.DepthAperyCubic
import E213.Lib.Math.Analysis.Cauchy.DepthFloorDetOne

/-!
# DepthResidueFloor — the self-pointing depth ladder, anchored at the residue floor

`diff s n = s(n+1) − s n` is a **self-pointing** step: given a sequence one can point at,
it points again — at how that sequence *changes* — reading the previous level's residue as
a fresh sequence.  `liftK k` iterates the self-pointing `k` times; a sequence has
**depth `d`** (`polyDepth d`) when the `d`-th re-pointing first stops moving (reaches a
constant floor).

Two ends of this iteration are already named in the development:

  * the **top** — `DepthCeilingResidue` — pointing at "the whole act of pointing"
    diagonalises and reproduces the surplus one level up, so the iteration **never
    closes**: *infinite depth is the residue*, the same self-covering as
    `FlatOntologyClosure.object1_not_surjective` (pointing has no exterior,
    `seed/AXIOM/05_no_exterior.md`);
  * the **floor** — `DepthFloorDetOne` — the constant cross-determinant `W = 1` of the
    `P = [[2,1],[1,1]]` orbit (`det P = 1`, the Cassini invariant, fixed point φ), the
    **self-same rule whose coefficients do not depend on `n`**: re-pointing it returns it
    unchanged, **depth 0**.  This is the residue's own algebraic image (`seed/AXIOM/
    05_no_exterior.md §5.6`, `research-notes/G29_residue.md`): `P(φ) = φ`, self-reference
    that closes immediately.

This file records the **ladder between them**, as a single ∅-axiom statement.  Read
through the residue lens, the depth is the count of how far a rule's `n`-dependence has
**drifted from pure self-reference** (the constant floor `W`):

| rule | step coefficient in `n` | depth | witness |
|---|---|---|---|
| `P`/φ floor (Cassini `W=1`) | constant (degree 0) | **0** | `W_isConst` |
| e (`Σ 1/n!`) | `n+1` (degree 1) | **1** | `euler_ratio_polyDepth` |
| ζ(2) (`(n+1)²uₙ₊₁=(11n²+11n+3)uₙ+n²uₙ₋₁`) | degree 2 | **2** | `zeta2_quadratic_rung` |
| ζ(3) (`n³aₙ=(34n³−51n²+27n−5)aₙ₋₁−(n−1)³aₙ₋₂`) | degree 3 | **3** | `aperyTop_polyDepth` |

The floor (`P`/φ) is where the rule *is* its own fixed point — no `n`-drift, the closure
of self-reference itself; each rung above adds one degree of `n`-dependence before the
re-pointing settles.  A limit like ζ(3) is never itself pinned by a finite reference (it
sits, like every irrational, with the residue surplus that no rational catches), yet the
**rule generating it** has finite self-pointing depth 3 — a residue-limit produced by a
finite-depth rule.

All zero-axiom.
-/

namespace E213.Lib.Math.Analysis.Cauchy.DepthResidueFloor

open E213.Lib.Math.Analysis.Cauchy.DepthPRecursive (polyDepth)
open E213.Lib.Math.Analysis.Cauchy.DivergenceDepth (ratio)
open E213.Lib.Math.Analysis.Cauchy.DepthPRecursiveInstances (euler_ratio_polyDepth)
open E213.Lib.Math.Analysis.Cauchy.DepthAperyCubic
  (zeta2Top aperyTop zeta2_quadratic_rung aperyTop_polyDepth)
open E213.Lib.Math.Analysis.Cauchy.DepthFloorDetOne (W W_isConst)

/-- The residue floor is depth 0: the `P`/φ Cassini cross-determinant `W` is already
    constant (`W_isConst`), so its self-pointing returns it unchanged — the self-same rule
    that is its own fixed point. -/
theorem floor_polyDepth0 : polyDepth 0 W := W_isConst

/-- ★★★ **The self-pointing depth ladder, anchored at the residue floor.**  From the
    `P`/φ Cassini floor (constant rule, **depth 0**) the depth climbs by one degree of
    `n`-dependence at each rung: e (**1**), ζ(2) (**2**), ζ(3) (**3**).  The depth is the
    count of self-pointings (`diff` applications) until the rule's drift from pure
    self-reference settles to a constant — `0` at the floor where the rule is its own
    fixed point, growing with the rule's `n`-degree above it. -/
theorem self_pointing_depth_ladder :
    polyDepth 0 W
    ∧ polyDepth 1 ratio
    ∧ polyDepth 2 zeta2Top
    ∧ polyDepth 3 aperyTop :=
  ⟨W_isConst, euler_ratio_polyDepth, zeta2_quadratic_rung.1, aperyTop_polyDepth⟩

end E213.Lib.Math.Analysis.Cauchy.DepthResidueFloor
