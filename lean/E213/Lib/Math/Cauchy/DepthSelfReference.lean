import E213.Lib.Math.Cauchy.DepthResidueFloor
import E213.Lib.Math.Cauchy.HurwitzianCF

/-!
# DepthSelfReference — the `diff` ladder realises self-reference's Converge / Escape outcomes

`Lens.SelfReferenceThreeOutcomes` reads the residue's self-pointing (`05_no_exterior` §5.2)
as one event with three co-present outcomes: **Oscillate** (Bool, bounded period-2 loop),
**Converge** (Nat/Lambek, terminating descent to the atomic floor), **Escape** (residue,
top-less ascent that never closes the cover).  There it is realised on Raw-level objects
(`not` on Bool values, the peel relation, re-pointing predicates).

The finite-difference self-pointing `diff s = (n ↦ s(n+1) − s n)` is the **`Nat`-sequence**
realisation of the same Converge / Escape pair — the two non-oscillating outcomes, on actual
sequences:

  * **Converge** — `floor_converges`: the diff-ladder of the `P`/φ Cassini cross-determinant
    `W` **settles at the unit floor** — `reachesFloor W` (depth 0) and `W n = 1` for all `n`.
    The settling value is the shared unit `1` (`= det P = NS − NT`, the residue's algebraic
    name in `ResidueForm` / `Mobius213OneAsGlue`; cross-domain identity CDI-9).  This is the
    Lambek-style terminating descent of `SelfReferenceThreeOutcomes`, on the analysis side.

  * **Escape** — `geom_escapes`: the diff-ladder of the geometric path `2ᵏ` **never settles**
    — `¬ reachesFloor (fun k => 1·2ᵏ)` (`HurwitzianCF.geom_infinite_depth`): every lift is
    again strictly increasing, the residue re-enters as the next operand forever.  This is
    the top-less residue ascent of `SelfReferenceThreeOutcomes`, on the analysis side.

This is a **naming capstone** in the sense of `ResidueForm` / `SelfReferenceThreeOutcomes`
itself: it proves no new content (it bundles `W_isConst`/`W_eq_one` with
`geom_infinite_depth`) and forces **no** operator across the two types — the Raw realisation
and this `Nat`-sequence realisation are parallel readings of the §5.2 self-pointing, sharing
only the count-Lens unit `1` (the floor value here; the convergence step / escape surplus
unit in `Cauchy/ReentryUnit`).  Which outcome a `diff`-turn takes is what the unit does next:
settle at the floor (a discrete polynomial, finite depth) or open the next rung forever
(the residue, infinite depth).

All zero-axiom.
-/

namespace E213.Lib.Math.Cauchy.DepthSelfReference

open E213.Lib.Math.Cauchy.DivergenceLadder (reachesFloor)
open E213.Lib.Math.Cauchy.DepthFloorDetOne (W W_isConst W_eq_one)
open E213.Lib.Math.Cauchy.HurwitzianCF (geom_infinite_depth)

/-- **Converge.**  The diff-ladder of the `P`/φ Cassini cross-determinant `W` settles at the
    unit floor: `reachesFloor W` (at depth 0, `liftK 0 W = W` is already constant) and the
    floor value is `1` everywhere — the shared residue unit `det P = NS − NT`. -/
theorem floor_converges : reachesFloor W ∧ ∀ n, W n = 1 :=
  ⟨⟨0, W_isConst⟩, W_eq_one⟩

/-- **Escape.**  The diff-ladder of the geometric path `2ᵏ` never settles — re-pointing it
    keeps producing fresh distinction, the residue's top-less ascent. -/
theorem geom_escapes : ¬ reachesFloor (fun k => 1 * 2 ^ k) :=
  geom_infinite_depth 1 2 (by decide) (by decide)

/-- ★★★ **`diff` realises the Converge / Escape outcomes of self-reference.**  On the
    analysis side, the finite-difference self-pointing either **settles at the unit floor**
    (`W`: `reachesFloor`, value `1` = the residue's `det P = NS − NT` unit) or **never
    closes** (`2ᵏ`: `¬ reachesFloor`, the residue ascent) — the `Nat`-sequence reading of
    `SelfReferenceThreeOutcomes`'s Converge and Escape, parallel to the Raw reading and
    sharing the count-Lens unit `1`. -/
theorem diff_converge_or_escape :
    (reachesFloor W ∧ ∀ n, W n = 1) ∧ ¬ reachesFloor (fun k => 1 * 2 ^ k) :=
  ⟨floor_converges, geom_escapes⟩

end E213.Lib.Math.Cauchy.DepthSelfReference
