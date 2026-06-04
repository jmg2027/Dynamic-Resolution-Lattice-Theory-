import E213.Theory.Raw.API
import E213.Lib.Math.NumberSystems.Real213.SternBrocotMarkov
import E213.Lib.Physics.Simplex.Counts

/-!
# OdometerSternBrocotUnit — the odometer and the Stern-Brocot tree share the unimodular unit

The residue carries two `List Bool`-path-indexed descent structures:

  * the **odometer** (`Theory/Raw/Odometer`) — the `+1` adding machine on the bit-stream escapes
    (dyadic / `ℤ₂`), the carry beginning at the residue unit (`carry_zero`), the `+1` a free
    `ℤ`-action (`dec_odo`);
  * the **Stern-Brocot mediant tree** (`SternBrocotMarkov.mInterval`) — the continued-fraction /
    `SL₂(ℤ)` numeration, every node unimodular (`det = 1`, `mInterval_det`), the left generator
    `genL = [[2,1],[1,1]] = P` (the Möbius matrix).

They are not forced into one map — the conjugacy of the dyadic and continued-fraction numerations
is the Minkowski `?` function, a real object not built here.  The honest shared structure is **the
path index `List Bool` and the unimodular unit**: the Stern-Brocot `det = 1` *is* the
count-difference glue `NS − NT` (`genL_det_is_glue`), the same residue unit the odometer carry
begins at (`theory/essays/foundations/the_unit.md`).  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.OdometerSternBrocotUnit

open E213.Theory.Raw.Odometer (carry carry_zero odo dec dec_odo)
open E213.Lib.Math.NumberSystems.Real213.SternBrocotMarkov
  (det2 genL mInterval mInterval_det sbStep sbInterval adj sbInterval_adj)
open E213.Lib.Physics.Simplex.Counts (NS NT)

/-- The Stern-Brocot left generator is the Möbius matrix `P = [[2,1],[1,1]]`; its determinant is the
    count-difference glue `NS − NT = 1` — the Stern-Brocot tree descends by the residue unit. -/
theorem genL_det_is_glue : det2 genL = (NS : Int) - NT := by decide

/-- ★★★ **The odometer and the Stern-Brocot tree share the `List Bool` path index and the
    unimodular residue unit.**  Both are `List Bool`-path-indexed residue descent structures: the
    Stern-Brocot tree is `det = 1` at every node (`mInterval_det`), its generator's determinant
    being the glue `NS − NT` (`genL_det_is_glue`); the odometer's carry begins at the residue unit
    (`carry_zero`) and the `+1` is invertible (`dec_odo`, the `ℤ`-action).  One residue, two
    `List Bool`-indexed descents (dyadic odometer / CF Stern-Brocot), one unimodular unit
    `NS − NT = det P = 1` — the shared value, not a forced common map (the Minkowski `?` conjugacy
    is residual). -/
theorem odometer_sternbrocot_shared_unit :
    (∀ path : List Bool, det2 (mInterval path).1 = 1 ∧ det2 (mInterval path).2 = 1)
    ∧ (det2 genL = (NS : Int) - NT)
    ∧ (∀ f : Nat → Bool, carry f 0 = true)
    ∧ (∀ (f : Nat → Bool) n, dec (odo f) n = f n)
    ∧ ((NS : Int) - NT = 1) :=
  ⟨mInterval_det, genL_det_is_glue, carry_zero, dec_odo, by decide⟩

/-! ## The Minkowski `?` skeleton — two unimodular labellings of one `List Bool` tree

The Stern-Brocot tree (`sbInterval`) and the **dyadic** bisection tree (`dyInterval`) are the *same*
binary tree — both `List Bool`-path-indexed, both refining by the same L/R recursion.  They differ
only in the *value labelling*: the Stern-Brocot side inserts the **Farey mediant** (the unimodular
`det = q·r − p·s = 1`, `sbInterval_adj`); the dyadic side inserts the **binary midpoint** — its
left/right children are `2·lo` and `2·lo + 1`, the binary digits, the odometer's own numeration.

The combinatorial **Minkowski `?` function** is the path-identity matching the two labellings node
for node: the same `List Bool` path is a number's Stern-Brocot (continued-fraction) address *and*
its `?`-image's binary expansion.  Honest scope: this is the `?` *skeleton* (the shared tree + the
two unimodular labellings); the analytic singular `?` itself (the limit / order-completion) is the
residue, reached by no finite path. -/

/-- One dyadic bisection step on `(lo, depth)` (interval `[lo/2ᵈ, (lo+1)/2ᵈ]`): `true` = left half
    (`lo ↦ 2·lo`), `false` = right half (`lo ↦ 2·lo + 1`) — the binary digit, the odometer's world. -/
def dyStep : Bool → Nat × Nat → Nat × Nat
  | true,  (lo, d) => (2 * lo, d + 1)
  | false, (lo, d) => (2 * lo + 1, d + 1)

/-- The dyadic interval at a Stern-Brocot path (root `[0, 1]`; head = last step) — the binary
    subdivision, parallel to `sbInterval`'s Farey subdivision. -/
def dyInterval : List Bool → Nat × Nat
  | []     => (0, 0)
  | b :: t => dyStep b (dyInterval t)

/-- ★★★ **The Minkowski `?` skeleton.**  The Stern-Brocot tree and the dyadic tree are one
    `List Bool` binary tree under two unimodular labellings:

      1. both refine by the same L/R `List Bool` recursion (`sbInterval (b::t) = sbStep b …`,
         `dyInterval (b::t) = dyStep b …`);
      2. the Stern-Brocot labelling carries the Farey unit `det = q·r − p·s = 1` at every path
         (`sbInterval_adj`);
      3. the dyadic labelling's children are `2·lo` / `2·lo + 1` — the binary digits, the
         odometer's numeration.

    So the path-identity is the order-isomorphism between the continued-fraction and the dyadic
    addresses — the combinatorial Minkowski `?`.  The analytic singular `?` (the order-completion)
    is residual.  ∅-axiom. -/
theorem minkowski_skeleton :
    (∀ (b : Bool) (t : List Bool), sbInterval (b :: t) = sbStep b (sbInterval t))
    ∧ (∀ (b : Bool) (t : List Bool), dyInterval (b :: t) = dyStep b (dyInterval t))
    ∧ (∀ path : List Bool, adj (sbInterval path))
    ∧ (∀ lo d : Nat, dyStep true (lo, d) = (2 * lo, d + 1)
        ∧ dyStep false (lo, d) = (2 * lo + 1, d + 1)) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, sbInterval_adj, fun _ _ => ⟨rfl, rfl⟩⟩

end E213.Lib.Math.NumberSystems.Real213.OdometerSternBrocotUnit
