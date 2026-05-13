import E213.Meta.Algebra213.CDDoubleStar
import E213.Theory.CDDouble.UniversalOrder4

/-!
# Generic CD-doubling lift demo

Demonstrates that with the generic
`[CommStarRing213 α] : StarRing213 (CDDouble α)` instance
registered (in `Theory/Internal/Algebra213CDDoubleStar.lean`),
the universal Order-4 mechanism `cdd_lift_squared`
applies to a *second* layer purely via Lean's typeclass
inference — no per-layer hand-written instance.

For any `[CommStarRing213 α]`:
  * `CDDouble α` is automatically a `StarRing213` (by the new instance)
  * Therefore `cdd_lift_squared` applies on `CDDouble (CDDouble α)`
    with `α` replaced by `CDDouble α` — by universal property of
    the abstract theorem

This is the "type-level ∀ n" closure for ONE iteration: the
generic instance gives a clean machinery-free derivation.

For deeper iteration, the chain breaks at `CDDouble (CDDouble α)`:
the result is a non-commutative star-ring (NOT
`CommStarRing213`), so the instance no longer fires.  This is the
intrinsic limit of `CommStarRing213 → StarRing213` as a single-
class lift — beyond this, weaker class structure (alternative,
power-associative) is needed, but the Order-4 mechanism itself
remains intact at every layer because `cdd_lift_squared`
requires only `StarRing213`, which CDDouble preserves *in
principle* — what fails is the automatic instance derivation.
-/

namespace E213.Theory.CDDouble.GenericLiftDemo

open E213.Meta.Algebra213
open E213.Meta.Algebra213.CDDouble
open E213.Theory.CDDouble.UniversalOrder4

/-- ★ Sanity demo: `cdd_lift_squared` at *second* CD layer, derived
    purely via the generic `[CommStarRing213 α] : StarRing213
    (CDDouble α)` instance.

    Setup: take any `[CommStarRing213 α]`.  By the generic instance,
    `CDDouble α` is `StarRing213`.  By `cdd_lift_squared` on the
    abstract `StarRing213` level, every `(0, u) : CDDouble (CDDouble α)`
    where `conj u * u = c` satisfies `(0, u)² = (-c, 0)`.

    No per-layer instance written.  All inferred. -/
theorem cdd_lift_squared_at_layer2 {α : Type} [CommStarRing213 α]
    (u c : CDDouble α)
    (h_unit : StarRing213.conj u * u = c) :
    let v : CDDouble (CDDouble α) := ⟨0, u⟩
    (v * v).re = -c ∧ (v * v).im = 0 :=
  cdd_lift_squared u c h_unit

end E213.Theory.CDDouble.GenericLiftDemo
