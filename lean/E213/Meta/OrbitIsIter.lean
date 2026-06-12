import E213.Meta.OrderWrap
import E213.Meta.Nat.Iterate213

/-!
# OrbitIsIter — the two genuine cross-domain unifications share one generator

The meta-analysis (`theory/meta/boundary_discipline.md` §1) finds that genuine
*cross-domain* (β) unification in 213 is rare and **clusters at the count/
successor floor** — only `OrderWrap` (ℤ-order ⟷ mod-`p` wrap) and `HyperLadder`
(`+,×,^` as one recursion) qualify.  This file sharpens that to a single fact,
witnessed in Lean: **the two β-successes are not two generators but two
deployments of *the* count-floor generator, `iter`.**

  * `orbit_eq_iter` — `OrderWrap.orbit s a k = Iterate213.iter s k a`: the orbit
    that drives the order/wrap obstruction *is* the count iterating the
    successor.  And `HyperLadder.hyperop` is `iter` iterating the rung-below
    (`hyperop_succ`).  So both genuine unifications flow from `iter` —
    successor-iterated (order) and operation-iterated (the tower).

The sharpened claim, now falsifiable: **`iter` is the site of genuine
cross-domain unification in 213; any future β-success will be `iter`-derived.**
This is why the unifications sit exactly at the count floor — `iter`'s second
argument *is* the count-Lens (`ℕ`), the most primitive view, and unification
distance grows with height precisely because higher structures stop being plain
`iter`-deployments.

∅-axiom: induction on the count + `iter_succ_outside` (the count is order-blind
on a single `f`), the same peel-equivalence that makes both deployments work.
-/

namespace E213.Meta.OrbitIsIter

open E213.Meta.OrderWrap (orbit)
open E213.Meta.Nat.Iterate213 (iter iter_succ_outside)

/-- ★★ **The order/wrap orbit is the count iterating the successor.**
    `OrderWrap.orbit s a k = iter s k a` — by induction on `k`, the
    successor-peel `orbit (k+1) = s (orbit k)` matching `iter`'s outside-peel
    (`iter_succ_outside`).  Together with `HyperLadder.hyperop_succ` (the tower
    is `iter` of the rung below), this exhibits the two genuine β-unifications as
    one generator, `iter`, applied to two functions. -/
theorem orbit_eq_iter {M : Type} (s : M → M) (a : M) :
    ∀ k, orbit s a k = iter s k a
  | 0     => rfl
  | k + 1 => by
      show s (orbit s a k) = iter s (k + 1) a
      rw [iter_succ_outside s k a, orbit_eq_iter s a k]

end E213.Meta.OrbitIsIter
