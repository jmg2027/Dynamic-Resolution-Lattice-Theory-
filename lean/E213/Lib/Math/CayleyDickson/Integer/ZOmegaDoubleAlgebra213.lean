import E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble
import E213.Lib.Math.CayleyDickson.Integer.ZOmegaAlgebra213
import E213.Meta.Algebra213.CDDoubleStar

/-!
# `ZOmegaDouble` as a `Ring213` + `IntegerNormed213` instance

ZOmegaDouble (= CD-double of Eisenstein integers, Type C L3, 12 units)
inherits its typeclass instances from `CDDouble ZOmega` (abstract
CD doubling functor over `CommStarRing213 ZOmega`).

`ZOmegaDouble` and `CDDouble ZOmega` are structurally identical
(`{ re, im : ZOmega }`) and their multiplications spell the same CD
formula `(a, b)·(c, d) = (ac - conj(d)b, da + b·conj(c))`.  A thin
bridge isomorphism transfers the abstract typeclass instances to the
concrete type without re-proving each ring axiom per-component.

Validates the parametric Algebra213 approach at Type C: ZOmega gains
CommStarRing213 via `ZOmegaAlgebra213`, then `CDDouble ZOmega`
auto-synthesises Ring213 + StarRing213 via `instRing213CDDouble` from
`CDDoubleStar`, and the bridge below pushes those instances onto the
concrete `ZOmegaDouble` structure.  Same recipe applies at every
subsequent layer (ZOmegaQuad, ZOmegaOct, …).
-/

namespace E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble

open E213.Meta.Algebra213
open E213.Lib.Math.CayleyDickson.Integer.ZOmega

/-! ## §1 — Bridge to abstract `CDDouble ZOmega` -/

/-- ZOmegaDouble → abstract CDDouble ZOmega. -/
def toCDDouble (u : ZOmegaDouble) : CDDouble ZOmega := ⟨u.re, u.im⟩

/-- Abstract CDDouble ZOmega → ZOmegaDouble. -/
def fromCDDouble (u : CDDouble ZOmega) : ZOmegaDouble := ⟨u.re, u.im⟩

theorem to_from (u : CDDouble ZOmega) : toCDDouble (fromCDDouble u) = u := by
  cases u; rfl

theorem from_to (u : ZOmegaDouble) : fromCDDouble (toCDDouble u) = u := by
  cases u; rfl

theorem toCDDouble_inj {u v : ZOmegaDouble}
    (h : toCDDouble u = toCDDouble v) : u = v := by
  have := congrArg fromCDDouble h
  rwa [from_to, from_to] at this

/-! ## §2 — Operation bridge: ZOmegaDouble.mul ↔ CDDouble.mul -/

/-- ZOmegaDouble.mul vs abstract CDDouble.mul on ZOmega base.  Both
    formulae expand to the same `(ac − conj(d)·b, da + b·conj(c))`
    where `conj` is `ZOmega.conj` (StarRing213.conj on ZOmega
    instance is `ZOmega.conj` by definition) and `−` is `+ neg` on
    ZOmega.  Closed by `Sub.sub` definitional unfolding +
    componentwise rfl. -/
theorem toCDDouble_mul (u v : ZOmegaDouble) :
    toCDDouble (u * v) = toCDDouble u * toCDDouble v := by
  apply CDDouble.ext
  · show (u * v).re = u.re * v.re + -(StarRing213.conj v.im * u.im)
    show u.re * v.re - (ZOmega.conj v.im) * u.im
       = u.re * v.re + -(StarRing213.conj v.im * u.im)
    rfl
  · show (u * v).im = v.im * u.re + u.im * StarRing213.conj v.re
    rfl

/-- Conjugation bridge: ZOmegaDouble.conj = CDDouble.conj via iso. -/
theorem toCDDouble_conj (u : ZOmegaDouble) :
    toCDDouble (ZOmegaDouble.conj u) = CDDouble.conj (toCDDouble u) := by
  apply CDDouble.ext
  · show ZOmega.conj u.re = StarRing213.conj u.re; rfl
  · show -u.im = -u.im; rfl

/-! ## §3 — Typeclass instances transferred via bridge

Concrete demonstration that `ZOmegaDouble` inherits its ring axioms
from the abstract `Ring213 (CDDouble ZOmega)` instance (synthesised
automatically via `instRing213CDDouble` once `CommStarRing213 ZOmega`
is registered).  The bridge `toCDDouble_inj` + `toCDDouble_mul`
push each axiom through. -/

/-- ★ ZOmegaDouble is associative — derived from
    `Ring213 (CDDouble ZOmega).mul_assoc` via the rfl-bridge. -/
theorem mul_assoc (u v w : ZOmegaDouble) :
    (u * v) * w = u * (v * w) := by
  apply toCDDouble_inj
  rw [toCDDouble_mul, toCDDouble_mul, toCDDouble_mul, toCDDouble_mul]
  exact Ring213.mul_assoc (toCDDouble u) (toCDDouble v) (toCDDouble w)

end E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble
