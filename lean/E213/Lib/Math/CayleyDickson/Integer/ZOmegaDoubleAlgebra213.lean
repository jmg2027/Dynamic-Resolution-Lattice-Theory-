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

/-! ## §4 — Add/Neg/Zero bridge (rfl) -/

theorem toCDDouble_add (u v : ZOmegaDouble) :
    toCDDouble (u + v) = toCDDouble u + toCDDouble v := by
  apply CDDouble.ext
  · show (u + v).re = u.re + v.re; rfl
  · show (u + v).im = u.im + v.im; rfl

theorem toCDDouble_neg (u : ZOmegaDouble) :
    toCDDouble (-u) = -(toCDDouble u) := by
  apply CDDouble.ext
  · show (-u).re = -u.re; rfl
  · show (-u).im = -u.im; rfl

theorem toCDDouble_zero : toCDDouble 0 = 0 := rfl

/-! ## §5 — Full Ring213 + StarRing213 instances on ZOmegaDouble

Every axiom is a 3-line bridge through `toCDDouble`: push the equality
to abstract side via `toCDDouble_inj` + per-operation bridges, then
apply the abstract `Ring213` / `StarRing213` field. -/

private theorem add_assoc' (u v w : ZOmegaDouble) :
    u + v + w = u + (v + w) := by
  apply toCDDouble_inj
  rw [toCDDouble_add, toCDDouble_add, toCDDouble_add, toCDDouble_add]
  exact Ring213.add_assoc _ _ _

private theorem add_comm' (u v : ZOmegaDouble) : u + v = v + u := by
  apply toCDDouble_inj
  rw [toCDDouble_add, toCDDouble_add]
  exact Ring213.add_comm _ _

private theorem add_zero' (u : ZOmegaDouble) : u + 0 = u := by
  apply toCDDouble_inj
  rw [toCDDouble_add, toCDDouble_zero]
  exact Ring213.add_zero _

private theorem add_left_neg' (u : ZOmegaDouble) : -u + u = 0 := by
  apply toCDDouble_inj
  rw [toCDDouble_add, toCDDouble_neg, toCDDouble_zero]
  exact Ring213.add_left_neg _

private theorem add_mul' (u v w : ZOmegaDouble) :
    (u + v) * w = u * w + v * w := by
  apply toCDDouble_inj
  rw [toCDDouble_mul, toCDDouble_add, toCDDouble_add,
      toCDDouble_mul, toCDDouble_mul]
  exact Ring213.add_mul _ _ _

private theorem mul_add' (u v w : ZOmegaDouble) :
    u * (v + w) = u * v + u * w := by
  apply toCDDouble_inj
  rw [toCDDouble_mul, toCDDouble_add, toCDDouble_add,
      toCDDouble_mul, toCDDouble_mul]
  exact Ring213.mul_add _ _ _

private theorem conj_add' (u v : ZOmegaDouble) :
    ZOmegaDouble.conj (u + v) = ZOmegaDouble.conj u + ZOmegaDouble.conj v := by
  apply toCDDouble_inj
  rw [toCDDouble_conj, toCDDouble_add,
      toCDDouble_add, toCDDouble_conj, toCDDouble_conj]
  exact StarRing213.conj_add _ _

private theorem conj_mul' (u v : ZOmegaDouble) :
    ZOmegaDouble.conj (u * v) = ZOmegaDouble.conj v * ZOmegaDouble.conj u := by
  apply toCDDouble_inj
  rw [toCDDouble_conj, toCDDouble_mul, toCDDouble_mul,
      toCDDouble_conj, toCDDouble_conj]
  exact StarRing213.conj_mul _ _

private theorem conj_conj' (u : ZOmegaDouble) :
    ZOmegaDouble.conj (ZOmegaDouble.conj u) = u := by
  apply toCDDouble_inj
  rw [toCDDouble_conj, toCDDouble_conj]
  exact StarRing213.conj_conj _

instance : Ring213 ZOmegaDouble where
  add_assoc    := add_assoc'
  add_comm     := add_comm'
  add_zero     := add_zero'
  add_left_neg := add_left_neg'
  mul_assoc    := mul_assoc
  add_mul      := add_mul'
  mul_add      := mul_add'

instance : StarRing213 ZOmegaDouble where
  conj      := ZOmegaDouble.conj
  conj_conj := conj_conj'
  conj_add  := conj_add'
  conj_mul  := conj_mul'

end E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble
