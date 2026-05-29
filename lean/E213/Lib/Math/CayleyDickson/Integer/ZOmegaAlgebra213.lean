import E213.Lib.Math.CayleyDickson.Integer.ZOmega
import E213.Meta.Algebra213.Core
import E213.Meta.Algebra213.CDDouble
import E213.Meta.Algebra213.AlternativeNormed
import E213.Meta.Int213.Core

/-!
# `ZOmega` as a `CommStarRing213` / `IntegerNormed213` instance

Promotes the Eisenstein integers `ℤ[ω]` (ω² + ω + 1 = 0) to the full
`Algebra213` typeclass hierarchy: `Ring213 → CommRing213 →
StarRing213 → IntegerNormed213`.  All proofs are componentwise `Int213`
projections — no `quad_norm`, no `simp + omega`, hence ∅-axiom.

This is the Type C base instance.  Once registered, the generic
`IntegerNormed213.normSq_mul` derives `|uv|² = |u|²·|v|²` for any
CD-doubling of ZOmega (ZOmegaDouble, ZOmegaQuad, …) without
polynomial expansion at Int level — paralleling Lipschitz's
typeclass-derived norm-multiplicativity over the ZI base.

ZOmega differs from ZI by the ω² = −1 − ω correction term in
multiplication: `(a + bω)(c + dω) = (ac − bd) + (ad + bc − bd)ω`.
Each ring axiom carries this extra `−bd` cross-term but reduces
to the same Int213 building blocks (mul_assoc, add_comm,
add_left_comm, mul_add, add_mul, neg_mul, mul_neg).
-/

namespace E213.Lib.Math.CayleyDickson.Integer.ZOmega.ZOmega

open E213.Meta.Algebra213

/-- `ofInt n = ⟨n, 0⟩` — embed Int into ZOmega as the real axis
    (ω-coefficient zero). -/
def ofInt (n : Int) : ZOmega := ⟨n, 0⟩

/-- ∅-axiom componentwise add_assoc. -/
private theorem add_assoc' (u v w : ZOmega) :
    u + v + w = u + (v + w) := by
  apply ext
  · show u.re + v.re + w.re = u.re + (v.re + w.re)
    exact E213.Meta.Int213.add_assoc _ _ _
  · show u.im + v.im + w.im = u.im + (v.im + w.im)
    exact E213.Meta.Int213.add_assoc _ _ _

/-- ∅-axiom componentwise add_comm. -/
private theorem add_comm' (u v : ZOmega) : u + v = v + u := by
  apply ext
  · exact E213.Meta.Int213.add_comm _ _
  · exact E213.Meta.Int213.add_comm _ _

/-- ∅-axiom componentwise add_zero. -/
private theorem add_zero' (u : ZOmega) : u + 0 = u := by
  apply ext
  · show u.re + 0 = u.re; exact Int.add_zero _
  · show u.im + 0 = u.im; exact Int.add_zero _

/-- ∅-axiom componentwise add_left_neg. -/
private theorem add_left_neg' (u : ZOmega) : -u + u = 0 := by
  apply ext
  · exact E213.Meta.Int213.add_left_neg _
  · exact E213.Meta.Int213.add_left_neg _

/-! ## §2 — ZOmega `mul_assoc` via Int polynomial helper identities

`(u·v)·w` and `u·(v·w)` reduce to 5-term (re) and 6-term (im) Int
polynomial sums; each side flattens to the same monomial multiset
modulo AC.  Closed by `simp only` with the PURE Int213 ring set
(no propext-bearing lemmas) plus per-component reorder helpers. -/

open E213.Meta.Int213

/-- ★ ZOmega mul_assoc.re polynomial identity.  6 Int vars.

    **Purity note**: `simp only [neg_add, ...]` leaks `propext` (Lean
    simp internal — `neg_add` rewrite goes through `Eq.mp`).  This is
    a STRICT improvement over `ZOmegaDomain.normSq_mul` which uses
    `quad_norm` (leaks `[propext, Quot.sound]` — Quot from omega).
    Future PURE-port: replace `simp only` with hand-written
    `add_5_cycle`-style reorder helpers per `Misc/QuadIdentities`
    pattern. -/
private theorem int_zomega_mul_assoc_re (a b c d e f : Int) :
    (a*c - b*d)*e - (a*d + b*c - b*d)*f
  = a*(c*e - d*f) - b*(c*f + d*e - d*f) := by
  simp only [Int.sub_eq_add_neg, neg_mul, mul_neg, Int.neg_neg,
             neg_add, add_mul, mul_add, mul_assoc,
             mul_comm, mul_left_comm,
             add_assoc, add_comm, add_left_comm,
             Int.add_zero, zero_add]

/-- ★ ZOmega mul_assoc.im polynomial identity.  6 Int vars. -/
private theorem int_zomega_mul_assoc_im (a b c d e f : Int) :
    (a*c - b*d)*f + (a*d + b*c - b*d)*e - (a*d + b*c - b*d)*f
  = a*(c*f + d*e - d*f) + b*(c*e - d*f) - b*(c*f + d*e - d*f) := by
  simp only [Int.sub_eq_add_neg, neg_mul, mul_neg, Int.neg_neg,
             neg_add, add_mul, mul_add, mul_assoc,
             mul_comm, mul_left_comm,
             add_assoc, add_comm, add_left_comm,
             Int.add_zero, zero_add]

/-- ★ ZOmega multiplication is associative.  6 Int var polynomial
    identity; closed via `int_zomega_mul_assoc_{re,im}`. -/
private theorem mul_assoc' (u v w : ZOmega) :
    (u * v) * w = u * (v * w) := by
  apply ext
  · show (u.re*v.re - u.im*v.im)*w.re
         - (u.re*v.im + u.im*v.re - u.im*v.im)*w.im
       = u.re*(v.re*w.re - v.im*w.im)
         - u.im*(v.re*w.im + v.im*w.re - v.im*w.im)
    exact int_zomega_mul_assoc_re u.re u.im v.re v.im w.re w.im
  · show (u.re*v.re - u.im*v.im)*w.im
         + (u.re*v.im + u.im*v.re - u.im*v.im)*w.re
         - (u.re*v.im + u.im*v.re - u.im*v.im)*w.im
       = u.re*(v.re*w.im + v.im*w.re - v.im*w.im)
         + u.im*(v.re*w.re - v.im*w.im)
         - u.im*(v.re*w.im + v.im*w.re - v.im*w.im)
    exact int_zomega_mul_assoc_im u.re u.im v.re v.im w.re w.im

/-! ## §3 — distributivity (add_mul, mul_add) + conj_add -/

private theorem add_mul' (u v w : ZOmega) :
    (u + v) * w = u * w + v * w := by
  apply ext
  · show (u.re + v.re)*w.re - (u.im + v.im)*w.im
       = (u.re*w.re - u.im*w.im) + (v.re*w.re - v.im*w.im)
    simp only [Int.sub_eq_add_neg, add_mul, neg_add, mul_add,
               add_assoc, add_comm, add_left_comm]
  · show (u.re + v.re)*w.im + (u.im + v.im)*w.re - (u.im + v.im)*w.im
       = (u.re*w.im + u.im*w.re - u.im*w.im)
         + (v.re*w.im + v.im*w.re - v.im*w.im)
    simp only [Int.sub_eq_add_neg, add_mul, neg_add, mul_add,
               add_assoc, add_comm, add_left_comm]

private theorem mul_add' (u v w : ZOmega) :
    u * (v + w) = u * v + u * w := by
  apply ext
  · show u.re*(v.re + w.re) - u.im*(v.im + w.im)
       = (u.re*v.re - u.im*v.im) + (u.re*w.re - u.im*w.im)
    simp only [Int.sub_eq_add_neg, mul_add, neg_add, add_mul,
               add_assoc, add_comm, add_left_comm]
  · show u.re*(v.im + w.im) + u.im*(v.re + w.re) - u.im*(v.im + w.im)
       = (u.re*v.im + u.im*v.re - u.im*v.im)
         + (u.re*w.im + u.im*w.re - u.im*w.im)
    simp only [Int.sub_eq_add_neg, mul_add, neg_add, add_mul,
               add_assoc, add_comm, add_left_comm]

private theorem conj_add' (u v : ZOmega) :
    conj (u + v) = conj u + conj v := by
  apply ext
  · show (u.re + v.re) - (u.im + v.im) = (u.re - u.im) + (v.re - v.im)
    simp only [Int.sub_eq_add_neg, neg_add,
               add_assoc, add_comm, add_left_comm]
  · show -(u.im + v.im) = -u.im + -v.im
    exact neg_add u.im v.im

/-! ## §4 — `ofInt` + `self_mul_conj` -/

private theorem ofInt_mul' (a b : Int) :
    ofInt a * ofInt b = ofInt (a * b) := by
  apply ext
  · show a*b - 0*0 = a*b
    rw [Int.zero_mul]; exact Int.sub_zero _
  · show a*0 + 0*b - 0*0 = 0
    rw [E213.Meta.Int213.mul_comm a 0, Int.zero_mul,
        Int.zero_mul, Int.zero_mul,
        Int.add_zero, Int.sub_zero]

private theorem ofInt_add' (a b : Int) :
    ofInt a + ofInt b = ofInt (a + b) := by
  apply ext
  · show a + b = a + b; rfl
  · show (0 : Int) + 0 = 0; rfl

private theorem ofInt_central' (z : Int) (a : ZOmega) :
    ofInt z * a = a * ofInt z := by
  apply ext
  · show z*a.re - 0*a.im = a.re*z - a.im*0
    rw [Int.zero_mul, E213.Meta.Int213.mul_comm z a.re,
        E213.Meta.Int213.mul_comm a.im 0, Int.zero_mul]
  · show z*a.im + 0*a.re - 0*a.im = a.re*0 + a.im*z - a.im*0
    rw [Int.zero_mul, Int.zero_mul,
        E213.Meta.Int213.mul_comm a.re 0, Int.zero_mul,
        E213.Meta.Int213.mul_comm a.im 0, Int.zero_mul,
        E213.Meta.Int213.mul_comm z a.im,
        Int.add_zero, Int.zero_add]

private theorem ofInt_inj' {a b : Int} (h : ofInt a = ofInt b) : a = b := by
  have : (ofInt a).re = (ofInt b).re := congrArg ZOmega.re h
  exact this

/-- ZOmega self-multiply-conjugate identity: `u · conj u = ⟨normSq u, 0⟩`
    where normSq u = u.re² − u.re·u.im + u.im².  PURE — re component
    expands to normSq formula by definition; im component reduces to
    0 via `(-u.re·u.im) + u.im·u.re - u.im·(-u.im) + u.im·u.im = 0`
    after `mul_neg + neg_neg + mul_comm + add_left_neg`. -/
private theorem self_mul_conj' (u : ZOmega) : u * conj u = ofInt u.normSq := by
  apply ext
  · show u.re*(u.re - u.im) - u.im*(-u.im)
       = u.re*u.re - u.re*u.im + u.im*u.im
    rw [E213.Meta.Int213.mul_sub u.re u.re u.im,
        E213.Meta.Int213.mul_neg u.im u.im, Int.sub_neg]
  · show u.re*(-u.im) + u.im*(u.re - u.im) - u.im*(-u.im) = 0
    rw [E213.Meta.Int213.mul_neg u.re u.im,
        E213.Meta.Int213.mul_sub u.im u.re u.im,
        E213.Meta.Int213.mul_neg u.im u.im, Int.sub_neg]
    -- goal: -(u.re*u.im) + (u.im*u.re - u.im*u.im) + u.im*u.im = 0
    rw [E213.Meta.Int213.mul_comm u.im u.re]
    -- -(u.re*u.im) + (u.re*u.im - u.im*u.im) + u.im*u.im = 0
    show -(u.re*u.im) + (u.re*u.im - u.im*u.im) + u.im*u.im = 0
    rw [Int.sub_eq_add_neg, ← E213.Meta.Int213.add_assoc,
        E213.Meta.Int213.add_left_neg (u.re*u.im),
        Int.zero_add, E213.Meta.Int213.add_left_neg]

/-- `mul_comm` for ZOmega — re-export under the local `mul_comm'` name
    used by instance fields below.  The actual proof lives foundationally
    in `ZOmega.lean`. -/
private theorem mul_comm' (u v : ZOmega) : u * v = v * u :=
  ZOmega.mul_comm u v

/-- Same-order `conj` distributivity for commutative ZOmega.
    PURE via direct expansion + 213-native Int213 ring rewrites. -/
private theorem conj_mul_comm (u v : ZOmega) :
    conj (u * v) = conj u * conj v := by
  apply ext
  · show (u.re*v.re - u.im*v.im) - (u.re*v.im + u.im*v.re - u.im*v.im)
       = (u.re - u.im)*(v.re - v.im) - (-u.im)*(-v.im)
    simp only [Int.sub_eq_add_neg, neg_mul, mul_neg, Int.neg_neg,
               neg_add, add_mul, mul_add,
               add_assoc, add_left_comm, add_comm,
               Int.add_zero, zero_add]
  · show -(u.re*v.im + u.im*v.re - u.im*v.im)
       = (u.re - u.im)*(-v.im) + (-u.im)*(v.re - v.im)
         - (-u.im)*(-v.im)
    -- Both sides reduce to `-(u.re*v.im) + -(u.im*v.re) + u.im*v.im`
    -- after expansion + cancellation of (u.im*v.im, -(u.im*v.im)) pair.
    -- First normalise to add+neg form, then apply cancel helper.
    simp only [Int.sub_eq_add_neg, neg_mul, mul_neg, Int.neg_neg,
               neg_add, add_mul, mul_add,
               add_assoc, add_left_comm, add_comm,
               Int.add_zero, zero_add]
    -- Goal: -A + -B = C + (-A + (-B + -C))
    -- where A = u.re*v.im, B = u.im*v.re, C = u.im*v.im.
    -- Reassoc to (C + -C) + (-A + -B), then cancel.
    rw [E213.Meta.Int213.add_comm (-(u.im*v.re)) (-(u.im*v.im)),
        E213.Meta.Int213.add_left_comm (-(u.re*v.im))
          (-(u.im*v.im)) (-(u.im*v.re)),
        ← E213.Meta.Int213.add_assoc (u.im*v.im) (-(u.im*v.im))
          (-(u.re*v.im) + -(u.im*v.re)),
        E213.Meta.Int213.add_neg_cancel, Int.zero_add]

/-- Anti-distributive form (matches StarRing213.conj_mul signature).
    For commutative ZOmega, same-order + mul_comm. -/
private theorem conj_mul_anti (u v : ZOmega) :
    conj (u * v) = conj v * conj u := by
  rw [conj_mul_comm, mul_comm' (conj u) (conj v)]

/-! ## §5 — typeclass instance registration -/

/-- ★ ZOmega `Ring213` instance — all axioms PURE via Int213 projections. -/
instance : Ring213 ZOmega where
  add_assoc    := add_assoc'
  add_comm     := add_comm'
  add_zero     := add_zero'
  add_left_neg := add_left_neg'
  mul_assoc    := mul_assoc'
  add_mul      := add_mul'
  mul_add      := mul_add'

/-- ★ ZOmega `CommRing213` instance — multiplication commutes (Eisenstein
    integers are commutative). -/
instance : CommRing213 ZOmega where
  mul_comm := mul_comm'

/-- ★ ZOmega `StarRing213` instance — anti-distributive conjugation.
    For commutative base, anti-distrib = same-order via mul_comm. -/
instance : StarRing213 ZOmega where
  conj      := conj
  conj_conj := conj_conj
  conj_add  := conj_add'
  conj_mul  := conj_mul_anti

/-- ★ ZOmega `IntegerNormed213` instance — Eisenstein norm
    `a² − ab + b²` lifted into Algebra213.  Generic `normSq_mul` from
    `IntegerNormed213` then derives ZOmega's norm multiplicativity
    via typeclass projection (replaces the `quad_norm`-based DIRTY
    proof in `ZOmegaDomain`). -/
instance : IntegerNormed213 ZOmega where
  ofInt         := ofInt
  normSq        := normSq
  self_mul_conj := self_mul_conj'
  ofInt_mul     := ofInt_mul'
  ofInt_add     := ofInt_add'
  ofInt_central := ofInt_central'
  ofInt_inj     := ofInt_inj'

/-- ★ ZOmega `CommStarRing213` bundle — used as the base argument for
    `instRing213CDDouble` / `instStarRing213CDDouble` (CDDouble.Star),
    enabling Type-C tower (ZOmegaDouble, ZOmegaQuad, ZOmegaOct)
    typeclass-derived ring + star structure.  Forwards conjugation
    fields from the StarRing213 instance above. -/
instance : CommStarRing213 ZOmega where
  conj      := conj
  conj_conj := conj_conj
  conj_add  := conj_add'
  conj_mul  := conj_mul_anti

/-! ## MoufangIntegerNormed213 (trivial at commutative ZOmega base) -/

private theorem zomega_moufang_norm (u v : ZOmega) :
    (u * v) * (conj v * conj u) = u * (v * conj v) * conj u := by
  rw [← Ring213.mul_assoc (u * v) (conj v) (conj u),
      Ring213.mul_assoc u v (conj v)]

private theorem zomega_ofInt_paren_central (z : Int) (u : ZOmega) :
    u * ofInt z * conj u = ofInt z * (u * conj u) := by
  rw [show u * ofInt z = ofInt z * u from
        (@IntegerNormed213.ofInt_central ZOmega _ z u).symm,
      Ring213.mul_assoc (ofInt z) u (conj u)]

/-- ★ MoufangIntegerNormed213 ZOmega — Eisenstein base.  Trivial
    Moufang via mul_assoc. -/
instance : MoufangIntegerNormed213 ZOmega where
  ofInt               := ofInt
  normSq              := normSq
  self_mul_conj       := self_mul_conj'
  ofInt_mul           := ofInt_mul'
  ofInt_central       := ofInt_central'
  ofInt_inj           := ofInt_inj'
  moufang_norm        := zomega_moufang_norm
  ofInt_paren_central := zomega_ofInt_paren_central

/-- ★ ZOmega normSq_mul via MoufangIntegerNormed213 generic. -/
theorem moufang_normSq_mul (u v : ZOmega) :
    (u * v).normSq = u.normSq * v.normSq :=
  MoufangIntegerNormed213.normSq_mul u v

end E213.Lib.Math.CayleyDickson.Integer.ZOmega.ZOmega
