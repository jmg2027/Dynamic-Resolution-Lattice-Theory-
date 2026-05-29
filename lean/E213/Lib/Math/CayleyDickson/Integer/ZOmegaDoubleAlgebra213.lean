import E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble
import E213.Lib.Math.CayleyDickson.Integer.ZOmegaAlgebra213
import E213.Meta.Algebra213.CDDoubleStar
import E213.Meta.Algebra213.AlternativeNormed

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

/-! ## §6 — `IntegerNormed213 ZOmegaDouble` (Phase 3 completion)

The actual completion of Type C base layer migration: the generic
`IntegerNormed213.normSq_mul` will derive ZOmegaDouble's norm
multiplicativity via typeclass projection, replacing any future
hand-written `quad_norm`/`hurwitz_ring` proof at this layer. -/

/-- `ofInt n = ⟨ofInt n, 0⟩` — embed Int along the real axis
    (re-component = ZOmega real axis = Int axis). -/
def ofInt (n : Int) : ZOmegaDouble := ⟨ZOmega.ZOmega.ofInt n, 0⟩

private theorem ofInt_re (n : Int) : (ofInt n).re = ZOmega.ZOmega.ofInt n :=
  rfl

private theorem ofInt_im (n : Int) : (ofInt n).im = 0 := rfl

private theorem ofInt_inj' {a b : Int} (h : ofInt a = ofInt b) : a = b := by
  have h_re : (ofInt a).re = (ofInt b).re := congrArg ZOmegaDouble.re h
  exact @IntegerNormed213.ofInt_inj ZOmega.ZOmega _ a b h_re

/-- ZOmega ofInt's conjugate equals itself — real-axis embed is conj-fixed. -/
private theorem zomega_ofInt_conj_self (n : Int) :
    ZOmega.ZOmega.conj (ZOmega.ZOmega.ofInt n) = ZOmega.ZOmega.ofInt n := by
  apply ZOmega.ZOmega.ext
  · show n - 0 = n
    rw [Int.sub_eq_add_neg, Int.neg_zero, Int.add_zero]
  · show -(0 : Int) = 0; rfl

/-- `x - 0 = x` at the Ring213 level. -/
private theorem ring_sub_zero {α : Type} [Ring213 α] [Sub α]
    (h_sub : ∀ x y : α, x - y = x + -y) (x : α) : x - 0 = x := by
  have h_neg_zero : -(0 : α) = 0 :=
    ((Ring213.add_left_neg (0 : α)).symm.trans (Ring213.add_zero _)).symm
  rw [h_sub, h_neg_zero, Ring213.add_zero]

private theorem zomega_sub_def (x y : ZOmega.ZOmega) :
    x - y = x + -y := rfl

private theorem zomega_sub_zero (x : ZOmega.ZOmega) : x - 0 = x :=
  ring_sub_zero zomega_sub_def x

private theorem ofInt_add' (a b : Int) :
    ofInt a + ofInt b = ofInt (a + b) := by
  apply ZOmegaDouble.ext
  · show ZOmega.ZOmega.ofInt a + ZOmega.ZOmega.ofInt b
       = ZOmega.ZOmega.ofInt (a + b)
    exact @IntegerNormed213.ofInt_add ZOmega.ZOmega _ a b
  · show (0 : ZOmega.ZOmega) + 0 = 0
    apply ZOmega.ZOmega.ext
    · show (0 : Int) + 0 = 0; rfl
    · show (0 : Int) + 0 = 0; rfl

private theorem ofInt_mul' (a b : Int) :
    ofInt a * ofInt b = ofInt (a * b) := by
  apply ZOmegaDouble.ext
  · show ZOmega.ZOmega.ofInt a * ZOmega.ZOmega.ofInt b
         - ZOmega.ZOmega.conj 0 * 0
       = ZOmega.ZOmega.ofInt (a * b)
    have h_conj_zero : ZOmega.ZOmega.conj (0 : ZOmega.ZOmega) = 0 := by
      apply ZOmega.ZOmega.ext
      · show (0 : Int) - 0 = 0; rfl
      · show -(0 : Int) = 0; rfl
    rw [h_conj_zero, Ring213.zero_mul, zomega_sub_zero]
    exact @IntegerNormed213.ofInt_mul ZOmega.ZOmega _ a b
  · show (0 : ZOmega.ZOmega) * ZOmega.ZOmega.ofInt a
         + 0 * ZOmega.ZOmega.conj (ZOmega.ZOmega.ofInt b)
       = 0
    rw [Ring213.zero_mul, Ring213.zero_mul, Ring213.add_zero]

private theorem ofInt_central' (z : Int) (a : ZOmegaDouble) :
    ofInt z * a = a * ofInt z := by
  apply ZOmegaDouble.ext
  · show ZOmega.ZOmega.ofInt z * a.re - ZOmega.ZOmega.conj a.im * 0
       = a.re * ZOmega.ZOmega.ofInt z - ZOmega.ZOmega.conj 0 * a.im
    have h_conj_zero : ZOmega.ZOmega.conj (0 : ZOmega.ZOmega) = 0 := by
      apply ZOmega.ZOmega.ext
      · show (0 : Int) - 0 = 0; rfl
      · show -(0 : Int) = 0; rfl
    rw [Ring213.mul_zero, h_conj_zero, Ring213.zero_mul,
        zomega_sub_zero, zomega_sub_zero]
    exact @IntegerNormed213.ofInt_central ZOmega.ZOmega _ z a.re
  · show a.im * ZOmega.ZOmega.ofInt z + 0 * ZOmega.ZOmega.conj a.re
       = 0 * a.re + a.im * ZOmega.ZOmega.conj (ZOmega.ZOmega.ofInt z)
    rw [Ring213.zero_mul, Ring213.zero_mul,
        Ring213.add_zero, Ring213.zero_add,
        zomega_ofInt_conj_self]

/-- ZOmega `conj` is additive-negation-compatible: `conj(-a) = -conj a`.
    Direct computation on the (re, im) representation. -/
private theorem zomega_conj_neg (a : ZOmega.ZOmega) :
    ZOmega.ZOmega.conj (-a) = -(ZOmega.ZOmega.conj a) := by
  apply ZOmega.ZOmega.ext
  · show (-a).re - (-a).im = -(a.re - a.im)
    show -a.re - -a.im = -(a.re - a.im)
    rw [show (a.re - a.im) = a.re + -a.im from rfl,
        E213.Meta.Int213.neg_add,
        show -a.re - -a.im = -a.re + -(-a.im) from rfl,
        Int.neg_neg]
  · show -(-a).im = -(-a.im); rfl

/-- The actual core: `u * conj u = ofInt (normSq u)` for ZOmegaDouble.
    Componentwise via ZOmega `self_mul_conj` + commutativity + ofInt_add. -/
private theorem self_mul_conj' (u : ZOmegaDouble) :
    u * ZOmegaDouble.conj u = ofInt u.normSq := by
  apply ZOmegaDouble.ext
  · show u.re * ZOmega.ZOmega.conj u.re
         - ZOmega.ZOmega.conj (-u.im) * u.im
       = ZOmega.ZOmega.ofInt (ZOmega.ZOmega.normSq u.re
                              + ZOmega.ZOmega.normSq u.im)
    rw [zomega_conj_neg u.im,
        show ((-ZOmega.ZOmega.conj u.im) * u.im : ZOmega.ZOmega)
           = -(ZOmega.ZOmega.conj u.im * u.im) from Ring213.neg_mul _ _]
    -- Goal: u.re * conj u.re - -(conj u.im * u.im) = ofInt (normSq u.re + normSq u.im)
    show u.re * ZOmega.ZOmega.conj u.re
         + -(-(ZOmega.ZOmega.conj u.im * u.im))
       = ZOmega.ZOmega.ofInt (ZOmega.ZOmega.normSq u.re
                              + ZOmega.ZOmega.normSq u.im)
    rw [Ring213.neg_neg (ZOmega.ZOmega.conj u.im * u.im)]
    -- Goal: u.re * conj u.re + conj u.im * u.im = ofInt (...)
    have h1 : u.re * ZOmega.ZOmega.conj u.re
            = ZOmega.ZOmega.ofInt (ZOmega.ZOmega.normSq u.re) :=
      @IntegerNormed213.self_mul_conj ZOmega.ZOmega _ u.re
    have h2 : u.im * ZOmega.ZOmega.conj u.im
            = ZOmega.ZOmega.ofInt (ZOmega.ZOmega.normSq u.im) :=
      @IntegerNormed213.self_mul_conj ZOmega.ZOmega _ u.im
    have h3 : ZOmega.ZOmega.conj u.im * u.im = u.im * ZOmega.ZOmega.conj u.im :=
      @CommRing213.mul_comm ZOmega.ZOmega _ _ _
    rw [h1, h3, h2]
    exact @IntegerNormed213.ofInt_add ZOmega.ZOmega _ _ _
  · show -u.im * u.re + u.im * ZOmega.ZOmega.conj (ZOmega.ZOmega.conj u.re)
       = 0
    have h_cc : ZOmega.ZOmega.conj (ZOmega.ZOmega.conj u.re) = u.re :=
      @StarRing213.conj_conj ZOmega.ZOmega _ u.re
    rw [h_cc, Ring213.neg_mul,
        @CommRing213.mul_comm ZOmega.ZOmega _ u.im u.re,
        Ring213.add_left_neg]

/-- `ZOmega.normSq (-a) = ZOmega.normSq a` (inline copy of the
    public `zomega_normSq_neg` below — placed here so the IntegerNormed213
    instance can reference it). -/
private theorem zomega_normSq_neg_pre (a : ZOmega.ZOmega) :
    ZOmega.ZOmega.normSq (-a) = ZOmega.ZOmega.normSq a := by
  show (-a.re) * (-a.re) - (-a.re) * (-a.im) + (-a.im) * (-a.im)
     = a.re * a.re - a.re * a.im + a.im * a.im
  rw [E213.Meta.Int213.neg_mul a.re (-a.re),
      E213.Meta.Int213.mul_neg a.re a.re, Int.neg_neg,
      E213.Meta.Int213.neg_mul a.re (-a.im),
      E213.Meta.Int213.mul_neg a.re a.im, Int.neg_neg,
      E213.Meta.Int213.neg_mul a.im (-a.im),
      E213.Meta.Int213.mul_neg a.im a.im, Int.neg_neg]

/-- `ZOmega.normSq (conj a) = ZOmega.normSq a` (inline pre-version,
    via `self_mul_conj` + `mul_comm` over commutative ZOmega). -/
private theorem zomega_normSq_conj_pre (a : ZOmega.ZOmega) :
    ZOmega.ZOmega.normSq (ZOmega.ZOmega.conj a) = ZOmega.ZOmega.normSq a := by
  have h1 : a * ZOmega.ZOmega.conj a
          = ZOmega.ZOmega.ofInt (ZOmega.ZOmega.normSq a) :=
    @IntegerNormed213.self_mul_conj ZOmega.ZOmega _ a
  have h2 : ZOmega.ZOmega.conj a * ZOmega.ZOmega.conj (ZOmega.ZOmega.conj a)
          = ZOmega.ZOmega.ofInt (ZOmega.ZOmega.normSq (ZOmega.ZOmega.conj a)) :=
    @IntegerNormed213.self_mul_conj ZOmega.ZOmega _ (ZOmega.ZOmega.conj a)
  rw [ZOmega.ZOmega.conj_conj a] at h2
  have h_comm : a * ZOmega.ZOmega.conj a = ZOmega.ZOmega.conj a * a :=
    @CommRing213.mul_comm ZOmega.ZOmega _ a (ZOmega.ZOmega.conj a)
  exact (@IntegerNormed213.ofInt_inj ZOmega.ZOmega _ _ _
          (h1.symm.trans (h_comm.trans h2))).symm

/-- `normSq (conj u) = normSq u` for ZOmegaDouble — componentwise. -/
private theorem normSq_conj' (u : ZOmegaDouble) :
    ZOmegaDouble.normSq (ZOmegaDouble.conj u) = ZOmegaDouble.normSq u := by
  show ZOmega.ZOmega.normSq (ZOmega.ZOmega.conj u.re)
         + ZOmega.ZOmega.normSq (-u.im)
     = ZOmega.ZOmega.normSq u.re + ZOmega.ZOmega.normSq u.im
  rw [zomega_normSq_conj_pre u.re, zomega_normSq_neg_pre u.im]

/-- `conj (ofInt z) = ofInt z` for ZOmegaDouble.  conj ⟨ZOmega.ofInt z, 0⟩
    = ⟨ZOmega.conj (ZOmega.ofInt z), -0⟩ = ⟨ZOmega.ofInt z, 0⟩. -/
private theorem ofInt_conj' (z : Int) :
    ZOmegaDouble.conj (ofInt z) = ofInt z := by
  apply ext
  · show ZOmega.ZOmega.conj (ZOmega.ZOmega.ofInt z) = ZOmega.ZOmega.ofInt z
    exact @IntegerNormed213.ofInt_conj ZOmega.ZOmega _ z
  · show -(0 : ZOmega.ZOmega) = 0
    apply ZOmega.ZOmega.ext
    · show -(0 : Int) = 0; exact Int.neg_zero
    · show -(0 : Int) = 0; exact Int.neg_zero

/-- ★ ZOmegaDouble `IntegerNormed213` instance.  Generic
    `IntegerNormed213.normSq_mul` then derives ZOmegaDouble's norm
    multiplicativity via typeclass projection — no `quad_norm`,
    no polynomial expansion. -/
instance : IntegerNormed213 ZOmegaDouble where
  ofInt         := ofInt
  normSq        := ZOmegaDouble.normSq
  self_mul_conj := self_mul_conj'
  ofInt_mul     := ofInt_mul'
  ofInt_add     := ofInt_add'
  ofInt_central := ofInt_central'
  ofInt_inj     := ofInt_inj'
  normSq_conj   := normSq_conj'
  ofInt_conj    := ofInt_conj'

/-- ★ Concrete witness: generic `normSq_mul` derives ZOmegaDouble's
    norm multiplicativity via typeclass — no `quad_norm` or
    polynomial expansion at Int level. -/
theorem normSq_mul (u v : ZOmegaDouble) :
    ZOmegaDouble.normSq (u * v)
      = ZOmegaDouble.normSq u * ZOmegaDouble.normSq v :=
  IntegerNormed213.normSq_mul u v

/-! ## §7 — Phase 4 foundation: `normSq_conj` + reverse self_mul_conj

For the Moufang norm-collapse identity at the CDDouble layer
(ZOmegaQuad / Cayley analog), we need the "reverse-order" form
`conj a * a = ofInt (normSq a)`.  This follows from `self_mul_conj`
applied to `conj a` plus `normSq (conj a) = normSq a` (norm is
conj-invariant). -/

/-- ZOmega-level `normSq (conj a) = normSq a`.  Pure typeclass proof:
    use commutativity (ZOmega is CommRing213) to bridge between
    `a · conj a = ofInt (normSq a)` and `conj a · a = ofInt (normSq (conj a))`,
    then apply `ofInt_inj`.  Avoids any polynomial expansion of the
    `(a.re - a.im)² - …` form, and avoids the propext-leaking
    `simp only [neg_add, …]` path. -/
private theorem zomega_normSq_conj (a : ZOmega.ZOmega) :
    ZOmega.ZOmega.normSq (ZOmega.ZOmega.conj a)
      = ZOmega.ZOmega.normSq a := by
  have h1 : a * ZOmega.ZOmega.conj a
          = ZOmega.ZOmega.ofInt (ZOmega.ZOmega.normSq a) :=
    @IntegerNormed213.self_mul_conj ZOmega.ZOmega _ a
  have h_self_cc : ZOmega.ZOmega.conj a * ZOmega.ZOmega.conj (ZOmega.ZOmega.conj a)
                 = ZOmega.ZOmega.ofInt (ZOmega.ZOmega.normSq (ZOmega.ZOmega.conj a)) :=
    @IntegerNormed213.self_mul_conj ZOmega.ZOmega _ (ZOmega.ZOmega.conj a)
  have h_cc : ZOmega.ZOmega.conj (ZOmega.ZOmega.conj a) = a :=
    @StarRing213.conj_conj ZOmega.ZOmega _ a
  rw [h_cc] at h_self_cc
  -- h_self_cc : conj a * a = ofInt (normSq (conj a))
  have h_comm : a * ZOmega.ZOmega.conj a = ZOmega.ZOmega.conj a * a :=
    @CommRing213.mul_comm ZOmega.ZOmega _ a (ZOmega.ZOmega.conj a)
  -- Combine: ofInt (normSq a) = a * conj a = conj a * a = ofInt (normSq (conj a))
  have h_combined : ZOmega.ZOmega.ofInt (ZOmega.ZOmega.normSq a)
                  = ZOmega.ZOmega.ofInt (ZOmega.ZOmega.normSq (ZOmega.ZOmega.conj a)) :=
    h1.symm.trans (h_comm.trans h_self_cc)
  exact (@IntegerNormed213.ofInt_inj ZOmega.ZOmega _ _ _ h_combined).symm

/-- ZOmega-level `normSq (-a) = normSq a` — direct via `(-x)² = x²`. -/
private theorem zomega_normSq_neg (a : ZOmega.ZOmega) :
    ZOmega.ZOmega.normSq (-a) = ZOmega.ZOmega.normSq a := by
  show (-a.re) * (-a.re) - (-a.re) * (-a.im) + (-a.im) * (-a.im)
     = a.re * a.re - a.re * a.im + a.im * a.im
  rw [show ∀ x y : Int, (-x) * (-y) = x * y from fun x y => by
        rw [E213.Meta.Int213.neg_mul, E213.Meta.Int213.mul_neg,
            Int.neg_neg],
      show ∀ x y : Int, (-x) * (-y) = x * y from fun x y => by
        rw [E213.Meta.Int213.neg_mul, E213.Meta.Int213.mul_neg,
            Int.neg_neg],
      show ∀ x y : Int, (-x) * (-y) = x * y from fun x y => by
        rw [E213.Meta.Int213.neg_mul, E213.Meta.Int213.mul_neg,
            Int.neg_neg]]

/-- ★ ZOmegaDouble-level `normSq (conj u) = normSq u`.  Componentwise
    via the two ZOmega-level facts above. -/
theorem normSq_conj (u : ZOmegaDouble) :
    ZOmegaDouble.normSq (ZOmegaDouble.conj u) = ZOmegaDouble.normSq u := by
  show ZOmega.ZOmega.normSq (ZOmega.ZOmega.conj u.re)
         + ZOmega.ZOmega.normSq (-u.im)
     = ZOmega.ZOmega.normSq u.re + ZOmega.ZOmega.normSq u.im
  rw [zomega_normSq_conj u.re, zomega_normSq_neg u.im]

/-- ★ Reverse-order self_mul_conj for ZOmegaDouble:
    `conj a * a = ofInt (normSq a)`.  Derived from forward
    `self_mul_conj` applied to `conj a` + `normSq_conj`. -/
theorem conj_mul_self (u : ZOmegaDouble) :
    ZOmegaDouble.conj u * u = ofInt (ZOmegaDouble.normSq u) := by
  have h_forward : ZOmegaDouble.conj u * ZOmegaDouble.conj (ZOmegaDouble.conj u)
                 = ofInt (ZOmegaDouble.normSq (ZOmegaDouble.conj u)) :=
    @IntegerNormed213.self_mul_conj ZOmegaDouble _ (ZOmegaDouble.conj u)
  rw [show ZOmegaDouble.conj (ZOmegaDouble.conj u) = u from
        @StarRing213.conj_conj ZOmegaDouble _ u,
      normSq_conj u] at h_forward
  exact h_forward

/-! ## §8 — MoufangIntegerNormed213 ZOmegaDouble (associative layer, trivial Moufang)

ZOmegaDouble is associative (Ring213, Phase 2.5), so the Moufang
norm-collapse identity follows trivially from `mul_assoc` — one
re-association.  The same `ofInt_paren_central` follows from
`mul_assoc` + `ofInt_central`.

This validates `MoufangIntegerNormed213` at the associative
quaternion-like layer of Type C (analog: Type A Lipschitz).  The
truly-non-trivial Moufang case is one CD layer higher
(ZOmegaQuad / Cayley) where associativity is lost. -/

private theorem zod_moufang_norm (u v : ZOmegaDouble) :
    (u * v) * (ZOmegaDouble.conj v * ZOmegaDouble.conj u)
      = u * (v * ZOmegaDouble.conj v) * ZOmegaDouble.conj u := by
  -- LHS: ((uv)·v*)·u* = (u·(v·v*))·u* = (u·(vv*))·u* via mul_assoc twice
  -- RHS (Lean parses as): (u · (v·v*)) · u* — same.
  rw [← Ring213.mul_assoc (u * v) (ZOmegaDouble.conj v)
                          (ZOmegaDouble.conj u),
      Ring213.mul_assoc u v (ZOmegaDouble.conj v)]

private theorem zod_ofInt_paren_central (z : Int) (u : ZOmegaDouble) :
    u * ofInt z * ZOmegaDouble.conj u
      = ofInt z * (u * ZOmegaDouble.conj u) := by
  rw [show u * ofInt z = ofInt z * u from
        (@IntegerNormed213.ofInt_central ZOmegaDouble _ z u).symm,
      Ring213.mul_assoc (ofInt z) u (ZOmegaDouble.conj u)]

/-- ★ MoufangIntegerNormed213 ZOmegaDouble — associative Type C
    base layer.  Moufang trivially via mul_assoc.  Validates the
    new typeclass at the easy layer; ZOmegaQuad (next layer) is
    where Moufang becomes the genuine non-trivial ingredient. -/
instance : MoufangIntegerNormed213 ZOmegaDouble where
  ofInt               := ofInt
  normSq              := ZOmegaDouble.normSq
  self_mul_conj       := self_mul_conj'
  ofInt_mul           := ofInt_mul'
  ofInt_central       := ofInt_central'
  ofInt_inj           := ofInt_inj'
  moufang_norm        := zod_moufang_norm
  ofInt_paren_central := zod_ofInt_paren_central

/-- ★ Witness: ZOmegaDouble's `normSq_mul` derived via the
    generic `MoufangIntegerNormed213.normSq_mul` (alternative path
    to the `IntegerNormed213.normSq_mul` Phase 3 derivation). -/
theorem moufang_normSq_mul (u v : ZOmegaDouble) :
    ZOmegaDouble.normSq (u * v)
      = ZOmegaDouble.normSq u * ZOmegaDouble.normSq v :=
  MoufangIntegerNormed213.normSq_mul u v

end E213.Lib.Math.CayleyDickson.Integer.ZOmegaDouble
