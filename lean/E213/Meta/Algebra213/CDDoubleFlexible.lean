import E213.Meta.Algebra213.CDDoubleMoufang

/-!
# Flexibility of `CDDouble` over a non-associative (alternative) base

`CDDouble α` is flexible — `(u·v)·u = u·(v·u)` — when the base `α` is an
**alternative** normed *-algebra with scalar (central + nuclear)
involution trace.  This is the layer past the octonion-analog where
`mul_assoc` is gone but flexibility survives (Sedenion = CDDouble Cayley).

The base class `FlexAlt213` bundles `MoufangIntegerNormed213` (norm) with
the trace polarization, reverse-norm `conj_mul_self`, scalar nuclearity,
left/right alternativity and base flexibility — all satisfied by Cayley.

**Status: foundation in place; `cd_flexible` pending the cross-pair.**
The `re`-component of `CDDouble`-flexibility splits (verified
numerically) into `L1=R1` (base `flexible`), `L4=R3` (`conj_sandwich`),
and the **cross-pair**
`(conj d·b)·a + conj b·(d·a) = a·(conj b·d) + (a·conj d)·b`.
The first two are discharged by the lemmas below; the cross-pair (which
mixes *both* conjugates) is the remaining crux — it needs linearized
flexibility plus double-trace bookkeeping and is not yet formalized.
Once it lands, `cd_flexible` + the `Cayley`/`Sedenion` instances follow.

Foundation lemmas (all PURE):
  * `conj_eq` — `conj a = ofInt (trace a) + -a`
  * `left_assoc_conj` / `right_assoc_conj` — `[conj b, b, X] = 0` etc.
  * `conj_sandwich` — `conj b·(b·conj c) = (conj c·conj b)·b`  (gives `L4=R3`)
  * `moufang_mid` — `(conj b·y)·b = conj b·(y·b)` (flexible + trace)
-/

namespace E213.Meta.Algebra213

open NonAssocRing213 NonAssocStarRing213 MoufangIntegerNormed213

/-- Alternative normed *-algebra with scalar-involution trace.  Carrier
    for the base of a flexible Cayley-Dickson double (Cayley etc.). -/
class FlexAlt213 (α : Type) extends MoufangIntegerNormed213 α where
  trace         : α → Int
  self_add_conj : ∀ a : α, a + conj a = ofInt (trace a)
  conj_mul_self : ∀ a : α, conj a * a = ofInt (normSq a)
  /-- `ofInt` scalars are left-nuclear. -/
  ofInt_nuc_l   : ∀ (z : Int) (a b : α), (ofInt z * a) * b = ofInt z * (a * b)
  /-- `ofInt` scalars are middle-nuclear. -/
  ofInt_nuc_m   : ∀ (z : Int) (a b : α), (a * ofInt z) * b = a * (ofInt z * b)
  /-- `ofInt` scalars are right-nuclear. -/
  ofInt_nuc_r   : ∀ (z : Int) (a b : α), a * (b * ofInt z) = (a * b) * ofInt z
  alt_left      : ∀ a b : α, (a * a) * b = a * (a * b)
  alt_right     : ∀ a b : α, a * (b * b) = (a * b) * b
  flexible      : ∀ a b : α, (a * b) * a = a * (b * a)

namespace FlexAlt213

variable {α : Type} [FlexAlt213 α]

/-- `conj a = ofInt (trace a) + -a`. -/
theorem conj_eq (a : α) : conj a = ofInt (trace a) + -a := by
  calc conj a
      = 0 + conj a := (NonAssocRing213.zero_add _).symm
    _ = (-a + a) + conj a := by rw [NonAssocRing213.add_left_neg]
    _ = -a + (a + conj a) := NonAssocRing213.add_assoc _ _ _
    _ = -a + ofInt (trace a) := by rw [self_add_conj]
    _ = ofInt (trace a) + -a := NonAssocRing213.add_comm _ _

/-- `[conj b, b, X] = 0`: `conj b · (b · X) = (conj b · b) · X`.
    Both sides reduce to `ofInt(trace b)·(b·X) − (b·b)·X` via `conj_eq`,
    `alt_left`, and left-nuclearity of the scalar. -/
theorem left_assoc_conj (b X : α) : conj b * (b * X) = (conj b * b) * X := by
  rw [conj_eq b, NonAssocRing213.add_mul (ofInt (trace b)) (-b) (b * X),
      NonAssocRing213.neg_mul b (b * X), ← FlexAlt213.alt_left b X,
      NonAssocRing213.add_mul (ofInt (trace b)) (-b) b,
      NonAssocRing213.neg_mul b b,
      NonAssocRing213.add_mul (ofInt (trace b) * b) (-(b * b)) X,
      NonAssocRing213.neg_mul (b * b) X,
      FlexAlt213.ofInt_nuc_l (trace b) b X]

/-- `[X, conj b, b] = 0`: `(X · conj b) · b = X · (conj b · b)`.
    Dual of `left_assoc_conj` via `alt_right` + middle-nuclearity. -/
theorem right_assoc_conj (X b : α) : (X * conj b) * b = X * (conj b * b) := by
  rw [conj_eq b, NonAssocRing213.mul_add X (ofInt (trace b)) (-b),
      NonAssocRing213.mul_neg X b,
      NonAssocRing213.add_mul (X * ofInt (trace b)) (-(X * b)) b,
      NonAssocRing213.neg_mul (X * b) b,
      FlexAlt213.ofInt_nuc_m (trace b) X b, ← FlexAlt213.alt_right X b,
      NonAssocRing213.add_mul (ofInt (trace b)) (-b) b,
      NonAssocRing213.neg_mul b b,
      NonAssocRing213.mul_add X (ofInt (trace b) * b) (-(b * b)),
      NonAssocRing213.mul_neg X (b * b)]

/-- Hurwitz "sandwich" with conjugates: `conj b·(b·conj c) = (conj c·conj b)·b`.
    Both collapse to `ofInt(normSq b)·conj c`. -/
theorem conj_sandwich (b c : α) :
    conj b * (b * conj c) = (conj c * conj b) * b := by
  rw [left_assoc_conj b (conj c), conj_mul_self b,
      ofInt_central (normSq b) (conj c), ← conj_mul_self b,
      ← right_assoc_conj (conj c) b]

/-- Middle-Moufang with a conjugate: `(conj b·y)·b = conj b·(y·b)`.
    From base `flexible` + central trace (`conj b = ofInt(trace b) − b`,
    the trace term is left-nuclear, the rest is `[b,y,b] = 0`). -/
theorem moufang_mid (b y : α) : (conj b * y) * b = conj b * (y * b) := by
  rw [conj_eq b, NonAssocRing213.add_mul (ofInt (trace b)) (-b) y,
      NonAssocRing213.neg_mul b y,
      NonAssocRing213.add_mul (ofInt (trace b) * y) (-(b * y)) b,
      NonAssocRing213.neg_mul (b * y) b,
      FlexAlt213.ofInt_nuc_l (trace b) y b, FlexAlt213.flexible b y,
      NonAssocRing213.add_mul (ofInt (trace b)) (-b) (y * b),
      NonAssocRing213.neg_mul b (y * b)]

end FlexAlt213

end E213.Meta.Algebra213
