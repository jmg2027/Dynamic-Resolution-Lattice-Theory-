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

**Status: cross-pair closed (∅-axiom).**  The `re`-component of
`CDDouble`-flexibility splits into `L1=R1` (base `flexible`), `L4=R3`
(`conj_sandwich`), and the **cross-pair**
`(conj d·b)·a + conj b·(d·a) = a·(conj b·d) + (a·conj d)·b` — the term
mixing *both* conjugates.  All three are now discharged: `flex_cross_pair`
proves the cross-pair from the alternating associator (`left_alt_polar` /
`right_alt_polar` give first-two / last-two antisymmetry, hence cyclic),
its scalar-slot vanishing (nuclearity), and its sign-flip under `conj`
(`conj x = ofInt (trace x) − x`); the residual collapses via the central
trace `conj d·b + conj b·d = ofInt (trace (conj d·b))`.

What remains for `cd_flexible` + the concrete `Cayley`/`Sedenion`
instances is *not* this crux but plumbing: a `Mul (CDDouble α)` over a
merely-`NonAssocStarRing213` base (the current instance needs base
associativity), or a direct concrete assembly of the `re`/`im` components
on `Sedenion` from `flex_cross_pair` + `conj_sandwich` + base `flexible`
once `FlexAlt213 Cayley` is registered.

Foundation lemmas (all PURE):
  * `conj_eq` — `conj a = ofInt (trace a) + -a`
  * `left_assoc_conj` / `right_assoc_conj` — `[conj b, b, X] = 0` etc.
  * `conj_sandwich` — `conj b·(b·conj c) = (conj c·conj b)·b`  (gives `L4=R3`)
  * `moufang_mid` — `(conj b·y)·b = conj b·(y·b)` (flexible + trace)
  * `flex_polar` / `left_alt_polar` / `right_alt_polar` — linearized
    flexibility / left- / right-alternativity (associator antisymmetry)
  * `flex_cross_pair` — the cross-pair (★ the former crux)
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

/-- Additive left-cancellation on the base. -/
private theorem add_lc (x p q : α) (h : x + p = x + q) : p = q := by
  have h2 : -x + (x + p) = -x + (x + q) := by rw [h]
  rwa [← NonAssocRing213.add_assoc, NonAssocRing213.add_left_neg,
       NonAssocRing213.zero_add, ← NonAssocRing213.add_assoc,
       NonAssocRing213.add_left_neg, NonAssocRing213.zero_add] at h2

/-- Pure additive reshuffle `(P+A)+(B+Q) = (P+Q)+(A+B)`. -/
private theorem reshuffle (P A B Q : α) :
    (P + A) + (B + Q) = (P + Q) + (A + B) := by
  rw [NonAssocRing213.add_assoc P A (B + Q),
      ← NonAssocRing213.add_assoc A B Q,
      NonAssocRing213.add_comm (A + B) Q,
      ← NonAssocRing213.add_assoc P Q (A + B)]

/-- **Linearized flexibility**: `(x·y)·z + (z·y)·x = x·(y·z) + z·(y·x)`.
    Polarize `flexible` at `x ↦ x + z`. -/
theorem flex_polar (x y z : α) :
    (x * y) * z + (z * y) * x = x * (y * z) + z * (y * x) := by
  have h := FlexAlt213.flexible (x + z) y
  rw [NonAssocRing213.add_mul x z y,
      NonAssocRing213.add_mul (x * y) (z * y) (x + z),
      NonAssocRing213.mul_add (x * y) x z,
      NonAssocRing213.mul_add (z * y) x z,
      NonAssocRing213.mul_add y x z,
      NonAssocRing213.add_mul x z (y * x + y * z),
      NonAssocRing213.mul_add x (y * x) (y * z),
      NonAssocRing213.mul_add z (y * x) (y * z),
      FlexAlt213.flexible x y, FlexAlt213.flexible z y,
      reshuffle (x * (y * x)) ((x * y) * z) ((z * y) * x) (z * (y * z)),
      reshuffle (x * (y * x)) (x * (y * z)) (z * (y * x)) (z * (y * z))] at h
  exact add_lc _ _ _ h

/-- **Linearized left alternativity**: the associator is antisymmetric in
    its first two arguments — `(x·w)·y + (w·x)·y = x·(w·y) + w·(x·y)`.
    Polarize `alt_left` at `x ↦ x + w`; the diagonal squares cancel via
    `alt_left x y` / `alt_left w y`. -/
theorem left_alt_polar (x w y : α) :
    (x * w) * y + (w * x) * y = x * (w * y) + w * (x * y) := by
  have h := FlexAlt213.alt_left (x + w) y
  rw [NonAssocRing213.add_mul x w (x + w),
      NonAssocRing213.mul_add x x w,
      NonAssocRing213.mul_add w x w,
      NonAssocRing213.add_mul (x * x + x * w) (w * x + w * w) y,
      NonAssocRing213.add_mul (x * x) (x * w) y,
      NonAssocRing213.add_mul (w * x) (w * w) y,
      NonAssocRing213.add_mul x w y,
      NonAssocRing213.add_mul x w (x * y + w * y),
      NonAssocRing213.mul_add x (x * y) (w * y),
      NonAssocRing213.mul_add w (x * y) (w * y),
      FlexAlt213.alt_left x y, FlexAlt213.alt_left w y,
      reshuffle (x * (x * y)) ((x * w) * y) ((w * x) * y) (w * (w * y)),
      reshuffle (x * (x * y)) (x * (w * y)) (w * (x * y)) (w * (w * y))] at h
  exact add_lc _ _ _ h

/-- **Linearized right alternativity**: the associator is antisymmetric in
    its last two arguments — `(x·y)·w + (x·w)·y = x·(y·w) + x·(w·y)`.
    Polarize `alt_right` at `y ↦ y + w`; the diagonal squares cancel via
    `alt_right x y` / `alt_right x w`. -/
theorem right_alt_polar (x y w : α) :
    (x * y) * w + (x * w) * y = x * (y * w) + x * (w * y) := by
  have h := FlexAlt213.alt_right x (y + w)
  rw [NonAssocRing213.add_mul y w (y + w),
      NonAssocRing213.mul_add y y w,
      NonAssocRing213.mul_add w y w,
      NonAssocRing213.mul_add x (y * y + y * w) (w * y + w * w),
      NonAssocRing213.mul_add x (y * y) (y * w),
      NonAssocRing213.mul_add x (w * y) (w * w),
      NonAssocRing213.mul_add x y w,
      NonAssocRing213.add_mul (x * y) (x * w) (y + w),
      NonAssocRing213.mul_add (x * y) y w,
      NonAssocRing213.mul_add (x * w) y w,
      FlexAlt213.alt_right x y, FlexAlt213.alt_right x w,
      reshuffle ((x * y) * y) (x * (y * w)) (x * (w * y)) ((x * w) * w),
      reshuffle ((x * y) * y) ((x * y) * w) ((x * w) * y) ((x * w) * w)] at h
  exact (add_lc _ _ _ h).symm

/-! ### The cross-pair via the associator

`assoc x y z := (x·y)·z − x·(y·z)` is **alternating** in an alternative
algebra: antisymmetric in the first two args (`left_alt_polar`), in the
last two (`right_alt_polar`), hence cyclic.  It is `0` on a scalar slot
(nuclearity) and flips sign under `conj` in any slot (`conj x = ofInt
(trace x) − x`).  These give the cross-pair directly. -/

/-- `a + b = 0 → a = -b` (additive inverse uniqueness). -/
private theorem eq_neg_of_add_eq_zero {a b : α} (h : a + b = 0) : a = -b := by
  calc a = a + 0 := (NonAssocRing213.add_zero a).symm
    _ = a + (b + -b) := by
          rw [NonAssocRing213.add_comm b (-b), NonAssocRing213.add_left_neg]
    _ = (a + b) + -b := (NonAssocRing213.add_assoc a b (-b)).symm
    _ = 0 + -b := by rw [h]
    _ = -b := NonAssocRing213.zero_add (-b)

/-- The associator `(x·y)·z − x·(y·z)`. -/
private def assoc (x y z : α) : α := (x * y) * z + -(x * (y * z))

/-- `x·(y·z) = (x·y)·z − assoc x y z` — the right-bracketing rewrite. -/
private theorem mul_right_eq (x y z : α) :
    x * (y * z) = (x * y) * z + -(assoc x y z) := by
  show x * (y * z) = (x * y) * z + -((x * y) * z + -(x * (y * z)))
  rw [NonAssocRing213.neg_add ((x * y) * z) (-(x * (y * z))), NonAssocRing213.neg_neg,
      ← NonAssocRing213.add_assoc ((x * y) * z) (-((x * y) * z)) (x * (y * z)),
      NonAssocRing213.add_comm ((x * y) * z) (-((x * y) * z)),
      NonAssocRing213.add_left_neg, NonAssocRing213.zero_add]

private theorem assoc_neg_l (x y z : α) : assoc (-x) y z = -(assoc x y z) := by
  show ((-x) * y) * z + -((-x) * (y * z)) = -((x * y) * z + -(x * (y * z)))
  rw [NonAssocRing213.neg_mul x y, NonAssocRing213.neg_mul (x * y) z,
      NonAssocRing213.neg_mul x (y * z), NonAssocRing213.neg_neg,
      NonAssocRing213.neg_add ((x * y) * z) (-(x * (y * z))), NonAssocRing213.neg_neg]

private theorem assoc_add_l (x x' y z : α) :
    assoc (x + x') y z = assoc x y z + assoc x' y z := by
  show ((x + x') * y) * z + -((x + x') * (y * z))
     = ((x * y) * z + -(x * (y * z))) + ((x' * y) * z + -(x' * (y * z)))
  rw [NonAssocRing213.add_mul x x' y, NonAssocRing213.add_mul (x * y) (x' * y) z,
      NonAssocRing213.add_mul x x' (y * z),
      NonAssocRing213.neg_add (x * (y * z)) (x' * (y * z))]
  exact NonAssocRing213.add_4_swap_mid ((x * y) * z) ((x' * y) * z)
          (-(x * (y * z))) (-(x' * (y * z)))

private theorem assoc_ofInt_l (n : Int) (y z : α) : assoc (ofInt n) y z = 0 := by
  show (ofInt n * y) * z + -(ofInt n * (y * z)) = 0
  rw [FlexAlt213.ofInt_nuc_l n y z, NonAssocRing213.add_comm,
      NonAssocRing213.add_left_neg]

private theorem assoc_conj_l (b y z : α) : assoc (conj b) y z = -(assoc b y z) := by
  rw [FlexAlt213.conj_eq b, assoc_add_l, assoc_ofInt_l, assoc_neg_l,
      NonAssocRing213.zero_add]

private theorem assoc_neg_m (x y z : α) : assoc x (-y) z = -(assoc x y z) := by
  show (x * (-y)) * z + -(x * ((-y) * z)) = -((x * y) * z + -(x * (y * z)))
  rw [NonAssocRing213.mul_neg x y, NonAssocRing213.neg_mul (x * y) z,
      NonAssocRing213.neg_mul y z, NonAssocRing213.mul_neg x (y * z),
      NonAssocRing213.neg_neg,
      NonAssocRing213.neg_add ((x * y) * z) (-(x * (y * z))), NonAssocRing213.neg_neg]

private theorem assoc_add_m (x y y' z : α) :
    assoc x (y + y') z = assoc x y z + assoc x y' z := by
  show (x * (y + y')) * z + -(x * ((y + y') * z))
     = ((x * y) * z + -(x * (y * z))) + ((x * y') * z + -(x * (y' * z)))
  rw [NonAssocRing213.mul_add x y y', NonAssocRing213.add_mul (x * y) (x * y') z,
      NonAssocRing213.add_mul y y' z, NonAssocRing213.mul_add x (y * z) (y' * z),
      NonAssocRing213.neg_add (x * (y * z)) (x * (y' * z))]
  exact NonAssocRing213.add_4_swap_mid ((x * y) * z) ((x * y') * z)
          (-(x * (y * z))) (-(x * (y' * z)))

private theorem assoc_ofInt_m (x : α) (n : Int) (z : α) : assoc x (ofInt n) z = 0 := by
  show (x * ofInt n) * z + -(x * (ofInt n * z)) = 0
  rw [FlexAlt213.ofInt_nuc_m n x z, NonAssocRing213.add_comm,
      NonAssocRing213.add_left_neg]

private theorem assoc_conj_m (x b z : α) : assoc x (conj b) z = -(assoc x b z) := by
  rw [FlexAlt213.conj_eq b, assoc_add_m, assoc_ofInt_m, assoc_neg_m,
      NonAssocRing213.zero_add]

/-- Associator antisymmetric in the first two slots. -/
private theorem assoc_swap12 (x y z : α) : assoc x y z = -(assoc y x z) := by
  apply eq_neg_of_add_eq_zero
  show ((x * y) * z + -(x * (y * z))) + ((y * x) * z + -(y * (x * z))) = 0
  rw [NonAssocRing213.add_4_swap_mid ((x * y) * z) (-(x * (y * z)))
        ((y * x) * z) (-(y * (x * z))),
      left_alt_polar x y z,
      NonAssocRing213.add_4_swap_mid (x * (y * z)) (y * (x * z))
        (-(x * (y * z))) (-(y * (x * z))),
      NonAssocRing213.add_comm (x * (y * z)) (-(x * (y * z))),
      NonAssocRing213.add_left_neg,
      NonAssocRing213.add_comm (y * (x * z)) (-(y * (x * z))),
      NonAssocRing213.add_left_neg, NonAssocRing213.add_zero]

/-- Associator antisymmetric in the last two slots. -/
private theorem assoc_swap23 (x y z : α) : assoc x y z = -(assoc x z y) := by
  apply eq_neg_of_add_eq_zero
  show ((x * y) * z + -(x * (y * z))) + ((x * z) * y + -(x * (z * y))) = 0
  rw [NonAssocRing213.add_4_swap_mid ((x * y) * z) (-(x * (y * z)))
        ((x * z) * y) (-(x * (z * y))),
      right_alt_polar x y z,
      NonAssocRing213.add_4_swap_mid (x * (y * z)) (x * (z * y))
        (-(x * (y * z))) (-(x * (z * y))),
      NonAssocRing213.add_comm (x * (y * z)) (-(x * (y * z))),
      NonAssocRing213.add_left_neg,
      NonAssocRing213.add_comm (x * (z * y)) (-(x * (z * y))),
      NonAssocRing213.add_left_neg, NonAssocRing213.add_zero]

/-- Associator is cyclic. -/
private theorem assoc_cyclic (x y z : α) : assoc x y z = assoc y z x := by
  rw [assoc_swap12 x y z, assoc_swap23 y x z, NonAssocRing213.neg_neg]

/-- **The Cayley-Dickson flexibility cross-pair** (the long-standing crux).
    `(conj d·b)·a + conj b·(d·a) = a·(conj b·d) + (a·conj d)·b`.

    The two `conj`-associator terms are equal by cyclic invariance
    (`hbal`), so they cancel; the residual `(conj d·b)·a + (conj b·d)·a =
    (a·conj b)·d + (a·conj d)·b` (`hCPprime`) holds because
    `conj d·b + conj b·d` is the central trace `ofInt (trace (conj d·b))`,
    and the matching expansion on the right cancels its associators
    (`hcross0`).  Pure FlexAlt213 algebra — no base associativity. -/
theorem flex_cross_pair (a b d : α) :
    (conj d * b) * a + conj b * (d * a)
      = a * (conj b * d) + (a * conj d) * b := by
  have hbal : assoc (conj b) d a = assoc a (conj b) d := by
    rw [assoc_conj_l b d a, assoc_conj_m a b d, assoc_cyclic a b d]
  have hcc : conj b * d = conj (conj d * b) := by
    rw [NonAssocStarRing213.conj_mul (conj d) b, NonAssocStarRing213.conj_conj d]
  have hz : conj d * b + conj b * d = ofInt (trace (conj d * b)) := by
    rw [hcc, FlexAlt213.self_add_conj (conj d * b)]
  have hcross0 :
      -(assoc a (conj d) b) + -(assoc a (conj b) d) = 0 := by
    rw [assoc_conj_m a d b, assoc_conj_m a b d, NonAssocRing213.neg_neg,
        NonAssocRing213.neg_neg, assoc_swap23 a d b, NonAssocRing213.add_left_neg]
  have hCPprime :
      (conj d * b) * a + (conj b * d) * a
        = (a * conj b) * d + (a * conj d) * b := by
    rw [← NonAssocRing213.add_mul (conj d * b) (conj b * d) a, hz,
        MoufangIntegerNormed213.ofInt_central (trace (conj d * b)) a, ← hz,
        NonAssocRing213.mul_add a (conj d * b) (conj b * d),
        mul_right_eq a (conj d) b, mul_right_eq a (conj b) d,
        NonAssocRing213.add_4_swap_mid ((a * conj d) * b) (-(assoc a (conj d) b))
          ((a * conj b) * d) (-(assoc a (conj b) d)),
        hcross0, NonAssocRing213.add_zero,
        NonAssocRing213.add_comm ((a * conj d) * b) ((a * conj b) * d)]
  rw [mul_right_eq (conj b) d a, mul_right_eq a (conj b) d, hbal,
      ← NonAssocRing213.add_assoc ((conj d * b) * a) ((conj b * d) * a)
        (-(assoc a (conj b) d)),
      hCPprime,
      NonAssocRing213.add_right_comm ((a * conj b) * d) ((a * conj d) * b)
        (-(assoc a (conj b) d))]

end FlexAlt213

end E213.Meta.Algebra213
