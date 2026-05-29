import E213.Meta.Algebra213.Core
import E213.Meta.Int213.Core

/-!
# `MoufangIntegerNormed213` — Cayley-layer Hurwitz norm via typeclass

Non-associative extension of `IntegerNormed213`.  Drops `mul_assoc`
(Cayley/octonion-layer onward is non-associative) but adds the single
Moufang identity `(uv)(v*u*) = u(vv*)u*` required for the generic
Hurwitz norm-multiplicativity proof to go through without polynomial
expansion at Int level.

Replaces the `hurwitz_ring`-based 32-Int-var brute force
(`maxHeartbeats 4000000` in `CayleyHeavy.normSq_mul`) with a calc-chain
of 7 rewrites at the typeclass abstract layer.

Classical Hurwitz pattern at Cayley:

  N(uv) = (uv) · (uv)*                          self_mul_conj⁻¹
        = (uv) · (v* u*)                        conj anti-dist
        = u · (v · v*) · u*                     ★ Moufang
        = u · ofInt(N v) · u*                   self_mul_conj
        = ofInt(N v) · (u · u*)                 parenthesised central
        = ofInt(N v) · ofInt(N u)               self_mul_conj
        = ofInt(N v · N u) = ofInt(N u · N v)   ofInt_mul + Int.mul_comm

Only the Moufang step and the parenthesised-central step need to be
supplied per concrete instance.  At Cayley both can be discharged via
Lipschitz-level ring algebra (no Int polynomial blowup).
-/

namespace E213.Meta.Algebra213

/-- Non-associative ring: drops `mul_assoc` from `Ring213`,
    keeps everything else.  Carrier for CD layers from Cayley up. -/
class NonAssocRing213 (α : Type) extends Add α, Neg α, Mul α, Zero α where
  add_assoc    : ∀ a b c : α, a + b + c = a + (b + c)
  add_comm     : ∀ a b   : α, a + b = b + a
  add_zero     : ∀ a     : α, a + 0 = a
  add_left_neg : ∀ a     : α, -a + a = 0
  add_mul      : ∀ a b c : α, (a + b) * c = a * c + b * c
  mul_add      : ∀ a b c : α, a * (b + c) = a * b + a * c

/-- `NonAssocRing213` with anti-distributive star involution. -/
class NonAssocStarRing213 (α : Type) extends NonAssocRing213 α where
  conj      : α → α
  conj_conj : ∀ a   : α, conj (conj a) = a
  conj_add  : ∀ a b : α, conj (a + b) = conj a + conj b
  conj_mul  : ∀ a b : α, conj (a * b) = conj b * conj a

/-- Any `Ring213` is trivially a `NonAssocRing213` (just drop the
    `mul_assoc` axiom).  Parametric bridge. -/
instance instNonAssocRing213OfRing213 (α : Type) [Ring213 α] :
    NonAssocRing213 α where
  add_assoc    := Ring213.add_assoc
  add_comm     := Ring213.add_comm
  add_zero     := Ring213.add_zero
  add_left_neg := Ring213.add_left_neg
  add_mul      := Ring213.add_mul
  mul_add      := Ring213.mul_add

/-- Any `StarRing213` is trivially a `NonAssocStarRing213` (drop
    `mul_assoc`).  Parametric bridge. -/
instance instNonAssocStarRing213OfStarRing213 (α : Type) [StarRing213 α] :
    NonAssocStarRing213 α where
  conj      := StarRing213.conj
  conj_conj := StarRing213.conj_conj
  conj_add  := StarRing213.conj_add
  conj_mul  := StarRing213.conj_mul

namespace NonAssocRing213

variable {α : Type} [inst : NonAssocRing213 α]

/-- Generic `zero_add` (non-assoc). -/
theorem zero_add (a : α) : 0 + a = a := by
  rw [NonAssocRing213.add_comm, NonAssocRing213.add_zero]

/-- Generic `add_left_comm` (non-assoc). -/
theorem add_left_comm (a b c : α) : a + (b + c) = b + (a + c) := by
  rw [← NonAssocRing213.add_assoc, NonAssocRing213.add_comm a b,
      NonAssocRing213.add_assoc]

/-- Generic `add_right_comm` (non-assoc). -/
theorem add_right_comm (a b c : α) : a + b + c = a + c + b := by
  rw [NonAssocRing213.add_assoc, NonAssocRing213.add_comm b c,
      ← NonAssocRing213.add_assoc]

/-- Generic `add_4_swap_mid` (non-assoc). -/
theorem add_4_swap_mid (A X Y Z : α) : A + X + (Y + Z) = A + Y + (X + Z) := by
  rw [NonAssocRing213.add_assoc A X (Y + Z), add_left_comm X Y Z,
      ← NonAssocRing213.add_assoc A Y (X + Z)]

/-- Generic `zero_mul` (non-assoc — uses only distributivity). -/
theorem zero_mul (a : α) : (0 : α) * a = 0 := by
  have h1 : (0 : α) * a = (0 + 0) * a :=
    congrArg (· * a) (NonAssocRing213.add_zero 0).symm
  rw [NonAssocRing213.add_mul] at h1
  have h2 : -(0 * a) + (0 * a) = -(0 * a) + (0 * a + 0 * a) :=
    congrArg ((-(0*a)) + ·) h1
  rw [NonAssocRing213.add_left_neg, ← NonAssocRing213.add_assoc,
      NonAssocRing213.add_left_neg, zero_add] at h2
  exact h2.symm

/-- Generic `mul_zero` (non-assoc). -/
theorem mul_zero (a : α) : a * (0 : α) = 0 := by
  have h1 : a * (0 : α) = a * (0 + 0) :=
    congrArg (a * ·) (NonAssocRing213.add_zero 0).symm
  rw [NonAssocRing213.mul_add] at h1
  have h2 : -(a * 0) + (a * 0) = -(a * 0) + (a * 0 + a * 0) :=
    congrArg ((-(a*0)) + ·) h1
  rw [NonAssocRing213.add_left_neg, ← NonAssocRing213.add_assoc,
      NonAssocRing213.add_left_neg, zero_add] at h2
  exact h2.symm

/-- Generic `neg_mul` (non-assoc). -/
theorem neg_mul (a b : α) : (-a) * b = -(a * b) := by
  have h1 : (-a + a) * b = (0 : α) * b := by rw [NonAssocRing213.add_left_neg]
  rw [NonAssocRing213.add_mul, zero_mul] at h1
  have h2 : -(a * b) + ((-a) * b + a * b) = -(a * b) + 0 := by rw [h1]
  rw [← NonAssocRing213.add_assoc, NonAssocRing213.add_comm (-(a*b)) (-a*b),
      NonAssocRing213.add_assoc, NonAssocRing213.add_left_neg,
      NonAssocRing213.add_zero, NonAssocRing213.add_zero] at h2
  exact h2

/-- Generic `mul_neg` (non-assoc). -/
theorem mul_neg (a b : α) : a * (-b) = -(a * b) := by
  have h1 : a * (-b + b) = a * (0 : α) := by rw [NonAssocRing213.add_left_neg]
  rw [NonAssocRing213.mul_add, mul_zero] at h1
  have h2 : -(a * b) + (a * (-b) + a * b) = -(a * b) + 0 := by rw [h1]
  rw [← NonAssocRing213.add_assoc, NonAssocRing213.add_comm (-(a*b)) (a*(-b)),
      NonAssocRing213.add_assoc, NonAssocRing213.add_left_neg,
      NonAssocRing213.add_zero, NonAssocRing213.add_zero] at h2
  exact h2

/-- Generic `neg_neg` (non-assoc). -/
theorem neg_neg (a : α) : -(-a) = a := by
  have h1 : -(-a) + (-a) = 0 := NonAssocRing213.add_left_neg (-a)
  have h2 : -(-a) + (-a) + a = 0 + a := by rw [h1]
  rw [NonAssocRing213.add_assoc, NonAssocRing213.add_left_neg,
      NonAssocRing213.add_zero, zero_add] at h2
  exact h2

/-- Generic `neg_add` (non-assoc). -/
theorem neg_add (a b : α) : -(a + b) = -a + -b := by
  have h_inv : (a + b) + (-b + -a) = 0 := by
    rw [NonAssocRing213.add_assoc a b (-b + -a),
        ← NonAssocRing213.add_assoc b (-b) (-a),
        NonAssocRing213.add_comm b (-b), NonAssocRing213.add_left_neg b,
        zero_add, NonAssocRing213.add_comm a (-a),
        NonAssocRing213.add_left_neg a]
  have h2 : -(a + b) + ((a + b) + (-b + -a)) = -(a + b) + 0 := by rw [h_inv]
  rw [← NonAssocRing213.add_assoc, NonAssocRing213.add_left_neg,
      zero_add, NonAssocRing213.add_zero] at h2
  rw [← h2, NonAssocRing213.add_comm (-b) (-a)]

end NonAssocRing213

namespace NonAssocStarRing213

variable {α : Type} [inst : NonAssocStarRing213 α]

/-- `conj 0 = 0` (non-assoc *-ring). -/
theorem conj_zero : conj (0 : α) = 0 := by
  have h : conj (0 : α) = conj 0 + conj 0 := by
    rw [← NonAssocStarRing213.conj_add, NonAssocRing213.add_zero]
  have h2 : -conj (0 : α) + conj 0 = 0 := NonAssocRing213.add_left_neg _
  calc conj (0 : α)
      = 0 + conj 0 := (NonAssocRing213.zero_add _).symm
    _ = (-conj 0 + conj 0) + conj 0 := by rw [h2]
    _ = -conj 0 + (conj 0 + conj 0) := NonAssocRing213.add_assoc _ _ _
    _ = -conj 0 + conj 0 := by rw [← h]
    _ = 0 := h2

/-- `conj (-a) = -conj a` (non-assoc *-ring). -/
theorem conj_neg (a : α) : conj (-a) = -(conj a) := by
  have h0 : conj (-a) + conj a = 0 := by
    rw [← NonAssocStarRing213.conj_add, NonAssocRing213.add_left_neg, conj_zero]
  calc conj (-a)
      = conj (-a) + 0 := (NonAssocRing213.add_zero _).symm
    _ = conj (-a) + (conj a + -conj a) := by
          rw [NonAssocRing213.add_comm (conj a) (-conj a),
              NonAssocRing213.add_left_neg]
    _ = (conj (-a) + conj a) + -conj a := (NonAssocRing213.add_assoc _ _ _).symm
    _ = 0 + -conj a := by rw [h0]
    _ = -conj a := NonAssocRing213.zero_add _

end NonAssocStarRing213

/-- Integer-normed non-associative *-ring with Moufang norm-collapse.
    The single non-associative ingredient required for the generic
    Hurwitz proof is the **Moufang at the norm-collapse triple**:
    `(u·v) · (conj v · conj u) = u · (v · conj v) · conj u`. -/
class MoufangIntegerNormed213 (α : Type) extends NonAssocStarRing213 α where
  ofInt         : Int → α
  normSq        : α → Int
  self_mul_conj : ∀ a   : α, a * conj a = ofInt (normSq a)
  ofInt_mul     : ∀ a b : Int, ofInt a * ofInt b = ofInt (a * b)
  ofInt_central : ∀ (z : Int) (a : α), ofInt z * a = a * ofInt z
  ofInt_inj     : ∀ {a b : Int}, ofInt a = ofInt b → a = b
  /-- Moufang norm-collapse identity. -/
  moufang_norm  : ∀ u v : α,
      (u * v) * (conj v * conj u) = u * (v * conj v) * conj u
  /-- Parenthesised-central commute (derivable in any flexible ring
      with central `ofInt`).  Taken as instance-level input here. -/
  ofInt_paren_central : ∀ (z : Int) (u : α),
      u * ofInt z * conj u = ofInt z * (u * conj u)

namespace MoufangIntegerNormed213

variable {α : Type} [inst : MoufangIntegerNormed213 α]

/-- Generic Cayley-layer Hurwitz norm-multiplicativity:
    `|u·v|² = |u|² · |v|²`.  Proved entirely at the typeclass level
    via the calc-chain — no `hurwitz_ring`, no Int-polynomial blowup,
    no `maxHeartbeats` bump.  PURE. -/
theorem normSq_mul (u v : α) :
    inst.normSq (u * v) = inst.normSq u * inst.normSq v := by
  apply inst.ofInt_inj
  calc inst.ofInt (inst.normSq (u * v))
      = (u * v) * NonAssocStarRing213.conj (u * v) :=
        (inst.self_mul_conj _).symm
    _ = (u * v) * (NonAssocStarRing213.conj v
                    * NonAssocStarRing213.conj u) := by
        rw [NonAssocStarRing213.conj_mul]
    _ = u * (v * NonAssocStarRing213.conj v)
              * NonAssocStarRing213.conj u :=
        inst.moufang_norm u v
    _ = u * inst.ofInt (inst.normSq v) * NonAssocStarRing213.conj u := by
        rw [inst.self_mul_conj v]
    _ = inst.ofInt (inst.normSq v) * (u * NonAssocStarRing213.conj u) :=
        inst.ofInt_paren_central (inst.normSq v) u
    _ = inst.ofInt (inst.normSq v) * inst.ofInt (inst.normSq u) := by
        rw [inst.self_mul_conj u]
    _ = inst.ofInt (inst.normSq v * inst.normSq u) := inst.ofInt_mul _ _
    _ = inst.ofInt (inst.normSq u * inst.normSq v) := by
        rw [E213.Meta.Int213.mul_comm]

end MoufangIntegerNormed213

end E213.Meta.Algebra213
