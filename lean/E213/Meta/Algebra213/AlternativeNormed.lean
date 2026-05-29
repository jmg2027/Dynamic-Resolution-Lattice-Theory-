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
